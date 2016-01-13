////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').value('cgBusyDefaults',{
    message:'Running tactics',
    backdrop: true,
    templateUrl: 'partials/running-tactics-indicator.html'
});

angular.module('keymaerax.controllers').controller('ProofCtrl',
//    ['$http', '$rootScope', '$cookies', '$routeParams', '$q', '$uibModal', '$timeout', 'sequentProofData', 'spinnerService',
    function($scope, $rootScope, $http, $cookies, $routeParams, $q, $uibModal, $timeout, sequentProofData, spinnerService) {

  $http.get('proofs/user/' + $cookies.get('userId') + "/" + $routeParams.proofId).success(function(data) {
      $scope.proofId = data.id;
      $scope.proofName = data.name;
      $scope.modelId = data.model;
      $scope.closed = data.closed;
      $scope.stepCount= data.stepCount;
      $scope.date = data.date;
      sequentProofData.fetchAgenda($scope, $cookies.get('userId'), $scope.proofId);
  });
  $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});

  $rootScope.$on('agenda.isEmpty', function(event) {
    $http.get('proofs/user/' + $cookies.get('userId') + "/" + $routeParams.proofId + '/progress').success(function(data) {
      if (data.status == 'closed') {
        var modalInstance = $uibModal.open({
          templateUrl: 'partials/prooffinisheddialog.html',
          controller: 'ProofFinishedDialogCtrl',
          size: 'md',
          resolve: {
            proofId: function() { return $scope.proofId; },
            status: function() { return data.status }
          }
        });
      } else {
        // should never happen
        showMessage($uibModal, 'Empty agenda even though proof is not closed (' + data.status + ')')
      }
    });
  });

  $scope.runningTask = {
    nodeId: undefined,
    taskId: undefined,
    future: undefined,
    start: function(nodeId, taskId) {
      $scope.runningTask.nodeId = nodeId;
      $scope.runningTask.taskId = taskId;
      $scope.runningTask.future = $q.defer();
      $scope.runningTask.future.promise.then(
        /* future resolved */ function(taskId) {
          var userId = $cookies.get('userId');
          var proofId = $routeParams.proofId;
          $http.get('proofs/user/' + userId + '/' + proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/result')
            .then(function(response) {
              if (response.data.type === 'taskresult') {
                if ($scope.runningTask.nodeId === response.data.parent.id) {
                  sequentProofData.updateAgendaAndTree(response.data);
                } else {
                  showMessage($uibModal, "Unexpected tactic result, parent mismatch: " + " expected " +
                    $scope.runningTask.nodeId + " but got " + response.data.parent.id);
                }
              } else {
                showCaughtErrorMessage($uibModal, response.data, "Unable to fetch tactic result")
              }
            })
            .catch(function(err) {
              console.log('Interpreting error as no tactic being applicable: ' + err);
              //@todo send better error message, now we have to guess that probably the tactic was not applicable
              $rootScope.$emit('proof.message', "No axiom/tactic applicable to that formula");
            })
            .finally(function() { spinnerService.hide('tacticExecutionSpinner'); });
        },
        /* future rejected */ function(reason) {
          if (reason !== 'stopped') showMessage($uibModal, reason);
          spinnerService.hide('tacticExecutionSpinner');
        }
      );
      $scope.runningTask.poll(taskId);
    },
    poll: function(taskId) {
      var userId = $cookies.get('userId');
      var proofId = $routeParams.proofId;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/status')
        .then(function(response) {
          if (response.data.status === 'done') $scope.runningTask.future.resolve(taskId);
          else $timeout($scope.runningTask.poll(taskId), 500);
        })
        .catch(function(error) { $scope.runningTask.future.reject(error); });
    },
    stop: function() {
      var userId = $cookies.get('userId');
      var proofId = $routeParams.proofId;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + $scope.runningTask.nodeId + '/' + $scope.runningTask.taskId + '/stop')
        .then(function(response) { $scope.runningTask.future.reject('stopped'); })
        .catch(function(err) { $scope.runningTask.future.reject(err); });
    }
  }
});

angular.module('keymaerax.controllers').controller('RunningTacticsCtrl',
        function ($scope, $http, $cookies, Tactics) {
   $scope.abort = function() {
     // TODO implement
   }
});

angular.module('keymaerax.controllers').controller('TaskCtrl',
  function($rootScope, $scope, $http, $cookies, $routeParams, $q, $uibModal, Tactics, sequentProofData, spinnerService) {
    $scope.proofId = $routeParams.proofId;
    $scope.userId = $cookies.get('userId');
    $scope.agenda = sequentProofData.agenda;
    $scope.prooftree = sequentProofData.proofTree;

    // Watch running tactics
    $scope.$on('handleDispatchedTactics', function(event, tId) {
        // TODO create defer per tId
        $scope.defer = $q.defer();
        $scope.defer.promise.then(function (tacticResult) {
            if (tacticResult == 'Finished') {
                $scope.fetchAgenda($cookies.get('userId'), $scope.proofId)
            } else {
                // TODO not yet used, but could be used to report an error in running the tactic
            }
        });
        if(!$scope.watchedTactics) {
            $scope.watchedTactics = [];
        }
        if(!$scope.watchedTactics[tId]) {
            $scope.watchedTactics[tId] = true;
            (function poll(){
               setTimeout(function() {
                    $http.get('proofs/user/' + $cookies.get('userId') + '/' + $scope.proofId + '/dispatchedTactics/' + tId)
                            .success(function(data) {
                            if(data.errorThrown || data.tacticInstStatus == 'Error') {
                              $uibModal.open({
                                templateUrl: 'partials/error_alert.html',
                                controller: 'ErrorAlertCtrl',
                                size: 'md',
                                resolve: {
                                  action: function () { return "Tactic Execution Failed -- see server console output for a full tactic execution trace."; },
                                  error: function () { return data; }
                                }});
                            } else if (data.tacticInstStatus == 'Running') {
                                poll();
                            } else {
                                $scope.defer.resolve(data.tacticInstStatus)
                        }
                    })
              }, 1000);
            })();
        }
    });

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Subsection on tree operations.
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    $scope.editLabel = function(node) {
        node.editing = true
    }

    $scope.saveLabel = function(node) {
        //TODO save the label.... http.put....
        node.editing = false
    }

    $scope.cancelEditing = function(node) {
        node.editing = false
    }

    $scope.toggle = function(scope) { scope.toggle() } // do need this.

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Subsection on selecting tasks
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//    $scope.selectAgendaItem = function(item) {
//      if ($scope.agenda.selected !== undefined) {
//        var oldSelection = $.grep($scope.agenda.items, function(e) { e.id === $scope.agenda.selected });
//        for (var i = 0; i < oldSelection.length; i++) oldSelection[i].selected = false;
//      }
//      $scope.agenda.selected = item.id;
//      item.selected = true;
//    }
//    $scope.selectAgendaItemById = function(itemId) {
//      $scope.selectAgendaItem($scope.agenda.itemsMap[itemId]);
//    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Subsection on executing tasks
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Executes a combinator language term.
    $scope.execute = function() {
        var nodeId = this.selectedTask.nodeId;
        var uri = "/proofs/user/" + $cookies.get('userId') + "/" + $routeParams.proofId + "/nodes/" + nodeId + "/tactics/runTerm"
        var dataObj = {clTerm: $scope.clTerm};

        $http.post(uri, dataObj)
             .success(function(data) {
                if(data.errorThrown) {
                   $uibModal.open({
                      templateUrl: 'partials/error_alert.html',
                      controller: 'ErrorAlertCtrl',
                      size: 'md',
                      resolve: {
                          action: function () { return "running term"; },
                          error: function () { return data; }
                      }});
                }
                else {
//                    Tactics.getDispatchedTacticsNotificationService().broadcastDispatchedTerm(data.id)
                    $rootScope.$broadcast('handleDispatchedTerm', data.id);
                }
             });
    }
    $scope.$on('handleDispatchedTerm', function(event, tId) {
        // TODO create defer per tId
        $scope.defer = $q.defer();
        $scope.defer.promise.then(function (tacticResult) {
            if (tacticResult == 'Finished') {
                $scope.fetchAgenda($cookies.get('userId'), $scope.proofId)
            } else {
                // TODO not yet used, but could be used to report an error in running the tactic
            }
        });
        if(!$scope.watchedTerms) {
            $scope.watchedTerms = [];
        }
        if(!$scope.watchedTerms[tId]) {
            (function poll(){
               setTimeout(function() {
                    $http.get('proofs/user/' + $cookies.get('userId') + '/' + $scope.proofId + '/dispatchedTerm/' + tId)
                         .success(function(data) {
//                            if (data.status == 'Running' || data.errorThrown) { //Errors might be thrown if the term isn't created yet...
                            if(data.errorThrown) {
                              $uibModal.open({
                                templateUrl: 'partials/error_alert.html',
                                controller: 'ErrorAlertCtrl',
                                size: 'md',
                                resolve: {
                                  action: function () { return "Combinator Term Execution Failed -- see server console output for a full tactic execution trace."; },
                                  error: function () { return data; }
                                }});
                            } else if (data.tacticInstStatus == 'Running') {
                                poll();
                            } else {
                                $scope.defer.resolve(data.status)
                            }
                         })
                         .error(function(data) { poll(); })
              }, 1000);
            })();
            $scope.watchedTerms[tId] = true;
        }
    });

    $scope.fetchNodeInfo = function(dispatched) {
      var uri = "/proofs/user/" + $cookies.get('userId') + "/" + dispatched.proofId + "/agendaDetails/" + dispatched.nodeId;
      $http.get(uri)
        .success(function(data) {
        data.readOnly = true;
        $scope.selectedTask = data;
      });
    }

    // forward scope queries to global Agenda/Tactics model
//    $scope.$watch('agenda',
//        function (newTasks) { if (newTasks) Agenda.setTasks(newTasks); }
//    );
//    $scope.$watch('selectedTask',
//        function() { return Agenda.getSelectedTask(); },
//        function(t) { if (t) Agenda.setSelectedTask(t); }
//    );
//    $scope.$watch('selectedTaskId',
//        function() { return Agenda.getSelectedTaskId(); }
//    );
    $scope.$watch('dispatchedTactics',
        function() { return Tactics.getDispatchedTactics(); },
        function(tId) { Tactics.removeDispatchedTactics(tId); }
    );



    $scope.undoLastStep = function() {
      var nodeId = sequentProofData.agenda.selectedId();
      var node = sequentProofData.agenda.itemsMap[nodeId];
      var top = node.deduction.sections[0].path[0];
      var topParent = sequentProofData.proofTree.nodesMap[top].parent;
      sequentProofData.prune($scope.userId, $scope.proofId, topParent);
    };

    $scope.doTactic = function(formulaId, tacticId) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();

      var base = 'proofs/user/' + userId + '/' + proofId + '/' + nodeId;
      var uri = formulaId !== undefined ?  base + '/' + formulaId + '/doAt/' + tacticId : base + '/do/' + tacticId;
      spinnerService.show('tacticExecutionSpinner')
      $http.get(uri)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit("proof.message", err.data.textStatus);
        });
    }

    $scope.doInputTactic = function(formulaId, tacticId, input) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      $http.post('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/' + formulaId + '/doInputAt/' + tacticId, input)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit("proof.message", err.data.textStatus);
        });
    }

    $scope.doSearch = function(tacticId, where) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/doSearch' + where + '/' + tacticId)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit('proof.message', err.data.textStatus);
        });
    }

    $scope.doCustomTactic = function() {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();
      var tacticText = $scope.customTactic;
      spinnerService.show('tacticExecutionSpinner');
      $http.post('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/doCustomTactic', tacticText)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit('proof.message', err.data.textStatus);
        });
    }

    //Save a name edited using the inline editor.
    $scope.saveProofName = function(newName) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      $http.post("proofs/user/" + userId + "/" + proofId + "/name/" + newName, {})
    }

    $scope.saveTaskName = function(newName) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();
      $http.post("proofs/user/" + userId + "/" + proofId + "/" + nodeId + "/name/" + newName, {});
    }
  });

angular.module('keymaerax.controllers').controller('ProofFinishedDialogCtrl',
        function($scope, $http, $cookies, $modalInstance, proofId) {
    $scope.validatedProofStatus = 'closed'

    $scope.cancel = function() {
        $modalInstance.dismiss('cancel');
    };

    $scope.validateProof = function() {
      $http.get("/proofs/user/" + $cookies.get('userId') + "/" + proofId + "/validatedStatus").success(function(data) {
        $scope.validatedProofStatus = data.status
      });
    }
});
