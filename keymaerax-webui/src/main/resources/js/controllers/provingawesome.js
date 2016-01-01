////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').value('cgBusyDefaults',{
    message:'Running tactics',
    backdrop: true,
    templateUrl: 'partials/running-tactics-indicator.html'
});

angular.module('keymaerax.controllers').controller('ProofCtrl', function($scope, $http, $cookies, $routeParams) {
  $http.get('proofs/user/' + $cookies.get('userId') + "/" + $routeParams.proofId).success(function(data) {
      $scope.proofId = data.id;
      $scope.proofName = data.name;
      $scope.modelId = data.model;
      $scope.closed = data.closed;
      $scope.stepCount= data.stepCount;
      $scope.date = data.date;
  });
  $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});

  //Save a name edited using the inline editor.
  $scope.saveProofName = function(newName) {
    $http.post("proofs/user/" + $cookies.get('userId') + "/" + $routeParams.proofId + "/name/" + newName, {})
  };
});

angular.module('keymaerax.controllers').controller('RunningTacticsCtrl',
        function ($scope, $http, $cookies, Tactics) {
   $scope.abort = function() {
     // TODO implement
   }
});

angular.module('keymaerax.controllers').controller('TaskCtrl',
  function($rootScope, $scope, $http, $cookies, $routeParams, $q, $uibModal, $sce, Tactics, sequentProofData) {
    $scope.proofId = $routeParams.proofId;
    $scope.userId = $cookies.get('userId');
    $scope.agenda = sequentProofData.agenda;
    $scope.prooftree = sequentProofData.proofTree;

    $scope.proof = {
        proofName: "blah"
    };
    //TODO: add functions  that allow renaming.

    $scope.$on('agendaIsEmpty', function() {
      $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId + '/progress').success(function(data) {
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
          showErrorMessage($uibModal, 'empty agenda even though proof is not closed (' + data.status + ')')
        }
      })
      .error(function() {
        showErrorMessage($uibModal, "error retrieving proof progress")
      })
    });

    sequentProofData.fetchAgenda($scope, $cookies.get('userId'), $scope.proofId);

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
             })
             .error(function() {
                showErrorMessage($uibModal, "encountered error during post on runTerm.")
             })
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
      })
      .error(function() {
        showErrorMessage($uibModal, "error encountered while trying to retrieve the proof history details.")
      })
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
      var nodeId = sequentProofData.agenda.selectedId;
      var node = sequentProofData.agenda.itemsMap[nodeId];
      var top = node.deduction.sections[0].path[0];
      var topParent = sequentProofData.proofTree.nodesMap[top].parent;
      sequentProofData.prune($scope.userId, $scope.proofId, nodeId, topParent);
    }

    $scope.doTactic = function(tacticId) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/do/' + tacticId).success(function(data) {
        if ($scope.nodeId === data.parent.id) {
          sequentProofData.updateAgendaAndTree(data);
        } else {
          console.log("Unexpected tactic result, parent mismatch: " + " expected " + $scope.nodeId + " but got " + data.parent.id)
        }
      });
    }

    $scope.doSearch = function(tacticId, where) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId;
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/doSearch' + where + '/' + tacticId).success(function(data) {
        if ($scope.nodeId === data.parent.id) {
          sequentProofData.updateAgendaAndTree(data);
        } else {
          console.log("Unexpected tactic result, parent mismatch: " + " expected " + $scope.nodeId + " but got " + data.parent.id)
        }
      });
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
      })
      .error(function() {
        showErrorMessage($uibModal, "error when validating proof")
      })
    }
});
