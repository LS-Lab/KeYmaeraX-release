////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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

  if(!$rootScope.agnedaIsEmptyEventIsDefined) {
      $rootScope.$on('agenda.isEmpty', function(event) {
          $rootScope.agnedaIsEmptyEventIsDefined = true;
          
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
  }

  $scope.runningTask = {
    nodeId: undefined,
    taskId: undefined,
    future: undefined,
    lastStep: undefined,
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
              $rootScope.$emit('proof.message', err.data.textStatus);
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
          if (response.data.lastStep !== undefined) $scope.runningTask.lastStep = response.data.lastStep.ruleName;
          if (response.data.status === 'done') $scope.runningTask.future.resolve(taskId);
          else $timeout($scope.runningTask.poll(taskId), 50);
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

angular.module('keymaerax.controllers').controller('TaskCtrl',
  function($rootScope, $scope, $http, $cookies, $routeParams, $q, $uibModal, Tactics, sequentProofData, spinnerService, derivationInfos) {
    $scope.proofId = $routeParams.proofId;
    $scope.userId = $cookies.get('userId');
    $scope.agenda = sequentProofData.agenda;
    $scope.prooftree = sequentProofData.proofTree;

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
    // Subsection on executing tasks
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

    $scope.fetchNodeInfo = function(dispatched) {
      var uri = "/proofs/user/" + $cookies.get('userId') + "/" + dispatched.proofId + "/agendaDetails/" + dispatched.nodeId;
      $http.get(uri)
        .success(function(data) {
        data.readOnly = true;
        $scope.selectedTask = data;
      });
    }

    $scope.undoLastStep = function() {
      var nodeId = sequentProofData.agenda.selectedId();
      var node = sequentProofData.agenda.itemsMap[nodeId];
      var top = node.deduction.sections[0].path[0];
      var topParent = sequentProofData.proofTree.nodesMap[top].parent;
      sequentProofData.prune($scope.userId, $scope.proofId, topParent);
    };

    $scope.exportSubgoal = function() {
        var proofId = $routeParams.proofId;
        var userId = $cookies.get('userId');
        var nodeId = sequentProofData.agenda.selectedId();

        var uri = 'proofs/user/export/' + userId + '/' + proofId + '/' + nodeId

        $http.get(uri)
            .then(function(response) {
                if(response.data.errorThrown) {
                    showCaughtErrorMessage($uibModal, response.data.message, response.data)
                }
                else {
                    showVerbatimMessage($uibModal, "Exported Subgoal", response.data.sequent);
                }
            })
    }

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
      var base = 'proofs/user/' + userId + '/' + proofId + '/' + nodeId;
      var uri = formulaId !== undefined ? base + '/' + formulaId + '/doInputAt/' + tacticId : base + '/doInput/' + tacticId
      $http.post(uri, input)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit("proof.message", err.data.textStatus);
        });
    }

    $scope.doTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      $http.get('proofs/user/' + userId + '/' + proofId + '/' + nodeId + '/' + fml1Id + '/' + fml2Id + '/doAt/' + tacticId)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$emit("proof.message", err.data.textStatus);
        });
    }

    $scope.doSearch = function(tacticId, where) { doSearchImpl(tacticId, where, undefined); }
    $scope.doSearchInput = function(tacticId, where, input) { doSearchImpl(tacticId, where, input); }
    doSearchImpl = function(tacticId, where, input) {
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      var uri = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/doSearch/' + where + '/' + tacticId
      var request = input !== undefined ? $http.post(uri, input) : $http.get(uri)
      request.then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
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
            if(err.data.errorThrown) {
                console.error("Error while executing custom tactic: " + err.data.textStatus);
                spinnerService.hide('tacticExecutionSpinner');
                //For custom tactics, show the tactic message and also the little yellow status bar.
                $rootScope.$emit('proof.message', err.data.textStatus);
                showCaughtTacticErrorMessage($uibModal, err.data.errorThrown, err.data.textStatus, err.data.tacticMsg)
            }
            else {
                console.error("Expected errorThrown field on error object but found something else: " + JSON.stringify(err))
            }
        });
    }

    $scope.openInputTacticDialog = function(tacticName, positionLocator) {
      var nodeId = sequentProofData.agenda.selectedId();
      var tactics = derivationInfos.byName($scope.userId, $scope.proofId, nodeId, tacticName)
        .then(function(response) {
          return response.data;
        });

      var modalInstance = $uibModal.open({
        templateUrl: 'templates/derivationInfoDialog.html',
        controller: 'DerivationInfoDialogCtrl',
        size: 'lg',
        resolve: {
          tactics: function() { return tactics; }
        }
      });

      modalInstance.result.then(function(derivation) {
        if (positionLocator === undefined) $scope.doInputTactic(undefined, tacticName, derivation);
        else $scope.doSearchInput(tacticName, positionLocator, derivation);
      })
    }

    $scope.openTacticEditor = function() {
      $uibModal.open({
        templateUrl: 'templates/tacticEditor.html',
        controller: 'TacticEditorCtrl',
        size: 'lg',
        resolve: {
          parentScope: function() { return $scope; }
        }
      })
    }

    $scope.simulate = function() {
      $uibModal.open({
        templateUrl: 'templates/simulator.html',
        controller: 'SimulatorCtrl',
        size: 'lg',
        resolve: {
          proofId: function() { return $routeParams.proofId; },
          userId: function() { return $cookies.get('userId'); },
          nodeId: function() { return sequentProofData.agenda.selectedId(); }
        }
      })
    }

    $scope.extractTactic = function() {
      var proofId = $routeParams.proofId;
      var userId = $cookies.get('userId');
      $http.get('proofs/user/' + userId + '/' + proofId + '/extract').success(function (data) {
        $uibModal.open({
          templateUrl: 'templates/tacticExtracted.html',
          controller: 'TacticExtractionCtrl',
          size: 'lg',
          resolve: {
            tacticText: function () {
              return data.tacticText;
            }
          }
        })
      })
    }

    $scope.downloadProblemSolution = function() {
        var proofId = $routeParams.proofId;
        var userId = $cookies.get('userId');
        $http.get('proofs/user/' + userId + '/' + proofId + '/download').success(function (data) {
            $uibModal.open({
                templateUrl: 'templates/tacticExtracted.html',
                controller: 'TacticExtractionCtrl',
                size: 'lg',
                resolve: {
                    tacticText: function () {
                        return data.fileContents;
                    }
                }
            })
        })
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
        function($scope, $http, $cookies, $uibModalInstance, proofId) {
    $scope.validatedProofStatus = 'closed'

    $scope.cancel = function() {
        $uibModalInstance.dismiss('cancel');
    };

    $scope.validateProof = function() {
      $http.get("/proofs/user/" + $cookies.get('userId') + "/" + proofId + "/validatedStatus").success(function(data) {
        $scope.validatedProofStatus = data.status
      });
    }
});
