////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('ProofCtrl',
//    ['$http', '$rootScope', '$cookies', '$routeParams', '$q', '$uibModal', '$timeout', 'sequentProofData', 'spinnerService',
    function($scope, $rootScope, $http, $cookies, $routeParams, $q, $uibModal, $timeout, sequentProofData, spinnerService) {

  $scope.userId = $cookies.get('userId');
  $scope.proofId = $routeParams.proofId;

  $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId).success(function(data) {
      $scope.proofId = data.id;
      $scope.proofName = data.name;
      $scope.modelId = data.model;
      $scope.closed = data.closed;
      $scope.stepCount= data.stepCount;
      $scope.date = data.date;
      sequentProofData.fetchAgenda($scope, $scope.userId, $scope.proofId);
  });
  $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});

  $scope.$on('agenda.isEmpty', function(event, data) {
    if (data.proofId == $scope.proofId) {
      // the current controller is responsible
      $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId + '/progress').success(function(data) {
        if (data.status == 'closed') {
          var modalInstance = $uibModal.open({
            templateUrl: 'partials/prooffinisheddialog.html',
            controller: 'ProofFinishedDialogCtrl',
            size: 'md',
            resolve: {
                userId: function() { return $scope.userId; },
                proofId: function() { return $scope.proofId; },
                proofName: function() { return $scope.proofName; }
            }
          });
        } else {
          // should never happen
          showMessage($uibModal, 'Empty agenda even though proof ' + $scope.proofId + ' is not closed (' + data.status + ')')
        }
      });
    }
  });

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
          $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/result')
            .then(function(response) {
              if (response.data.type === 'taskresult') {
                $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
                if ($scope.runningTask.nodeId === response.data.parent.id) {
                  sequentProofData.updateAgendaAndTree($scope.proofId, response.data);
                  sequentProofData.tactic.fetch($scope.userId, $scope.proofId);
                } else {
                  showMessage($uibModal, "Unexpected tactic result, parent mismatch: " + " expected " +
                    $scope.runningTask.nodeId + " but got " + response.data.parent.id);
                }
              } else {
                showCaughtErrorMessage($uibModal, response.data, "Unable to fetch tactic result")
              }
            })
            .catch(function(err) {
              $rootScope.$broadcast('proof.message', err.data);
            })
            .finally(function() { spinnerService.hide('tacticExecutionSpinner'); });
        },
        /* future rejected */ function(reason) {
          $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
          if (reason !== 'stopped') showMessage($uibModal, reason);
          spinnerService.hide('tacticExecutionSpinner');
        }
      );
      $scope.runningTask.poll(taskId);
    },
    poll: function(taskId) {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/status')
        .then(function(response) {
          if (response.data.lastStep !== undefined) $scope.runningTask.lastStep = response.data.lastStep.ruleName;
          if (response.data.status === 'done') $scope.runningTask.future.resolve(taskId);
          else $timeout($scope.runningTask.poll(taskId), 50);
        })
        .catch(function(error) { $scope.runningTask.future.reject(error); });
    },
    stop: function() {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.runningTask.nodeId + '/' + $scope.runningTask.taskId + '/stop')
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
    $scope.tactic = sequentProofData.tactic;
    sequentProofData.tactic.reset();

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
      var uri = "/proofs/user/" + $scope.userId + "/" + dispatched.proofId + "/agendaDetails/" + dispatched.nodeId;
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
        var nodeId = sequentProofData.agenda.selectedId();

        var uri = 'proofs/user/export/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId

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
      var nodeId = sequentProofData.agenda.selectedId();
      var base = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId;
      var uri = formulaId !== undefined ?  base + '/' + formulaId + '/doAt/' + tacticId : base + '/do/' + tacticId;
      spinnerService.show('tacticExecutionSpinner')
      $http.get(uri)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$broadcast("proof.message", err.data);
        });
    }

    $scope.doInputTactic = function(formulaId, tacticId, input) {
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      var base = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId;
      var uri = formulaId !== undefined ? base + '/' + formulaId + '/doInputAt/' + tacticId : base + '/doInput/' + tacticId
      $http.post(uri, input)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$broadcast("proof.message", err.data);
        });
    }

    $scope.doTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/' + fml1Id + '/' + fml2Id + '/doAt/' + tacticId)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
          $rootScope.$broadcast("proof.message", err.data);
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
          $rootScope.$broadcast('proof.message', err.data);
        });
    }

    $scope.onTacticScript = function(tacticText) {
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      $http.post('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/doCustomTactic', tacticText)
        .then(function(response) { $scope.runningTask.start(nodeId, response.data.taskId); })
        .catch(function(err) {
            if(err.data.errorThrown) {
                console.error("Error while executing custom tactic: " + err.data.textStatus);
                spinnerService.hide('tacticExecutionSpinner');
                //For custom tactics, show the tactic message and also the little yellow status bar.
                $rootScope.$broadcast('proof.message', err.data);
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

    $scope.executeTacticDiff = function() {
      $scope.onTacticScript($scope.tactic.tacticDiff);
    };

    $scope.simulate = function() {
      $uibModal.open({
        templateUrl: 'templates/simulator.html',
        controller: 'SimulatorCtrl',
        size: 'lg',
        resolve: {
          proofId: function() { return $scope.proofId; },
          userId: function() { return $scope.userId; },
          nodeId: function() { return sequentProofData.agenda.selectedId(); }
        }
      })
    }

    //@todo duplicate with sequent.js#getCounterExample
    $scope.getCounterExample = function() {
      spinnerService.show('counterExampleSpinner');
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.agenda.selectedId() + '/counterExample')
        .then(function(response) {
          var dialogSize = (response.data.result === 'cex.found') ? 'lg' : 'md';
          $uibModal.open({
            templateUrl: 'templates/counterExample.html',
            controller: 'CounterExampleCtrl',
            size: dialogSize,
            resolve: {
              result: function() { return response.data.result; },
              origFormula: function() { return response.data.origFormula; },
              cexFormula: function() { return response.data.cexFormula; },
              cexValues: function() { return response.data.cexValues; }
            }
          });
        })
        .finally(function() { spinnerService.hide('counterExampleSpinner'); });
    }

    $scope.downloadProblemSolution = function() {
        $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/download').success(function (data) {
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
      $http.post("proofs/user/" + $scope.userId + "/" + $scope.proofId + "/name/" + newName, {})
    }

    $scope.saveTaskName = function(newName) {
      var nodeId = sequentProofData.agenda.selectedId();
      $http.post("proofs/user/" + $scope.userId + "/" + $scope.proofId + "/" + nodeId + "/name/" + newName, {});
    }
  });

angular.module('keymaerax.controllers').controller('ProofFinishedDialogCtrl',
        function($scope, $http, $cookies, $uibModalInstance, FileSaver, Blob, userId, proofId, proofName) {

    // empty open proof until fetched from server
    $scope.proof = {
      proofId: '',
      isProved: false,
      tactic: '',
      provable: ''
    }

    // fetch proof
    $http.get("/proofs/user/" + userId + "/" + proofId + "/validatedStatus").then(function(response) {
      $scope.proof = response.data; // no transformation, pass on to HTML as is
    });

    // just close the dialog
    $scope.cancel = function() { $uibModalInstance.dismiss('cancel'); };

    // don't trust local cache, fetch new from server
    //@todo duplicate with proofs.js downloadTactic
    $scope.downloadTactic = function() {
      $http.get("/proofs/user/" + userId + "/" + proofId + "/extract").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, proofName + '.kyt');
      });
    }

    // don't trust local cache, fetch new from server
    //@todo duplicate with proofs.js downloadLemma
    $scope.downloadLemma = function() {
      $http.get("/proofs/user/" + userId + "/" + proofId + "/lemma").then(function(response) {
        var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
        FileSaver.saveAs(data, proofName + '.kyp');
      });
    }
});
