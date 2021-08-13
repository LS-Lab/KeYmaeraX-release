////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('ProofCtrl',
    function($scope, $rootScope, $http, $route, $routeParams, $q, $uibModal, $timeout,
             sequentProofData, spinnerService, sessionService, derivationInfos) {

  $scope.userId = sessionService.getUser();
  $scope.proofId = $routeParams.proofId;
  sequentProofData.clear(); // @note we load a new proof, so clear agenda and proof tree

  $scope.runningRequest = {
    canceller: undefined
  }

  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Definitions.
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  $scope.sequentProofData = sequentProofData;
  $scope.definitions = undefined;
  $scope.$watch('sequentProofData.agenda.selectedTab', function(newValue, oldValue) {
    if (newValue != oldValue) {
      derivationInfos.sequentApplicableDefinitions($scope.userId, $scope.proofId, newValue).then(function(defs) {
        $scope.definitions = defs;
      });
    }
  });

  $scope.setDefinition = function(what, repl) {
    derivationInfos.setDefinition($scope.userId, $scope.proofId, what, repl);
  }

  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Explanations and help.
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  $scope.taskExplanation = {
    selection: "Rule",
    proofStateNodeId: undefined,
    proofStateNode: undefined
  };
  $scope.stepAxiom = function() {
    var selectedItem = sequentProofData.agenda.selectedItem()
    if (selectedItem) {
      var node = sequentProofData.proofTree.highlightedNode(); // set in sequentproof.js when hovering over sequent rule annotations
      if (!node) {
        // default: show last rule
        var topNodeId = selectedItem.deduction.sections[0].path[0];
        node = sequentProofData.proofTree.node(topNodeId);
      }
      if (node) {
        //@note add name to derivation so that we can display it as a step
        //@note unicode name as rule name
        var displayRuleName = node.rule ? node.rule.name : undefined;
        if (node.rule && node.rule.derivation) node.rule.derivation.name = displayRuleName;
        return [node.rule];
      }
      else return [];
    } else return [];
  }

  $scope.intro.introOptions = {
    steps: [
    {
        element: '#provingautomation',
        intro: "Automatic proof search. Unfold all operators automatically. Undo proof steps.",
        position: 'bottom'
    },
    {
        element: '#provingbasictactics',
        intro: "Basic tactics for propositional reasoning, hybrid programs, differential equations, and arithmetic are applied somewhere in the goal.",
        position: 'bottom'
    },
    {
        element: '#provingadditionaltools',
        intro: "Advanced proof tools (inspection, finding counterexamples, synthesizing assumptions).",
        position: 'bottom'
    },
    {
        element: '#provingtab',
        intro: "Each unfinished branch of a proof is displayed on its own tab",
        position: 'bottom'
    },
    {
        element: '#provingsequentview',
        intro: "The sequent view shows the current open proof goal at the top. Hover over formulas to find out where tactics can be applied. Left-click to apply default proof tactic. Right-click for a list of tactics to choose from. Hover over <code>&#8866;</code> for tactics that work on the entire sequent.",
        position: 'bottom'
    },
    {
        element: '#provingtactics',
        intro: "Proofs can be programmed in addition to clicking. Learn tactic programming by observing how the tactic is built while you click in the sequent above. Augment by typing into the text box. Get auto-completion by typing a formula number <code>1.</code> followed by a dot. Either re-run the entire tactic from scratch, or execute the modifications only.",
        position: 'bottom'
    }
    ],
    showStepNumbers: false,
    exitOnOverlayClick: true,
    exitOnEsc: true,
    nextLabel: 'Next', // could use HTML in labels
    prevLabel: 'Previous',
    skipLabel: 'Exit',
    doneLabel: 'Done'
  }

  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Object initialization from server.
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  $http.get("/config/tool").success(function(data) {
    $scope.tool = data.tool;
  });

  $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId).success(function(data) {
      $scope.proofId = data.id;
      $scope.proofName = data.name;
      $scope.modelId = data.model;
      $scope.closed = data.closed;
      $scope.stepCount= data.stepCount;
      $scope.date = data.date;
      if (data.stepCount == 0 && data.tactic !== undefined && data.tactic !== null) {
        spinnerService.show('tacticExecutionSpinner')
        $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/usedLemmas').then(function(response) {
          var usedLemmas = response.data.lemmas
          if (usedLemmas.length > 0) {
            var modalInstance = $uibModal.open({
              templateUrl: 'templates/modalMessageTemplate.html',
              controller: 'ModalMessageCtrl',
              size: 'md',
              resolve: {
                title: function() { return "Prove lemmas"; },
                message: function() { return "The proof uses " + usedLemmas.length + " unproved lemmas; do you want to check them now?"; },
                mode: function() { return "yesno"; }
              }
            });

            modalInstance.result.then(
              function() {
                // yes: prove all lemmas and on success prove theorem
                var lemmaLoader = $q.defer();
                usedLemmas.reduce(function(result, lemma) {
                  return result.then(function(response) {
                    spinnerService.show('tacticExecutionSpinner');
                    console.log("Opening lemma: " + lemma.name + "(" + lemma.proofId + ")");
                    return $http.get('proofs/user/' + $scope.userId + '/' + lemma.proofId);
                  }).then(function(response) {
                    spinnerService.show('tacticExecutionSpinner');
                    console.log("Proving lemma: " + lemma.name + "(" + lemma.proofId + ")");
                    return $http.get('proofs/user/' + $scope.userId + '/' + lemma.proofId + '/initfromtactic')
                  }).then(function(response) {
                    spinnerService.show('tacticExecutionSpinner');
                    return $scope.runningTask.start(lemma.proofId, '()', response.data.taskId, response.data.info,
                      function(taskResult) {
                        console.log("Done proving: " + lemma.name + "(" + lemma.proofId + ")")
                      },
                      function(taskError) {
                        console.log("Failed proving: " + lemma.name + "(" + lemma.proofId + ")")
                      },
                      undefined
                    );
                  }).then(function(response) {
                    spinnerService.show('tacticExecutionSpinner');
                    console.log("Validating proof: " + lemma.name + "(" + lemma.proofId + ")");
                    return $http.get("proofs/user/" + $scope.userId + "/" + lemma.proofId + "/validatedStatus");
                  }).then(function(response) {
                    console.log("Done validating proof: " + lemma.name + "(" + lemma.proofId + ")");
                  });
                }, lemmaLoader.promise).then(function(response) {
                  // finally open imported but not yet executed proof
                  console.log("Now proving theorem " + $scope.proofId);
                  spinnerService.show('tacticExecutionSpinner');
                  $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/initfromtactic')
                    .then(function(response) { $scope.runningTask.start($scope.proofId, '()', response.data.taskId, response.data.info,
                                               $scope.updateFreshProof, $scope.broadcastProofError, undefined); })
                    .catch(function(err) {
                      spinnerService.hide('tacticExecutionSpinner');
                      $rootScope.$broadcast("proof.message", err.data);
                    });
                });
                lemmaLoader.resolve();
              },
              function() {
                // no: open imported but not yet executed proof, run tactic with unproved lemmas remaining open
                $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/initfromtactic')
                  .then(function(response) { $scope.runningTask.start($scope.proofId, '()', response.data.taskId, response.data.info,
                                             $scope.updateFreshProof, $scope.broadcastProofError, undefined); })
                  .catch(function(err) {
                    spinnerService.hide('tacticExecutionSpinner');
                    $rootScope.$broadcast("proof.message", err.data);
                  });
              }
            );
          } else {
            $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/initfromtactic')
              .then(function(response) { $scope.runningTask.start($scope.proofId, '()', response.data.taskId, response.data.info,
                                         $scope.updateFreshProof, $scope.broadcastProofError, undefined); })
              .catch(function(err) {
                spinnerService.hide('tacticExecutionSpinner');
                $rootScope.$broadcast("proof.message", err.data);
              });
          }
        });
      } else {
        spinnerService.show('proofLoadingSpinner');
        sequentProofData.fetchAgenda($scope.userId, $scope.proofId);
        derivationInfos.sequentApplicableDefinitions($scope.userId, $scope.proofId, sequentProofData.agenda.selectedTab).then(function(defs) {
          $scope.definitions = defs;
        });
      }
  });
  $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});

  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof updates.
  ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  $scope.updateFreshProof = function(taskResult) {
    if (taskResult.type === 'taskresult') {
      if ($scope.proofId === taskResult.proofId) {
        if ($scope.runningTask.nodeId === taskResult.parent.id) {
          $route.reload();
        } else {
          showMessage($uibModal, "Unexpected tactic result, parent mismatch: expected " +
            $scope.runningTask.nodeId + " but got " + taskResult.parent.id);
        }
      } else {
        showMessage($uibModal, "Unexpected tactic result, proof mismatch: expected " +
          $scope.proofId + " but got " + taskResult.proofId);
      }
    } else {
      showCaughtErrorMessage($uibModal, taskResult, "Unable to fetch tactic result")
    }
  }

  $scope.updateMainProof = function(taskResult) {
    if (taskResult.type === 'taskresult') {
      if ($scope.proofId === taskResult.proofId) {
        if ($scope.runningTask.nodeId === taskResult.parent.id) {
          if (taskResult.newNodes.length >= 10) {
            var modalInstance = $uibModal.open({
              templateUrl: 'templates/modalMessageTemplate.html',
              controller: 'ModalMessageCtrl',
              size: 'md',
              resolve: {
                title: function() { return "Large proof step result"; },
                message: function() { return "Proof step resulted in " + taskResult.newNodes.length +
                  " additional proof goals. Do you want to keep all goals (displaying may take a long time)?"; },
                mode: function() { return "okcancel"; }
              }
            });
            modalInstance.result.then(
              function () {
                $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
                sequentProofData.updateAgendaAndTree($scope.userId, taskResult.proofId, taskResult);
                sequentProofData.tactic.fetch($scope.userId, taskResult.proofId);
              },
              function () {
                sequentProofData.undoLastProofStep($scope.userId, $scope.proofId, function() {
                  // nothing to do, didn't update proof tree and tactic yet
                });
              }
            );
          } else {
            $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
            sequentProofData.updateAgendaAndTree($scope.userId, taskResult.proofId, taskResult);
            sequentProofData.tactic.fetch($scope.userId, taskResult.proofId);
          }
        } else {
          showMessage($uibModal, "Unexpected tactic result, parent mismatch: expected " +
            $scope.runningTask.nodeId + " but got " + taskResult.parent.id);
        }
      } else {
        showMessage($uibModal, "Unexpected tactic result, proof mismatch: expected " +
          $scope.proofId + " but got " + taskResult.proofId);
      }
    } else {
      showCaughtErrorMessage($uibModal, taskResult, "Unable to fetch tactic result")
    }
  }

  $scope.broadcastProofError = function(err) {
    $rootScope.$broadcast('proof.message', {
      errorThrown: err.data.errorThrown,
      textStatus: err.data.textStatus,
      causeMsg: err.data.causeMsg,
      tacticMsg: err.data.tacticMsg,
      taskStepwiseRequest: $scope.runningTask.taskStepwiseRequest
    })
  }

  $scope.spinnerController = {
    close: function(name) {
      spinnerService.hide(name)
    }
  }

  $scope.runningTask = {
    proofId: undefined,
    nodeId: undefined,
    taskId: undefined,
    taskStepwiseRequest: undefined,
    future: undefined,
    lastStep: undefined,
    info: undefined,
    start: function(proofId, nodeId, taskId, info, onTaskComplete, onTaskError, taskStepwiseRequest) {
      $scope.runningTask.proofId = proofId;
      $scope.runningTask.nodeId = nodeId;
      $scope.runningTask.taskId = taskId;
      $scope.runningTask.info = info;
      $scope.runningTask.taskStepwiseRequest = taskStepwiseRequest;
      $scope.runningTask.future = $q.defer();
      var runningTaskPromise = $scope.runningTask.future.promise.then(
        /* future resolved */ function(taskId) {
          return $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/result')
            .then(function(response) { onTaskComplete(response.data); })
            .catch(function(err) { onTaskError(err); })
            .finally(function() { spinnerService.hide('tacticExecutionSpinner'); });
        },
        /* future rejected */ function(reason) {
          $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
          spinnerService.hide('tacticExecutionSpinner');
          if (reason !== 'stopped') showMessage($uibModal, reason);
          else if (sequentProofData.agenda.items().length <= 0) sequentProofData.fetchAgenda($scope.userId, $scope.runningTask.proofId);
          return reason;
        }
      );
      $scope.runningTask.poll(taskId, 0);
      return runningTaskPromise;
    },
    poll: function(taskId, elapsed) {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/status')
        .then(function(response) {
          if (response.data.currentStep) $scope.runningTask.currentStep = response.data.currentStep;
          if (response.data.progress) $scope.runningTask.progress = response.data.progress;
          if (response.data.status === 'done') $scope.runningTask.future.resolve(taskId);
          else if (elapsed <= 20) $timeout(function() { $scope.runningTask.poll(taskId, elapsed+1); }, 50);
          else $timeout(function() { $scope.runningTask.poll(taskId, elapsed); }, 1000);
        })
        .catch(function(error) { $scope.runningTask.future.reject(error); });
    },
    stop: function() {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + $scope.runningTask.taskId + '/stop')
        .then(function(response) {
          if ($scope.runningTask.future) $scope.runningTask.future.reject('stopped');
        })
        .catch(function(err) {
          if ($scope.runningTask.future) $scope.runningTask.future.reject(err);
        });
    }
  }

  $scope.toggleTacticVerbosity = function() {
    sequentProofData.tactic.verbose = !sequentProofData.tactic.verbose;
    sequentProofData.tactic.fetch($scope.userId, $scope.proofId);
  }
});

angular.module('keymaerax.controllers').controller('InitBrowseProofCtrl',
    function($scope, $rootScope, $http, $routeParams, $q, $uibModal, $timeout, sequentProofData, spinnerService, sessionService) {

  $scope.proofId = $routeParams.proofId;
  $scope.userId = sessionService.getUser();
  sequentProofData.clear(); // @note we load a new proof, so clear agenda and proof tree

  $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId).success(function(data) {
      $scope.proofId = data.id;
      $scope.proofName = data.name;
      $scope.modelId = data.model;
      $scope.closed = data.closed;
      $scope.stepCount= data.stepCount;
      $scope.date = data.date;
      if (data.stepCount == 0 && data.tactic !== undefined && data.tactic !== null) {
        // imported but not yet executed proof
        spinnerService.show('tacticExecutionSpinner')
        $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/initfromtactic')
          .then(function(response) { $scope.runningTask.start($scope.proofId, '()', response.data.taskId,
                                     $scope.updateFreshProof, $scope.broadcastProofError, undefined); })
          .catch(function(err) {
            spinnerService.hide('tacticExecutionSpinner');
            $rootScope.$broadcast("proof.message", err.data);
          });
      } else {
        sequentProofData.fetchBrowseAgenda($scope.userId, $scope.proofId);
      }
  });
  $scope.$emit('routeLoaded', {theview: 'proofs/:proofId/browse'});

  $scope.updateFreshProof = function(taskResult) {
    if (taskResult.type === 'taskresult') {
      if ($scope.proofId === taskResult.proofId) {
        if ($scope.runningTask.nodeId === taskResult.parent.id) {
          sequentProofData.fetchBrowseAgenda($scope.userId, $scope.proofId);
        } else {
          showMessage($uibModal, "Unexpected tactic result, parent mismatch: expected " +
            $scope.runningTask.nodeId + " but got " + taskResult.parent.id);
        }
      } else {
        showMessage($uibModal, "Unexpected tactic result, proof mismatch: expected " +
          $scope.proofId + " but got " + taskResult.proofId);
      }
    } else {
      showCaughtErrorMessage($uibModal, taskResult, "Unable to fetch tactic result")
    }
  }

  $scope.broadcastProofError = function(err) {
    $rootScope.$broadcast('proof.message', {
      errorThrown: err.data.errorThrown,
      textStatus: err.data.textStatus,
      causeMsg: err.data.causeMsg,
      tacticMsg: err.data.tacticMsg,
      taskStepwiseRequest: $scope.runningTask.taskStepwiseRequest
    })
  }

  $scope.spinnerController = {
    close: function(name) {
      spinnerService.hide(name)
    }
  }

  //@todo task service (see also ProofCtrl)
  $scope.runningTask = {
    proofId: undefined,
    nodeId: undefined,
    taskId: undefined,
    taskStepwiseRequest: undefined,
    future: undefined,
    currentStep: undefined,
    progress: [],
    info: undefined,
    start: function(proofId, nodeId, taskId, info, onTaskComplete, onTaskError, taskStepwiseRequest) {
      $scope.runningTask.proofId = proofId;
      $scope.runningTask.nodeId = nodeId;
      $scope.runningTask.taskId = taskId;
      $scope.runningTask.info = info;
      $scope.runningTask.taskStepwiseRequest = taskStepwiseRequest;
      $scope.runningTask.future = $q.defer();
      var runningTaskPromise = $scope.runningTask.future.promise.then(
        /* future resolved */ function(taskId) {
          return $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/result')
            .then(function(response) { onTaskComplete(response.data); })
            .catch(function(err) { onTaskError(err); })
            .finally(function() { spinnerService.hide('tacticExecutionSpinner'); });
        },
        /* future rejected */ function(reason) {
          $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
          spinnerService.hide('tacticExecutionSpinner');
          if (reason !== 'stopped') showMessage($uibModal, reason);
          else if (sequentProofData.agenda.items().length <= 0) sequentProofData.fetchAgenda($scope.userId, $scope.runningTask.proofId);
          return reason;
        }
      );
      $scope.runningTask.poll(taskId, 0);
      return runningTaskPromise;
    },
    poll: function(taskId, elapsed) {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + taskId + '/status')
        .then(function(response) {
          if (response.data.currentStep) $scope.runningTask.currentStep = response.data.currentStep;
          if (response.data.progress) $scope.runningTask.progress = response.data.progress;
          if (response.data.status === 'done') $scope.runningTask.future.resolve(taskId);
          else if (elapsed <= 20) $timeout(function() { $scope.runningTask.poll(taskId, elapsed+1); }, 50);
          else $timeout(function() { $scope.runningTask.poll(taskId, elapsed); }, 1000);
        })
        .catch(function(error) { $scope.runningTask.future.reject(error); });
    },
    stop: function() {
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.runningTask.proofId + '/' + $scope.runningTask.nodeId + '/' + $scope.runningTask.taskId + '/stop')
        .then(function(response) { $scope.runningTask.future.reject('stopped'); })
        .catch(function(err) { $scope.runningTask.future.reject(err); });
    }
  }
});

angular.module('keymaerax.controllers').controller('BrowseProofCtrl',
    function($scope, $rootScope, $http, $routeParams, $q, $uibModal, $timeout, sequentProofData, spinnerService, sessionService) {

  $scope.proofId = $routeParams.proofId;
  $scope.userId = sessionService.getUser();
  $scope.agenda = sequentProofData.agenda;
  $scope.prooftree = sequentProofData.proofTree;
});

angular.module('keymaerax.controllers').controller('TaskCtrl',
  function($rootScope, $scope, $http, $route, $routeParams, $q, $uibModal, $location, $timeout,
           Tactics, sequentProofData, spinnerService,
           derivationInfos, sessionService, Poller, FileSaver, Proofs) {
    $scope.proofId = $routeParams.proofId;
    $scope.userId = sessionService.getUser();
    $scope.agenda = sequentProofData.agenda;
    $scope.prooftree = sequentProofData.proofTree;
    $scope.tactic = sequentProofData.tactic;
    $scope.backend = {
      busypoller: Poller.poll("tools/vitalSigns", 2000 /*2s*/),
      connectionTestResult: undefined
    };

    $scope.menu = {
      hpmenu: {
        kind: 'box'
      },
      odemenu: {
        kind: 'box'
      }
    }

    sequentProofData.tactic.reset();

    $scope.$on('$destroy', function() {
        $scope.backend.busypoller.data.cancel = true;
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

    $scope.undoLastProofStep = function() {
      sequentProofData.undoLastProofStep($scope.userId, $scope.proofId, function() {
        $scope.resetProof();
        // undo may reload entirely
        //@todo refreshes to empty conjecture
        $scope.tactic = sequentProofData.tactic;
        $scope.agenda = sequentProofData.agenda;
        $scope.proofTree = sequentProofData.proofTree;
      });
    };

    $scope.setFormulaMode = function(mode) {
      sequentProofData.formulas.mode = mode;
    }

    $scope.getFormulaMode = function() {
      return sequentProofData.formulas.mode;
    }

    $scope.stickyEdit = function() {
      return sequentProofData.formulas.mode == 'edit' && sequentProofData.formulas.stickyEdit;
    }

    $scope.setStickyEdit = function(stickyEdit) {
      sequentProofData.formulas.stickyEdit = stickyEdit;
    }

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

    $scope.stepwiseTactic = function(stepwiseRequest) {
      spinnerService.show('magnifyingglassSpinner')
      $http(stepwiseRequest).then(function(response) {
        var onStepwiseTaskComplete = function(taskResult) {
          $http.get('proofs/user/' + $scope.userId + '/' + taskResult.proofId + '/trace').then(function(response) {
            var modalInstance = $uibModal.open({
              templateUrl: 'templates/magnifyingglass.html',
              controller: 'MagnifyingGlassDialogCtrl',
              scope: $scope,
              size: 'magnifyingglass',
              resolve: {
                proofInfo: function() {
                  return {
                    userId: $scope.userId,
                    proofId: "", //@note irrelevant for dialog
                    nodeId: "",  //@note irrelevant for dialog
                    detailsProofId: response.data.detailsProofId
                  }
                },
                tactic: function() { return response.data.tactic; },
                proofTree: function() { return response.data.proofTree; },
                openGoals: function() { return response.data.openGoals; }
              }
            });
          })
          .finally(function() {
            spinnerService.hide('magnifyingglassSpinner');
          });
        }

        var onStepwiseTaskError = function(err) {
          spinnerService.hide('magnifyingglassSpinner');
          $uibModal.open({
            templateUrl: 'templates/modalMessageTemplate.html',
            controller: 'ModalMessageCtrl',
            size: 'sm',
            resolve: {
              title: function() { return "Immediate error"; },
              message: function() { return "Tactic did not make progress at all"; },
              mode: function() { return "ok"; }
            }
          });
        }

        $scope.runningTask.start(response.data.proofId, response.data.nodeId, response.data.taskId, response.data.info,
          onStepwiseTaskComplete, onStepwiseTaskError);
      })
      .catch(function(err) {
        spinnerService.hide('magnifyingglassSpinner');
        showCaughtTacticErrorMessage($uibModal, err.data.errorThrown, err.data.textStatus, err.data.tacticMsg);
      });
    }

    $scope.openProofstepBrowser = function(tab) {
      var prevMode = sequentProofData.formulas.mode;
      sequentProofData.formulas.mode = 'select';
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/lemmabrowserdialog.html',
        controller: 'LemmaBrowserCtrl',
        size: 'lg',
        resolve: {
          userId: function() { return $scope.userId; },
          proofId: function() { return $scope.proofId; },
          nodeId: function() { return sequentProofData.agenda.selectedId(); },
          formulaId: function() { return undefined; },
          formula: function() { return undefined; },
          tab: function() { return tab; }
        }
      });
      modalInstance.result.then(
        function (tactic) {
          sequentProofData.formulas.mode = prevMode;
          if (tactic.input) $scope.doInputTactic(tactic.formulaId, tactic.tacticId, tactic.input);
          else $scope.doTactic(tactic.formulaId, tactic.tacticId);
        },
        function () { sequentProofData.formulas.mode = prevMode; }
      );
    }

    $scope.doTactic = function(formulaId, tacticId) {
      var nodeId = sequentProofData.agenda.selectedId();
      var node = sequentProofData.proofTree.node(nodeId);
      var selected = sequentProofData.formulas.selectedIn(node.getSequent());
      if (selected.length >= node.getSequent().ante.length + node.getSequent().succ.length) selected = undefined;
      var base = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId;
      if (selected) {
        $scope.onTacticScript(tacticId + (formulaId ? '(' + formulaId + ')' : '') + ' using "' + selected.join('::') +
          (selected.length > 0 ? '::' : '') + 'nil"', false)
      } else {
        var uri = formulaId !== undefined ?  base + '/' + formulaId + '/doAt/' + tacticId : base + '/do/' + tacticId;
        var stepwise = { method: 'GET', url: uri + '?stepwise=true' };
        spinnerService.show('tacticExecutionSpinner')
        $http.get(uri + '?stepwise=false')
          .then(function(response) { $scope.runningTask.start($scope.proofId, nodeId, response.data.taskId, response.data.info, $scope.updateMainProof, $scope.broadcastProofError, stepwise); })
          .catch(function(err) {
            spinnerService.hide('tacticExecutionSpinner');
            $rootScope.$broadcast("proof.message", err.data);
          });
      }
    }

    $scope.doInputTactic = function(formulaId, tacticId, input) {
      var nodeId = sequentProofData.agenda.selectedId();
      var node = sequentProofData.proofTree.node(nodeId);
      var selected = sequentProofData.formulas.selectedIn(node.getSequent());
      if (selected.length >= node.getSequent().ante.length + node.getSequent().succ.length) selected = undefined;
      spinnerService.show('tacticExecutionSpinner');
      var base = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId;
      if (selected) {
        var args = input.map(function(e) { return '"' + e.value.replace("\"", "\\\"") + '"'; }).join(',');
        $scope.onTacticScript(tacticId + '(' + args + (formulaId ? ',' + formulaId.replace(',','.') : '') + ')' +
          ' using "' + selected.join('::') + (selected.length > 0 ? '::' : '') + 'nil"', false)
      } else {
        var uri = formulaId !== undefined ? base + '/' + formulaId + '/doInputAt/' + tacticId : base + '/doInput/' + tacticId
        var stepwise = { method: 'POST', url: uri + '?stepwise=true', data: input};
        $http.post(uri + '?stepwise=false', input)
          .then(function(response) { $scope.runningTask.start($scope.proofId, nodeId, response.data.taskId, response.data.info, $scope.updateMainProof, $scope.broadcastProofError, stepwise); })
          .catch(function(err) {
            spinnerService.hide('tacticExecutionSpinner');
            $rootScope.$broadcast("proof.message", err.data);
          });
      }
    }

    $scope.doTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
      var nodeId = sequentProofData.agenda.selectedId();
      spinnerService.show('tacticExecutionSpinner');
      var uri = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/' + fml1Id + '/' + fml2Id + '/doAt/' + tacticId;
      var stepwise = { method: 'GET', url: uri + '?stepwise=true' };
      $http.get(uri + '?stepwise=false')
        .then(function(response) { $scope.runningTask.start($scope.proofId, nodeId, response.data.taskId, response.data.info, $scope.updateMainProof, $scope.broadcastProofError, stepwise); })
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
      var uri = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/doSearch/' + where + '/' + tacticId;
      var stepwise = input !== undefined ? { method: 'POST', url: uri + '?stepwise=true', data: input } : { method: 'GET', url: uri + '?stepwise=true' };
      var request = input !== undefined ? $http.post(uri + '?stepwise=false', input) : $http.get(uri + '?stepwise=false')
      request.then(function(response) { $scope.runningTask.start($scope.proofId, nodeId, response.data.taskId, response.data.info, $scope.updateMainProof, $scope.broadcastProofError, stepwise); })
        .catch(function(err) {
          spinnerService.hide('tacticExecutionSpinner');
        });
    }

    $scope.onTacticScript = function(tacticText, stepwise) {
      //@todo forward all to onMultiNodeTactic once it is robustified
      var doallTactic = tacticText.replace(/^doall\((.*)\)/g, function(match, inner, offset, string) {
        return inner;
      });
      if (doallTactic !== tacticText) $scope.onMultiNodeTactic({text: doallTactic, stepwise: stepwise}, undefined);
      else {
        var nodeId = sequentProofData.agenda.selectedId();
        if (nodeId != undefined) {
          if (tacticText != "nil") {
            spinnerService.show('tacticExecutionSpinner');
            var uri = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/doCustomTactic';
            var updateProof = stepwise ? $scope.updateFreshProof : $scope.updateMainProof
            return $http.post(uri + '?stepwise='+stepwise, tacticText)
              .then(function(response) { $scope.runningTask.start($scope.proofId, nodeId, response.data.taskId, response.data.info,
                                         updateProof, $scope.broadcastProofError, undefined); })
              .catch(function(err) {
                spinnerService.hideAll();
                if (err.data.errorThrown != undefined) {
                  //@note errors that occur before scheduling (parsing etc.), but not tactic execution errors -> cannot repeat from here
                  $rootScope.$broadcast('proof.message', err.data);
                } else {
                  console.error("Expected errorThrown field on error object but found something else: " + JSON.stringify(err));
                }
              });
          } // else nothing to do
        } else {
          console.error("Undefined selected node in agenda when trying to run the tactic script '" + tacticText + "'");
        }
      }
    }

    $scope.onNodeInTacticSelected = function(nodeId) {
      if (nodeId) {
        $scope.taskExplanation.proofStateNodeId = nodeId;
        $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/node').success(function(data) {
          $scope.taskExplanation.proofStateNode = data;
        });
        if ($scope.agenda.contains(nodeId)) {
          $scope.agenda.selectById(nodeId);
        }
      } else {
        $scope.taskExplanation.proofStateNodeId = undefined;
        $scope.taskExplanation.proofStateNode = undefined;
      }
    }

    $scope.onMultiNodeTactic = function(tactic, nodes) {
      var nodeIds = nodes ? nodes : sequentProofData.agenda.itemIds();
      //@todo robustness like runningTask / refactor runningTask to also use future when polling
      spinnerService.show('tacticExecutionSpinner');
      var tacticRunner = $q.defer();
      nodeIds.reduce(function(result, nodeId) {
        return result.then(function(response) {
          if (tactic.id) {
            var base = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId;
            var uri = tactic.formulaId !== undefined ?  base + '/' + tactic.formulaId + '/doAt/' + tactic.id : base + '/do/' + tactic.id;
            var stepwise = { method: 'GET', url: uri + '?stepwise=true' };
            return $http.get(uri + '?stepwise=false')
          } else if (tactic.text) {
            var uri = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/doCustomTactic';
            return $http.post(uri + '?stepwise='+tactic.stepwise, tactic.text)
          }
        }).then(function(response) {
          var taskId = response.data.taskId;
          var taskDone = $q.defer();
          function poll() {
            $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/' + taskId + '/status').
              then(function(response) {
                if (response.data.status === 'done') taskDone.resolve(taskId);
                else $timeout(poll, 1000);
              }).catch(function(error) {
                taskDone.reject(error);
              });
          }
          poll();
          return taskDone.promise;
        }).then(function(taskId) {
          return $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + nodeId + '/' + taskId + '/result')
        }).then(function(response) {
          var taskResult = response.data;
          $rootScope.$broadcast('proof.message', { textStatus: "", errorThrown: "" });
          sequentProofData.updateAgendaAndTree($scope.userId, taskResult.proofId, taskResult);
          sequentProofData.tactic.fetch($scope.userId, taskResult.proofId);
        })
      }, tacticRunner.promise).then(function(response) {
        // done on all nodes
      }).finally(function() {
        spinnerService.hide('tacticExecutionSpinner');
      });
      tacticRunner.resolve();
    }

    $scope.openTacticPosInputDialog = function(tacticName, positionLocator) {
      var nodeId = sequentProofData.agenda.selectedId();
      var tactics = derivationInfos.byName($scope.userId, $scope.proofId, nodeId, tacticName)
        .then(function(response) {
          return response.data;
        });

      var prevMode = sequentProofData.formulas.mode;
      sequentProofData.formulas.mode = 'select';

      var modalInstance = $uibModal.open({
        templateUrl: 'templates/inputtacticdialog.html',
        controller: 'DerivationInfoDialogCtrl',
        size: 'lg',
        resolve: {
          tactics: function() { return tactics; },
          readOnly: function() { return false; },
          userId: function() { return $scope.userId; },
          proofId: function() { return $scope.proofId; },
          defaultPositionLocator: function() { return positionLocator; },
          sequent: function() { return sequentProofData.proofTree.nodesMap[nodeId].getSequent(); }
        }
      });

      modalInstance.result.then(function(data) {
        if (data.input.length > 0) $scope.doInputTactic(data.position, tacticName, data.input);
        else $scope.doTactic(data.position, tacticName);
      }).finally(function() {
        sequentProofData.formulas.mode = prevMode;
      })
    }

    $scope.rulehelp = {
      codeName: undefined,
      derivationInfo: undefined
    };

    $scope.fetchRuleHelp = function(codeName) {
      if ($scope.rulehelp.codeName !== codeName) {
        $scope.rulehelp.codeName = codeName;
        derivationInfos.byName($scope.userId, $scope.proofId, $scope.nodeId, codeName).then(function(response) {
          if (response.data.length > 0) {
            $scope.rulehelp.derivationInfo = response.data[0].standardDerivation;
          } else {
            $scope.rulehelp.derivationInfo = undefined;
          }
        });
      }
      // return name of the ng-template in proofawesesome.html
      return 'rulehelp.html';
    }

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
    $scope.getCounterExample = function(additionalAssumptions) {
      var requestCanceller = $q.defer();
      $scope.$parent.runningRequest.canceller = requestCanceller;
      spinnerService.show('counterExampleSpinner');
      var nodeId = sequentProofData.agenda.selectedId();
      var node = sequentProofData.proofTree.node(nodeId);
      var selected = sequentProofData.formulas.selectedIndicesIn(node.getSequent());
      var additional = additionalAssumptions ? additionalAssumptions : {};
      var url = 'proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.agenda.selectedId() + '/counterExample'
      $http.get(url, { params: { assumptions: additional, fmlIndices: JSON.stringify(selected) }, timeout: requestCanceller.promise })
        .then(function(response) {
          var dialogSize = (response.data.result === 'cex.found') ? 'lg' : 'md';
          var modalInstance = $uibModal.open({
            templateUrl: 'templates/counterExample.html',
            controller: 'CounterExampleCtrl',
            size: dialogSize,
            resolve: {
              result: function() { return response.data.result; },
              origFormula: function() { return response.data.origFormula; },
              cexFormula: function() { return response.data.cexFormula; },
              cexValues: function() { return response.data.cexValues; },
              speculatedValues: function() { return response.data.speculatedValues; }
            }
          });
          modalInstance.result.then(
            function(result) {
              // dialog closed with request to recalculate using additional assumptions
              $scope.getCounterExample(result);
            },
            function() { /* dialog cancelled */ }
          );
        })
        .catch(function(err) {
          $uibModal.open({
            templateUrl: 'templates/parseError.html',
            controller: 'ParseErrorCtrl',
            size: 'md',
            resolve: {
              model: function () { return undefined; },
              error: function () { return err.data; }
          }});
        })
        .finally(function() { spinnerService.hide('counterExampleSpinner'); });
    }

    $scope.getODEConditions = function() {
      var requestCanceller = $q.defer();
      $scope.$parent.runningRequest.canceller = requestCanceller;
      spinnerService.show('odeConditionsSpinner');
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.agenda.selectedId() + '/odeConditions', { timeout: requestCanceller.promise })
        .then(function(response) {
          $uibModal.open({
            templateUrl: 'templates/odeConditions.html',
            controller: 'ODEConditionsCtrl',
            size: 'lg',
            resolve: {
              sufficient: function() { return response.data.sufficient; },
              necessary: function() { return response.data.necessary; }
            }
          });
        })
        .catch(function(err) {
          if (err.data != null) {
            $uibModal.open({
              templateUrl: 'templates/modalMessageTemplate.html',
              controller: 'ModalMessageCtrl',
              size: 'md',
              resolve: {
                title: function() { return "Unable to find ODE conditions"; },
                message: function() { return err.data.textStatus; },
                mode: function() { return "ok"; }
              }
            })
          } // request cancelled by user
        })
        .finally(function() { spinnerService.hide('odeConditionsSpinner'); });
    }

    $scope.getPegasusODECandidates = function() {
      var requestCanceller = $q.defer();
      $scope.$parent.runningRequest.canceller = requestCanceller;
      spinnerService.show('odeConditionsSpinner');
      $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.agenda.selectedId() + '/pegasusCandidates', { timout: requestCanceller.promise })
        .then(function(response) {
          $uibModal.open({
            templateUrl: 'templates/pegasusCandidates.html',
            controller: 'PegasusCandidatesCtrl',
            size: 'lg',
            resolve: {
              candidates: function() { return response.data.candidates; }
            }
          });
        })
        .catch(function(err) {
          if (err.data != null) {
            $uibModal.open({
              templateUrl: 'templates/modalMessageTemplate.html',
              controller: 'ModalMessageCtrl',
              size: 'md',
              resolve: {
                title: function() { return "Unable to find Pegasus invariant candidates"; },
                message: function() { return err.data.textStatus; },
                mode: function() { return "ok"; }
              }
            })
          } // else request cancelled by user
        })
        .finally(function() { spinnerService.hide('odeConditionsSpinner'); });
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

    $scope.restartBackend = function() { $http.get("tools/restart"); }
    $scope.testBackendConnection = function() {
      $http.get("tools/testConnection").then(function(response) {
        $scope.backend.connectionTestResult = true;
        $uibModal.open({
          templateUrl: 'templates/modalMessageTemplate.html',
          controller: 'ModalMessageCtrl',
          size: 'md',
          resolve: {
            title: function() { return "Connection test successful"; },
            message: function() { return "The tool connection is operational."; },
            mode: function() { return "ok"; }
          }
        })
      })
      .catch(function(err) {
        $scope.backend.connectionTestResult = false;
        $uibModal.open({
          templateUrl: 'templates/modalMessageTemplate.html',
          controller: 'ModalMessageCtrl',
          size: 'md',
          resolve: {
            title: function() { return "Error testing connection"; },
            message: function() { return err.data.textStatus; },
            mode: function() { return "ok"; }
          }
        })
      })
    }
      
    //Save a name edited using the inline editor.
    $scope.saveProofName = function(newName) {
      $http.post("proofs/user/" + $scope.userId + "/" + $scope.proofId + "/name/" + newName, {})
    }

    $scope.trimTo = function(str, len) {
      return str.length > len ? str.substring(0, len) + "..." : str;
    }

    $scope.taskPrefixLabel = function(nodeId) {
      var labels = $scope.prooftree.node(nodeId).labels;
      return labels.length > 1 ? $scope.trimTo(labels[0], 10) : undefined;
    }

    $scope.taskPostfixLabel = function(nodeId) {
      var labels = $scope.prooftree.node(nodeId).labels;
      return labels.length > 0 ? $scope.trimTo(labels[labels.length - 1], 10) : undefined;
    }

    $scope.taskLabels = function(nodeId) {
      return $scope.prooftree.node(nodeId).labels.map(function (l) { return trimTo(l, 10); }).join('&nbsp;<i class="fa fa-angle-right"></i>&nbsp;')
    }

    $scope.saveTaskName = function(newName, oldName) {
      if (newName !== oldName) $scope.doInputTactic(undefined, "label", [{ param: "label", type: "string", value: '"' + newName + '"' }]);
    }

    $scope.openLemmaProof = function(taskId) {
      var lemmaName = $scope.taskPostfixLabel(taskId).substring(6)
      var uri     = 'models/users/' + sessionService.getUser() + '/model/' + encodeURIComponent(lemmaName) + '/openOrCreateLemmaProof'
      var dataObj = {
        parentProofId: $scope.proofId,
        parentTaskId: taskId
      }

      $http.post(uri, dataObj).
        success(function(data) {
          var proofid = data.id
          // we may want to switch to ui.router
          $location.path('proofs/' + proofid);
        }).
        error(function(data, status, headers, config) {
          console.log('Error starting new proof for model ' + $routeParams.modelId)
        });
    }

    $scope.openModelEditor = function (modelId) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeldialog.html',
        controller: 'ModelDialogCtrl',
        size: 'fullscreen',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function() { return modelId; },
          mode: function() { return 'proofedit'; },
          proofid: function() { return $scope.proofId; }
        }
      });
    }

    // all tasks finished

    // empty open proof until fetched from server
    $scope.proof = {};
    $scope.resetProof = function() {
      $scope.proof.proofId = '';
      $scope.proof.checking = true;
      //isProved: true/false is reported from server
      $scope.proof.isProved = undefined;
      $scope.proof.tactic = '';
      $scope.proof.provable = '';
    }
    $scope.resetProof();

    $scope.$on('agenda.isEmpty', function(event, data) {
      if (data.proofId == $scope.proofId) {
        // the current controller is responsible
        $http.get('proofs/user/' + $scope.userId + "/" + $scope.proofId + '/progress').success(function(data) {
          if (data.status == 'closed') {
            // fetch proof
            $http.get("/proofs/user/" + $scope.userId + "/" + $scope.proofId + "/validatedStatus").then(function(response) {
              $scope.proof = response.data; // no transformation, pass on to HTML as is
            });
          } else {
            // should never happen
            showMessage($uibModal, 'Empty agenda even though proof ' + $scope.proofId + ' is not closed (' + data.status + ')')
          }
        });
      }
    });

    $scope.$on('agenda.branchClosed', function(event, data) {
      if (data.proofId == $scope.proofId) {
        // the current controller is responsible
        spinnerService.show('branchClosedSpinner');
        $timeout(function() { spinnerService.hide('branchClosedSpinner'); }, 2000);
      }
    });

    $scope.browseProof = function() {
      $location.path('/proofs/' + $scope.proof.proofId + '/browse');
    };

    $scope.downloadLemma = function() {
      Proofs.downloadLemma($scope.userId, {id: $scope.proofId, name: $scope.proofName});
    }
    $scope.downloadProofArchive = function() {
      Proofs.downloadProofArchive($scope.userId, {id: $scope.proofId, name: $scope.proofName});
    }
  });
