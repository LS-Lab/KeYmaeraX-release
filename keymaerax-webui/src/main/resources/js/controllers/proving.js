////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proving (Agenda list and history on the left, selected sequent in the main pane)
// @deprecated Use provingawesome.js instead
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').value('cgBusyDefaults',{
    message:'Running tactics',
    backdrop: true,
    templateUrl: 'partials/running-tactics-indicator.html'
});

angular.module('keymaerax.controllers').controller('ProofCtrl', function($scope, $http, $cookies, $routeParams) {
  $http.get('proofs/user/' + $cookies.userId + "/" + $routeParams.proofId).success(function(data) {
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
    $http.post("proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/name/" + newName, {})
  };
});

angular.module('keymaerax.controllers').controller('RunningTacticsCtrl',
        function ($scope, $http, $cookies, Tactics) {
   $scope.abort = function() {
     // TODO implement
   }
});

angular.module('keymaerax.controllers').controller('TaskListCtrl',
  function($rootScope, $scope, $http, $cookies, $routeParams, $q, $modal, $sce, Agenda, Tactics) {
    $scope.proofId = $routeParams.proofId;

    $scope.fetchAgenda = function(userId, proofId) {
        $http.get('proofs/user/' + userId + "/" + proofId + '/agenda').success(function(data) {
            $scope.agenda = data;
            //Create a goalLabel for each task.
            for(var i = 0; i < $scope.agenda.length; i++) {
                var task = $scope.agenda[i];
                for(var j = 0; j < task.proofNode.infos.length; j++) {
                    var info = task.proofNode.infos[j];
                    if(info.key == "branchLabel") {
                        task.goalLabel = info.value
                    }
                }
                if(!task.goalLabel) { //If we did not find a pre-defined branch label, just use the nodeId.
                    if(task.nodeId.length < 7) {
                        task.goalLabel = "Unlabeled Goal " //+ task.nodeId
                    }
                    else {
                        task.goalLabel = "Unlabeled Goal " //+ task.nodeId.substring(0,2) + ".." + task.nodeId.substring(task.nodeId.length-4)
                    }
                }
            }
            if ($scope.agenda.length > 0) {
                // TODO should only update the view automatically if user did not navigate somewhere else manually
                $scope.setSelected($scope.agenda[0]);
                $scope.refreshTree();
            } else {
                // proof might be finished
                $scope.refreshTree();
                $http.get('proofs/user/' + userId + "/" + proofId + '/progress').success(function(data) {
                  if (data.status == 'closed') {
                    var modalInstance = $modal.open({
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
                    showErrorMessage($modal, 'empty agenda even though proof is not closed (' + data.status + ')')
                  }
                })
                .error(function() {
                  showErrorMessage($modal, "error retrieving proof progress")
                })
            }
        }).error(function(data) {
            if (data.status == 'notloaded') {
                // TODO open modal dialog and ask if proof should be loaded
            } else if (data.status == 'loading') {
                $scope.proofIsLoading = $q.defer()
                $scope.proofIsLoading.promise.then(function() {
                    // TODO proof is now loaded, fetch tree and tasks
                })
            }
        });
    }

    $scope.fetchAgenda($cookies.userId, $scope.proofId)

    $scope.addSubtree = function(parentId, subtree) {
        for(var i = 0 ; i < $scope.treedata.length; i++) {
            var node = $scope.treedata[i];
            if(node.id === parentId) {
                subtree.map(function(x) { node.push(x) })
            }
            if(node.children != []) {
                $scope.addSubtree(parentId, node.children[i]);
            }
        }
    }

    // Watch running tactics
    $scope.$on('handleDispatchedTactics', function(event, tId) {
        // TODO create defer per tId
        $scope.defer = $q.defer();
        $scope.defer.promise.then(function (tacticResult) {
            if (tacticResult == 'Finished') {
                $scope.fetchAgenda($cookies.userId, $scope.proofId)
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
                    $http.get('proofs/user/' + $cookies.userId + '/' + $scope.proofId + '/dispatchedTactics/' + tId)
                            .success(function(data) {
                            if(data.errorThrown || data.tacticInstStatus == 'Error') {
                              $modal.open({
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
    // Get & populate the tree.
    $scope.treedata = [];

    $scope.proofTree =  {
        beforeDrag: function(x) { false } //disable dragging.
    }

    // Label editing controllers.

    //
    /**
     * Update the sequent view when a node of the proof tree is clicked.
     *
     * When the node is an open node, it's associated with an agenda item (which has a sequent).
     * Otherwise, we need to construct a new task (not in the agenda).
     */
    $scope.click = function(node) {
        if ($scope.selectedTask == undefined || $scope.selectedTask.nodeId != node.id) {
          var isAgendaItem = false;
          for(var i = 0 ; i < Agenda.getTasks().length; i++) {
              var task = Agenda.getTasks()[i]
              if(task.nodeId === node.id) {
                  //select agenda item. The sequent view listens to the agenda.
                  isAgendaItem = true;
                  $scope.setSelected(task);
                  break;
              }
          }
          if(!isAgendaItem) {
              $http.get("/proofs/" + $scope.proofId + "/sequent/" + node.id)
                  .success(function(proofNode) {
                      //TODO -- sufficient to display sequent, but may need more for interaction
                      if(proofNode.errorThrown) {
                        showCaughtErrorMessage($modal, proofNode, "Error enoucntered while trying to get proof node.")
                      }
                      else {
                                            var agendaItem = {
                                              "nodeId": proofNode.id,
                                              "proofNode": proofNode,
                                              "readOnly": true
                                            }
                                            $scope.setSelected(agendaItem);
                      }
                  })
                  .error(function() {
                      var msg = "Error: this proof is not on the Agenda and the server could not find it.";
                      showErrorMessage($modal, msg)
                  })
          }
        }
    }

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
    $scope.proofHistoryPageSize = 10
    $scope.proofHistoryNumPages = 5

    $scope.setSelected = function(agendaItem) {
        $scope.selectedTask = agendaItem;
    }

    $scope.isSelected = function(agendaItem) {
        $scope.selectedTask == agendaItem;
    }


    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    // Subsection on executing tasks
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //Executes a combinator language term.
    $scope.execute = function() {
        var nodeId = this.selectedTask.nodeId;
        var uri = "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/nodes/" + nodeId + "/tactics/runTerm"
        var dataObj = {clTerm: $scope.clTerm};

        $http.post(uri, dataObj)
             .success(function(data) {
                if(data.errorThrown) {
                   $modal.open({
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
                showErrorMessage($modal, "encountered error during post on runTerm.")
             })
    }
    $scope.$on('handleDispatchedTerm', function(event, tId) {
        // TODO create defer per tId
        $scope.defer = $q.defer();
        $scope.defer.promise.then(function (tacticResult) {
            if (tacticResult == 'Finished') {
                $scope.fetchAgenda($cookies.userId, $scope.proofId)
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
                    $http.get('proofs/user/' + $cookies.userId + '/' + $scope.proofId + '/dispatchedTerm/' + tId)
                         .success(function(data) {
//                            if (data.status == 'Running' || data.errorThrown) { //Errors might be thrown if the term isn't created yet...
                            if(data.errorThrown) {
                              $modal.open({
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

    $scope.refreshTree = function() {
        //pulling this variable out so that I can print it back out.
        var nodeId = null
        var uri = (nodeId === null) ?
            "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/" :
            "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/" + nodeId;

//        $http.get(uri)
//            .success(function(data) {
//                    var printNode = function(n) {
//                        if(n === null) {
//                            return "Could not load proof tree."
//                        }
//                        var childrenResults;
//                        if(n.children.length > 0) {
//                            childrenResults = "<ol>" + n.children.map(printNode) + "</ol>"
//                        }
//                        else {
//                            childrenResults = ""
//                        }
//                        return "<li>" + n.label + childrenResults + "</li>"
//                    };
//                    $scope.treedata = data
//
//                    var perNode = ""
//                    for(var i =0; i<data.length; i++) {
//                        perNode += printNode(data[i])
//                    };
//
//                    $scope.hacmstree = $sce.trustAsHtml("<ol>" + perNode + "</ol>") //Security!!!
//            })
//            .error(function() {
//                alert("error encountered while trying to retrieve the tree.")
//            })
    }

    $scope.fetchHistory = function() {
      var uri = "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/proofhistory";
      $http.get(uri)
        .success(function(data) {
            if(data.errorThrown) {
                showCaughtErrorMessage($modal, data, "Error encountered while trying to get proof history.")
            }
            else {
              $scope.proofHistory = [];
              $scope.currentProofHistoryPage = 1;
              for (var i = 0; i < data.length; i++) {
                var tacticName = data[i].tactic.name;
                var tactic = Tactics.getRuleTactics()[tacticName];
                if (tactic !== undefined) {
                  var tacticInst = {
                    id: data[i].tactic.id,
                    name: tactic.name,
                    label: tactic.label,
                    tooltip: tactic.tooltip
                  }
                  var historyItem = {
                    index: i,
                    dispatched: data[i].dispatched,
                    tactic: tacticInst
                  }
                  $scope.proofHistory.push(historyItem)
                } else {
                  showErrorMessage($modal, "pretty printing undefined for tactic " + tacticName)
                }
              }
            }
        })
        .error(function() {
          showErrorMessage($modal, "error encountered while trying to retrieve the proof history.")
        })
    }

    $scope.fetchNodeInfo = function(dispatched) {
      var uri = "/proofs/user/" + $cookies.userId + "/" + dispatched.proofId + "/agendaDetails/" + dispatched.nodeId;
      $http.get(uri)
        .success(function(data) {
        data.readOnly = true;
        $scope.selectedTask = data;
      })
      .error(function() {
        showErrorMessage($modal, "error encountered while trying to retrieve the proof history details.")
      })
    }

    $scope.$watch('agenda',
        function (newTasks) { if (newTasks) Agenda.setTasks(newTasks); }
    );
    $scope.$watch('selectedTask',
        function() { return Agenda.getSelectedTask(); },
        function(t) { if (t) Agenda.setSelectedTask(t); }
    );
    $scope.$watch('dispatchedTactics',
        function() { return Tactics.getDispatchedTactics(); },
        function(tId) { Tactics.removeDispatchedTactics(tId); }
    );
  });

angular.module('keymaerax.controllers').controller('ProofFinishedDialogCtrl',
        function($scope, $http, $cookies, $modalInstance, proofId) {
    $scope.validatedProofStatus = 'closed'

    $scope.cancel = function() {
        $modalInstance.dismiss('cancel');
    };

    $scope.validateProof = function() {
      $http.get("/proofs/user/" + $cookies.userId + "/" + proofId + "/validatedStatus").success(function(data) {
        $scope.validatedProofStatus = data.status
      })
      .error(function() {
        showErrorMessage($modal, "error when validating proof")
      })
    }
});
