var keymaeraProofControllers = angular.module('keymaeraProofControllers', ['ngCookies', 'angularTreeview', 'ui.bootstrap']);

keymaeraProofControllers.factory('Models', function () {
    var models = [];

    return {
        getModels: function() {
            return models;
        },
        setModels: function(m) {
            models = m;
        },
        addModel: function(model) {
            models.push(model);
        },
        addModels: function(m) {
            for (var i = 0; i < m.length; i++) {
                models.push(m[i]);
            }
        }
    };
});

/**
 * Definition of Agenda
 */
keymaeraProofControllers.factory('Agenda', function () {

    /**
     * tasks is a list of { $hashKey, nodeId = "_0_0...", proofId = hash, proofNode = {sequent, children ...} }
     */
    var tasks = [];
    /**
     * a task looks like { $hashKey, nodeId = "_0_0...", proofId = hash, proofNode = {sequent, children ...} }
     */
    var selectedTask;

    return {
        getTasks: function() {
            return tasks;
        },
        setTasks: function(t) {
            tasks = t;
        },
        addTask: function(task) {
            tasks.push(task);
        },
        addTasks: function(t) {
            for (var i = 0; i < t.length; i++) {
                tasks.push(t[i]);
            }
        },
        getSelectedTask: function() {
            return selectedTask;
        },
        setSelectedTask: function(t) {
            selectedTask = t;
        }
    };
});

keymaeraProofControllers.factory('Tactics', function ($rootScope) {

    var ruleTactics = {
        // TODO add rules, move into own file
        "dl.and-left" :
            { "name" : "dl.and-left",
              "label" : "\\(\\left(\\wedge l \\right) \\frac{\\Gamma, \\phi, \\psi ~\\vdash~ \\Delta}{\\Gamma,\\phi \\wedge \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.and-right" :
            { "name" : "dl.and-right",
              "label" : "\\(\\left(\\wedge r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\wedge \\psi,\\Delta}\\)"
            },
        "dl.or-left" :
            { "name" : "dl.or-left",
              "label" : "\\(\\left(\\vee l \\right) \\frac{\\Gamma,\\phi ~\\vdash~ \\Delta \\qquad \\Gamma,\\psi ~\\vdash~ \\Delta}{\\Gamma \\phi \\vee \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.or-right" :
            { "name" : "dl.or-right",
              "label" : "\\(\\left(\\vee r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\vee \\psi,\\Delta}\\)"
            },
        "dl.imply-left" :
            { "name" : "dl.imply-left",
              "label" : "\\(\\left(\\rightarrow l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma \\phi \\rightarrow \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.imply-right" :
            { "name" : "dl.imply-right",
              "label" : "\\(\\left(\\rightarrow r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\rightarrow \\psi,\\Delta}\\)"
            },
        "dl.equiv-left" :
            { "name" : "dl.equiv-left",
              "label" : "TODO: \\(\\leftrightarrow l\\)"
            },
        "dl.equiv-right" :
            { "name" : "dl.equiv-right",
              "label" : "TODO: \\(\\leftrightarrow r\\)"
            },
        "dl.not-left" :
            { "name" : "dl.not-left",
              "label" : "\\(\\left(\\neg l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta}{\\Gamma,\\neg\\phi ~\\vdash~ \\Delta}\\)"
            },
        "dl.not-right" :
            { "name" : "dl.not-right",
              "label" : "\\(\\left(\\neg r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\neg \\phi, \\Delta}\\)"
            },
        "dl.close-true" :
            { "name" : "dl.close-true",
              "label" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma ~\\vdash~ \\textit{true},\\Delta}\\)"
            },
        "dl.close-false" :
            { "name" : "dl.close-false",
              "label" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma, \\textit{false} ~\\vdash~ \\Delta}\\)"
            },
        "dl.skolemize" :
            { "name" : "dl.skolemize",
              "label" : "TODO: skolemize"
            },
        "dl.box-assign" :
            { "name" : "dl.box-assign",
              "label" : "\\(\\left(\\left[:=\\right]\\right) \\frac{\\forall x. x = t \\to \\phi(x)}{\\left[x := t\\right]\\phi(x)}\\)"
            },
        "dl.box-choice" :
            { "name" : "dl.box-choice",
              "label" : "\\(\\left(\\left[\\cup\\right]\\right) \\frac{\\left[\\alpha\\right]\\phi \\qquad \\left[\\beta\\right]\\phi}{\\left[\\alpha \\cup \\beta\\right]\\phi}\\)"
            },
        "dl.box-induction" :
            { "name" : "dl.box-induction",
              "label" : "\\(\\left(\\left[\\alpha^*\\right] \\text{ind}\\right) \\frac{\\left(\\phi \\wedge \\left[\\alpha^*\\right]\\left(\\phi \\rightarrow \\left[\\alpha\\right] \\phi \\right)\\right) }{\\left[\\alpha^*\\right]\\phi}\\)"
            },
        "dl.induction" :
            { "name" : "dl.induction",
              "label" : "\\(\\left(\\left[\\alpha^*\\right] \\text{ind}\\right) \\frac{\\Gamma ~\\vdash~ \\phi, \\Delta \\quad \\Gamma ~\\vdash~ \\forall^\\alpha \\left(\\phi \\to \\left[\\alpha\\right]\\phi\\right) \\quad \\Gamma ~\\vdash~ \\forall^\\alpha \\left(\\phi \\to \\psi \\right)}{\\Gamma ~\\vdash~ \\left[\\alpha^*\\right]\\psi,\\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(\\phi\\)", "placeholder" : "Invariant", "type" : "text" } ]
            },
        "dl.box-ndetassign" :
            { "name" : "dl.box-ndetassign",
              "label" : "\\(\\left(\\left[:= *\\right]\\right) \\frac{\\forall x. \\phi(x)}{\\left[x := *\\right]\\phi}\\)"
            },
        "dl.box-seq" :
            { "name" : "dl.box-seq",
              "label" : "\\(\\left(\\left[~;~\\right]\\right) \\frac{\\left[\\alpha\\right]\\left[\\beta\\right]\\phi}{\\left[\\alpha;\\beta\\right]\\phi}\\)"
            },
        "dl.box-test" :
            { "name" : "dl.box-test",
              "label" : "\\(\\left(\\left[?\\right]\\right) \\frac{H \\rightarrow \\phi)}{\\left[?H\\right]\\phi}\\)"
            },
        "dl.cut" :
            { "name" : "dl.cut",
              "label" : "\\(\\left(\\text{cut}\\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\quad \\Gamma,\\phi ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(\\phi\\)", "placeholder" : "Formula", "type" : "text" } ]
            },
        "dl.qe" :
            { "name" : "dl.qe",
              "label" : "\\(\\left(\\text{QE}\\right) \\frac{\\text{QE}(\\phi)}{\\phi} \\)",
              "input" : [ { "name" : "0", "label" : "Tool", "placeholder" : "Mathematica", "type" : "text" } ]
            },
        "dl.equalityRewriting" :
            { "name" : "dl.equalityRewriting",
              "label" : "\\(\\left(\\text{Foo}\\right) \\frac{Foo}{Bar}\\)",
              "input" : [ { "name" : "0", "label" : "Assumption", "placeholder" : "ante:3", "type" : "text" },
                          { "name" : "1", "label" : "Position", "placeholder" : "succ:2,0", "type" : "text" },
                          { "name" : "2", "label" : "Disjoint", "placeholder" : "true", "type" : "text" }
               ]
            }
    };
    var userTactics = {
        // TODO has to come from the database
    };

    var dispatchedTacticsIds = [];

    var dispatchedTacticsNotificationService = {};
    dispatchedTacticsNotificationService.broadcastDispatchedTactics = function(tId) {
        $rootScope.$broadcast('handleDispatchedTactics', tId);
    };

    return {
        getRuleTactics: function() { return ruleTactics; },
        getUserTactics: function() { return userTactics; },
        getDispatchedTactics: function() { return dispatchedTacticsIds; },
        addDispatchedTactics: function(tId) { dispatchedTacticsIds.push(tId); },
        removeDispatchedTactics: function(tId) {
            var i;
            while((i = arr.indexOf(item)) !== -1) { arr.splice(i, 1); }
        },
        getDispatchedTacticsNotificationService: function() { return dispatchedTacticsNotificationService; }
    };
});

keymaeraProofControllers.value('cgBusyDefaults',{
    message:'Running tactics',
    backdrop: true,
    templateUrl: 'partials/running-tactics-indicator.html'
});

keymaeraProofControllers.controller('DashboardCtrl',
  function ($scope, $cookies, $http) {
    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $http.get('/users/' + $cookies.userId + '/dashinfo')
        .success(function(data) {
            $scope.open_proof_count = data.open_proof_count;
        })

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  });

keymaeraProofControllers.controller('ModelUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, Models) {

     $scope.addModel = function() {
         $.ajax({
               url: "user/" + $cookies.userId + "/modeltextupload/" + $scope.modelName,
               type: "POST",
               data: window.UPLOADED_FILE_CONTENTS,
               async: true,
               dataType: 'json',
               contentType: 'application/json',
               success: function(data) {
                   while (Models.getModels().length != 0) { Models.getModels().shift() }
                   $http.get("models/users/" + $cookies.userId).success(function(data) {
                       Models.addModels(data);
                       $scope.modelName = '';
                       // TODO reset file chooser
                   });
               },
               error: this.ajaxErrorHandler
         });
     };

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
  });

keymaeraProofControllers.controller('ModelListCtrl',
  function ($scope, $http, $cookies, $modal, $location, Models) {
    $scope.models = [];
    $http.get("models/users/" + $cookies.userId).success(function(data) {
        $scope.models = data
    });

    $scope.open = function (modelid) {
        var modalInstance = $modal.open({
          templateUrl: 'partials/modeldialog.html',
          controller: 'ModelDialogCtrl',
          size: 'lg',
          resolve: {
            modelid: function () { return modelid; }
          }
        });
    };

    $scope.showPrfs = function(modelId) {
        $location.path('/models/' + modelId + "/proofs")
    }

    $scope.$watch('models',
        function (newModels) { if (newModels) Models.setModels(newModels); }
    );
    $scope.$emit('routeLoaded', {theview: 'models'});
  })

keymaeraProofControllers.controller('ModelDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.userId + "/model/" + modelid).success(function(data) {
      $scope.model = data
  });

  $scope.ok = function () {
    $modalInstance.close();
  };

//  $scope.cancel = function () {
//    $modalInstance.dismiss('cancel');
//  };
});

keymaeraProofControllers.controller('ModelProofCreateCtrl',
  function ($scope, $http, $cookies, $routeParams, $location) {
    $scope.createProof = function() {
        var proofName        = $scope.proofName ? $scope.proofName : ""
        var proofDescription = $scope.proofDescription ? $scope.proofDescription : ""
        var uri              = 'models/users/' + $cookies.userId + '/model/' + $routeParams.modelId + '/createProof'
        var dataObj          = {proofName : proofName, proofDescription : proofDescription}

        $http.post(uri, dataObj).
            success(function(data) {
                var proofid = data.id
                // we may want to switch to ui.router
                $location.path('proofs/' + proofid);
            }).
            error(function(data, status, headers, config) {
                alert('TODO handle errors properly.')
            });
    }
    $scope.$emit('routeLoaded', {theview: '/models/:modelId/proofs/create'})
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The proof lists
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

// Proof list for all models belonging to a user.
keymaeraProofControllers.controller('ProofListCtrl',
  function ($scope, $http, $cookies,$location, $routeParams) {
    $scope.openPrf = function(proofId) {
        $location.path('/proofs/' + proofId)
    }
    //Load the proof list and emit as a view.
    $http.get('models/users/' + $cookies.userId + "/proofs").success(function(data) {
      $scope.allproofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'allproofs'});
  });

// Proof list for an individual model
keymaeraProofControllers.controller('ModelProofsCtrl',
  function ($scope, $http, $cookies,$location, $routeParams) {
    $scope.openPrf = function(proofId) {
        $location.path('/proofs/' + proofId)
    }
    $scope.loadProof = function(proof) {
        proof.loadStatus = 'Loading'
        $http.get('proofs/user/' + $cookies.userId + "/" + proof.id).success(function(data) {
            proof.loadStatus = data.loadStatus
        })
    }
    //Load the proof list and emit as a view.
    $http.get('models/users/' + $cookies.userId + "/model/" + $routeParams.modelId + "/proofs").success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Proofs
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
keymaeraProofControllers.controller('ProofCtrl',
  function($scope, $http, $cookies, $routeParams) {
    $http.get('proofs/user/' + $cookies.userId + "/" + $routeParams.proofId).success(function(data) {
        $scope.proofId = data.id;
        $scope.proofName = data.name;
        $scope.modelId = data.model;
        $scope.closed = data.closed;
        $scope.stepCount= data.stepCount;
        $scope.date = data.date;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});
  });

keymaeraProofControllers.controller('TaskListCtrl',
  function($scope, $http, $cookies, $routeParams, $q, $modal, Agenda, Tactics) {
    $scope.proofId = $routeParams.proofId;

    $scope.fetchAgenda = function(userId, proofId) {
        $http.get('proofs/user/' + userId + "/" + proofId + '/agenda').success(function(data) {
            $scope.agenda = data;
            if ($scope.agenda.length > 0) {
                // TODO should only update the view automatically if user did not navigate somewhere else manually
                $scope.setSelected($scope.agenda[0]);
            } else {
                // proof finished
                $scope.refreshTree();
                var modalInstance = $modal.open({
                  templateUrl: 'partials/prooffinisheddialog.html',
                  controller: 'ProofFinishedDialogCtrl',
                  size: 'md',
                  resolve: {
                    proofId: function() { return $scope.proofId; }
                  }
                });
            }
        }).error(function(data) {
            if (data.errorThrown == 'proof not loaded') {
                // TODO open modal dialog and ask if proof should be loaded
            } else if (data.errorThrown == 'proof is loading') {
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
        (function poll(){
           setTimeout(function() {
                $http.get('proofs/user/' + $cookies.userId + '/' + $scope.proofId + '/dispatchedTactics/' + tId)
                        .success(function(data) {
                    if (data.tacticInstStatus == 'Running') {
                      poll();
                    } else {
                        $scope.defer.resolve(data.tacticInstStatus)
                    }
                })
          }, 1000);
        })();
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
     *
     * Following the example at https://github.com/JimLiu/angular-ui-tree/blob/master/demo/js/groups.js
     * $scope is the controller scope while scope is the tree scope. See UI Tree documentation.
     */
    $scope.click = function(scope) {
        var selectedNode = scope.$modelValue

        var isAgendaItem = false;
        for(var i = 0 ; i < Agenda.getTasks().length; i++) {
            var task = Agenda.getTasks()[i]
            if(task.nodeId === selectedNode.id) {
                //select agenda item. The sequent view listens to the agenda.
                $scope.setSelected(task);
                isAgendaItem = true;
                break;
            }
        }
        if(!isAgendaItem) {
            $http.get("/proofs/" + $scope.proofId + "/sequent/" + selectedNode.id)
                .success(function(proofNode) {
                    //Todo -- figure out what else has to go in the task object.
                    var task = {
                        "proofNode" : proofNode,
                        "enabled" : false
                    };
                    $scope.setSelected(task);
                })
                .error(function() {
                    var msg = "Error: this proof is not on the Agenda and the server could not find it.";
                    alert(msg);
                    console.error(msg);
                })
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
    $scope.setSelected = function(agendaItem) {
        $scope.selectedTask = agendaItem;
        $scope.refreshTree();
    }
    $scope.isSelected = function(agendaItem) {
        $scope.selectedTask == agendaItem;
    }

    $scope.refreshTree = function() {
        //pulling this variable out so that I can print it back out.
        var nodeId = null
        var uri = (nodeId === null) ?
            "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/" :
            "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/" + nodeId;

        $http.get(uri)
            .success(function(data) {
                $scope.treedata = data;
            })
            .error(function() {
                alert("error encountered while trying to retrieve the tree.")
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

keymaeraProofControllers.controller('ProofFinishedDialogCtrl',
        function($scope, $http, $modalInstance, proofId) {
    $scope.cancel = function () {
        $modalInstance.dismiss('cancel');
    };
});

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Sequents and proof rules
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('ProofRuleDialogCtrl',
        function ($scope, $http, $cookies, $modalInstance, proofId, nodeId, formula, isAnte, Tactics) {
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formula = formula;
  $scope.isAnte = isAnte;
  $scope.ruleTactics = [];
  $scope.userTactics = [];

  var fId = ((formula !== undefined) ? formula.id : "sequent")
  var uri = 'proofs/user/' + $cookies.userId + '/' + proofId + '/nodes/' + nodeId + '/formulas/' + fId + '/tactics'

  $http.get(uri).success(function(data) {
      $scope.ruleTactics = [];
      $scope.userTactics = [];
      for (var i = 0; i < data.length; i++) {
          var tacticName = data[i].name;
          var tactic = Tactics.getRuleTactics()[tacticName];
          if (tactic !== undefined) {
//              tactic.id = data[i].id;
              var tacticInst = {
                id: data[i].id,
                name: tactic.name,
                label: tactic.label,
                input: tactic.input !== undefined ? tactic.input.slice() : tactic.input
              }
              $scope.ruleTactics.push(tacticInst);
          }
          tactic = Tactics.getUserTactics()[tacticName];
          if (tactic !== undefined) {
              tactic.id = data[i].id;
              $scope.userTactics.push(tactic);
          }
      }
  });

  var internalApplyTactics = function(t, uriPostfix, saturate) {
        var inputParams = {}
        if (t.input !== undefined) {
            for (i = 0; i < t.input.length; ++i) {
                inputParams[t.input[i].name] = t.input[i].value
            }
        }
        var saturateWhere = saturate ? '/' + ($scope.formula !== undefined ? 'saturateCurrent'
                                                                           : (isAnte ? "saturateAnte" : "saturateSucc"))
                                     : '';
        $http.post(uri + '/' + uriPostfix + saturateWhere, inputParams).success(function(data) {
            var dispatchedTacticId = data.tacticInstId;
            $modalInstance.close(dispatchedTacticId);
            Tactics.addDispatchedTactics(dispatchedTacticId);
            Tactics.getDispatchedTacticsNotificationService().broadcastDispatchedTactics(dispatchedTacticId);
        });
    }

  $scope.applyTactics = function(t) {
    internalApplyTactics(t, 'run/' + t.id, false)
  }
  $scope.applyTacticsByName = function(tName) {
    internalApplyTactics(t, 'runByName/' + tName, false)
  }
  $scope.applyTacticsFF = function(t) {
    internalApplyTactics(t, 'run/' + t.id, true)
  }
  $scope.applyTacticsByNameFF = function(tName) {
    internalApplyTactics(t, 'runByName/' + tName, true)
  }

  $scope.cancel = function () {
    $modalInstance.dismiss('cancel');
  };

});

keymaeraProofControllers.controller('RunningTacticsCtrl',
        function ($scope, $http, $cookies, Tactics) {
   $scope.abort = function() {
     // TODO implement
   }
});

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Development Tools -- these can be removed before release.
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('DevCtrl',
  function ($scope, $http, $cookies, $routeParams) {
    $scope.deletedb = function() {
        $http.get("/dev/deletedb")
            .success(function(data) {
                alert("Database cleared.")
            })
    }
});

