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

keymaeraProofControllers.factory('Tasks', function () {

    var tasks = [];
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

    var tactics = {
        // TODO add rules, move into own file
        "dl.and-left" :
            { "name" : "dl.and-left",
              "latex" : "\\(\\left(\\wedge l \\right) \\frac{\\Gamma, \\phi, \\psi ~\\vdash~ \\Delta}{\\Gamma,\\phi \\wedge \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.and-right" :
            { "name" : "dl.and-right",
              "latex" : "\\(\\left(\\wedge r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\wedge \\psi,\\Delta}\\)"
            },
        "dl.or-left" :
            { "name" : "dl.or-left",
              "latex" : "\\(\\left(\\vee l \\right) \\frac{\\Gamma,\\phi ~\\vdash~ \\Delta \\qquad \\Gamma,\\psi ~\\vdash~ \\Delta}{\\Gamma \\phi \\vee \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.or-right" :
            { "name" : "dl.or-right",
              "latex" : "\\(\\left(\\vee r \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\vee \\psi,\\Delta}\\)"
            },
        "dl.imply-left" :
            { "name" : "dl.imply-left",
              "latex" : "\\(\\left(\\rightarrow l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta \\qquad \\Gamma ~\\vdash~ \\psi,\\Delta}{\\Gamma \\phi \\rightarrow \\psi ~\\vdash~ \\Delta}\\)"
            },
        "dl.imply-right" :
            { "name" : "dl.imply-right",
              "latex" : "\\(\\left(\\rightarrow r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\rightarrow \\psi,\\Delta}\\)"
            },
        "dl.equiv-left" :
            { "name" : "dl.equiv-left",
              "latex" : "TODO: \\(\\leftrightarrow l\\)"
            },
        "dl.equiv-right" :
            { "name" : "dl.equiv-right",
              "latex" : "TODO: \\(\\leftrightarrow r\\)"
            },
        "dl.not-left" :
            { "name" : "dl.not-left",
              "latex" : "\\(\\left(\\neg l \\right) \\frac{\\Gamma ~\\vdash~ \\phi,\\Delta}{\\Gamma,\\neg\\phi ~\\vdash~ \\Delta}\\)"
            },
        "dl.not-right" :
            { "name" : "dl.not-right",
              "latex" : "\\(\\left(\\neg r \\right) \\frac{\\Gamma, \\phi ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\neg \\phi, \\Delta}\\)"
            },
        "dl.close-true" :
            { "name" : "dl.close-true",
              "latex" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma ~\\vdash~ \\textit{true},\\Delta}\\)"
            },
        "dl.close-false" :
            { "name" : "dl.close-false",
              "latex" : "\\(\\left(\\textit{true} r \\right) \\frac{}{\\Gamma, \\textit{false} ~\\vdash~ \\Delta}\\)"
            },
        "dl.skolemize" :
            { "name" : "dl.skolemize",
              "latex" : "TODO: skolemize"
            },
        "dl.box-assign" :
            { "name" : "dl.box-assign",
              "latex" : "\\(\\left(\\left[\\coloneq\\right]\\right) \\frac{\\phi(t)}{\\left[x \\coloneq t\\right]\\phi(x)}\\)"
            },
        "dl.box-choice" :
            { "name" : "dl.box-choice",
              "latex" : "\\(\\left(\\left[\\cup\\right]\\right) \\frac{\\left[\\alpha\\right]\\phi \\qquad \\left[\\beta\\right]\\phi}{\\left[\\alpha \\cup \\beta\\right]\\phi}\\)"
            },
        "dl.box-induction" :
            { "name" : "dl.box-induction",
              "latex" : "\\(\\left(\\left[\\alpha^*\\right] \\text{induction}\\right) \\frac{\\left(\\phi \\wedge \\left[\\alpha^*\\right]\\left(\\phi \\rightarrow \\left[\\alpha\\right] \\phi \\right)\\right) }{\\left[\\alpha^*\\right]\\phi}\\)"
            },
        "dl.box-ndetassign" :
            { "name" : "dl.box-ndetassign",
              "latex" : "\\(\\left(\\left[\\coloneq *\\right]\\right) \\frac{\\forall x. \\phi(x)}{\\left[x \\coloneq *\\right]\\phi}\\)"
            },
        "dl.box-seq" :
            { "name" : "dl.box-seq",
              "latex" : "\\(\\left(\\left[\\;\\right]\\right) \\frac{\\left[\\alpha\\right]\\left[\\beta\\right]\\phi}{\\left[\\alpha;\\beta\\right]\\phi}\\)"
            },
        "dl.box-test" :
            { "name" : "dl.box-test",
              "latex" : "\\(\\left(\\left[\\?\\right]\\right) \\frac{H \\rightarrow \\phi)}{\\left[?H\\right]\\phi}\\)"
            }
    };

    var dispatchedTacticsIds = [];

    var dispatchedTacticsNotificationService = {};

    //    dispatchedTacticsNotificationService.message = '';

    dispatchedTacticsNotificationService.broadcastDispatchedTactics = function(tId) {
        $rootScope.$broadcast('handleDispatchedTactics', tId);
    };

    return {
        getTactics: function() { return tactics; },
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

        // TODO wait for proof to be loaded, then fetch tasks
    });
    $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});
  });

keymaeraProofControllers.controller('TaskListCtrl',
  function($scope, $http, $cookies, $routeParams, $q, Tasks, Tactics) {
    $scope.proofId = $routeParams.proofId;

    $http.get('proofs/user/' + $cookies.userId + "/" + $routeParams.proofId + '/tasks').success(function(data) {
        $scope.tasks = data;
    });

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
                    // TODO fetch the new open goals, update the tree, update the task list
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

    // Get & populate the tree.
    $scope.treedata = [];

    $scope.setSelected = function(task) {
        $scope.selectedTask = task;
        //pulling this variable out so that I can print it back out.
        var treeresource = "/proofs/user/" + $cookies.userId + "/tree/" + $scope.proofId + "/" + task.nodeId
        alert("getting tree data from \n" + "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree")
        $http.get("/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree")
                .success(function(data) {
            alert("setting tree data from \n" + "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree")
            $scope.treedata = data;
        });


    }

    $scope.$watch('tasks',
        function (newTasks) { if (newTasks) Tasks.setTasks(newTasks); }
    );
    $scope.$watch('selectedTask',
        function() { return Tasks.getSelectedTask(); },
        function(t) { if (t) Tasks.setSelectedTask(t); }
    );
    $scope.$watch('dispatchedTactics',
        function() { return Tactics.getDispatchedTactics(); },
        function(tId) { Tactics.removeDispatchedTactics(tId); }
    );
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Sequents and proof rules
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('ProofRuleDialogCtrl',
        function ($scope, $http, $cookies, $modalInstance, proofId, nodeId, formula, Tactics) {
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formula = formula;
  $scope.tactics = [];

  var fId = ((formula !== undefined) ? formula.id : "sequent")
  var uri = 'proofs/user/' + $cookies.userId + '/' + proofId + '/nodes/' + nodeId + '/formulas/' + fId + '/tactics'
  $http.get(uri).success(function(data) {
      $scope.tactics = [];
      for (var i = 0; i < data.length; i++) {
          var tacticName = data[i].name;
          var tactic = Tactics.getTactics()[tacticName];
          if (tactic !== undefined) {
            tactic.id = data[i].id;
            $scope.tactics.push(tactic);
          }
      }
  });

  $scope.applyTactics = function(t) {
    $http.post(uri + "/run/" + t.id)
            .success(function(data) {
        var dispatchedTacticId = data.tacticInstId;
        $modalInstance.close(dispatchedTacticId);
        Tactics.addDispatchedTactics(dispatchedTacticId);
        Tactics.getDispatchedTacticsNotificationService().broadcastDispatchedTactics(dispatchedTacticId);
    });
  }
  $scope.autoTactic = function() {
    // run on formula "sequent"
    alert("Auto")
  }
  $scope.stepTactic = function(f) {
    // if f undefined, run on formula "sequent"
    alert("Step")
  }
  $scope.hideTactic = function(f) {
    alert("Hide")
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

