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

keymaeraProofControllers.factory('Tactics', function () {

    var tactics = {
        "keymaera.imply-left" :
            // TODO add rules, move into own file
            { "name" : "keymaera.imply-left",
              "latex" : "\\(\\left[\\rightarrow r \\right] \\frac{\\Gamma, \\phi ~\\vdash~ \\psi,\\Delta}{\\Gamma ~\\vdash~ \\phi \\rightarrow \\psi,\\Delta}\\)"
            },
        "keymaera.and-left" :
            { "name" : "keymaera.and-left",
              "latex" : "\\(\\left[\\wedge l \\right] \\frac{\\Gamma, \\phi, \\psi ~\\vdash~ \\Delta}{\\Gamma,\\phi \\wedge \\psi ~\\vdash~ \\Delta}\\)"
            }
    };

    return {
        getTactics: function() {
            return tactics;
        }
    };
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
    });
//    $http.get('proofs/user/' + $cookies.userId + "/"+ $routeParams.proofId + "/root").success(function(data) {
//        $scope.proofTree = data
//    });
    $scope.$emit('routeLoaded', {theview: 'proofs/:proofId'});
  });

keymaeraProofControllers.controller('TaskListCtrl',
  function($scope, $http, $cookies, $routeParams, Tasks) {
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

    // Initialize the tree to an empty array.
    $scope.treedata = [];

    $scope.setSelected = function(task) {
        $scope.selectedTask = JSON.parse(task);
        //pulling this variable out so that I can print it back out.
        var treeresource = "/proofs/user/" + $cookies.userId + "/tree/" + "TASK ID HERE" + "/" + "NODE ID HERE"
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
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Sequents and proof rules
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('ProofRuleDialogCtrl',
        function ($scope, $http, $cookies, $modalInstance, proofid, taskid, nodeid, formulaid, formula, Tactics) {
  $scope.proofid = proofid;
  $scope.taskid = taskid;
  $scope.nodeid = nodeid;
  $scope.formulaid = formulaid;
  $scope.formula = formula;

  var uriPrefix = 'proofs/user/' + $cookies.userId + '/' + proofid + '/tasks/' + taskid;
  var uri =
    (nodeid !== undefined) ? ('/nodes/' + nodeid + '/formulas/' + formulaid + '/tactics')
                           : ('/formulas/' + formulaid + '/tactics');

  $http.get(uriPrefix + uri).success(function(data) {
      $scope.tactics = [];
      for (var i = 0; i < data.length; i++) {
          var tacticName = data[i].name;
          var tactic = Tactics.getTactics()[tacticName];
          $scope.tactics.push(tactic);
      }
  });

  $scope.applyTactics = function(t) {
    $http.post(uriPrefix + uri + "/run/" + t.id)
            .success(function(data) {
        alert("Tactic dispatched: " + data)
    });
  }

  $scope.cancel = function () {
    $modalInstance.dismiss('cancel');
  };

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

