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

keymaeraProofControllers.controller('ProofInfoCtrl',
    function($scope, $rootScope, $http, $cookies, $modal, $routeParams) {
        $scope.proof = {
            proofName: "blah"
        };

        //TODO: add functions  that allow renaming.
    }
)
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Mathematica Config
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

keymaeraProofControllers.controller('MathematicaConfig',
  function($scope, $rootScope, $http, $cookies, $modal, $routeParams) {
    $http.get("/config/mathematica/suggest")
      .success(function(data) {
          $scope.mathematicaConfigSuggestion = data
      })
      .error(function() {
          console.error("Unhandled error when attempting to get Mathematica configuration.")
      });

    $http.get("/config/mathematica")
      .success(function(data) {
          if (data.linkName !== "" && data.jlinkLibPath !== "") {
            $scope.linkName = data.linkName;
            $scope.jlinkLibPath = data.jlinkLibDir;
          }
//          else {
//            $http.get("/config/mathematica/suggest")
//                .success(function(data) {
//                    $scope.linkName = data.kernelPath + "/" + data.kernelName;
//                    $scope.jlinkLibPath = data.jlinkPath + "/" + data.jlinkName;
//                })
//          }
      })
      .error(function() {
          console.error("Unhandled error when attempting to get Mathematica configuration.")
      });

    $scope.configureMathematica = function() {
        var uri     = "/config/mathematica"
        var linkName = $scope.linkName ? $scope.linkName : "";
        var jlinkLibPath = $scope.jlinkLibPath ? $scope.jlinkLibPath : "";
        var dataObj = {linkName: linkName, jlinkLibDir: jlinkLibPath}

        $http.post(uri, dataObj)
            .success(function(data) {
                if (data.success) {
                    $scope.MathematicaForm.linkName.$setValidity("FileExists", true);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", true);

                    $modal.open({
                        templateUrl: 'partials/mathematicaconfig_update.html',
                        controller: 'MathematicaConfig.UpdateDialog',
                        size: 'md'
                    })

                    $("#mathematicaConfigurationAlert").hide();
                    $rootScope.mathematicaIsConfigured = data.configured;
                }
                else {
                    var kernelNameExists = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) > -1 &&
                      data.linkNamePrefix == $scope.linkName
                    var jlinkExists = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) > -1 &&
                      data.jlinkLibDirPrefix == $scope.jlinkLibPath

                    $scope.linkNameOkPrefix = data.linkNamePrefix
                    $scope.linkNameWrong = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) > -1 ?
                        $scope.linkName.substring(data.linkNamePrefix.length, $scope.linkName.length) :
                        ".../" + $scope.mathematicaConfigSuggestion.kernelName
                    $scope.linkNameIncomplete = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) == -1

                    $scope.jlinkLibPathOkPrefix = data.jlinkLibDirPrefix
                    $scope.jlinkLibPathWrong = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) > -1 ?
                      $scope.jlinkLibPath.substring(data.jlinkLibDirPrefix.length, $scope.jlinkLibPath.length) :
                      ".../" + $scope.mathematicaConfigSuggestion.jlinkName
                    $scope.jlinkPathIncomplete = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) == -1

                    $scope.MathematicaForm.linkName.$setValidity("FileExists", kernelNameExists);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", jlinkExists);
                }
            })
            .error(function(data) {
                alert("error: " + JSON.stringify(data))
            })
    }

    $scope.setDefaultMathKernel = function() {
      $scope.linkName = $scope.mathematicaConfigSuggestion.kernelPath + $scope.mathematicaConfigSuggestion.kernelName
    }

    $scope.setDefaultJLinkLibPath = function() {
      $scope.jlinkLibPath = $scope.mathematicaConfigSuggestion.jlinkPath + $scope.mathematicaConfigSuggestion.jlinkName
    }
});

keymaeraProofControllers.controller('MathematicaConfig.FailureDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});
keymaeraProofControllers.controller('MathematicaConfig.UpdateDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});

keymaeraProofControllers.controller('DashboardCtrl.ShutdownDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      alert("No!")
      $window.close();
  }
});


keymaeraProofControllers.controller('DashboardCtrl.ShutdownDialog', function($scope, $http, $cookies, $modalInstance) {
$scope.noModalForHelpDialogHack = true
});





////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

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
    var makeRuleLabel = function(name, top, bot) {
        return "\\(\\left(" + name + "  \\right) " + "\\frac{" + top + "}{" + bot + "}\\)";
    }

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
              "label" : "\\( \\left( \\forall r \\right) \\frac{\\Gamma ~\\vdash~ \\phi\\left(s\\left(X_1,\\ldots,X_n\\right)\\right)}{\\Gamma ~\\vdash~ \\forall x . \\phi(x), \\Delta} \\)"
            },
        "dl.decomposeQuan" :
            { "name" : "dl.decomposeQuan",
              "label" : "\\( \\left( \\textit{decompose} \\right) \\frac{(\\forall/\\exists) x_1. \\left( \\ldots (\\forall/\\exists) x_n . \\phi \\right)}{(\\forall/\\exists) \\vec{x} . \\phi } \\)"
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
        "dl.diffcut" :
            { "name" : "dl.diffcut",
              "label" : "\\(\\left(\\text{diff. cut}\\right) \\frac{\\Gamma ~\\vdash~ \\left[x'=\\theta \\& H \\right] C, \\Delta \\quad \\Gamma ~\\vdash~ \\left[x'=\\theta \\& H \\wedge C \\right]\\phi, \\Delta}{\\Gamma ~\\vdash~ \\left[x' = \\theta \\& H \\right] \\phi, \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "\\(C\\)", "placeholder" : "Formula", "type" : "text" } ]
            },
        "dl.diffsolution" :
            { "name" : "dl.diffsolution",
              "label" : "\\(\\left(\\text{ODE solve}\\right) \\frac{\\Gamma, H \\wedge S ~\\vdash~ \\Delta}{\\Gamma ~\\vdash~ \\left[x' = \\theta \\& H \\right] \\phi, \\Delta} \\text{ where } S \\text{ solves } x'=\\theta\\)",
            },
        "dl.qe" :
            { "name" : "dl.qe",
              "label" : "\\(\\left(\\text{QE}\\right) \\frac{\\text{QE}(\\phi)}{\\phi} \\)",
              "input" : [ { "name" : "0", "label" : "Tool", "placeholder" : "Mathematica", "type" : "text" } ]
            },
        "dl.diffinvariant" :
            {
                "name" : "dl.diffinvariant",
                "label" : makeRuleLabel("\\text{DI}",
                "\\Gamma, H ~\\vdash~ F, \\Delta \\quad \\Gamma ~\\vdash~\\forall^{\\alpha}(H \\rightarrow F_{x_1, \\ldots , x_n}^{\\theta_1, \\ldots , \\theta_n}, \\Delta)",
                "\\Gamma ~\\vdash~ \\left[ x_1' = \\theta_1, \\ldots , x_n' = \\theta_n, H \\right]F, \\Delta")
            },
        "dl.diffweaken" :
            {
                "name" : "dl.diffweaken",
                "label" : makeRuleLabel("\\text{DW}",
                "\\Gamma ~\\vdash~\\forall^{\\alpha}(H \\rightarrow \\phi, \\Delta)",
                "\\Gamma ~\\vdash~ \\left[ x' = \\theta \\& H \\right]\\phi, \\Delta")
            },
        "dl.diffconstify" :
            {
                "name" : "dl.diffconstify",
                "label" : makeRuleLabel("\\text{Dconstify}",
                "\\Gamma(\\theta()) ~\\vdash~ \\left[ x' = \\theta() \\& H(\\theta()) \\right]\\phi(\\theta()), \\Delta(\\theta())",
                "\\Gamma ~\\vdash~ \\left[ x' = \\theta \\& H \\right]\\phi, \\Delta")
            },
        "dl.equalityRewriting" :
            { "name" : "dl.equalityRewriting",
              "label" : "\\(\\left(= \\text{rewrite}\\right) \\frac{\\Gamma, \\phi(t) ~\\vdash \\psi(t), \\Delta}{\\Gamma, x=t, \\phi(x) ~\\vdash \\psi(x), \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "Assumption", "placeholder" : "ante:3", "type" : "text" },
                          { "name" : "1", "label" : "Position", "placeholder" : "succ:2,0", "type" : "text" },
                          { "name" : "2", "label" : "Disjoint", "placeholder" : "true", "type" : "text" }
               ]
            },
        "dl.instantiate" :
            { "name" : "dl.instantiate",
              "label" : "\\(\\left(\\forall l\\right) \\frac{\\Gamma,\\phi(X) ~\\vdash~ \\Delta}{\\Gamma, \\forall x \\phi(x) ~\\vdash~ \\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "x", "placeholder" : "v", "type" : "text" },
                          { "name" : "1", "label" : "X", "placeholder" : "term", "type" : "text" }
               ]
            },
        "dl.axiomClose" :
            { "name" : "dl.axiomClose",
              "label" : "\\(\\left(\\text{axiom close}\\right) \\frac{*}{\\Gamma,\\phi ~\\vdash~ \\phi,\\Delta}\\)",
              "input" : [ { "name" : "0", "label" : "antecedent", "placeholder" : "ante:0", "type" : "text" },
                          { "name" : "1", "label" : "succedent", "placeholder" : "succ:1", "type" : "text" }
               ]
            },
        "dl.hide" :
            { "name" : "dl.hide",
              "label" : "\\(\\left(\\text{weaken}\\right) \\frac{\\Gamma ~\\vdash~ \\Delta}{\\Gamma,\\phi ~\\vdash~ \\psi,\\Delta}\\)"
            },
        "keymaerax.arithmetic" :
            { "name" : "keymaerax.arithmetic",
              "label" : "\\(\\left(\\text{QE}\\right) \\frac{QE(\\forall X. \\Phi(X) ~\\vdash~ \\Psi(X))}{\\Phi(X_1,\\ldots,X_n) ~\\vdash~ \\Psi(X_1,\\ldots,X_n)}\\)"
            },
        "keymaerax.default":
            { "name" : "keymaerax.default",
              "label" : "KeYmaera Master Tactic"
            },
        "keymaerax.step":
            { "name": "keymaerax.step",
              "label": "KeYmaera Step Tactic"
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
//    dispatchedTacticsNotificationService.broadcastDispatchedTerm = function(termId) {
//            $rootScope.$broadcast('handleDispatchedTerm', termId);
//        };


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

keymaeraProofControllers.controller('DashboardCtrl.LicenseDialog', function($scope, $http, $modal, $cookies, $modalInstance) {
  $scope.rejectLicense = function() {
    alert("KeYmaera X cannot be used without accepting the license -- we are now shutting down KeYmaera X. To accept the license, restart KeYmaera X and click 'Accept'");
    $modalInstance.dismiss('cancel')

    var modalInstance = $modal.open({
      templateUrl: 'partials/shutdown_dialog.html',
      controller: 'DashboardCtrl.ShutdownDialog',
      backdrop: "static",
      size: 'sm'
    });

    $http.get("/shutdown")
  };

  $scope.cancel = function() {
    $http.post("/licenseacceptance")
        .success(function(data) {}) //ok
        .error(function() { console.error("Failed to udpate database after accepting license!")});
    $modalInstance.dismiss('cancel');
  }
});


keymaeraProofControllers.controller('DashboardCtrl',
  function ($scope, $modal, $cookies, $http) {
    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $scope.noModalForHelpDialogHack = false;
    $http.get("/licenseacceptance")
         .success(function(data) {
            if(!data.success && !$scope.licenseDialogDisplayed) {
                $scope.licenseDialogDisplayed = true;
                var modalInstance = $modal.open({
                  templateUrl: 'partials/license_dialog.html',
                  controller: 'DashboardCtrl.LicenseDialog',
                  backdrop: "static",
                  size: 'lg'
                });
            }
         })
         .error(function() {

         });

    $http.get("/keymaeraXVersion")
        .success(function(data) {
            $scope.keymaeraXVersion = data.keymaeraXVersion
        })
        .error(function() {
            console.error("Unhandled error when attempting to get KeYmaera X version.")
        });

    $scope.mathematicaIsConfigured = true;
    $http.get("/config/mathematicaStatus")
        .success(function(data) {
            $scope.mathematicaIsConfigured = data.configured;
        })
        .error(function() {
            console.error("Unhandled error when attempting to get Mathematica status.")
        });


    $http.get('/users/' + $cookies.userId + '/dashinfo')
        .success(function(data) {
            $scope.open_proof_count = data.open_proof_count;
            $scope.all_models_count = data.all_models_count;
            $scope.proved_models_count = data.proved_models_count;
        })


    $scope.isLocal = false;
    $http.get('/isLocal')
        .success(function(data) {
            $scope.isLocal = data.success;
        })

    $scope.shutdown = function() {
        var modalInstance = $modal.open({
          templateUrl: 'partials/shutdown_dialog.html',
          controller: 'DashboardCtrl.ShutdownDialog',
          backdrop: "static",
          size: 'sm'
        });

        $http.get("/shutdown")
    };

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  });

keymaeraProofControllers.controller('ModelUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, $route, $modal, Models) {

     $scope.runPreloadedProof = function(model) {
        $http.post("/models/users/" + $scope.userId + "/model/" + model.id + "/initialize")
            .success(function(data) {
                console.log("yay! Take the user to the proof load page?")
            })
     };

     $scope.addModel = function() {
          var file = keyFile.files[0];

          var fr = new FileReader();
          fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); };
          fr.onload = function(e) {
               $.ajax({
                     url: "user/" + $cookies.userId + "/modeltextupload/" + $scope.modelName,
                     type: "POST",
                     data: e.target.result,
                     async: true,
                     dataType: 'json',
                     contentType: 'application/json',
                     success: function(data) {
                         if(data.errorThrown) {
                            $modal.open({
                               templateUrl: 'partials/modelloadingerror.html',
                               controller: 'ModelUploadCtrl.ShowLoadingError',
                               size: 'md',
                                  resolve: {
                                     errorMsg: function () { return data.textStatus; }
                                   }});
                         }
                         else {
                            //Update the models list -- this should result in the view being updated?
                            while (Models.getModels().length != 0) {
                               Models.getModels().shift()
                            }
                            $http.get("models/users/" + $cookies.userId).success(function(data) {
                                Models.addModels(data);
                                $route.reload();
                            });
                         }
                     },
                     error: this.ajaxErrorHandler
               });
          };

          fr.readAsText(file);
     };

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

keymaeraProofControllers.controller('ModelUploadCtrl.ShowLoadingError', function($scope, $modalInstance, errorMsg) {
  $scope.error = errorMsg
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
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

    $scope.openTactic = function (modelid) {
        var modalInstance = $modal.open({
          templateUrl: 'partials/modeltacticdialog.html',
          controller: 'ModelTacticDialogCtrl',
          size: 'lg',
          resolve: {
            modelid: function () { return modelid; }
          }
        });
    };

    $scope.runTactic = function (modelid) {
      $http.post("user/" + $cookies.userId + "/model/" + modelid + "/tactic/run").success(function(data) {
          console.log("Done running tactic")
      });
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

keymaeraProofControllers.controller('ModelTacticDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.userId + "/model/" + modelid + "/tactic").success(function(data) {
      $scope.tactic = data
  });

  $scope.ok = function () {
    $modalInstance.close();
  };
});

keymaeraProofControllers.controller('ModelProofCreateCtrl',
  function ($scope, $http, $cookies, $routeParams, $location) {
   /*
   * Creates a new proof using a default name, so that the use doesn't have to enter new input.
   */
    $scope.createDefaultProofForModel = function(modelId) {
        var proofName        = "Untitled Proof"
        var proofDescription = ""
        var uri              = 'models/users/' + $cookies.userId + '/model/' + modelId + '/createProof'
        var dataObj          = {proofName : proofName, proofDescription : proofDescription}

        $http.post(uri, dataObj).
            success(function(data) {
                var proofid = data.id
                // we may want to switch to ui.router
                $location.path('proofs/' + proofid);
            }).
            error(function(data, status, headers, config) {
                console.log('Error starting new proof for model ' +modelId)
            });
    };
    $scope.createDefaultProof = function() {
      $scope.createDefaultProofForModel($routeParams.modelId)
    };

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
                console.log('Error starting new proof for model ' + $routeParams.modelId)
            });
    }
    $scope.$emit('routeLoaded', {theview: '/models/:modelId/proofs/create'})
  });

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// The proof lists
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

var pollProofStatus = function(proof, userId, http) {
   setTimeout(function() {
      http.get('proofs/user/' + userId + '/' + proof.id + '/status')
              .success(function(data) {
          if (data.status == undefined) {
            console.log("Continue polling proof status");
            pollProofStatus(proof, userId, http);
          } else if (data.status == 'loading') {
            console.log("Continue polling proof status");
            pollProofStatus(proof, userId, http);
          } else if (data.status == 'loaded') {
            console.log("Received proof status " + data.status);
            proof.loadStatus = data.status
          } else {
            console.error("Received unknown proof status " + data.status)
          }
      }).
      error(function(data, status, headers, config) {
          console.log('Unable to poll proof status.')
      });
  }, 1000);
}

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

    $scope.loadProof = function(proof) {
        proof.loadStatus = 'loading'
        $http.get('proofs/user/' + $cookies.userId + "/" + proof.id).success(function(data) {
            proof.loadStatus = data.loadStatus
            // when server loads proof itself asynchronously
            if (data.loadStatus == 'loading') {
              console.log("Start polling proof status");
              pollProofStatus(proof, $cookies.userId, $http);
            }
        }).
        error(function(data, status, headers, config) {
          // TODO check that it is a time out
          console.log("Start polling proof status");
          pollProofStatus(proof, $cookies.userId, $http);
        });
    }

    $scope.$emit('routeLoaded', {theview: 'allproofs'});
  });

// Proof list for an individual model
keymaeraProofControllers.controller('ModelProofsCtrl',
  function ($scope, $http, $cookies,$location, $routeParams) {
    $scope.openPrf = function(proofId) {
        $location.path('/proofs/' + proofId)
    }

    //Todo: should "inherit" this from the modelproofscreatectrl rather than copy/pasting here.
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
                console.log('Error starting new proof for model ' + $routeParams.modelId)
            });
    }

    $scope.loadProof = function(proof) {
      proof.loadStatus = 'loading'
      $http.get('proofs/user/' + $cookies.userId + "/" + proof.id).success(function(data) {
        proof.loadStatus = data.loadStatus
        // when server loads proof itself asynchronously
        if (data.loadStatus == 'loading') {
          console.log("Start polling proof status");
          pollProofStatus(proof, $cookies.userId, $http);
        }
      }).
      error(function(data, status, headers, config) {
        // TODO check that it is a time out
        console.log("Start polling proof status");
        pollProofStatus(proof, $cookies.userId, $http);
      });
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

    //Save a name edited using the inline editor.
    $scope.saveProofName = function(newName) {
      $http.post("proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/name/" + newName, {})
    };
  });

keymaeraProofControllers.controller('HACMSTreeCtrl',
  function($scope, $http, $cookies, $routeParams) {
    $scope.proofId = $routeParams.proofId;

$scope.treeContents = "asdf"
    { //grab tree data.
        var uri = "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/"
        $http.get(uri)
            .success(function(data) {
                $scope.treeContents = printNode(data);
            })
            .error(function() {
                console.log("Error encountered while trying to retrieve the tree.")
            })
    }


    var printNode = function(n) {
        if(n === null) {
            return "Could not load proof tree."
        }
        var childrenResults;
        if(n.children.length > 0) {
            childrenResults = "<ol>" + n.children.map(printNode) + "</ol>"
        }
        else {
            childrenResults = ""
        }
        return "<li>" + n.label + childrenResults + "</li>"
    };

    $scope.$emit('routeLoaded', {theview: '/prooftree/:proofId'})
  });

keymaeraProofControllers.controller('TaskListCtrl',
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
                    console.error('empty agenda even though proof is not closed (' + data.status + ')')
                  }
                })
                .error(function() {
                  console.error("error retrieving proof progress")
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
                        if (data.tacticInstStatus == 'Running' || data.errorThrown) {
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
                      var agendaItem = {
                        "nodeId": proofNode.id,
                        "proofNode": proofNode,
                        "readOnly": true
                      }
                      $scope.setSelected(agendaItem);
                  })
                  .error(function() {
                      var msg = "Error: this proof is not on the Agenda and the server could not find it.";
                      console.error(msg);
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
                    alert("Error when trying to run your custom tactic: " + JSON.stringify(data))
                }
                else {
//                    Tactics.getDispatchedTacticsNotificationService().broadcastDispatchedTerm(data.id)
                    $rootScope.$broadcast('handleDispatchedTerm', data.id);
                }
             })
             .error(function() {
                console.error("encountered error during post on runTerm.")
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
                            if (data.status == 'Running' || data.errorThrown) { //Errors might be thrown if the term isn't created yet...
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
              console.log("pretty printing undefined for tactic " + tacticName)
            }
          }
        })
        .error(function() {
          console.error("error encountered while trying to retrieve the proof history.")
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
        console.error("error encountered while trying to retrieve the proof history details.")
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
        console.error("error when validating proof")
      })
    }
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
                tooltip: tactic.tooltip,
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

