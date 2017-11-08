angular.module('keymaerax.controllers').controller('FormulaUploadCtrl',
  function ($scope, $http, $route, $uibModal, Models, sessionService, spinnerService) {
    $scope.userId = sessionService.getUser();

    $scope.addModelFromFormula = function(modelName, formula) {
      $http.post('/user/' + $scope.userId + '/modelFromFormula/' + modelName, formula)
          .success(function(data) {
            if(data.errorThrown) {
              console.log("Could not create the model because " + JSON.stringify(data))
              showCaughtErrorMessage($uibModal, data, "Model Creation Failed")
            }
            else {
              $route.reload();
            }
          })
    }
  }
);

angular.module('keymaerax.controllers').controller('ModelUploadCtrl',
  function ($scope, $http, $route, $uibModalInstance, $uibModal, $location, Models, sessionService, spinnerService) {
     /** Model data */
     $scope.model = {
       uri: undefined,
       modelName: undefined,
       content: undefined,
       kind: 'kyx'
     };

     $scope.updateModelContentFromFile = function(fileName, fileContent) {
       if (!(fileName.endsWith('.kyx') || fileName.endsWith('.kyx.txt') ||
             fileName.endsWith('.kya') || fileName.endsWith('.kya.txt'))) {
         showMessage($uibModal, "Unknown file extension",
                                "Expected file extension: .kyx / .kya / .kyx.txt / .kya.txt", "md");
       } else {
         var isKyx = fileName.endsWith('.kyx') || fileName.endsWith('.kyx.txt');
         $scope.model.kind = isKyx ? 'kyx' : 'kya';
         $scope.model.content = fileContent;
         $scope.model.uri = "file://" + fileName;
       }
     };

     $scope.updateModelContentFromURL = function() {
       if ($scope.model.uri && !$scope.model.uri.startsWith('file://') &&
            ($scope.model.uri.endsWith('.kyx') || $scope.model.uri.endsWith('.kyx.txt')
            || $scope.model.uri.endsWith('.kya') || $scope.model.uri.endsWith('.kya.txt'))) {
         $http.get($scope.model.uri).then(function(response) {
            var isKyx = $scope.model.uri.endsWith('.kyx') || $scope.model.uri.endsWith('.kyx.txt');
            $scope.model.kind = isKyx ? 'kyx' : 'kya';
            $scope.model.content = response.data;
         })
       }
     }

     $scope.uploadContent = function(startProof) {
       var url =  "user/" + sessionService.getUser() +
         ($scope.model.kind == 'kya' ? "/archiveupload/" : "/modeltextupload/" + $scope.model.modelName);
       upload(url, $scope.model.content, startProof && $scope.model.kind == 'kyx');
     }

     $scope.close = function() { $uibModalInstance.close(); };

     var upload = function(url, content, startProof) {
       spinnerService.show('caseStudyImportSpinner');
       $http.post(url, content)
         .then(function(response) {
           if (!response.data.success) {
             if (response.data.errorText) {
               showMessage($uibModal, "Error Uploading Model", response.data.errorText, "md")
             } else {
               showMessage($uibModal, "Unknown Error Uploading Model", "An unknown error that did not raise an uncaught exception occurred while trying to insert a model into the database. Perhaps see the server console output for more information.", "md")
             }
           } else { //Successfully uploaded model!
             $scope.close();
             var modelId = response.data.modelId;
             if (startProof) {
               var uri = 'models/users/' + sessionService.getUser() + '/model/' + modelId + '/createProof'
               $http.post(uri, {proofName: '', proofDescription: ''}).
                 success(function(data) { $location.path('proofs/' + data.id); }).
                 error(function(data, status, headers, config) {
                   console.log('Error starting new proof for model ' + modelId)
                 });
             } else {
               //Update the models list -- this should result in the view being updated?
               while (Models.getModels().length != 0) {
                 Models.getModels().shift()
               }
               $http.get("models/users/" + sessionService.getUser()).success(function(data) {
                 Models.addModels(data);
                 $route.reload();
               });
             }
           }
         })
         .catch(function(err) {
           $uibModal.open({
             templateUrl: 'templates/parseError.html',
             controller: 'ParseErrorCtrl',
             size: 'lg',
             resolve: {
               model: function () { return content; },
               error: function () { return err.data; }
           }});
         })
         .finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
     }

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $uibModal, $route,
    $location, FileSaver, Blob, Models, spinnerService, sessionService, firstTime) {
  $scope.models = [];
  $scope.userId = sessionService.getUser();
  $scope.intro.firstTime = firstTime;

  $scope.intro.introOptions = {
    steps: [
    {
        element: '#modelarchiving',
        intro: "Extract all models (with or without) their proofs into a .kya archive file.",
        position: 'bottom'
    },
    {
        element: '#modelupload',
        intro: "Upload .kyx model files or .kya archive files.",
        position: 'bottom'
    },
    {
        element: '#modeltutorialimport',
        intro: "Click 'Import' to add tutorials to your models overview.",
        position: 'bottom'
    },
    {
        element: '#modelopen',
        intro: "Inspect model definitions.",
        position: 'bottom'
    },
    {
        element: '#modelactions',
        intro: "Start new proofs, generate monitor conditions, and synthesize test cases here.",
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

  $http.get("models/users/" + $scope.userId).then(function(response) {
      $scope.models = response.data;
  });

  $scope.examples = [];
  $scope.activeTutorialSlide = 0;
  $http.get("examples/user/" + $scope.userId + "/all").then(function(response) {
      $scope.examples = response.data;
  });

  $scope.open = function (modelId) {
    var modalInstance = $uibModal.open({
      templateUrl: 'partials/modeldialog.html',
      controller: 'ModelDialogCtrl',
      size: 'fullscreen',
      resolve: {
        userid: function() { return $scope.userId; },
        modelid: function() { return modelId; },
        mode: function() { return Models.getModel(modelId).isExercise ? 'exercise' : 'edit'; }
      }
    });
  };

  $scope.openNewModelDialog = function() {
    $uibModal.open({
      templateUrl: 'templates/modeluploaddialog.html',
      controller: 'ModelUploadCtrl',
      size: 'fullscreen'
    });
  };

  $scope.importRepo = function(repoUrl) {
    spinnerService.show('caseStudyImportSpinner');
    var userId = sessionService.getUser();
    $http.post("models/users/" + userId + "/importRepo", repoUrl).success(function(data) {
      $http.get("models/users/" + userId).success(function(data) {
        Models.addModels(data);
        if($location.path() == "/models") {
          $route.reload();
        } else {
          $location.path( "/models" );
        }
      }).finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
    })
  };

  $scope.deleteModel = function(modelId) {
    $http.post("/user/" + sessionService.getUser() + "/model/" + modelId + "/delete").success(function(data) {
      if(data.errorThrown) {
        showCaughtErrorMessage($uibModal, data, "Model Deleter")
      } else {
        console.log("Model " + modelId + " was deleted. Getting a new model list and reloading the route.")
        $http.get("models/users/" + sessionService.getUser()).success(function(data) {
          Models.addModels(data);
          $route.reload();
        });
      }
    })
  };

  $scope.downloadModel = function(modelid) {
    $http.get("user/" + $scope.userId + "/model/" + modelid).then(function(response) {
      var modelName = response.data.name;
      var fileContent = new Blob([response.data.keyFile], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(fileContent, modelName + '.kyx');
    });
  }

  currentDateString = function() {
    var today = new Date();
    var dd = today.getDate();
    var mm = today.getMonth() + 1; //@note January is 0
    var yyyy = today.getFullYear();

    if(dd < 10) dd = '0' + dd
    if(mm < 10) mm='0'+mm
    return mm + dd + yyyy;
  }

  $scope.downloadAllModels = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/noProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'models_' + currentDateString() + '.kya');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  $scope.downloadModels = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/noProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'models_' + currentDateString() + '.kya');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  //@note almost duplicate of proofs.js downloadAllProofs
  $scope.downloadAllProofs = function() {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/downloadAllModels/withProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, 'proofs_'+ currentDateString() +'.kya');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  //@note duplicate of proofs.js downloadModelProofs
  $scope.downloadModelProofs = function(modelId) {
    spinnerService.show('modelProofExportSpinner');
    $http.get("/models/user/" + $scope.userId + "/model/" + modelId + "/downloadProofs").then(function(response) {
      var data = new Blob([response.data.fileContents], { type: 'text/plain;charset=utf-8' });
      FileSaver.saveAs(data, modelId + '_' + currentDateString() + '.kya');
    })
    .finally(function() { spinnerService.hide('modelProofExportSpinner'); });
  }

  $scope.openTactic = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeltacticdialog.html',
        controller: 'ModelTacticDialogCtrl',
        size: 'fullscreen',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.runTactic = function (modelid) {
    $http.post("user/" + $scope.userId + "/model/" + modelid + "/tactic/run").then(function(response) {
        if (respnse.data.errorThrown) showCaughtErrorMessage($uibModal, response.data, "Error While Running Tactic");
        else console.log("Done running tactic");
    });
  }

  $scope.modelplex = function(modelid) {
    var modalInstance = $uibModal.open({
      templateUrl: 'templates/modelplex.html',
      controller: 'ModelPlexCtrl',
      size: 'fullscreen',
      resolve: {
        userid: function() { return $scope.userId; },
        modelid: function() { return modelid; }
      }
    })
  }

  $scope.testsynthesis = function(modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'templates/testsynthesis.html',
        controller: 'TestSynthCtrl',
        size: 'lg',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function() { return modelid; }
        }
      })
    }

  $scope.$watch('models',
      function (newModels) { if (newModels) Models.setModels(newModels); }
  );
  $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelDialogCtrl',
    function ($scope, $http, $uibModal, $uibModalInstance, $location, Models, userid, modelid, mode) {
  $scope.mode = mode;

  $http.get("user/" + userid + "/model/" + modelid).then(function(response) {
      $scope.model = response.data;
      $scope.origModel = JSON.parse(JSON.stringify(response.data)); // deep copy
  });

  /** Deletes all proofs of the model */
  $scope.deleteModelProofs = function() {
    $http.post('user/' + userid + "/model/" + modelid + "/deleteProofs").success(function(data) {
      if (data.success) {
        $scope.model.numProofs = 0;
      }
    });
  }

  $scope.saveModelData = function() {
    if ($scope.origModel.name !== $scope.model.name || $scope.origModel.title !== $scope.model.title
     || $scope.origModel.description !== $scope.model.description
     || $scope.origModel.keyFile !== $scope.model.keyFile) {
      if ($scope.model.numProofs > 0) {
        var modelCopyName = $scope.model.name + ' (Copy ';
        var i = 1;
        while ($scope.checkName(modelCopyName + i + ')') !== true) { ++i; }
        var url = "user/" + userid + "/modeltextupload/" + modelCopyName + i + ')';
        $http.post(url, $scope.model.keyFile).then(function(response) {
          $scope.model.id = response.data.modelId;
          $scope.model.name = modelCopyName + i + ')';
          $scope.origModel = JSON.parse(JSON.stringify($scope.model)); // deep copy
        })
        .catch(function(err) {
          $uibModal.open({
            templateUrl: 'templates/parseError.html',
            controller: 'ParseErrorCtrl',
            size: 'lg',
            resolve: {
              model: function () { return $scope.model.keyFile; },
              error: function () { return err.data; }
          }});
        });
      } else {
        var data = {
          name: $scope.model.name,
          title: $scope.model.title,
          description: $scope.model.description,
          content: $scope.model.keyFile
        };
        $http.post("user/" + userid + "/model/" + modelid + "/update", data).then(function(response) {
          var model = Models.getModel(modelid);
          model.name = $scope.model.name;
          model.title = $scope.model.title;
          model.description = $scope.model.description;
          model.keyFile = $scope.model.keyFile;
          $scope.origModel = JSON.parse(JSON.stringify($scope.model)); // deep copy
        })
        .catch(function(err) {
          $uibModal.open({
            templateUrl: 'templates/parseError.html',
            controller: 'ParseErrorCtrl',
            size: 'lg',
            resolve: {
              model: function () { return $scope.model.keyFile; },
              error: function () { return err.data; }
          }});
        });
      }
    }
  }

  $scope.startProof = function() {
    $uibModalInstance.close();
    var uri = 'models/users/' + userid + '/model/' + $scope.model.id + '/createProof'
    $http.post(uri, {proofName: '', proofDescription: ''}).
      success(function(data) { $location.path('proofs/' + data.id); }).
      error(function(data, status, headers, config) {
        console.log('Error starting new proof for model ' + modelid)
      });
  }

  $scope.modelIsComplete = function() { return $scope.model && $scope.model.keyFile.indexOf('__________') < 0; }

  $scope.checkName = function(name) {
    var nameIsUnique = $.grep(Models.getModels(), function(m) { return m.name === name && m.id !== modelid; }).length == 0;
    if (name === undefined || name === "") return "Name is mandatory. Please enter a name.";
    else if (!nameIsUnique) return "Model with name " + name + " already exists. Please choose a different name."
    else return true;
  }

  $scope.ok = function() {
    $uibModalInstance.close();
    // Update the models list
    while (Models.getModels().length != 0) { Models.getModels().shift(); }
    $http.get("models/users/" + userid).success(function(data) {
      Models.addModels(data);
    });
  };
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $uibModalInstance, userid, modelid) {
  $http.get("user/" + userid + "/model/" + modelid + "/tactic").then(function(response) {
      $scope.modelId = modelid;
      $scope.tactic = response.data;
  });

  $scope.ok = function () { $uibModalInstance.close(); };
});
