angular.module('keymaerax.controllers').controller('FormulaUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, $route, $uibModal, Models, spinnerService) {
    $scope.userId = $cookies.get('userId');

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
  function ($scope, $http, $cookies, $cookieStore, $route, $uibModal, Models, spinnerService) {

     $scope.runPreloadedProof = function(model) {
        $http.post("/models/users/" + $scope.userId + "/model/" + model.id + "/initialize")
            .success(function(data) {
                if(data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Proof Preloader")
                } else {
                    console.log("yay! Take the user to the proof load page?")
                }
            })
     };

      $scope.deleteModel = function(modelId) {
          $http.post("/user/" + $cookies.get('userId') + "/model/" + modelId + "/delete").success(function(data) {
              if(data.errorThrown) {
                  showCaughtErrorMessage($uibModal, data, "Model Deleter")
              } else {
                  console.log("Model " + modelId + " was deleted. Getting a new model list and reloading the route.")
                  $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
                      Models.addModels(data);
                      $route.reload();
                  });
              }
          })
      };

     $scope.numFilesAvailable = function() {
       return keyFile == undefined || keyFile.files == undefined ? 0 : keyFile.files.length
     }

     $scope.isKyxFile = function() {
       return $scope.numFilesAvailable() > 0 && keyFile.files[0].name.endsWith('.kyx');
     }

     $scope.isKyaFile = function() {
       return $scope.numFilesAvailable() > 0 && keyFile.files[0].name.endsWith('.kya');
     }

     $scope.addModel = function(modelName) {
          var file = keyFile.files[0];

          var fr = new FileReader();
          fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); };
          fr.onload = function(e) {

            var fileContent = e.target.result;
            var url = "user/" + $cookies.get('userId');
            if (file.name.endsWith('.kyx')) url = url + "/modeltextupload/" + modelName;
            else if (file.name.endsWith('.kya')) url = url + "/archiveupload/";

            spinnerService.show('caseStudyImportSpinner');

            $http.post(url, fileContent)
              .then(function(response) {
                if(!response.data.success) {
                  if(response.data.errorText) {
                    showMessage($uibModal, "Error Uploading File", response.data.errorText, "md")
                  }
                  else {
                    showMessage($uibModal, "Unknown Error Uploading File", "An unknown error that did not raise an uncaught exception occurred while trying to insert a model into the database. Perhaps see the server console output for more information.", "md")
                  }
                }
                else { //Successfully uploaded model!
                  //Update the models list -- this should result in the view being updated?
                  while (Models.getModels().length != 0) {
                    Models.getModels().shift()
                  }
                  $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
                    Models.addModels(data);
                    $route.reload();
                  });
                }
              })
              .catch(function(err) {
                $uibModal.open({
                  templateUrl: 'templates/parseError.html',
                  controller: 'ParseErrorCtrl',
                  size: 'lg',
                  resolve: {
                    model: function () { return fileContent; },
                    error: function () { return err.data; }
                }});
              })
              .finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
          };

          fr.readAsText(file);
     };

     $scope.importRepo = function(repoUrl) {
      spinnerService.show('caseStudyImportSpinner');
      $http.post("models/users/" + $cookies.get('userId') + "/importRepo", repoUrl).success(function(data) {
        $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
          Models.addModels(data);
          $route.reload();
        }).finally(function() { spinnerService.hide('caseStudyImportSpinner'); });
      })
     }

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $cookies, $uibModal,
    $location, FileSaver, Blob, Models, spinnerService, firstTime) {
  $scope.models = [];
  $scope.userId = $cookies.get('userId');
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
  $http.get("examples/user/" + $scope.userId + "/all").then(function(response) {
      $scope.examples = response.data;
  });

  $scope.open = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeldialog.html',
        controller: 'ModelDialogCtrl',
        size: 'lg',
        resolve: {
          userid: function() { return $scope.userId; },
          modelid: function () { return modelid; }
        }
      });
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
        size: 'lg',
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
      size: 'lg',
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
})

angular.module('keymaerax.controllers').controller('ModelDialogCtrl', function ($scope, $http, $uibModalInstance, Models, userid, modelid) {
  $http.get("user/" + userid + "/model/" + modelid).then(function(response) {
      $scope.model = response.data;
  });

  $scope.saveModelData = function() {
    var data = {
      name: $scope.model.name,
      title: $scope.model.title,
      description: $scope.model.description
    };
    $http.post("user/" + userid + "/model/" + modelid + "/update", data).then(function(response) {
      var model = $.grep(Models.getModels(), function(m) { return m.id === modelid; })[0];
      model.name = $scope.model.name;
      model.title = $scope.model.title;
      model.description = $scope.model.description;
    })
  }

  $scope.checkName = function(name) {
    var nameIsUnique = $.grep(Models.getModels(), function(m) { return m.name === name && m.id !== modelid; }).length == 0;
    if (name === undefined || name === "") return "Name is mandatory. Please enter a name.";
    else if (!nameIsUnique) return "Model with name " + name + " already exists. Please choose a different name."
    else return true;
  }

  $scope.ok = function() { $uibModalInstance.close(); };
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $uibModalInstance, userid, modelid) {
  $http.get("user/" + userid + "/model/" + modelid + "/tactic").then(function(response) {
      $scope.modelId = modelid;
      $scope.tactic = response.data;
  });

  $scope.ok = function () { $uibModalInstance.close(); };
});