angular.module('keymaerax.controllers').controller('ModelUploadCtrl',
  function ($scope, $http, $cookies, $cookieStore, $route, $uibModal, Models) {

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

     $scope.addModel = function() {
          var file = keyFile.files[0];

          var fr = new FileReader();
          fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); };
          fr.onload = function(e) {
            var model = e.target.result;
            $http.post("user/" + $cookies.get('userId') + "/modeltextupload/" + $scope.modelName, model)
              .then(function(response) {
                if(!response.data.success) {
                  if(response.data.errorText) {
                    showMessage($uibModal, "Error Uploading Model", response.data.errorText, "md")
                  }
                  else {
                    showMessage($uibModal, "Unknown Error Uploading Model", "An unknown error that did not raise an uncaught exception occurred while trying to insert a model into the database. Perhaps see the server console output for more information.", "md")
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
                    model: function () { return model; },
                    error: function () { return err.data; }
                }});
              });
          };

          fr.readAsText(file);
     };

     $scope.importRepo = function(repoUrl) {
      $http.post("models/users/" + $cookies.get('userId') + "/importRepo", repoUrl).success(function(data) {
        $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
          Models.addModels(data);
          $route.reload();
        });
      })
     }

     $scope.$watch('models',
        function () { return Models.getModels(); }
     );

     $scope.$emit('routeLoaded', {theview: 'models'});
});

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $cookies, $uibModal, $location, Models) {
  $scope.models = [];
  $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
      $scope.models = data;
  });

  $scope.examples = [];
  $http.get("examplesList/").success(function(data) {
      $scope.examples = data;
  });

  $scope.open = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeldialog.html',
        controller: 'ModelDialogCtrl',
        size: 'lg',
        resolve: {
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.openTactic = function (modelid) {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/modeltacticdialog.html',
        controller: 'ModelTacticDialogCtrl',
        size: 'lg',
        resolve: {
          modelid: function () { return modelid; }
        }
      });
  };

  $scope.runTactic = function (modelid) {
    $http.post("user/" + $cookies.get('userId') + "/model/" + modelid + "/tactic/run")
    .success(function(data) {
        if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Error While Running Tactic")
        else console.log("Done running tactic")
    });
  }

  $scope.$watch('models',
      function (newModels) { if (newModels) Models.setModels(newModels); }
  );
  $scope.$emit('routeLoaded', {theview: 'models'});
})

angular.module('keymaerax.controllers').controller('ModelDialogCtrl', function ($scope, $http, $cookies, $uibModalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid).success(function(data) {
      $scope.model = data
  });

  $scope.ok = function () { $uibModalInstance.close(); };
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $cookies, $uibModalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid + "/tactic").success(function(data) {
      $scope.tactic = data
  });

  $scope.ok = function () { $uibModalInstance.close(); };
});