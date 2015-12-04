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
            .error(function() {
                showErrorMessage($uibModal, "Proof failed to load.");
            })
     };

     $scope.addModel = function() {
          var file = keyFile.files[0];

          var fr = new FileReader();
          fr.onerror = function(e) { alert("Could not even open your file: " + e.getMessage()); };
          fr.onload = function(e) {
               $.ajax({
                     url: "user/" + $cookies.get('userId') + "/modeltextupload/" + $scope.modelName,
                     type: "POST",
                     data: e.target.result,
                     async: true,
                     dataType: 'json',
                     contentType: 'application/json',
                     success: function(data) {
                         if(data.errorThrown) {
                            $uibModal.open({
                               templateUrl: 'partials/error_alert.html',
                               controller: 'ErrorAlertCtrl',
                               size: 'md',
                               resolve: {
                                  action: function () { return "loading model"; },
                                  error: function () { return data; }
                               }});
                         }
                         else {
                            //Update the models list -- this should result in the view being updated?
                            while (Models.getModels().length != 0) {
                               Models.getModels().shift()
                            }
                            $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
                                if(data.errorThrown) showErrorMessage($uibModal, data, "Could not get models for user " + $cookies.get('userId'))
                                Models.addModels(data);
                                $route.reload();
                            })
                            .error(function() {
                                showErrorMessage($uibModal, "Could not retrieve model list.")
                            })
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

angular.module('keymaerax.controllers').controller('ModelListCtrl', function ($scope, $http, $cookies, $uibModal, $location, Models) {
  $scope.models = [];
  $http.get("models/users/" + $cookies.get('userId')).success(function(data) {
      if(data.errorThrown) showErrorMessage($uibModal, data, "Could not get models for user " + $cookies.get('userId'))
      $scope.models = data
  })
  .error(function() {
      showErrorMessage($uibModal, "Could not retrieve model list")
  })

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
    })
    .error(function() {
      showErrorMessage($uibModal, "Error While Running Tactic")
    });
  }

  $scope.$watch('models',
      function (newModels) { if (newModels) Models.setModels(newModels); }
  );
  $scope.$emit('routeLoaded', {theview: 'models'});
})

angular.module('keymaerax.controllers').controller('ModelDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid).success(function(data) {
      $scope.model = data
  });

  $scope.ok = function () { $modalInstance.close(); };
});

angular.module('keymaerax.controllers').controller('ModelTacticDialogCtrl', function ($scope, $http, $cookies, $modalInstance, modelid) {
  $http.get("user/" + $cookies.get('userId') + "/model/" + modelid + "/tactic").success(function(data) {
      $scope.tactic = data
  });

  $scope.ok = function () { $modalInstance.close(); };
});