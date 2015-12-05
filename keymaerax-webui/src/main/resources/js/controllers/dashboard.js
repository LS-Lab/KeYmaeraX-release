angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      alert("KeYmaeraX is shut down. Please close the window and restart the server to continue using KeYmaera X.")
      $window.close();
  }
});

angular.module('keymaerax.controllers').controller('DashboardCtrl.ShutdownDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.noModalForHelpDialogHack = true
});

angular.module('keymaerax.controllers').controller('DashboardCtrl.LicenseDialog', function($scope, $http, $uibModal, $cookies, $modalInstance) {
  $scope.rejectLicense = function() {
    alert("KeYmaera X cannot be used without accepting the license -- we are now shutting down KeYmaera X. To accept the license, restart KeYmaera X and click 'Accept'");
    $modalInstance.dismiss('cancel')

    var modalInstance = $uibModal.open({
      templateUrl: 'partials/shutdown_dialog.html',
      controller: 'DashboardCtrl.ShutdownDialog',
      backdrop: "static",
      size: 'sm'
    });

    $http.get("/shutdown")
  };

  $scope.cancel = function() {
    $http.post("/licenseacceptance")
        .success(function(data) {
            if(data.errorThrown) {
                showCaughtErrorMessage($uibModal, data, "License Acceptance Failed")
            }
        }) //ok
        .error(function() {
            showErrorMessage($uibModal, "License Acceptance Failed")
        });
    $modalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('DashboardCtrl', function ($scope, $uibModal, $cookies, $http) {
  // Set the view for menu active class
  $scope.$on('routeLoaded', function (event, args) {
    $scope.theview = args.theview;
  });

  $scope.noModalForHelpDialogHack = false;
  $http.get("/licenseacceptance")
       .success(function(data) {
          if(!data.success && !$scope.licenseDialogDisplayed) {
              $scope.licenseDialogDisplayed = true;
              var modalInstance = $uibModal.open({
                templateUrl: 'partials/license_dialog.html',
                controller: 'DashboardCtrl.LicenseDialog',
                backdrop: "static",
                size: 'lg'
              });
          }
       })
       .error(function() {
          showErrorMessage($uibModal, "Failed to Query for License Acceptance.");
       });

  $http.get("/keymaeraXVersion")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not get the server's KeYmaera X version")
          else  {
              $scope.keymaeraXVersion = data.keymaeraXVersion
              if(data.upToDate != null) {
                  $scope.versionInfoAvailable = true
                  $scope.upToDate = data.upToDate
                  $scope.latestVersion = data.latestVersion
              }
              else {
                  $scope.versionInfoAvailable = false
              }
          }
      })
      .error(function() {
          var message = "Unhandled error when attempting to get KeYmaera X version."
          showErrorMessage($uibModal, message);
      });

  $scope.mathematicaIsConfigured = true;
  $http.get("/config/mathematicaStatus")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not retrieve Mathematica status")
          else
              $scope.mathematicaIsConfigured = data.configured;
      })
      .error(function() {
          var message = "Unhandled error when attempting to get Mathematica status.";
          showErrorMessage($uibModal, message);
      });


  $http.get('/users/' + $cookies.get('userId') + '/dashinfo')
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not retrieve dashboard info for user " + $cookies.get('userId'))
          else {
              $scope.open_proof_count = data.open_proof_count;
               $scope.all_models_count = data.all_models_count;
              $scope.proved_models_count = data.proved_models_count;
          }
      })
      .error(function() {
          showErrorMessage($uibModal, "Failed to get dashInfo for this uer.")
      })


  $scope.isLocal = false;
  $http.get('/isLocal')
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Could not determine if the KeYmaera X server is running locally")
          $scope.isLocal = data.success;
      })
      .error(function() {
          showErrorMessage($uibModal, "Error encountered when trying to determine if the KeYmaera X server is running locally.")
      })

  $scope.shutdown = function() {
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/shutdown_dialog.html',
        controller: 'DashboardCtrl.ShutdownDialog',
        backdrop: "static",
        size: 'sm'
      });

      $http.get("/shutdown")
           .error(function() {
              showErrorMessage($uibModal, "Failed to shutdown! Server may already be offline.");
           })
  };

  $scope.$emit('routeLoaded', {theview: 'dashboard'});
});