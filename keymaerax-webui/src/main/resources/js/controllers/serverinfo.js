angular.module('keymaerax.controllers').controller('ServerInfoCtrl', ['$scope', '$uibModal', '$http', function ($scope, $uibModal, $http) {
  // Set the view for menu active class
  $scope.$on('routeLoaded', function (event, args) {
    $scope.theview = args.theview;
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
      });

    $scope.isLocal = true;
    $http.get('/isLocal')
        .success(function(data) {
            if(data.errorThrown) {
                $scope.isLocal = false;
                showCaughtErrorMessage($uibModal, data, "Could not determine if the KeYmaera X server is running locally")
            }
            $scope.isLocal = data.success;
        });

  $http.get('/licenses')
    .success(function(data) {
      if(data.errorThrown) {
        $scope.copyright = "Unable to retrieve copyright"
        $scope.copyrightShort = "Unable to retrieve copyright"
        $scope.license = "Unable to retrieve license"
        $scope.licensesThirdParty = "Unable to retrieve third-party licenses";
        showCaughtErrorMessage($uibModal, data, "Unable to retrieve copyright and licenses")
      }
      $scope.copyright = data.copyright
      $scope.copyrightShort = data.copyrightShort
      $scope.license = data.license
      $scope.licensesThirdParty = data.licensesThirdParty;
    });

  $scope.$emit('routeLoaded', {theview: 'dashboard'});
}]);

angular.module('keymaerax.controllers').controller('LicenseDialogCtrl', ['$scope', '$uibModalInstance', function($scope, $uibModalInstance) {
  $scope.rejectLicense = function() {
    alert("KeYmaera X cannot be used without accepting the license -- guest use/registration rejected");
    $uibModalInstance.dismiss('cancel')
  };

  $scope.ok = function() {
    $uibModalInstance.close('accept');
  }
}]);

angular.module('keymaerax.controllers').controller('ServerOfflineDialogCtrl', ['$scope', '$http', '$uibModalInstance', '$interval', function ($scope, $http, $uibModalInstance, $interval) {
  var heartbeat = $interval(function() {
    console.log("Pinging server...")
    $http.get("/isLocal").then(
    function(response) {
      $uibModalInstance.close();
      $interval.cancel(heartbeat);
      heartbeat = undefined;
      // reload proof (continuing proof without reloading );
      // do not reload models (model edit dialog disappears on reload and model may not be stored yet)
      if (location.hash.startsWith("#/proofs")) location.reload();
    },
    function(error) {
      // /isLocal is still failing == server is still offline
    });
  }, 10000);

}])
