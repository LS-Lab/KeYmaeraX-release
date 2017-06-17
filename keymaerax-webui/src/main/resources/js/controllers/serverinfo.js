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
    $http.get("/isLocal").success(function(data) {
      // close the modal every time, because the failing /isLocal request will open another dialog...
      // when we're back online, we close the final window and it stays closed
      $uibModalInstance.close();
      $interval.cancel(heartbeat);
      heartbeat = undefined;
    });
  }, 10000);

}])
