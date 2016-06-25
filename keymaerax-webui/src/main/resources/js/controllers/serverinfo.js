angular.module('keymaerax.controllers').controller('ServerInfoCtrl', ['$scope', '$uibModal', '$cookies', '$http', function ($scope, $uibModal, $cookies, $http) {
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