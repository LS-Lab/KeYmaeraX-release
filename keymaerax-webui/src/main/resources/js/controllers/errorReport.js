function showCaughtErrorMessage(modal, data, message) {
  console.error("Error was caught: " + message)
  modal.open({
    templateUrl: 'partials/error_alert.html',
    controller: 'ErrorAlertCtrl',
    size: 'md',
    resolve: {
      action: function () { return message; },
      error: function () { return data; }
    }
  });
}
function showErrorMessage(modal, message) {
  var data = {
    errorText: "Error was not properly handled by server, so we did not get an error info response. See server STDOUT and STDERR for more info."
  }
  showCaughtErrorMessage(modal, data, message)
}

angular.module('keymaerax.controllers').controller('ErrorAlertCtrl', function($scope, $modalInstance, $modal, action, error) {
  $scope.action = action;
  $scope.errorText = error.textStatus;
  $scope.errorTrace = error.errorThrown;
  $scope.report = function() {
    $modalInstance.dismiss('cancel');
    var modalInstance = $modal.open({
        templateUrl: 'partials/error_report.html',
        controller: 'ErrorReportCtrl',
        size: 'md',
        resolve: {
           error: function () { return error; }
        }
    });
  }
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('ErrorReportCtrl', function($scope, $modalInstance, $http, error) {
  $http.get("/kyxConfig").success(function(data) {
    $scope.kyxConfig = data.kyxConfig;
    });
  $scope.errorText = error.textStatus;
  $scope.errorTrace = error.errorThrown;
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});
