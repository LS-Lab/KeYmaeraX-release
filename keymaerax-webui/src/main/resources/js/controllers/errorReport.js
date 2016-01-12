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

function showMessage(modal, title, message, size) {
  var modalInstance = modal.open({
    templateUrl: 'templates/modalMessageTemplate.html',
    controller: 'ModalMessageCtrl',
    size: size,
    resolve: {
      title: function() { return title; },
      message: function() { return message; }
    }
  })
}

angular.module('keymaerax.controllers').controller('ErrorAlertCtrl', function($scope, $uibModalInstance, $uibModal, action, error) {
  $scope.action = action;
  $scope.errorText = error.textStatus;
  $scope.errorTrace = error.errorThrown;
  $scope.report = function() {
    $uibModalInstance.dismiss('cancel');
    var modalInstance = $uibModal.open({
        templateUrl: 'partials/error_report.html',
        controller: 'ErrorReportCtrl',
        size: 'md',
        resolve: {
           error: function () { return error; }
        }
    });
  }
  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('ParseErrorCtrl', function($scope, $uibModal, $uibModalInstance, error, model) {
  $scope.message = error.textStatus;
  $scope.location = error.location;
  $scope.stacktraceCollapsed=true;
  $scope.errorThrown = error.errorThrown;
  $scope.dismiss = function() { $uibModalInstance.dismiss('OK'); }
  $scope.modelWithErrorMsg = function() {
    var lines = $.map(model.split('\n'), function(e, i) { return (i+1) + ': ' + e; });
    var lineStr = error.location.line + ': ';
    var inlineErrorMsg = new Array(lineStr.length + error.location.column).join(' ') + '^----' + error.textStatus;
    lines.splice(error.location.line, 0, inlineErrorMsg);
    return lines.join('\n');
  }
});

angular.module('keymaerax.controllers').controller('ErrorReportCtrl', function($scope, $uibModalInstance, $http, error) {
  $http.get("/kyxConfig").success(function(data) {
    $scope.kyxConfig = data.kyxConfig;
    });
  $scope.errorText = error.textStatus;
  $scope.errorTrace = error.errorThrown;
  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('ModalMessageCtrl', function($scope, $uibModalInstance, title, message) {
  $scope.title = title;
  $scope.message = message;
  $scope.ok = function() { $uibModalInstance.close(); }
});
