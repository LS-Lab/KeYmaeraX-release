function showCaughtErrorMessage(modal, data, message) {
  console.error("Error was caught: " + message);
  modal.open({
    templateUrl: 'partials/error_alert.html',
    controller: 'ErrorAlertCtrl',
    size: 'lg',
    resolve: {
      action: function () { return message; },
      error: function () { return data; }
    }
  });
}

function showClientErrorMessage(modal, message) {
  console.error("Client-side error: " + message);
  modal.open({
    templateUrl: 'templates/clientErrorAlert.html',
    controller: 'ClientErrorAlertCtrl',
    size: 'md',
    resolve: {
      message: function () { return message; }
    }
  });
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

angular.module('keymaerax.errorHandlers', []).factory('ResponseErrorHandler', ['$q', '$injector', function($q, $injector) {

  var responseInterceptor = {
    responseError: function(rejection) {
      if (rejection.status === 500) {
        // report uncaught server-side exception
        var uibModal = $injector.get('$uibModal'); // inject manually to avoid circular dependency
        var modalInstance = uibModal.open({
          templateUrl: 'partials/error_alert.html',
          controller: 'ErrorAlertCtrl',
          size: 'lg',
          resolve: {
            url: function() { return rejection.config.url; },
            message: function () { return rejection.data.textStatus; },
            error: function () { return rejection.data; }
          }
        });
        $q.resolve(rejection);
      } else {
        $q.reject(rejection);
      }
    }
  }

  return responseInterceptor;

}]);

angular.module('keymaerax.controllers').controller('ErrorAlertCtrl', function($scope, $uibModalInstance, $uibModal, url, message, error) {
  $scope.errorText = message !== undefined && message !== '' ? message : 'Sorry, no message available. Please look at the stack trace.';
  $scope.url = url;
  $scope.errorTrace = error.errorThrown;
  $scope.stacktraceCollapsed = true;
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

angular.module('keymaerax.controllers').controller('ClientErrorAlertCtrl', function($scope, $uibModalInstance, $uibModal, message) {
  $scope.message = message;
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
  $scope.details = error.details;
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
