function showCaughtErrorMessage(modal, data, message) {
  console.error("Error was caught: " + message);
  modal.open({
    templateUrl: 'partials/error_alert.html',
    controller: 'ErrorAlertCtrl',
    size: 'lg',
    resolve: {
      action: function () { return message; },
      error: function () { return data; },
      context: function () { return {}; }
    }
  });
}

function showCaughtTacticErrorMessage(modal, errorThrown, message, tacticMsg) {
  console.error("Tactic error was caught: " + message);
  modal.open({
    templateUrl: 'templates/tacticError.html',
    controller: 'TacticErrorCtrl',
    size: 'lg',
    resolve: {
      error: function () { return errorThrown; },
      tacticMsg: function() { return tacticMsg; },
      message: function() { return message; }
    }});
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
      message: function() { return message; },
      mode: function() { return "ok"; }
    }
  })
}

angular.module('keymaerax.errorHandlers', []).factory('ResponseErrorHandler', ['$q', '$injector', function($q, $injector) {

  //@todo have pollers register here
  var pollRequests = [ '/isLocal', 'tools/vitalSigns' ];

  var responseInterceptor = {
    loginPromise: null,
    response: function(response) {
      if (response.data !== undefined && response.data !== null && response.data.type === 'error') {
        console.error(response.data.textStatus);
        // server-created error response -> reject so that $http.get and $http.post error handlers are invoked
        return $q.reject(response);
      } else if (response.data !== undefined && response.data !== null && response.data.type === 'uncaught') {
        console.error(response.data.textStatus);
        // server-created error response -> reject so that $http.get and $http.post error handlers are invoked
        return $q.reject(response);
      }
      return response;
    },
    responseError: function(rejection) {
      // user cancelled has status==-1 just like server unavailable (both are abort, but user cancelled is resolved from a timeout promise with value=='usercancelled')
      if (rejection.status == -1 && (!rejection.config.timeout || !rejection.config.timeout.$$state || rejection.config.timeout.$$state.value != 'usercancelled')) {
        // server unavailable
        if (!pollRequests.includes(rejection.config.url)) {
          var $uibModal = $injector.get('$uibModal'); // inject manually to avoid circular dependency
          $injector.get("spinnerService").hideAll();
          $uibModal.open({
            //@note template instead of template URL, since server is offline already
            template: '<div class="modal-header"><h3 class="modal-title">Server is offline</h3></div><div class="modal-body"><p>The KeYmaera X server is unavailable. All your recent work is saved (except for the click that just failed). If you run KeYmaera X locally, just restart the server (<kbd>java -jar keymaerax.jar</kbd>)</p><p>This dialog will close automatically when the server is online again.</p></div>',
            controller: 'ServerOfflineDialogCtrl',
            size: 'md',
            backdrop: 'static',
            animation: false
          });
        }
        return $q.reject(rejection);
      } else if (rejection.status == -1 && (rejection.config.timeout && rejection.config.timeout.$$state && rejection.config.timeout.$$state.value == 'usercancelled')) {
        // notify server that request was cancelled so that long-running tool computations are cancelled as well
        var $http = $injector.get('$http');
        $http.get("tools/cancel");
      } else if (rejection.status === 500) {
        // report uncaught server-side exception
        var $uibModal = $injector.get('$uibModal'); // inject manually to avoid circular dependency
        $uibModal.open({
          templateUrl: 'partials/error_alert.html',
          controller: 'ErrorAlertCtrl',
          size: 'lg',
          resolve: {
            url: function() { return rejection.config.url; },
            message: function () { return rejection.data.textStatus; },
            error: function () { return rejection.data; },
            context: function () { return {}; }
          }
        });
        // forward to .catch handlers
        return $q.reject(rejection);
      } else if (rejection.status === 401 || rejection.status === 403) {
        // session expired or user does not have privileges to access data -> display login
        var $uibModal = $injector.get('$uibModal'); // inject manually to avoid circular dependency
        var $http = $injector.get('$http');
        var deferred = $q.defer();
        // on a page with multiple async requests: show login only on first such request, chain all others to successful login
        if (this.loginPromise == null) {
          var modalInstance = $uibModal.open({
            templateUrl: 'templates/logindialog.html',
            controller: 'LoginDialogCtrl',
            size: 'md',
            backdrop: 'static'
          });
          this.loginPromise = modalInstance.result.then(deferred.resolve, deferred.reject);
        } else {
          this.loginPromise.then(deferred.resolve, deferred.reject);
        }
        // When the user is logged in, make the same backend call again and chain the request
        return deferred.promise.then(function() {
          this.loginPromise = null;
          return $http(rejection.config);
        });
      } else {
        // somebody else has to handle
        return $q.reject(rejection);
      }
    }
  }

  return responseInterceptor;

}]);

angular.module('keymaerax.controllers').controller('ErrorAlertCtrl', function($scope, $uibModalInstance, $uibModal, url,
    message, error, context) {
  $scope.errorText = message !== undefined && message !== '' ? message : 'Sorry, no message available. Please look at the stack trace.';
  $scope.url = url;
  $scope.errorTrace = error.errorThrown;
  $scope.stacktraceCollapsed = true;
  $scope.context = context !== undefined ? context : {};
  $scope.report = function() {
    $uibModalInstance.dismiss('cancel');
    var modalInstance = $uibModal.open({
        templateUrl: 'partials/error_report.html',
        controller: 'ErrorReportCtrl',
        size: 'lg',
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
        size: 'lg',
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
    if (model) {
      var lines = $.map(model.split('\n'), function(e, i) { return ("00" + (i+1)).slice(-3) + ': ' + e; });
      if (error.location) {
        // line numbers are always 000:_ (5 chars)
        var errorColumnIdx = error.location.column >= 0 ? error.location.column + 5 :
          error.location.line >= 0 ? lines[error.location.line-1].length+1 : lines[lines.length-1].length+1;
        var inlineErrorMsg = new Array(errorColumnIdx).join(' ') + '^----' + error.textStatus;
        if (error.location.line >= 0) lines.splice(error.location.line, 0, inlineErrorMsg);
        else lines.splice(lines.length, 0, inlineErrorMsg);
        return lines.join('\n');
      } else {
        return lines.join('\n');
      }
    } else ""
  }
});

angular.module('keymaerax.controllers').controller('TacticErrorCtrl', function($scope, $uibModalInstance, $uibModal, message, tacticMsg, error) {
  $scope.message = message !== undefined && message !== '' ? message : 'Sorry, no message available. Please look at the stack trace.';
  $scope.errorTrace = error;
  $scope.stacktraceCollapsed = true;
  $scope.tacticMsg = tacticMsg;
  $scope.report = function() {
    $uibModalInstance.dismiss('cancel');
    var modalInstance = $uibModal.open({
      templateUrl: 'partials/error_report.html',
      controller: 'ErrorReportCtrl',
      size: 'lg',
      resolve: {
        error: function () { return error; }
      }
    });
  }
  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('ErrorReportCtrl', function($scope, $uibModalInstance, $http, error) {
  $http.get("/kyxConfig").success(function(data) {
    $scope.kyxConfig = data.kyxConfig;
  });
  $http.get("/keymaeraXVersion").success(function(data) {
    $scope.kyxVersion = data.keymaeraXVersion;
  });
  $http.get("/isLocal").success(function(data) {
    $scope.isLocal = data.success;
  });
  $scope.errorText = error.textStatus;
  $scope.errorTrace = error.errorThrown;
  $scope.userDescription = undefined
  $scope.subjectText = "KeYmaera X help request"

  encodeText = function(str) {
    // replace characters not encoded by encodeURIComponent manually
    return encodeURIComponent(str).replace(/[-_.~!*'()]/g, function(c) {
      return '%' + c.charCodeAt(0).toString(16);
    });
  }

  $scope.bodyText = function() {
    return encodeText("Description\n" + ($scope.userDescription ? $scope.userDescription : "") +
      "\n\nKeYmaera X v" + ($scope.kyxVersion ? $scope.kyxVersion : "Unknown") + ($scope.isLocal ? " (local)" : " (web.keymaerax.org)") +
      ($scope.omitSysConfig ? "\n\nSystem configuration unreported" : "\n\nSystem configuration\n" + ($scope.kyxConfig ? $scope.kyxConfig : "Unavailable")) +
      "\n\nError message\n" + ($scope.errorText ? $scope.errorTest : "Unavailable") +
      "\n\nError trace\n" + ($scope.errorTrace ? $scope.errorTrace : "Unavailable"));
  }

  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('ModalMessageCtrl', function($scope, $uibModalInstance,
    title, message, mode, oktext, notext, canceltext) {
  $scope.title = title;
  $scope.message = message;
  $scope.mode = mode;
  switch(mode) {
      case "ok":
        $scope.oktext = oktext ? oktext : "OK";
        break;
      case "okcancel":
        $scope.oktext = oktext ? oktext : "OK";
        $scope.canceltext = canceltext ? canceltext: "Cancel";
        break;
      case "yesnocancel":
        $scope.oktext = oktext ? oktext : "Yes";
        $scope.notext = notext ? notext : "No";
        $scope.canceltext = canceltext ? canceltext: "Cancel";
        break;
  };
  $scope.ok = function() { $uibModalInstance.close("ok"); };
  $scope.no = function() { $uibModalInstance.close("no"); };
  $scope.cancel = function() { $uibModalInstance.dismiss(); };
}).value("oktext", undefined).
   value("notext", undefined).
   value("canceltext", undefined);

angular.module('keymaerax.controllers').controller('LoginDialogCtrl', ['$scope', '$http', '$uibModal', '$uibModalInstance', 'sessionService', function($scope, $http, $uibModal, $uibModalInstance, sessionService) {
  $scope.username = ""
  $scope.password = ""

  $scope.processLogin = function() { login($scope.username, $scope.password); }

  $scope.close = function() { $uibModalInstance.dismiss("Close"); }

  login = function(username, password) {
    if (username === "guest") {
      // guests have to accept the license every time
      var modalInstance = $uibModal.open({
        templateUrl: 'partials/license_dialog.html',
        controller: 'LicenseDialogCtrl',
        backdrop: "static",
        size: 'lg'
      });
      modalInstance.result.then(function() {
        $http.get("/user/" + username + "/" + password + "/mode/0").then(function(response) {
          if(response.data.type == "LoginResponse") {
            if(response.data.success) {
              sessionService.setToken(response.data.sessionToken);
              sessionService.setUser(response.data.value);
              sessionService.setUserAuthLevel(response.data.userAuthLevel);
              $uibModalInstance.close("Login success");
            } else {
              $uibModalInstance.dismiss("Please check user name and/or password");
              showMessage($uibModal, "Login failed", "Please check user name and/or password. Or register a new account.");
            }
          }
        });
      })
    } else {
      $http.get("/user/" + username + "/" + password + "/mode/0")
      .then(function(response) {
        if(response.data.type == "LoginResponse") {
          if(response.data.success) {
            sessionService.setToken(response.data.sessionToken);
            sessionService.setUser(response.data.value);
            $uibModalInstance.close("Login success");
          } else {
            $uibModalInstance.dismiss("Please check user name and/or password");
            showMessage($uibModal, "Login failed", "Please check user name and/or password. Or register a new account.");
          }
        }
      });
    }
  }
}]);
