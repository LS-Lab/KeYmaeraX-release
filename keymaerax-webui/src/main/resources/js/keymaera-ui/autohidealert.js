angular.module('keymaerax.ui.directives').directive('k4AutoHideAlert', function($timeout, $uibModal) {
  return {
    scope: {
      timeout: '@',
      isVisible: '=',
      message: '=',
      causeMsg: '=',
      taskStepwiseRequest: '=',
      details: '=',
      severity: '='
    },
    link: link,
    restrict: 'E',
    replace: false,
    templateUrl: 'templates/autohidealert.html'
  }

  function link(scope, element, attrs) {
    scope.$watch('isVisible', function(newValue, oldValue) {
      if (newValue && scope.timeout >= 0) $timeout(function () { scope.isVisible = false; }, scope.timeout);
    });

    scope.report = function() {
      var modalInstance = $uibModal.open({
          templateUrl: 'partials/error_report.html',
          controller: 'ErrorReportCtrl',
          size: 'fullwidth',
          windowClass: 'modal-errorreport',
          resolve: {
             error: function () { return { textStatus: scope.message + scope.causeMsg, errorThrown: scope.details }; }
          }
      });
    }

    scope.formattedMessage = function(msg) {
      return msg ? msg.replace(/\n/g, "<br/>") : msg
    }
  }
});