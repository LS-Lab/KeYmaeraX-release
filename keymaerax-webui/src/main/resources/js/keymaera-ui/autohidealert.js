angular.module('keymaerax.ui.directives', ['ngSanitize']);

angular.module('keymaerax.ui.directives').directive('k4AutoHideAlert', function($timeout) {
  return {
    scope: {
      timeout: '@',
      isVisible: '=',
      message: '=',
      details: '='
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
  }
});