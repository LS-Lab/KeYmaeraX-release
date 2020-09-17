angular.module('keymaerax.ui.directives')
  .directive('k4TacticName', ['$compile', function($compile) {
    return {
      restrict: 'E',
      scope: {
        name: '@',
        codeName: '@',
        longName: '@'
      },
      link: function(scope, elt, attrs) {
          var element = angular.element('<span>' +
            (scope.longName ? '<span>' + scope.longName + '</span>&nbsp;' : '') +
            (scope.name !== scope.codeName && scope.name !== scope.longName ? '<span>' + scope.name + '</span>&nbsp;' : '') +
            '<code>{{codeName}}</code></span>');
          elt.append(element);
          $compile(element)(scope);
      }
    }
  }]);
