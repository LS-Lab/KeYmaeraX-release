angular.module('keymaerax.ui.directives')
  .directive('k4TacticName', ['$compile', function($compile) {
    return {
      restrict: 'E',
      scope: {
        name: '@',
        codeName: '@'
      },
      link: function(scope, elt, attrs) {
          var element = angular.element('<span><span>' + scope.name + '</span>&nbsp;<code>{{codeName}}</code></span>');
          elt.append(element);
          $compile(element)(scope);
      }
    }
  }]);
