angular.module('keymaerax.ui.directives')
  .directive('k4SequentRuleInfo', [function() {
    return {
      restrict: 'AE',
      scope: {
          userId: '@',
          proofId: '@',
          nodeId: '@',
          tactic: '='
      },
      templateUrl: 'templates/sequentRuleTemplate.html',
      link: function(scope, element, attrs) {
        scope.saveValue = function(input, newValue) {
          return input.saveValue(scope.userId, scope.proofId, scope.nodeId, newValue);
        }
      }
    }
  }]);
