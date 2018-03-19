angular.module('keymaerax.ui.directives')
  .directive('k4AxiomKeySelector', [function() {
    return {
      restrict: 'AE',
      scope: {
        axiom: '=',
        readonly: '='
      },
      templateUrl: 'templates/axiomKeySelectorTemplate.html',
      link: function(scope, element, attrs) {
        scope.selectedKeyPos = function() {
          var s = scope.axiom;
          return s.selectedKeyPos ? s.selectedKeyPos : s.defaultKeyPos;
        }

        scope.selectKeyEnd = function(to) {
          //@note assumes either implication/equivalence/equality or conditional equivalence/equality
          var currentKeyPos = scope.selectedKeyPos();
          scope.axiom.selectedKeyPos = currentKeyPos.slice(0, currentKeyPos.lastIndexOf('.')+1) + to;
        }
      }
    }
  }]);
