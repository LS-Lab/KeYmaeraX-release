angular.module('keymaerax.ui.directives')
  .directive('k4TacticInfo', ['$http', 'derivationInfos', function($http, derivationInfos) {
    return {
      restrict: 'AE',
      scope: {
          userId: '@',
          proofId: '@',
          nodeId: '@',
          formulaId: '@',
          tactic: '=',
          onTactic: '&',     // onTactic(formulaId, tacticId)
          onInputTactic: '&' // onInputTactic(formulaId, tacticId, input)
      },
      templateUrl: 'templates/tacticInfoTemplate.html',
      link: function(scope, element, attrs) {
        scope.applyTactic = function(tacticId) {
          scope.onTactic({formulaId: scope.formulaId, tacticId: tacticId});
        }

        scope.applyInputTactic = function(tactic) {
          scope.onInputTactic({formulaId: scope.formulaId, tacticId: tactic.id, input: tactic.derivation.input});
        }
      }
    }
  }]);
