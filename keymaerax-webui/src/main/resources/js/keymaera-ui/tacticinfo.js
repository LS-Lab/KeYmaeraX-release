angular.module('keymaerax.ui.directives')
  .directive('k4TacticInfo', [function() {
    return {
      restrict: 'AE',
      scope: {
          userId: '@',
          proofId: '@',
          nodeId: '@',
          formulaId: '@',
          axiomReadonly: '=',
          tactic: '=',
          onTactic: '&',     // onTactic(formulaId, tacticId)
          onInputTactic: '&' // onInputTactic(formulaId, tacticId, input)
      },
      templateUrl: 'templates/tacticInfoTemplate.html',
      link: function(scope) {
        scope.applyTactic = function(tacticId) {
          let s = scope.tactic.selectedDerivation().derivation;
          if (s.selectedKeyPos && s.selectedKeyPos !== s.defaultKeyPos) {
            scope.onInputTactic({ formulaId: scope.formulaId, tacticId: 'useAt',
                                  input: [{param: 'axiom', value: s.canonicalName },
                                          {param: 'key', value: '' + s.selectedKeyPos }] });
          } else {
            scope.onTactic({formulaId: scope.formulaId, tacticId: tacticId});
          }
        }

        scope.applyInputTactic = function(tactic) {
          scope.onInputTactic({formulaId: scope.formulaId, tacticId: tactic.id, input: tactic.derivation.input});
        }
      }
    }
  }]);
