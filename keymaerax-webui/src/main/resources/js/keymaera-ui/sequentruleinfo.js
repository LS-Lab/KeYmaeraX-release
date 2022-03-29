angular.module('keymaerax.ui.directives')
  .directive('k4SequentRuleInfo', ['$http', function($http) {
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

        scope.inputSuggestions = [];

        scope.generateInputs = function() {
          if (scope.tactic.derivation && scope.tactic.derivation.inputGenerator && scope.tactic.derivation.inputGenerator !== '') {
            scope.isLoading = true;
            return $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + scope.tactic.derivation.inputGenerator)
              .then(function(response) {
                scope.isLoading = false;
                if (response.data.candidates && response.data.candidates.length > 0) {
                  var result = response.data.candidates[0].fmls;
                  scope.inputSuggestions = result;
                  return result;
                } else return [];
              });
          } else return [];
        }
      }
    }
  }]).filter("odeTactic", function() {
    return function(x) {
      switch (x) {
        case "PostInv": return "ODE (postcondition is invariant)"
        case "PreInv": return "Precondition is invariant"
        case "PreDomFalse": return "diffUnpackEvolDomain (𝜞∧Q unsatisfiable)"
        case "DomImpPost": return "dW"
        case "PreNoImpPost": return "Precondition does not imply postcondition"
        case "Unknown": return "ODE"
        default: return x;
      }
    };
  });
