angular.module('sequent', ['ngSanitize', 'formula', 'ui.bootstrap', 'ngCookies', 'angularSpinners'])
  .directive('k4Sequent', ['$rootScope', '$uibModal', '$http', 'spinnerService', function($rootScope, $uibModal, $http, spinnerService) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            sequent: '=',
            readOnly: '=?',
            collapsed: '=?',
            onApplyTactic: '&',
            onApplyInputTactic: '&',
            onApplyTwoPositionTactic: '&'
        },
        link: function(scope, elem, attr) {
            scope.getCounterExample = function() {
                spinnerService.show('counterExampleSpinner');
                $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/counterExample')
                    .then(function(response) {
                      $uibModal.open({
                        templateUrl: 'templates/counterExample.html',
                        controller: 'CounterExampleCtrl',
                        size: 'lg',
                        resolve: {
                          result: function() { return response.data.result; },
                          origFormula: function() { return response.data.origFormula; },
                          cexFormula: function() { return response.data.cexFormula; },
                          cexValues: function() { return response.data.cexValues; }
                        }
                      });
                    })
                    .finally(function() { spinnerService.hide('counterExampleSpinner'); });
            }

            scope.onTactic = function(formulaId, tacticId) {
              scope.onApplyTactic({formulaId: formulaId, tacticId: tacticId});
            }

            scope.onInputTactic = function(formulaId, tacticId, input) {
              scope.onApplyInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }

            scope.onTwoPositionTactic = function(fml1Id, fml2Id, tacticId) {
              scope.onApplyTwoPositionTactic({fml1Id: fml1Id, fml2Id: fml2Id, tacticId: tacticId});
            }

            scope.onDragStart = function(event) {
              angular.element(event.target.firstChild.firstChild).removeClass('hlhover'); // remove hover effect on drag

            }

            scope.formulaDrop = function(dragData) {
              var formulas = $.grep(scope.sequent.ante, function(e, i) { return e.id === dragData; });
              if (formulas.length == 1) {
                var formula = formulas[0];
                if (formula.formula.name === 'equals') {
                  scope.onApplyTactic({formulaId: formula.id, tacticId: 'allL2R'})
                } else {
                  $rootScope.$emit('proof.message', 'Drop formulas of the form "lhs=rhs" only')
                }
              } else {
                $rootScope.$emit('proof.message', 'Drop antecedent formulas only')
              }
            }
        },
        templateUrl: 'partials/collapsiblesequent.html'
    };
  }]);
