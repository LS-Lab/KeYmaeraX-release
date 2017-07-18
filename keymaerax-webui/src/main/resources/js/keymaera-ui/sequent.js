angular.module('sequent', ['ngSanitize', 'formula', 'ui.bootstrap', 'ngCookies', 'angularSpinners'])
  .directive('k4Sequent', ['$rootScope', '$uibModal', '$http', 'spinnerService', 'derivationInfos',
      function($rootScope, $uibModal, $http, spinnerService, derivationInfos) {
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
            scope.sequentSuggestions = [];

            if (!scope.readOnly) {
              derivationInfos.sequentSuggestionDerivationInfos(scope.userId, scope.proofId, scope.nodeId)
                .then(function(response) {
                  scope.sequentSuggestions = response.data;
                });
            }

            //@todo duplicate with provingawesome.js#getCounterExample
            scope.getCounterExample = function() {
                spinnerService.show('counterExampleSpinner');
                $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/counterExample')
                    .then(function(response) {
                      var dialogSize = (response.data.result === 'cex.found') ? 'lg' : 'md';
                      $uibModal.open({
                        templateUrl: 'templates/counterExample.html',
                        controller: 'CounterExampleCtrl',
                        size: dialogSize,
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

            scope.openInputTacticDialog = function(tacticName) {
              var tactics = derivationInfos.byName(scope.userId, scope.proofId, scope.nodeId, tacticName)
                .then(function(response) {
                  return response.data;
                });

              var modalInstance = $uibModal.open({
                templateUrl: 'templates/derivationInfoDialog.html',
                controller: 'DerivationInfoDialogCtrl',
                size: 'lg',
                resolve: {
                  tactics: function() { return tactics; },
                  readOnly: function() { return false; }
                }
              });

              modalInstance.result.then(function(derivation) {
                scope.onInputTactic(undefined, tacticName, derivation);
              })
            }

            scope.turnstileDrop = function(dragData) {
              var formulas = $.grep(scope.sequent.ante, function(e, i) { return e.id === dragData; });
              if (formulas.length == 1) {
                var formula = formulas[0];
                if (formula.formula.name === 'equals') {
                  scope.onApplyTactic({formulaId: formula.id, tacticId: 'allL2R'})
                } else {
                  $rootScope.$emit('proof.message', { textStatus: 'Drop formulas of the form "lhs=rhs" only', errorThrown: "" })
                }
              } else {
                $rootScope.$emit('proof.message', { textStatus: 'Drop antecedent formulas only', errorThrown: "" })
              }
            }

            scope.isFOL = function(formula) {
              //@todo implement
              return true;
            }

            turnstileTooltipOpen = false;
            scope.turnstileDragEnter = function(dragData) { turnstileTooltipOpen = true; }
            scope.turnstileDragLeave = function(dragData) { turnstileTooltipOpen = false; }
            scope.isTurnstileTooltipOpen = function() {return turnstileTooltipOpen;}
        },
        templateUrl: 'partials/collapsiblesequent.html'
    };
  }]);
