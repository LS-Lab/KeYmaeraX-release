angular.module('sequent', ['ngSanitize', 'formula', 'ui.bootstrap', 'ngCookies', 'angularSpinners'])
  .directive('k4Sequent', ['$uibModal', '$http', 'spinnerService', function($uibModal, $http, spinnerService) {
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
            onApplyInputTactic: '&'
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
                    .catch(function(error) {
                      showErrorMessage($uibModal, "Unable to find a counter example, root cause: " + error.data);
                    })
                    .finally(function() { spinnerService.hide('counterExampleSpinner'); });
            }

            scope.onTactic = function(formulaId, tacticId) {
              scope.onApplyTactic({formulaId: formulaId, tacticId: tacticId});
            }

            scope.onInputTactic = function(formulaId, tacticId, input) {
              scope.onApplyInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }
        },
        templateUrl: 'partials/collapsiblesequent.html'
    };
  }]);
