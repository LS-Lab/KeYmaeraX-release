angular.module('sequent', ['ngSanitize','formula'])
  .directive('k4Sequent', function() {
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
        link: function($scope, $sce, $uibModal, $http, $cookies, Tactics) {
            $scope.getCounterExample = function() {
                $uibModal.open({
                    templateUrl: 'partials/counterExample.html',
                    controller: 'counterExampleCtrl',
                    size: 'lg',
                    resolve: {
                      proofId: function() { return $scope.proofId; },
                      nodeId: function() { return $scope.nodeId; }
                    }
                    });
            }

            $scope.onTactic = function(formulaId, tacticId) {
              $scope.onApplyTactic({formulaId: formulaId, tacticId: tacticId});
            }

            $scope.onInputTactic = function(formulaId, tacticId, input) {
              $scope.onApplyInputTactic({formulaId: formulaId, tacticId: tacticId, input: input});
            }
        },
        templateUrl: 'partials/collapsiblesequent.html'
    };
  });