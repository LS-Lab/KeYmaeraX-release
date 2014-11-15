angular.module('sequent', ['ngSanitize','formula'])
  .directive('k4Sequent', function() {
    return {
        restrict: 'AE',
        scope: {
            proofId: '=',
            nodeId: '=',
            sequent: '='
        },
        controller: function($scope, $sce, $modal, Agenda) {
            //$scope.sequent = JSON.parse($scope.taskJson)
            // TODO should issue events other controllers can subscribe to
            $scope.handleFormulaClick = function(f) {
                var modalInstance = $modal.open({
                  templateUrl: 'partials/proofruledialog.html',
                  controller: 'ProofRuleDialogCtrl',
                  size: 'lg',
                  resolve: {
                    proofId: function() { return $scope.proofId; },
                    nodeId: function() { return $scope.nodeId; },
                    formula: function() { return f; }
                  }
                });
            };

            $scope.handleTurnstileClick = function() {
                var modalInstance = $modal.open({
                  templateUrl: 'partials/proofruledialog.html',
                  controller: 'ProofRuleDialogCtrl',
                  size: 'lg',
                  resolve: {
                    proofId: function() { return $scope.proofId; },
                    nodeId: function() { return $scope.nodeId; },
                    formula: function() { return; }
                  }
                });
            }

            $scope.$watch('selectedTask',
                function () { return Agenda.getSelectedTask(); }
            );
        },
        templateUrl: 'partials/sequent.html'
    };
  });