angular.module('sequent', ['ngSanitize','formula'])
  .directive('k4Sequent', function() {
    return {
        restrict: 'AE',
        scope: {
            proofid: '=',
            taskid: '=',
            nodeid: '=',
            sequent: '='
        },
        controller: function($scope, $sce, $modal, Tasks) {
            // TODO should issue events other controllers can subscribe to
            $scope.handleFormulaClick = function(f) {
                var modalInstance = $modal.open({
                  templateUrl: 'partials/proofruledialog.html',
                  controller: 'ProofRuleDialogCtrl',
                  size: 'lg',
                  resolve: {
                    proofid: function() { return $scope.proofid; },
                    taskid: function() { return $scope.taskid; },
                    nodeid: function() { return $scope.nodeid; },
                    formulaid: function() { return f.id; },
                    formula: function() { return f.formula; }
                  }
                });
            };

            $scope.handleTurnstileClick = function() {
                alert("Turnstile")
                //ApiClient.runGlobalTactic(ClientState.uid, 0, $scope.proofid, $scope.nodeid,
                //      function (resp) { alert(JSON.stringify(resp)); });">
            }

            $scope.$watch('selectedTask',
                function () { return Tasks.getSelectedTask(); }
            );
        },
        templateUrl: 'partials/sequent.html'
    };
  });