angular.module('sequentproof', ['ngSanitize','sequent','formula'])
  .directive('k4Sequentproof', function() {
    return {
        restrict: 'AE',
        scope: {
            proofId: '=',
            nodeId: '=',
            sequent: '=',
            readOnly: '=?'
        },
        controller: function($scope, $sce, $modal, $http, $cookies, Agenda, Tactics) {
            $scope.$watch('selectedTask',
                function () { return Agenda.getSelectedTask(); }
            );
        },
        templateUrl: 'partials/singletracksequentproof.html'
    };
  });