angular.module('formula', ['ngSanitize'])
  .directive('k4Formula', function() {
    return {
        restrict: 'E',
        scope: {
            pId: '=',
            nId: '=',
            formula: '=',
            highlight: '='
        },
        controller: function($scope, $sce, $cookies, Tactics) {

          $scope.dropped = [];
          $scope.onDropFormula = function(event, ui, formula) {
            // TODO retrieve applicable position rules and show dialog, then execute rule
            console.log($scope.dropped[0] + " -> " + formula)
          };
        },
        templateUrl: 'partials/formula-renderer.html'
    };
  });