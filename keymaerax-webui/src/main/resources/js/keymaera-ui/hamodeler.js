angular.module('keymaerax.ui.hamodeler', ['ngSanitize'])
  .directive('k4HybridAutomatonModeler', ['$http', '$uibModal', '$window', function($http, $uibModal, $window) {
  return {
    restrict: 'AE',
    scope: {
      theme: '@',
      layout: '@',
      code: '=',
      onChange: '&'
    },
    controller: ['$scope', function($scope) {
      var mermaid = $window.mermaid;
      mermaid.initialize({
        theme: $scope.theme,
        useMaxWidth: 'true',
        flowchart: { curve: 'basis' }
      });

      $scope.toggleLayout = function() {
        $scope.layout = $scope.layout=='TD' ? 'LR' : 'TD';
        $scope.renderAutomaton();
      }

      $scope.renderAutomaton = function() {
        var code = 'flowchart ' + $scope.layout + '\n' + $scope.code;
        mermaid.render('graphDiv', code, function(svgCode, bindFunctions) {
          $('#automatonview').html(svgCode);
          $scope.onChange({code: $scope.code, svg: svgCode});
        });
      }

      $scope.aceChanged = function(delta) {
        $scope.renderAutomaton();
      }
    }],
    templateUrl: 'templates/hamodeler.html'
  }
}]);
