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
        logLevel: 3,
        securityLevel: 'loose',
        useMaxWidth: 'true',
        flowchart: { curve: 'basis' }
      });

      $scope.aceChanged = function(delta) {
        var code = 'flowchart ' + $scope.layout + '\n' + $scope.code;
        mermaid.render('graphDiv', code, function(svgCode, bindFunctions) {
          $('#automatonview').html(svgCode);
          $scope.onChange({code: code, svg: svgCode});
        });
      }
    }],
    templateUrl: 'templates/hamodeler.html'
  }
}]);
