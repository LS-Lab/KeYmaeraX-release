angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $rootScope, $http, $cookies, $uibModal, $routeParams) {

    $http.get("/config/systeminfo").then(function(response) {
      $scope.systemInfo = response.data;
    });

    $scope.toolChange = function() {
      $http.post("/config/tool", $scope.tool).success(function(data) {
        $scope.tool = data.tool;
      });
    }

    $scope.getTool = function() {
      $http.get("/config/tool").success(function(data) {
        $scope.tool = data.tool;
      });
    }

    $scope.getTool();
});