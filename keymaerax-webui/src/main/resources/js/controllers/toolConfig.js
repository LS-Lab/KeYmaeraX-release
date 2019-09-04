angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $http) {

    $scope.systemInfo = {
      info: undefined,
      warning: undefined
    }

    $scope.toolStatus = {
      tool: undefined,
      initialized: undefined,
      error: undefined,
      errorDetails: undefined
    }

    $http.get("/config/systeminfo").then(function(response) {
      $scope.systemInfo.info = response.data;
      $scope.systemInfo.error = response.data.jvmArchitecture.includes("32");
    });

    $scope.toolChange = function() {
      $http.post("/config/tool", $scope.toolStatus.tool).success(function(data) {
        $scope.toolStatus.tool = data.tool;
        $scope.toolStatus.initialized = true;
        $scope.toolStatus.error = undefined;
        $scope.toolStatus.errorDetails = undefined;
      }).error(function(data, status) {
        $scope.toolStatus.initialized = false;
        $scope.toolStatus.error = data.textStatus;
        $scope.toolStatus.errorDetails = data.causeMsg;
      });
    }

    $scope.getTool = function() {
      $http.get("/config/tool").success(function(data) {
        $scope.toolStatus.tool = data.tool;
        $scope.toolStatus.initialized = true;
        $scope.toolStatus.error = undefined;
        $scope.toolStatus.errorDetails = undefined;
      }).error(function(data, status) {
        $scope.toolStatus.initialized = false;
        $scope.toolStatus.error = data.textStatus;
        $scope.toolStatus.errorDetails = data.causeMsg;
      });
    }

    $scope.getTool();
});