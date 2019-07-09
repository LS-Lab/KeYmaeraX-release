angular.module('keymaerax.services').service('ToolConfigService', function($http) {
  var toolConfig = {};

  this.toolChange = function() {
    $http.post("/config/tool", toolConfig.tool).success(function(data) {
      toolConfig.configured = data.configured;
      toolConfig.tool = data.tool;
    });
  }

  this.getTool = function() {
    $http.get("/config/tool").success(function(data) {
      toolConfig.configured = data.configured;
      toolConfig.tool = data.tool;
    });
  }

  this.getToolConfig = function() { return toolConfig; }

  this.getTool();
});

angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $http, ToolConfigService) {

    $scope.toolConfig = ToolConfigService.getToolConfig();

    $http.get("/config/systeminfo").success(function(data) {
      $scope.systemInfo = data;
    });

    $scope.toolChange = ToolConfigService.toolChange;
    $scope.getTool = ToolConfigService.getTool;
});