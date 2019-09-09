angular.module('keymaerax.services').service('ToolConfigService', function($http) {
  var systemInfo = {
    info: undefined,
    warning: undefined
  }

  var toolStatus = {
    tool: undefined,
    initialized: undefined,
    error: undefined,
    errorDetails: undefined
  }

  this.fetchSystemInfo = function() {
    $http.get("/config/systeminfo").then(function(response) {
      systemInfo.info = response.data;
      systemInfo.error = response.data.jvmArchitecture.includes("32");
    });
  }

  this.toolChange = function() {
    $http.post("/config/tool", toolStatus.tool).success(function(data) {
      toolStatus.tool = data.tool;
      toolStatus.initialized = true;
      toolStatus.error = undefined;
      toolStatus.errorDetails = undefined;
    }).error(function(data, status) {
      toolStatus.initialized = false;
      toolStatus.error = data.textStatus;
      toolStatus.errorDetails = data.causeMsg;
    });
  }

  this.getTool = function() {
    $http.get("/config/tool").success(function(data) {
      toolStatus.tool = data.tool;
      toolStatus.initialized = true;
      toolStatus.error = undefined;
      toolStatus.errorDetails = undefined;
    }).error(function(data, status) {
      toolStatus.initialized = false;
      toolStatus.error = data.textStatus;
      toolStatus.errorDetails = data.causeMsg;
    });
  }

  this.getToolStatus = function() { return toolStatus; }
  this.getSystemInfo = function() { return systemInfo; }

  this.getTool();
  this.fetchSystemInfo();
});

angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $http, ToolConfigService) {
    $scope.toolStatus = ToolConfigService.getToolStatus();
    $scope.systemInfo = ToolConfigService.getSystemInfo();
    $scope.toolChange = ToolConfigService.toolChange;
    $scope.getTool = ToolConfigService.getTool;
});