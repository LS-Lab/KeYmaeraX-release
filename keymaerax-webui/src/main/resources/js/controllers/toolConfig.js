angular.module('keymaerax.services').service('ToolConfigService', function($http) {
  var systemInfo = {
    info: undefined,
    warning: undefined
  }

  var toolStatus = {
    tool: undefined,
    initialized: undefined,
    error: undefined,
    errorDetails: undefined,
    isInitialized: function(t) { return this.tool===t && !this.initializing && this.initialized && this.error === undefined; },
    isInitializing: function(t) { return this.tool===t && this.initializing; },
    isError: function(t) { return this.tool===t && !this.initializing && !this.initialized && this.error !== undefined; }
  }

  this.fetchSystemInfo = function() {
    $http.get("/config/systeminfo").then(function(response) {
      systemInfo.info = response.data;
      systemInfo.error = response.data.jvmArchitecture.includes("32");
    });
  }

  this.toolChange = function() {
    if (toolStatus.tool) {
      toolStatus.initializing = true;
      toolStatus.initialized = undefined;
      toolStatus.error = undefined;
      toolStatus.errorDetails = undefined;
      $http.post("/config/tool", toolStatus.tool).success(function(data) {
        toolStatus.initialized = true;
        toolStatus.tool = data.tool;
      }).error(function(data, status) {
        toolStatus.initialized = false;
        toolStatus.error = data.textStatus;
        toolStatus.errorDetails = data.causeMsg;
      }).finally(function() {
        toolStatus.initializing = false;
      });
    } else getTool();
  }

  this.getTool = function() {
    toolStatus.initializing = true;
    toolStatus.initialized = undefined;
    toolStatus.error = undefined;
    toolStatus.errorDetails = undefined;
    $http.get("/config/tool").success(function(data) {
      toolStatus.initialized = true;
      toolStatus.tool = data.tool;
    }).error(function(data, status) {
      toolStatus.initialized = false;
      toolStatus.error = data.textStatus;
      toolStatus.errorDetails = data.causeMsg;
    }).finally(function() {
      toolStatus.initializing = false;
    });
  }

  this.getToolStatus = function() { return toolStatus; }
  this.getSystemInfo = function() { return systemInfo; }

  this.getTool();
  this.fetchSystemInfo();
});

angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $uibModalInstance, ToolConfigService) {
    $scope.toolStatus = ToolConfigService.getToolStatus();
    $scope.systemInfo = ToolConfigService.getSystemInfo();
    $scope.toolChange = ToolConfigService.toolChange;

    $scope.close = function() {
      $uibModalInstance.close();
    }

    $scope.$watch('toolStatus.tool', function(newValue, oldValue, scope) {
      if (newValue !== oldValue) scope.toolChange();
    })
});

angular.module('keymaerax.controllers').controller('ToolStatus',
  function($scope, ToolConfigService) {
    $scope.toolStatus = ToolConfigService.getToolStatus();
});
