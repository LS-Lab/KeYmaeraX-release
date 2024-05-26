angular.module('keymaerax.services').service('ToolConfigService', function($http) {
  var systemInfo = {
    info: undefined,
    warning: undefined,
    isLocal: false
  }

  var toolStatus = {
    tool: undefined,
    initialized: undefined,
    error: undefined,
    errorDetails: undefined,
    isInitialized: function(t) { return this.tool===t && !this.initializing && this.configured && this.initialized && this.error === undefined; },
    isInitializing: function(t) { return this.tool===t && this.initializing; },
    isError: function(t) { return this.tool===t && !this.initializing && !this.initialized && this.error !== undefined; },
    isUnconfigured: function(t) { return this.tool===t && !this.initializing && !this.configured && this.error === undefined; },
  }

  var config = {
    content: undefined,
    origContent: undefined
  }

  this.fetchSystemInfo = function() {
    $http.get('/isLocal').success(function(data) {
      if (data.errorThrown) systemInfo.isLocal = false
      else systemInfo.isLocal = data.success;

      if (systemInfo.isLocal) {
        $http.get("/config/systeminfo").then(function(response) {
          systemInfo.info = response.data;
        });
      }
    });
  }

  this.fetchFullConfig = function() {
    $http.get('/isLocal').success(function(data) {
      if (data.errorThrown) systemInfo.isLocal = false
      else systemInfo.isLocal = data.success;
      if (systemInfo.isLocal) {
        $http.get("/config/fullContent").then(function(response) {
          config.content = response.data.content;
          config.origContent = response.data.content;
        });
      }
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
        toolStatus.configured = data.configured;
        toolStatus.tool = data.tool;
      }).error(function(data, status) {
        toolStatus.initialized = false;
        toolStatus.configured = false;
        toolStatus.error = data ? (data.textStatus ? data.textStatus : "Unknown error, server may have crashed")
                                : "Unknown error, server may have crashed";
        toolStatus.errorDetails = data ? data.causeMsg : "";
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
      toolStatus.configured = data.configured;
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
  this.getConfig = function() { return config; }

  this.getTool();
  this.fetchSystemInfo();
});

angular.module('keymaerax.controllers').controller('ToolConfig',
  function($scope, $uibModalInstance, $http, $uibModal, ToolConfigService) {
    $scope.toolStatus = ToolConfigService.getToolStatus();
    $scope.systemInfo = ToolConfigService.getSystemInfo();
    $scope.toolChange = ToolConfigService.toolChange;

    $scope.config = {
      mode: "toolConfig",
      full: ToolConfigService.getConfig()
    }

    $scope.close = function() {
      $uibModalInstance.close();
    }

    $scope.setMode = function(mode) {
      if (mode === 'advancedConfig') ToolConfigService.fetchFullConfig();
      $scope.config.mode = mode
    }

    $scope.saveFullConfig = function() {
      var uri     = "/config/fullContent"
      var dataObj = { content: $scope.config.full.content };
      $http.post(uri, dataObj)
        .success(function(data) {
          $scope.close();
          var modalInstance = $uibModal.open({
            templateUrl: 'templates/modalMessageTemplate.html',
            controller: 'ModalMessageCtrl',
            size: 'md',
            resolve: {
              title: function() { return "Restart required"; },
              message: function() { return "Please restart KeYmaera X for configuration changes to take effect"; },
              mode: function() { return "ok"; }
            }
          });
        })
        .error(function(data) {
          showCaughtErrorMessage($uibModal, data, "Error saving configuration")
        })
    }

    $scope.$watch('toolStatus.tool', function(newValue, oldValue, scope) {
      if (newValue !== oldValue) scope.toolChange();
    })
});

angular.module('keymaerax.controllers').controller('ToolStatus',
  function($scope, ToolConfigService) {
    $scope.toolStatus = ToolConfigService.getToolStatus();
});
