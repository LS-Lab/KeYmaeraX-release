angular.module('keymaerax.controllers').controller('WolframEngineConfig',
  function($scope, $rootScope, $http, $uibModal, ToolConfigService) {
    $scope.jlinkTcpip = {
      port: undefined,
      machine: undefined
    };

    $scope.origJlinkTcpip = {}

    $http.get("/config/wolframengine/suggest")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get a suggested Wolfram Engine configuration.")
          else $scope.wolframEngineConfigSuggestion = data
      });

    $http.get("/config/wolframengine")
      .success(function(data) {
          if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Failed to retrieve the server's current Wolfram Engine configuration")
          else if (data.linkName !== "" && data.jlinkLibPath !== "") {
              $scope.linkName = data.linkName;
              $scope.jlinkLibPath = data.jlinkLibDir;
              var portMachine = data.jlinkTcpip.split("@");
              var port = parseInt(portMachine[0]);
              if (isNaN(port)) $scope.jlinkTcpip.port = undefined;
              else $scope.jlinkTcpip.port = port;
              $scope.jlinkTcpip.machine = portMachine.length > 1 ? portMachine[1] : undefined;

              $scope.origLinkName = $scope.linkName;
              $scope.origJlinkLibPath = $scope.jlinkLibPath;
              $scope.origJlinkTcpip.port = $scope.jlinkTcpip.port;
              $scope.origJlinkTcpip.machine = $scope.jlinkTcpip.machine;
          }
      });

    $scope.configureWolframEngine = function() {
        var uri     = "/config/wolframengine"
        var linkName = $scope.linkName ? $scope.linkName : "";
        var jlinkLibPath = $scope.jlinkLibPath ? $scope.jlinkLibPath : "";
        var jlinkTcpip = $scope.jlinkTcpip.port ? "" + ($scope.jlinkTcpip.machine ? $scope.jlinkTcpip.port + "@" + $scope.jlinkTcpip.machine
                                                                                          : $scope.jlinkTcpip.port)
                                                : "false";
        var dataObj = { linkName: linkName, jlinkLibDir: jlinkLibPath, jlinkTcpip: jlinkTcpip };

        $scope.$parent.toolStatus.initializing = true;
        $http.post(uri, dataObj)
            .success(function(data) {
                if (data.success) {
                    $scope.WolframEngineForm.linkName.$setValidity("FileExists", true);
                    $scope.WolframEngineForm.jlinkLibDir.$setValidity("FileExists", true);
                    $scope.origLinkName = $scope.linkName;
                    $scope.origJlinkLibPath = $scope.jlinkLibPath;
                    $scope.origJlinkTcpip.port = $scope.jlinkTcpip.port;
                    $scope.origJlinkTcpip.machine = $scope.jlinkTcpip.machine;
                    $("#mathematicaConfigurationAlert").hide();
                    $rootScope.mathematicaIsConfigured = data.configured;
                    ToolConfigService.getTool();
                } else if (data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Wolfram Engine configuration")
                } else {
                    var kernelNameExists = $scope.linkName.indexOf($scope.wolframEngineConfigSuggestion.suggestion.kernelName) > -1 &&
                      data.linkNamePrefix == $scope.linkName
                    var jlinkExists = $scope.jlinkLibPath.indexOf($scope.wolframEngineConfigSuggestion.suggestion.jlinkName) > -1 &&
                      data.jlinkLibDirPrefix == $scope.jlinkLibPath

                    $scope.linkNameOkPrefix = data.linkNamePrefix
                    $scope.linkNameWrong = $scope.linkName.indexOf($scope.wolframEngineConfigSuggestion.suggestion.kernelName) > -1 ?
                        $scope.linkName.substring(data.linkNamePrefix.length, $scope.linkName.length) :
                        ".../" + $scope.wolframEngineConfigSuggestion.suggestion.kernelName
                    $scope.linkNameIncomplete = $scope.linkName.indexOf($scope.wolframEngineConfigSuggestion.suggestion.kernelName) == -1

                    $scope.jlinkLibPathOkPrefix = data.jlinkLibDirPrefix
                    $scope.jlinkLibPathWrong = $scope.jlinkLibPath.indexOf($scope.wolframEngineConfigSuggestion.suggestion.jlinkName) > -1 ?
                      $scope.jlinkLibPath.substring(data.jlinkLibDirPrefix.length, $scope.jlinkLibPath.length) :
                      ".../" + $scope.wolframEngineConfigSuggestion.suggestion.jlinkName
                    $scope.jlinkPathIncomplete = $scope.jlinkLibPath.indexOf($scope.wolframEngineConfigSuggestion.suggestion.jlinkName) == -1

                    $scope.WolframEngineForm.linkName.$setValidity("FileExists", kernelNameExists);
                    $scope.WolframEngineForm.jlinkLibDir.$setValidity("FileExists", jlinkExists);
                }
            }).error(function(data) {
                showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Mathematica configuration.")
            }).finally(function() {
              $scope.$parent.toolStatus.initializing = false;
            })
    }

    $scope.setDefaultMathKernel = function() {
      $scope.linkName = $scope.wolframEngineConfigSuggestion.suggestion.kernelPath + $scope.wolframEngineConfigSuggestion.suggestion.kernelName
    }

    $scope.setDefaultJLinkLibPath = function() {
      $scope.jlinkLibPath = $scope.wolframEngineConfigSuggestion.suggestion.jlinkPath + $scope.wolframEngineConfigSuggestion.suggestion.jlinkName
    }

    $scope.defaultWolframEnginePaths = function() {
      $scope.setDefaultMathKernel();
      $scope.setDefaultJLinkLibPath();
      $scope.configureWolframEngine();
    }

    $scope.resetWolframEnginePaths = function() {
      if ($scope.linkName != $scope.origLinkName || $scope.jlinkLibPath != $scope.origJlinkLibPath ||
          $scope.jlinkTcpip.port != $scope.origJlinkTcpip.port || $scope.jlinkTcpip.machine != $scope.origJlinkTcpip.machine) {
        $scope.linkName = $scope.origLinkName;
        $scope.jlinkLibPath = $scope.origJlinkLibPath;
        $scope.jlinkTcpip.port = $scope.origJlinkTcpip.port;
        $scope.jlinkTcpip.machine = $scope.origJlinkTcpip.machine;
        $scope.configureWolframEngine();
      }
    }
});

angular.module('keymaerax.controllers').controller('WolframEngineConfig.FailureDialog', function($scope, $uibModalInstance) {
  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});
