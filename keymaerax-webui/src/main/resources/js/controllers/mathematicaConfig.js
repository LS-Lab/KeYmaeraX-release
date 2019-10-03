angular.module('keymaerax.controllers').controller('MathematicaConfig',
  function($scope, $rootScope, $http, $uibModal, ToolConfigService) {
    $scope.jlinkTcpip = {
      port: undefined,
      machine: undefined
    };

    $scope.origJlinkTcpip = {}

    $http.get("/config/mathematica/suggest")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get a suggested Mathematica configuration.")
          else $scope.mathematicaConfigSuggestion = data
      });

    $http.get("/config/mathematica")
      .success(function(data) {
        if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Failed to retrieve the server's current Mathematica configuration")
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

    $scope.configureMathematica = function() {
        var uri     = "/config/mathematica"
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
                    $scope.MathematicaForm.linkName.$setValidity("FileExists", true);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", true);
                    $scope.origLinkName = $scope.linkName;
                    $scope.origJlinkLibPath = $scope.jlinkLibPath;
                    $scope.origJlinkTcpip.port = $scope.jlinkTcpip.port;
                    $scope.origJlinkTcpip.machine = $scope.jlinkTcpip.machine;
                    $("#mathematicaConfigurationAlert").hide();
                    $rootScope.mathematicaIsConfigured = data.configured;
                    ToolConfigService.getTool();
                } else if (data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Mathematica configuration")
                } else {
                    var kernelNameExists = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.suggestion.kernelName) > -1 &&
                      data.linkNamePrefix == $scope.linkName
                    var jlinkExists = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.suggestion.jlinkName) > -1 &&
                      data.jlinkLibDirPrefix == $scope.jlinkLibPath

                    $scope.linkNameOkPrefix = data.linkNamePrefix
                    $scope.linkNameWrong = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.suggestion.kernelName) > -1 ?
                        $scope.linkName.substring(data.linkNamePrefix.length, $scope.linkName.length) :
                        ".../" + $scope.mathematicaConfigSuggestion.suggestion.kernelName
                    $scope.linkNameIncomplete = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.suggestion.kernelName) == -1

                    $scope.jlinkLibPathOkPrefix = data.jlinkLibDirPrefix
                    $scope.jlinkLibPathWrong = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.suggestion.jlinkName) > -1 ?
                      $scope.jlinkLibPath.substring(data.jlinkLibDirPrefix.length, $scope.jlinkLibPath.length) :
                      ".../" + $scope.mathematicaConfigSuggestion.suggestion.jlinkName
                    $scope.jlinkPathIncomplete = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.suggestion.jlinkName) == -1

                    $scope.MathematicaForm.linkName.$setValidity("FileExists", kernelNameExists);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", jlinkExists);
                }
            })
            .error(function(data) {
                showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Mathematica configuration.")
            }).finally(function() {
              $scope.$parent.toolStatus.initializing = false;
            })
    }

    $scope.setDefaultMathKernel = function() {
      $scope.linkName = $scope.mathematicaConfigSuggestion.suggestion.kernelPath + $scope.mathematicaConfigSuggestion.suggestion.kernelName
    }

    $scope.setDefaultJLinkLibPath = function() {
      $scope.jlinkLibPath = $scope.mathematicaConfigSuggestion.suggestion.jlinkPath + $scope.mathematicaConfigSuggestion.suggestion.jlinkName
    }

    $scope.defaultMathematicaPaths = function() {
      $scope.setDefaultMathKernel();
      $scope.setDefaultJLinkLibPath();
      $scope.configureMathematica();
    }

    $scope.resetMathematicaPaths = function() {
      if ($scope.linkName != $scope.origLinkName || $scope.jlinkLibPath != $scope.origJlinkLibPath ||
          $scope.jlinkTcpip.port != $scope.origJlinkTcpip.port || $scope.jlinkTcpip.machine != $scope.origJlinkTcpip.machine) {
        $scope.linkName = $scope.origLinkName;
        $scope.jlinkLibPath = $scope.origJlinkLibPath;
        $scope.jlinkTcpip.port = $scope.origJlinkTcpip.port;
        $scope.jlinkTcpip.machine = $scope.origJlinkTcpip.machine;
        $scope.configureMathematica();
      }
    }
});

angular.module('keymaerax.controllers').controller('MathematicaConfig.FailureDialog', function($scope, $uibModalInstance) {
  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});
