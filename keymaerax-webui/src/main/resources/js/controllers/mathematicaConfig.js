angular.module('keymaerax.controllers').controller('MathematicaConfig',
  function($scope, $rootScope, $http, $cookies, $uibModal, $routeParams) {
    $http.get("/config/mathematica/suggest")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get a suggested Mathematica configuration.")
          else $scope.mathematicaConfigSuggestion = data
      })
      .error(function() {
          showErrorMessage($uibModal, "Encountered an error when attempting to get a suggested Mathematica configuration.")
      });

    $http.get("/config/mathematica")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Failed to retrieve the server's current Mathematica configuration")
          else {
              if (data.linkName !== "" && data.jlinkLibPath !== "") {
                  $scope.linkName = data.linkName;
                  $scope.jlinkLibPath = data.jlinkLibDir;
              }
//          else {
//            $http.get("/config/mathematica/suggest")
//                .success(function(data) {
//                    $scope.linkName = data.kernelPath + "/" + data.kernelName;
//                    $scope.jlinkLibPath = data.jlinkPath + "/" + data.jlinkName;
//                })
//          }
          }
      })
      .error(function() {
          showErrorMessage($uibModal, "Failed to retrieve the server's current Mathematica configuration.")
      });

    $scope.configureMathematica = function() {
        var uri     = "/config/mathematica"
        var linkName = $scope.linkName ? $scope.linkName : "";
        var jlinkLibPath = $scope.jlinkLibPath ? $scope.jlinkLibPath : "";
        var dataObj = {linkName: linkName, jlinkLibDir: jlinkLibPath}

        $http.post(uri, dataObj)
            .success(function(data) {
                if (data.success) {
                    $scope.MathematicaForm.linkName.$setValidity("FileExists", true);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", true);

                    $uibModal.open({
                        templateUrl: 'partials/mathematicaconfig_update.html',
                        controller: 'MathematicaConfig.UpdateDialog',
                        size: 'md'
                    })

                    $("#mathematicaConfigurationAlert").hide();
                    $rootScope.mathematicaIsConfigured = data.configured;
                }
                else if(data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Mathematica configuration")
                }
                else {
                    var kernelNameExists = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) > -1 &&
                      data.linkNamePrefix == $scope.linkName
                    var jlinkExists = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) > -1 &&
                      data.jlinkLibDirPrefix == $scope.jlinkLibPath

                    $scope.linkNameOkPrefix = data.linkNamePrefix
                    $scope.linkNameWrong = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) > -1 ?
                        $scope.linkName.substring(data.linkNamePrefix.length, $scope.linkName.length) :
                        ".../" + $scope.mathematicaConfigSuggestion.kernelName
                    $scope.linkNameIncomplete = $scope.linkName.indexOf($scope.mathematicaConfigSuggestion.kernelName) == -1

                    $scope.jlinkLibPathOkPrefix = data.jlinkLibDirPrefix
                    $scope.jlinkLibPathWrong = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) > -1 ?
                      $scope.jlinkLibPath.substring(data.jlinkLibDirPrefix.length, $scope.jlinkLibPath.length) :
                      ".../" + $scope.mathematicaConfigSuggestion.jlinkName
                    $scope.jlinkPathIncomplete = $scope.jlinkLibPath.indexOf($scope.mathematicaConfigSuggestion.jlinkName) == -1

                    $scope.MathematicaForm.linkName.$setValidity("FileExists", kernelNameExists);
                    $scope.MathematicaForm.jlinkLibDir.$setValidity("FileExists", jlinkExists);
                }
            })
            .error(function(data) {
                showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Mathematica configuration.")
            })
    }

    $scope.setDefaultMathKernel = function() {
      $scope.linkName = $scope.mathematicaConfigSuggestion.kernelPath + $scope.mathematicaConfigSuggestion.kernelName
    }

    $scope.setDefaultJLinkLibPath = function() {
      $scope.jlinkLibPath = $scope.mathematicaConfigSuggestion.jlinkPath + $scope.mathematicaConfigSuggestion.jlinkName
    }
});

angular.module('keymaerax.controllers').controller('MathematicaConfig.FailureDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});

angular.module('keymaerax.controllers').controller('MathematicaConfig.UpdateDialog', function($scope, $http, $cookies, $modalInstance) {
  $scope.cancel = function() {
      $modalInstance.dismiss('cancel');
  }
});