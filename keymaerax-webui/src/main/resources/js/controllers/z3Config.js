angular.module('keymaerax.controllers').controller('Z3Config',
  function($scope, $rootScope, $http, $uibModal, ToolConfigService) {
    $scope.z3Config = {
      z3Path: undefined
    };

    $scope.origZ3Path = {};

    $http.get("/config/z3/suggest")
      .success(function(data) {
          if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get the default Z3 configuration.")
          else $scope.z3ConfigSuggestion = data
      });

    $http.get("/config/z3")
      .success(function(data) {
        if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Failed to retrieve the server's current Z3 configuration")
        else if (data.z3Path !== "") {
          $scope.z3Path = data.z3Path;
          $scope.origZ3Path = $scope.z3Path;
        }
      });

    $scope.configureZ3 = function() {
        var uri     = "/config/z3"
        var z3Path = $scope.z3Path ? $scope.z3Path : "";
        var dataObj = { z3Path: z3Path };

        $scope.$parent.toolStatus.initializing = true;
        $http.post(uri, dataObj)
            .success(function(data) {
                if (data.success) {
                    $scope.Z3Form.z3Path.$setValidity("FileExists", true);
                    $scope.origZ3Path = $scope.z3Path;
                    $("#z3ConfigurationAlert").hide();
                    ToolConfigService.getTool();
                } else if (data.errorThrown) {
                    showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Z3 configuration")
                } else {
                    $scope.Z3Form.z3Path.$setValidity("FileExists", false);
                }
            })
            .error(function(data) {
                showCaughtErrorMessage($uibModal, data, "Exception encountered while attempting to set a user-defined Z3 configuration.")
            }).finally(function() {
              $scope.$parent.toolStatus.initializing = false;
            })
    }

    $scope.setDefaultZ3Path = function() {
      $scope.z3Path = $scope.z3ConfigSuggestion.z3Path
    }

    $scope.defaultZ3Path = function() {
      $scope.setDefaultZ3Path();
      $scope.configureZ3();
    }

    $scope.resetZ3Path = function() {
      if ($scope.z3Path != $scope.origZ3Path) {
        $scope.z3Path = $scope.origZ3Path;
        $scope.configureZ3();
      }
    }
});

angular.module('keymaerax.controllers').controller('Z3Config.FailureDialog', function($scope, $uibModalInstance) {
  $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
  }
});
