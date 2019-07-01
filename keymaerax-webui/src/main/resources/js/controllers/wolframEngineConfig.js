angular.module('keymaerax.controllers').controller('WolframEngineConfig',
  function($scope, $rootScope, $http, $uibModal) {
    $http.get("/config/wolframengine/suggest")
      .success(function(data) {
          if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get a suggested Wolfram Engine configuration.")
          else $scope.wolframEngineConfigSuggestion = data
      });

    $http.get("/config/wolframengine")
      .success(function(data) {
          if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Failed to retrieve the server's current Wolfram Engine configuration")
          // no further configuration necessary with WolframScript
      });
});
