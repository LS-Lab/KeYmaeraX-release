angular.module('keymaerax.controllers').controller('WolframScriptConfig',
  function($scope, $rootScope, $http, $uibModal) {
    $http.get("/config/wolframscript/suggest")
      .success(function(data) {
          if (data.errorThrown) showCaughtErrorMessage($uibModal, data, "Encountered an error when attempting to get a suggested WolframScript configuration.")
          else $scope.wolframScriptConfigSuggestion = data
      });
});
