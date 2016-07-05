angular.module('keymaerax.controllers').controller('TacticEditorCtrl',
  function($scope, $uibModal, $uibModalInstance, parentScope) {

  $scope.customTactic = parentScope.customTactic;

  $scope.execute = function() {
    if($scope.customTactic == "") {
      alert("Cannot execute an empty tactic.")
    } else {
      $uibModalInstance.close('execute');
      parentScope.customTactic = $scope.customTactic;
      parentScope.doCustomTactic();
    }
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});