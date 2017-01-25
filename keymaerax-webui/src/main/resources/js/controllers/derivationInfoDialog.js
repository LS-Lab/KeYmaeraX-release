angular.module('keymaerax.controllers').controller('DerivationInfoDialogCtrl',
    function($scope, $uibModalInstance, tactics, readOnly) {

  $scope.tactic = tactics[0];
  $scope.readOnly = readOnly;

  $scope.applyInputTactic = function(input) {
    $uibModalInstance.close(input);
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
