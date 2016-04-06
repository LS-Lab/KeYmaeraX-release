angular.module('keymaerax.controllers').controller('DerivationInfoDialogCtrl',
    function($scope, $uibModalInstance, tactics) {

  $scope.tactic = tactics[0];

  $scope.applyInputTactic = function(input) {
    $uibModalInstance.close(input);
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
