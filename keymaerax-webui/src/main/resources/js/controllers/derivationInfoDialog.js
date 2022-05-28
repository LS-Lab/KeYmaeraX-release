angular.module('keymaerax.controllers').controller('DerivationInfoDialogCtrl',
    function($scope, $uibModalInstance, tactics, readOnly, userId, proofId, nodeId, defaultPositionLocator, sequent) {

  $scope.tactic = tactics[0];
  $scope.readOnly = readOnly;
  $scope.userId = userId;
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.defaultPositionLocator = defaultPositionLocator;
  $scope.sequent = sequent;

  $scope.applyInputTactic = function(input) {
    $uibModalInstance.close({position: defaultPositionLocator, input: input});
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

  $scope.formulaSelected = function(formulaId, input) {
    $uibModalInstance.close({position: formulaId, input: input});
  }

  $scope.saveValue = function(input, newValue) {
    return input.saveValue($scope.userId, $scope.proofId, $scope.nodeId, newValue);
  }

});
