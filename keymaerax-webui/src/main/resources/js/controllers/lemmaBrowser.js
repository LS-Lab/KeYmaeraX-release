angular.module('keymaerax.controllers').controller('LemmaBrowserCtrl',
    function($scope, $uibModalInstance, derivationInfos, userId, proofId, nodeId, formulaId, formula) {

  $scope.userId = userId;
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formulaId = formulaId;
  $scope.formula = formula;

  $scope.derivationInfos = {
    filter: undefined,
    order: 'standardDerivation.name',
    infos: []
  };

  derivationInfos.allDerivationInfos(userId, proofId, nodeId).then(function(response) {
    $scope.derivationInfos.infos = response.data;
  });

  $scope.applyTactic = function(formulaId, tacticId) {
    $uibModalInstance.close({formulaId: formulaId, tacticId: tacticId});
  }

  $scope.applyInputTactic = function(formulaId, tacticId, input) {
    $uibModalInstance.close({formulaId: formulaId, tacticId: tacticId, input: input});
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
