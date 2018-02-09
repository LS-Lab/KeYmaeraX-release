angular.module('keymaerax.controllers').controller('LemmaBrowserCtrl',
    function($scope, $uibModalInstance, derivationInfos, sequentProofData, userId, proofId, nodeId, formulaId, formula) {

  $scope.userId = userId;
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formulaId = formulaId;
  $scope.formula = formula;
  $scope.sequent = sequentProofData.proofTree.node(nodeId).getSequent();

  $scope.derivationInfos = {
    filter: undefined,
    order: 'standardDerivation.name',
    infos: []
  };

  derivationInfos.allDerivationInfos(userId, proofId, nodeId).then(function(response) {
    $scope.derivationInfos.infos = response.data;
  });

  $scope.applyTactic = function(formulaId, tacticId) {
    var fmlId = formulaId ? formulaId : sequentProofData.formulas.highlighted;
    sequentProofData.formulas.highlighted = undefined;
    $uibModalInstance.close({formulaId: fmlId, tacticId: tacticId});
  }

  $scope.applyInputTactic = function(formulaId, tacticId, input) {
    var fmlId = formulaId ? formulaId : sequentProofData.formulas.highlighted;
    sequentProofData.formulas.highlighted = undefined;
    $uibModalInstance.close({formulaId: fmlId, tacticId: tacticId, input: input});
  }

  $scope.formulaSelected = function(formulaId, tacticId) {
    if (sequentProofData.formulas.highlighted != formulaId) {
      sequentProofData.formulas.highlighted = formulaId;
    } else {
      sequentProofData.formulas.highlighted = undefined;
    }
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
