angular.module('keymaerax.controllers').controller('LemmaBrowserCtrl',
    function($scope, $uibModalInstance, derivationInfos, sequentProofData, userId, proofId, nodeId, formulaId) {

  $scope.userId = userId;
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formulaId = formulaId;
  $scope.sequent = sequentProofData.proofTree.node(nodeId).getSequent();

  $scope.derivationInfos = {
    filter: undefined,
    order: 'standardDerivation.name',
    infos: [],
    lemmas: []
  };

  $scope.loadDerivationInfos = function() {
    derivationInfos.allDerivationInfos(userId, proofId, nodeId).then(function(response) {
      $scope.derivationInfos.infos = response.data;
    });
  }

  $scope.loadLemmas = function() {
    derivationInfos.allLemmas(userId).then(function(response) {
      $scope.derivationInfos.lemmas = response.data;
    })
  }

  //@see sequent.js/useLemma
  $scope.useLemma = function(formulaId, lemma) {
    if (lemma.useLemmaTac && lemma.useLemmaTac != "verbatim") {
      var tactic = lemma.useLemmaTac ? (lemma.useLemmaTac != "custom" ? lemma.useLemmaTac : lemma.customTac) : undefined;
      var input = [{ type: "string", param: "lemma", value: lemma.name},
                   { type: "string", param: "tactic", value: tactic }];
      $scope.applyInputTactic(formulaId, "useLemma", input);
    } else {
      var input = [{ type: "string", param: "lemma", value: lemma.name}];
      $scope.applyInputTactic(formulaId, "useLemma", input);
    }
  }

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
