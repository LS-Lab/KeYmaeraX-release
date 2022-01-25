angular.module('keymaerax.controllers').controller('LemmaBrowserCtrl',
    function($scope, $uibModal, $uibModalInstance, derivationInfos, sequentProofData, userId, proofId, nodeId, formulaId, tab) {

  $scope.userId = userId;
  $scope.proofId = proofId;
  $scope.nodeId = nodeId;
  $scope.formulaId = formulaId;
  $scope.sequent = sequentProofData.proofTree.node(nodeId).getSequent();
  $scope.tab = tab == 'lemmas' ? 2 : 1;


  $scope.derivationInfos = {
    filter: undefined,
    order: 'standardDerivation.longName',
    displayLevel: 'browse',
    infos: [],
    lemmas: []
  };

  $scope.loadDerivationInfos = function() {
    $scope.axiomsLoading = true;
    derivationInfos.allDerivationInfos(userId, proofId, nodeId).then(function(response) {
      $scope.derivationInfos.infos = response.data;
      $scope.axiomsLoading = false;
    });
  }

  $scope.loadLemmas = function() {
    $scope.lemmasLoading = true;
    derivationInfos.allLemmas(userId).then(function(response) {
      $scope.derivationInfos.lemmas = response.data;
      $scope.lemmasLoading = false;
    })
  }

  //@see sequent.js/useLemma
  $scope.useLemma = function(formulaId, lemma) {
    if (lemma.useLemmaTac && lemma.useLemmaTac != "verbatim") {
      var tactic = lemma.useLemmaTac ? (lemma.useLemmaTac != "custom" ? lemma.useLemmaTac : lemma.customTac) : undefined;
      var input = [{ type: "string", param: "lemma", value: lemma.name},
                   { type: "string", param: "tactic", value: tactic }];
      $uibModalInstance.close({formulaId: formulaId, tacticId: "useLemma", input: input});
    } else {
      var input = [{ type: "string", param: "lemma", value: lemma.name}];
      $uibModalInstance.close({formulaId: formulaId, tacticId: "useLemma", input: input});
    }
  }

  $scope.applyTactic = function(tactic) {
    return function(formulaId, tacticId) {
      var fmlId = formulaId ? formulaId : sequentProofData.formulas.highlighted;
      $scope.executeTactic(tactic, fmlId, {formulaId: fmlId, tacticId: tacticId});
    }
  }

  $scope.applyInputTactic = function(tactic) {
    return function(formulaId, tacticId, input) {
      var fmlId = formulaId ? formulaId : sequentProofData.formulas.highlighted;
      $scope.executeTactic(tactic, fmlId, {formulaId: fmlId, tacticId: tacticId, input: input});
    }
  }

  $scope.executeTactic = function(tactic, formulaId, retVal) {
    if (tactic.selectedDerivation().numPositionArgs == 0 || (formulaId && formulaId !== '')) {
      sequentProofData.formulas.highlighted = undefined;
      $uibModalInstance.close(retVal);
    } else {
      $uibModal.open({
        templateUrl: 'templates/modalMessageTemplate.html',
        controller: 'ModalMessageCtrl',
        size: 'sm',
        resolve: {
          title: function() { return "Position needed"; },
          message: function() { return "Please select where to apply the tactic in the sequent at the top of the browse dialog"; },
          mode: function() { return "ok"; },
          oktext: function() { return "OK"; }
        }
      });
    }
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
