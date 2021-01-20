angular.module('keymaerax.ui.directives')
  .directive('k4ProofList', ['$uibModal', 'Proofs', function($uibModal, Proofs) {
    return {
      restrict: 'AE',
      scope: {
        userId: '@',
        modelId: '@'
      },
      templateUrl: 'partials/proof-list.html',
      link: function(scope, element, attrs) {
        scope.createProof = function(modelId, proofName, proofDescription) {
          Proofs.createProof(userId, modelId, proofName, proofDescription);
        };

        scope.deleteProof = function(proof) {
          Proofs.deleteProof(scope.userId, proof);
        };

        scope.downloadTactic = function(proof) {
          Proofs.downloadTactic(scope.userId, proof);
        };

        scope.downloadLemma = function(proof) {
          Proofs.downloadLemma(scope.userId, proof);
        };

        scope.downloadPartialProof = function(proof) {
          Proofs.downloadProofArchive(scope.userId, proof)
        };

        scope.openTactic = function (proofid) {
          var modalInstance = $uibModal.open({
            templateUrl: 'partials/prooftacticdialog.html',
            controller: 'ProofTacticDialogCtrl',
            size: 'fullscreen',
            resolve: {
              userid: function() { return scope.userId; },
              proofid: function() { return proofid; },
              title: function() { return "Tactic"; },
              message: function() { return undefined; }
            }
          });
        };

        scope.downloadModelProofs = function(modelId) {
          Proofs.downloadModelProofs(scope.userId, modelId);
        };

        scope.downloadAllProofs = function() {
          Proofs.downloadAllProofs(scope.userId);
        };

        Proofs.loadProofList(scope.userId, scope.modelId);
        scope.proofs = Proofs.proofs;
      }
    }
  }]
)
