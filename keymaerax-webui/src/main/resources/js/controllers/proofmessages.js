angular.module('keymaerax.controllers').controller('ProofMessagesCtrl',
  function($rootScope, $scope) {

  $scope.proofMessage = {
    text: "",
    isVisible: false
  }

  $rootScope.$on('agenda.updateWithoutProgress', function() {
    $scope.proofMessage.text = "The tactic did not make progress";
    $scope.proofMessage.isVisible = true;
  });

  $rootScope.$on('proof.message', function(event, message) {
    $scope.proofMessage.text = message + ": please check the JavaScript console of your browser for details";
    $scope.proofMessage.isVisible = true;
  });

})