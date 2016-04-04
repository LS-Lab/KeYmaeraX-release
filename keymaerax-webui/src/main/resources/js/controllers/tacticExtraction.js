angular.module('keymaerax.controllers').controller('TacticExtractionCtrl',
  function($scope, $uibModal, $uibModalInstance, tacticText) {
    $scope.tacticText = tacticText

    $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
    }
  });