////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Counter example
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('CounterExampleCtrl',
    function($scope, $uibModalInstance, result, origFormula, cexFormula, cexValues, speculatedValues) {

  $scope.result = result;
  $scope.origFormula = origFormula;
  $scope.cexFormula = cexFormula;
  $scope.cexValues = cexValues;
  $scope.speculatedValues = speculatedValues;

  $scope.cancel = function() {
    $uibModalInstance.dismiss('ok');
  }

});
