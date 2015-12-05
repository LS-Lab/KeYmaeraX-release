////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Counter example
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

angular.module('keymaerax.controllers').controller('counterExampleCtrl', function($scope, $modalInstance, $uibModal, $cookies, $http, proofId, nodeId) {
  $http.get('proofs/user/' + $cookies.get('userId') + '/' + proofId + '/nodes/' + nodeId + '/counterExample')
  .success(function(data) {
      $scope.cntEx = data.cntEx;
  });
  $scope.cancel = function() {
    $modalInstance.dismiss('ok');
  }
});