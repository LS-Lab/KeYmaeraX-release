angular.module('keymaerax.controllers').controller('ModelPlexCtrl',
    function($scope, $uibModalInstance, $http, spinnerService, userid, modelid) {

  $scope.mxdata = {
    modelid: modelid,
    monitorkind: 'controller',
    monitor: undefined,
    additionalMonitorVars: [],
    mandatoryMonitorVars: []
  }

  $http.get("user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/mandatoryVars")
    .then(function(response) {
      $scope.mxdata.mandatoryMonitorVars = response.data.mandatoryVars;
    })

  $scope.modelplex = function() {
    spinnerService.show('modelplexExecutionSpinner')
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.mxdata.modelid + "/modelplex/generate/" + $scope.mxdata.monitorkind,
           params: {vars: JSON.stringify($scope.mxdata.additionalMonitorVars)}})
      .then(function(response) {
        $scope.mxdata.monitor = response.data.monitor;
      })
      .finally(function() { spinnerService.hide('modelplexExecutionSpinner'); });
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
