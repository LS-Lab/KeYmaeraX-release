angular.module('keymaerax.controllers').controller('TestSynthCtrl',
    function($scope, $uibModalInstance, $http, spinnerService, FileSaver, Blob, userid, modelid) {

  $scope.testsynthdata = {
    modelid: modelid,
    monitorkind: 'controller',
    numInstances: 1,
    timeout: 0,
    kinds: {compliant: true, incompliant: false}, //@todo with definable safety margin
    metric: undefined,
    testCases: {
      plot: undefined,
      caseInfos: [
        { name: "Foo",
          // bar chart comparing pre/post
          // test case runs? series of test cases that test a simulation run...
          pre: [ { v: "x", val: 5.13}, { v: "y", val: 1 } ],
          post: [ { v: "x", val: 6.34}, { v: "y", val: 0.5 } ]
        },
        { name: "Bar",
          // bar chart comparing pre/post
          // test case runs? series of test cases that test a simulation run...
          pre: [ { v: "x", val: 4.87}, { v: "y", val: 2 } ],
          post: [ { v: "x", val: 3.54}, { v: "y", val: 2.3 } ]
        }
      ]
    }
  }

  $scope.testgenerate = function() {
    spinnerService.show('testSynthesisExecutionSpinner')
    $http({method: 'GET',
           url: "user/" + userid + "/model/" + $scope.testsynthdata.modelid + "/testcase/generate/" +
                          $scope.testsynthdata.monitorkind + '/' + $scope.testsynthdata.numInstances + '/' + $scope.testsynthdata.timeout,
           params: {kinds: JSON.stringify($scope.testsynthdata.kinds)}})
      .then(function(response) {
        $scope.testsynthdata.testCases.plot = response.data.plot;
        $scope.testsynthdata.testCases.metric = response.data.metric; //.(html|string|plainString)
      })
      .finally(function() { spinnerService.hide('testSynthesisExecutionSpinner'); });
  }

  $scope.cancel = function() {
    $uibModalInstance.dismiss('cancel');
  }

});
