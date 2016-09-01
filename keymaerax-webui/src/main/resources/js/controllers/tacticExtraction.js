angular.module('keymaerax.controllers').controller('TacticExtractionCtrl',
  function($scope, $uibModal, $uibModalInstance, tacticText) {
    $scope.tacticText = tacticText

    $scope.cancel = function() {
      $uibModalInstance.dismiss('cancel');
    }
  });

angular.module('keymaerax.controllers').controller('VerbatimMessageCtrl',
    function($scope, $uibModal, $uibModalInstance, title, verbatimText) {
        $scope.title = title
        $scope.verbatimText = verbatimText

        $scope.cancel = function() {
            $uibModalInstance.dismiss('cancel');
        }
    });

function showVerbatimMessage(modal, title, verbatimText) {
    var modalInstance = modal.open({
        templateUrl: 'templates/verbatimTemplate.html',
        controller: 'VerbatimMessageCtrl',
        size: 'md',
        resolve: {
            title: function() { return title; },
            verbatimText: function() { return verbatimText; }
        }
    })
}
