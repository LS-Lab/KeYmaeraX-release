angular.module('keymaerax.controllers').controller('HACMSTreeCtrl', function($scope, $http, $uibModal, $routeParams, sessionService) {
  $scope.proofId = $routeParams.proofId;

  $scope.treeContents = "asdf"
  { //grab tree data.
      var uri = "/proofs/user/" + sessionService.getUser() + "/" + $routeParams.proofId + "/tree/"
      $http.get(uri)
          .success(function(data) {
              if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Error encountered while trying to retrieve the tree.")
              $scope.treeContents = printNode(data);
          });
  }


  var printNode = function(n) {
      if(n === null) {
          return "Could not load proof tree."
      }
      var childrenResults;
      if(n.children.length > 0) {
          childrenResults = "<ol>" + n.children.map(printNode) + "</ol>"
      }
      else {
          childrenResults = ""
      }
      return "<li>" + n.label + childrenResults + "</li>"
  };

  $scope.$emit('routeLoaded', {theview: '/prooftree/:proofId'})
});