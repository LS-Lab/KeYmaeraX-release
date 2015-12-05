angular.module('keymaerax.controllers').controller('HACMSTreeCtrl', function($scope, $http, $cookies, $uibModal, $routeParams) {
  $scope.proofId = $routeParams.proofId;

  $scope.treeContents = "asdf"
  { //grab tree data.
      var uri = "/proofs/user/" + $cookies.get('userId') + "/" + $routeParams.proofId + "/tree/"
      $http.get(uri)
          .success(function(data) {
              if(data.errorThrown) showCaughtErrorMessage($uibModal, data, "Error encountered while trying to retrieve the tree.")
              $scope.treeContents = printNode(data);
          })
          .error(function() {
              showErrorMessage($uibModal, "Error encountered while trying to retrieve the tree.")
          })
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