angular.module('keymaerax.controllers').controller('HACMSTreeCtrl', function($scope, $http, $cookies, $routeParams) {
  $scope.proofId = $routeParams.proofId;

  $scope.treeContents = "asdf"
  { //grab tree data.
      var uri = "/proofs/user/" + $cookies.userId + "/" + $routeParams.proofId + "/tree/"
      $http.get(uri)
          .success(function(data) {
              if(data.errorThrown) showCaughtErrorMessage($modal, data, "Error encountered while trying to retrieve the tree.")
              $scope.treeContents = printNode(data);
          })
          .error(function() {
              showErrorMessage($modal, "Error encountered while trying to retrieve the tree.")
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