var keymaeraProofControllers = angular.module('keymaeraProofControllers', []);

keymaeraProofControllers.controller('DashboardCtrl', ['$scope', '$http',
  function ($scope, $http) {
    // HACK: want to have signed in users
    $http.get("user/0/create");

    // Set the view for menu active class
    $scope.$on('routeLoaded', function (event, args) {
      $scope.theview = args.theview;
    });

    $scope.$emit('routeLoaded', {theview: 'dashboard'});
  }]);

keymaeraProofControllers.controller('ModelListCtrl', ['$scope', '$http',
  function ($scope, $http) {
//    $http.get('models/').success(function(data) {
//      $scope.models = data;
//    });
    $scope.$emit('routeLoaded', {theview: 'models'});
  }]);

keymaeraProofControllers.controller('ModelProofCreateCtrl', ['$scope', '$http',
  function ($scope, $http) {
    // HACK: just to load some file
    jQuery.get('examples/ETCS-safety.key', function(fileContent) {
        $http.post("proofs/0", fileContent).success(function(data) {
            $scope.proofId = data.proofid;
        });
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);

keymaeraProofControllers.controller('ProofListCtrl', ['$scope', '$http',
  function ($scope, $http) {
    $http.get('proofs/').success(function(data) {
      $scope.proofs = data;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);

keymaeraProofControllers.controller('ProofDetailCtrl', ['$scope', '$http',
  function($scope, $http) {
    $http.get('user/0/proofs/' + $scope.proofId).success(function(data) {
        $scope.proofTree = data.proofTree;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);