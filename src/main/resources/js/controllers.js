var keymaeraProofControllers = angular.module('keymaeraProofControllers', ['ngCookies']);

keymaeraProofControllers.controller('DashboardCtrl', ['$scope', '$http', '$cookies', '$cookieStore',
  function ($scope, $http, $cookies, $cookieStore) {
    //MODEL LIST
    $scope.models = [];

    //Populate the models list with data from the server.
    $http.get("models/users/" + $cookies.userId).success(function(data,status,headers,config) {
        for(var i=0;i<data.length;i++) {
            $scope.models.push(data[i])
        }
    });

    $scope.addModel = function() {
        var model = {
            id : $scope.id,
            name : $scope.name,
            date : $scope.date,
            userId : $scope.userId,
            keyFile: $scope.keyFile
        }
        $scope.models.push(model)
    }


//    //////////////
//    // Model List
//    //////////////
//    $scope.models = []
//
//    var modelList = $http.get("models/user")
//    alert(modelList)
////      for(var i = 0 ; i < result.length; i++) {
////
////        var currResult = result[i];
////        table.append(
////            "<tr>" +
////                "<td>" + currResult.id.substring(0,5) + "</td>" +
////                "<td>" + currResult.date + "</td>" +
////                "<td>" + currResult.name + "</td>" +
////                "<td>" + "" + "</td>" + //remove description?
////                "<td>" + makeDropdown(currResult.id) + "</td>" +
////            "</tr>"
////        )
////      }
//    })
//
//    //Adds a model to the view; does not CREATE a new model.
//    $scope.addModel() {
//      var model = {
//        id: $scope.id,
//        name: $scope.name,
//        date: $scope.date,
//        keyFile: $scope.keyFile
//      };
//    }


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
            $http.get('user/0/proofs/' + data.proofid).success(function(data) {
                $scope.proofTree = [ data.proofTree.model ];
                globalProofTree = [ data.proofTree.model ];
            });
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

keymaeraProofControllers.controller('ProofDetailCtrl', ['$scope', '$http', '$routeParams',
  function($scope, $http, $routeParams) {
    $http.get('user/0/proofs/' + $routeParams.proofId).success(function(data) {
        $scope.proofId = data.proofid;
        $scope.proofTree = data.proofTree;
    });
    $scope.$emit('routeLoaded', {theview: 'proofs'});
  }]);