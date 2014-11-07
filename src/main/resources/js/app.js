var keymaeraProofApp = angular.module('keymaeraProofApp', [
  'ngRoute',
  'ngCookies',
  'angularTreeview',
  'ui.bootstrap',
  'keymaeraProofControllers',
  'treeControl',
  'progressMeter',
  'proofProgressChart'
]);

keymaeraProofApp.config(['$routeProvider',
  function($routeProvider) {
    $routeProvider.
      when('/dashboard', {
        templateUrl: 'partials/dashboard.html',
        controller: 'DashboardCtrl'
      }).
      when('/models', {
        templateUrl: 'partials/model-list.html',
        controller: 'ModelListCtrl'
      }).
      when('/models/:modelId', {
        templateUrl: 'partials/model-detail.html',
        controller: 'ModelDetailCtrl'
      }).
      when('/models/:modelId/proofs', {
        templateUrl: 'partials/modelproof-list.html',
        controller: 'ModelProofsCtrl'
      }).
      when('/models/:modelId/proofs/create', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proof-create.html',
        controller: 'ModelProofCreateCtrl'
      }).
      when('/proofs', {
        templateUrl: 'partials/proof-list.html',
        controller: 'ProofListCtrl'
      }).
      when('/test', {
        templateUrl: 'partials/test.html',
        controller: 'TestCtrl'
      }).
      when('/proofs/:proofId', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proof-breadcrumbs.html',
        controller: 'ProofDetailCtrl'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]);