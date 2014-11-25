var keymaeraProofApp = angular.module('keymaeraProofApp', [
  'ngRoute',
  'ngCookies',
  'ngSanitize',
  'angularTreeview',
  'ui.tree',
  'cgBusy',
  'ui.bootstrap',
  'ui.bootstrap.tabs',
  'keymaeraProofControllers',
  'progressMeter',
  'proofProgressChart',
  'formula',
  'mathjaxformula',
  'mathjaxbind',
  'sequent'
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
      when('/proofs/:proofId', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proof.html',
        controller: 'ProofCtrl'
      }).
      when('/dev', {
        templateUrl: 'partials/dev.html',
        controller: 'DevCtrl'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]);
