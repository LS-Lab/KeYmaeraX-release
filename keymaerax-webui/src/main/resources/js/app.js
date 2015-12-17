  var keymaeraProofApp = angular.module('keymaeraProofApp', [
  'ngRoute',
  'ngCookies',
  'ngSanitize',
  'ngAnimate',
  'angularTreeview',
  'ui.tree',
  'cgBusy',
  'ui.bootstrap',
  'ui.bootstrap.tabs',
  'ui.bootstrap.tooltip',
  'ui.bootstrap.popover',
  'ui.bootstrap.collapse',
  'keymaerax.controllers',
  'keymaerax.ui.mouseevents',
  'progressMeter',
  'proofProgressChart',
  'formula',
  'mathjaxformula',
  'mathjaxbind',
  'sequent',
  'sequentproof',
  'xeditable'
], function($rootScopeProvider) {
  $rootScopeProvider.digestTtl(1000);
});

keymaeraProofApp.run(function(editableOptions) {
  editableOptions.theme = 'bs3';
});

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
      when('/tutorials', {
        templateUrl: 'partials/tutorials.html'
      }).
      when('/usage', {
        templateUrl: 'partials/usage.html'
      }).
      when('/syntax', {
        templateUrl: 'partials/syntax.html'
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
        templateUrl: 'partials/proofawesome.html',
        controller: 'ProofCtrl'
      }).
      when('/prooftree/:proofId', {
        templateUrl: 'partials/prooftree-hacms.html',
        controller: 'HACMSTreeCtrl'
      }).
      when('/dev', {
        templateUrl: 'partials/dev.html',
        controller: 'DevCtrl'
      }).
      when('/mathematica', {
        templateUrl: 'partials/mathematica_config.html',
        controller: 'MathematicaConfig'
      }).
      when('/license', {
                templateUrl: 'partials/license_dialog.html',
                controller: 'DashboardCtrl.License'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]);

// triggers for tooltip and popover
keymaeraProofApp.config(['$tooltipProvider', function($tooltipProvider) {
  $tooltipProvider.setTriggers({
    'contextmenu': 'blur'
  });
}]);
