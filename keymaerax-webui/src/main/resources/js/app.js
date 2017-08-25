  var keymaeraProofApp = angular.module('keymaeraProofApp', [
  'ngRoute',
  'ngCookies',
  'ngFileSaver',
  'ngSanitize',
  'ngAnimate',
  'ngclipboard',
  'ngTextcomplete',
  'angularSpinners',
  'angular-intro',
  'chart.js',
  'hljs',
  'focus-if',
  'ui.bootstrap',
  'ui.bootstrap.tabs',
  'ui.bootstrap.tooltip',
  'ui.bootstrap.popover',
  'ui.bootstrap.collapse',
  'ui.bootstrap.accordion',
  'ui.bootstrap.modal',
  'keymaerax.controllers',
  'keymaerax.errorHandlers',
  'keymaerax.interceptors',
  'keymaerax.services',
  'keymaerax.ui.binding',
  'keymaerax.ui.keyevents',
  'keymaerax.ui.mouseevents',
  'keymaerax.ui.tacticeditor',
  'keymaerax.ui.directives',
  'formula',
  'sequent',
  'sequentproof',
  'xeditable'
], function($rootScopeProvider) {
  $rootScopeProvider.digestTtl(1000);
});

keymaeraProofApp.run(function(editableOptions) {
  editableOptions.theme = 'bs3';
});

keymaeraProofApp.run(function($templateCache, $http) {
  // cache templates for popovers, otherwise they're only populated on second show
  $http.get('templates/axiomPopoverTemplate.html', { cache: $templateCache });
  $http.get('templates/sequentRuleTemplate.html', { cache: $templateCache });
  $http.get('templates/formulaDndTooltipTemplate.html', { cache: $templateCache });
  $http.get('templates/tacticError.html', { cache: $templateCache });
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
        controller: 'ModelListCtrl',
        resolve: { firstTime: function() { return false; } }
      }).
      when('/modelsFirstTime', {
        templateUrl: 'partials/model-list.html',
        controller: 'ModelListCtrl',
        resolve: { firstTime: function() { return true; } }
      }).
      when('/guestmodels', {
        templateUrl: 'partials/guest-model-list.html',
        controller: 'ModelListCtrl',
        resolve: { firstTime: function() { return true; } }
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
        templateUrl: 'partials/proof-list.html',
        controller: 'ProofListCtrl'
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
      when('/guestproofs', {
        templateUrl: 'partials/guest-proof-list.html',
        controller: 'ProofListCtrl'
      }).
      when('/proofs/:proofId', {
        //templateUrl: 'partials/proof-detail.html',
        templateUrl: 'partials/proofawesome.html',
        controller: 'ProofCtrl'
      }).
      when('/proofs/:proofId/browse', {
        templateUrl: 'partials/browseproofawesome.html',
        controller: 'InitBrowseProofCtrl'
      }).
      when('/createModelFromFormula', {
        templateUrl: 'partials/formula_to_model_textbox.html',
        controller: 'FormulaUploadCtrl'
      }).
      when('/dev', {
        templateUrl: 'partials/dev.html',
        controller: 'DevCtrl'
      }).
      when('/tools', {
        templateUrl: 'partials/tool_config.html',
        controller: 'ToolConfig'
      }).
      when('/license', {
                templateUrl: 'partials/license_page.html',
                controller: 'ServerInfoCtrl'
      }).
      when('/import', {
                templateUrl: 'partials/import.html',
                controller: 'ModelUploadCtrl'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]).run(
    function($rootScope, $location, sessionService) {
      // watch route changes
      $rootScope.$on("$routeChangeStart", function(event, next, current) {
        if (sessionService.isGuest()) {
          // guest user, replace model-list.html (most requests in default model-list.html will fail for missing access rights).
          if (next.templateUrl == "partials/model-list.html" ) {
            // redirect to guest models
            $location.path( "/guestmodels" );
          } else if (next.templateUrl == "partials/proof-list.html" ) {
            // redirect to guest proof list
            $location.path( "/guestproofs" );
          }
        }
      });
     }
  );

// triggers for tooltip and popover
keymaeraProofApp.config(['$uibTooltipProvider', function($uibTooltipProvider) {
  $uibTooltipProvider.setTriggers({
    'rightClick': 'blur'
  });
}]);

// intercept all generic ErrorResponses, intercept all requests to add authentication header
keymaeraProofApp.config(['$httpProvider', function($httpProvider) {
  $httpProvider.interceptors.push('ResponseErrorHandler');
  $httpProvider.interceptors.push('authInjector');
}])

keymaeraProofApp.config(function (hljsServiceProvider) {
  hljsServiceProvider.setOptions({
    // replace tab with 2 spaces
    tabReplace: '  '
  });
});
