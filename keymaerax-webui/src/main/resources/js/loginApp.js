  var loginApp = angular.module('loginApp', [
  'ngRoute',
  'ngCookies',
  'ngSanitize',
  'ngAnimate',
  'ui.bootstrap',
  'keymaerax.controllers',
  'keymaerax.errorHandlers',
  'keymaerax.interceptors',
  'keymaerax.services'
], function($rootScopeProvider) {
  $rootScopeProvider.digestTtl(1000);
});

loginApp.config(['$routeProvider',
  function($routeProvider) {
    $routeProvider.
      when('/dashboard', {
        templateUrl: 'partials/dashboard.html',
        controller: 'DashboardCtrl'
      }).
      otherwise({
        redirectTo: '/dashboard'
      });
  }]);

// intercept all generic ErrorResponses, intercept all requests to add authentication header
loginApp.config(['$httpProvider', function($httpProvider) {
  $httpProvider.interceptors.push('ResponseErrorHandler');
  $httpProvider.interceptors.push('authInjector');
}])
