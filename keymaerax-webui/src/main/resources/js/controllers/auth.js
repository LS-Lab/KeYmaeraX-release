angular.module('keymaerax.interceptors').factory('authInjector', ['$q', '$injector', 'sessionService', function($q, $injector, sessionService) {
  var sessionInjector = {
    request: function(config) {
      if (!sessionService.isAnonymous()) {
        config.headers['x-session-token'] = sessionService.getToken();
      }
      return config;
    }
  };
  return sessionInjector;
}])