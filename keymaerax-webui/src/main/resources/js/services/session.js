angular.module('keymaerax.services').factory('sessionService', ['$cookies', function($cookies) {

  //todo session recovery interceptor

  var serviceDef = {
    setToken: function(token) { $cookies.put('sessionToken', token, { path: '/' }); },
    getToken: function() { return $cookies.get('sessionToken', { path: '/' }); },
    setUser: function(user) { $cookies.put('userId', user, { path: '/' }); },
    getUser: function() { return $cookies.get('userId', { path: '/' }); },
    isAnonymous: function() { return $cookies.get('sessionToken', { path: '/' }) === undefined; }
  }
  return serviceDef;
}])