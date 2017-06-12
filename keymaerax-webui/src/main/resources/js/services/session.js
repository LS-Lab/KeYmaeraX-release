angular.module('keymaerax.services').factory('sessionService', ['$cookies', function($cookies) {

  //todo session recovery interceptor

  //todo avoid cookies
  var serviceDef = {
    setToken: function(token) { $cookies.put('sessionToken', token, { path: '/' }); },
    getToken: function() { return $cookies.get('sessionToken', { path: '/' }); },
    setUser: function(user) { $cookies.put('userId', user, { path: '/' }); },
    getUser: function() { return $cookies.get('userId', { path: '/' }); },
    setUserAuthLevel: function(level) { $cookies.put('userAuthLevel', level, { path: '/' }); },
    getUserAuthLevel: function() { return $cookies.get('userAuthLevel', { path: '/' }); },
    isGuest: function() { return $cookies.get('userAuthLevel', { path: '/' }) == 3; },
    isAnonymous: function() { return $cookies.get('sessionToken', { path: '/' }) === undefined; }
  }
  return serviceDef;
}])