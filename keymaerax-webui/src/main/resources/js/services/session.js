angular.module('keymaerax.services').factory('sessionService', ['$cookies', function($cookies) {

  //todo session recovery interceptor

  var serviceDef = {
    setToken: function(token) { $cookies.put('sessionToken', token); },
    getToken: function() { return $cookies.get('sessionToken'); },
    setUser: function(user) { $cookies.put('userId', user); },
    getUser: function() { return $cookies.get('userId'); },
    isAnonymous: function() { return $cookies.get('sessionToken') === undefined; }
  }
  return serviceDef;
}])