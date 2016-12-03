angular.module('keymaerax.ui.keyevents', [])

/** Shift-enter directive */
angular.module('keymaerax.ui.keyevents')
  .directive('ngShiftEnter', ['$parse', function($parse) {
    return function(scope, element, attrs) {
      var fn = $parse(attrs.ngShiftEnter);
      element.bind('keypress', function(event) {
        scope.$apply(function() { if (event.which == 13 && event.shiftKey) event.preventDefault(); });
      });
      element.bind('keyup', function(event) {
        scope.$apply(function() {
          if (event.which == 13 && event.shiftKey) {
            event.preventDefault();
            fn(scope, {$event:event});
          }
        });
      });
    };
  }]);

angular.module('keymaerax.ui.keyevents')
  .directive('ngEnter', ['$parse', function($parse) {
    return function(scope, element, attrs) {
      var fn = $parse(attrs.ngEnter);
      element.bind('keypress', function(event) {
        scope.$apply(function() { if (event.which == 13 && !event.shiftKey) event.preventDefault(); });
      });
      element.bind('keyup', function(event) {
        scope.$apply(function() {
          if (event.which == 13 && !event.shiftKey) {
            event.preventDefault();
            fn(scope, {$event:event});
          }
        });
      });
    };
  }]);
