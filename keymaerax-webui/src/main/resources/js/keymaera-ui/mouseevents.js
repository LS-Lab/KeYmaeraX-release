angular.module('keymaerax.ui.mouseevents', [])

/** Right-click directive */
angular.module('keymaerax.ui.mouseevents')
  .directive('ngRightClick', ['$parse', function($parse) {
    return function(scope, element, attrs) {
        var fn = $parse(attrs.ngRightClick);
        element.bind('contextmenu', function(event) {
            scope.$apply(function() {
                event.preventDefault();
                fn(scope, {$event:event});
            });
        });
    };
  }]);

angular.module('keymaerax.ui.mouseevents')
  .directive('k4Draggable', ['$parse', function($parse) {
    return {
      restrict: 'A',
      link: function(scope, element, attrs) {
        element[0].draggable = true;
        var dragStart = attrs.onDragStart !== undefined ? $parse(attrs.onDragStart) : undefined;

        element[0].addEventListener('dragstart', function(event) {
          event.dataTransfer.effectAllowed = 'move';
          var dragData = JSON.stringify(attrs.dragData)
          //@note hack to make data available in dragenter and dragleave
          event.dataTransfer.setData('k4/dragdata/' + dragData, dragData);
          angular.element(event.target).addClass('k4-drag');
          scope.$apply(dragStart(scope, {event: event}));
        });

        element[0].addEventListener('dragend', function(event) {
          angular.element(event.target).removeClass('k4-drag');
        });
      }
    }
  }]);

angular.module('keymaerax.ui.mouseevents')
  .directive('k4Droppable', ['$parse', function($parse) {
    return {
      restrict: 'A',
      scope: {
        onDrop: '&',
        onDragEnter: '&',
        onDragLeave: '&'
      },
      link: function(scope, element, attrs) {
        element[0].addEventListener('dragover', function(event) {
          event.dataTransfer.dropEffect = 'move';
          // allows us to drop
          if (event.preventDefault) event.preventDefault();
          angular.element(event.target).addClass('k4-drag-over');
          // see JavaScript spec: event.dataTransfer.getData('dragData') does not return the data set during dragstart!
        });

        element[0].addEventListener('dragenter', function(event) {
          angular.element(event.target).addClass('k4-drag-over');
          var data = $.grep(event.dataTransfer.types, function(e, i) { return e.substr(0, 'k4/dragdata/'.length) === 'k4/dragdata/' });
          var dragData = data.length == 1 ? JSON.parse(data[0].substr('k4/dragdata/'.length)) : undefined;
          scope.$apply(scope.onDragEnter({dragData: dragData}));
        });

        element[0].addEventListener('dragleave', function(event) {
          angular.element(event.target).removeClass('k4-drag-over');
          var data = $.grep(event.dataTransfer.types, function(e, i) { return e.substr(0, 'k4/dragdata/'.length) === 'k4/dragdata/' });
          var dragData = data.length == 1 ? JSON.parse(data[0].substr('k4/dragdata/'.length)) : undefined;
          scope.$apply(scope.onDragLeave({dragData: dragData}));
        });

        element[0].addEventListener('drop', function(event) {
          // Stops some browsers from redirecting
          if (event.stopPropagation) event.stopPropagation();
          angular.element(event.target).removeClass('k4-drag-over');
          var data = $.grep(event.dataTransfer.types, function(e, i) { return e.substr(0, 'k4/dragdata/'.length) === 'k4/dragdata/' });
          var dragData = data.length == 1 ? JSON.parse(data[0].substr('k4/dragdata/'.length)) : undefined;
          scope.$apply(scope.onDrop({dragData: dragData}));
        });
      }
    }
  }]);
