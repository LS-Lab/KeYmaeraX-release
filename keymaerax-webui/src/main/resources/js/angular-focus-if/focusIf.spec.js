(function() {
    'use strict';
    describe('Directive: focus-if [A]', function() {
        var $scope,
            $compile,
            $timeout,
            $document,
            tpl = '<input type="text" focus-if="{{watchProperty}}" focus-delay="{{delay}}" />',
            element;

        beforeEach(module('focus-if'));

        beforeEach(function() {
            jasmine.addMatchers({
                toHaveFocus: function() {
                    return {
                        compare: function(dom) {
                            var focused;
                            if (!(dom instanceof Node)) {
                                dom = dom[0];
                            }
                            focused = dom == document.activeElement;
                            return {
                                pass: focused,
                                message: focused ? 'Expected ' + dom + ' not to have focus'
                                    : 'Expected ' + dom + ' to have focus'
                            };
                        }
                    };
                }
            });
        });

        beforeEach(inject(function($rootScope, _$compile_, _$timeout_, _$document_) {
            $scope = $rootScope.$new();
            $compile = _$compile_;
            $timeout = _$timeout_;
            $document = _$document_;
        }));

        afterEach(function() {
            element.remove();
        });

        describe('<input focus-if>', function() {
            it('should have focus immediately', onLinkTest);
        });

        describe('<input focus-if focus-delay="500">', function() {
            it('should have focus after 500ms', function() {
                $scope.delay = 500;
                onLinkTest();
            });
        });

        function onLinkTest() {
            compile();
            flush();
            expect(element).toHaveFocus();
        }

        function compile() {
            element = $compile(tpl)($scope);
            angular.element($document[0].body).append(element);
        }

        function flush() {
            $timeout.flush(($scope.delay || 0) - 1);
            expect(element).not.toHaveFocus();
            $timeout.flush(1);
        }

        describe('<input focus-if="watchProperty">', function() {
            beforeEach(watchBeforeEach);
            it('should not have focus immediately when $scope.watchProperty is falsy', falsyWatchTest);
            it('should have focus immediately when $scope.watchProperty is truthy', truthyWatchTest);
        });

        describe('<input focus-if="watchProperty" focus-delay="500">', function() {
            beforeEach(function() {
                $scope.delay = 500;
                watchBeforeEach();
            });
            it('should not have focus after 500ms when $scope.focus-if is falsy', falsyWatchTest);
            it('should have focus after 500ms when $scope.focus-if is truthy', truthyWatchTest);
        });

        function watchBeforeEach() {
            $scope.watchProperty = 'focus';
            $scope.focus = false;
            compile();
        }

        function falsyWatchTest() {
            $timeout.verifyNoPendingTasks();
            expect(element).not.toHaveFocus();
        }

        function truthyWatchTest() {
            falsyWatchTest();
            $scope.focus = true;
            $scope.$digest();
            flush();
            expect(element).toHaveFocus();
        }
    });
})();
