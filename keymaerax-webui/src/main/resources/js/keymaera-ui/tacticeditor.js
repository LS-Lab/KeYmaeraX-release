angular.module('keymaerax.ui.tacticeditor', ['ngSanitize', 'ngTextcomplete'])
  .directive('k4TacticEditor', ['$http', 'derivationInfos', 'Textcomplete', 'sequentProofData',
      function($http, derivationInfos, Textcomplete, sequentProofData) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onTacticScript: '&'
        },
        link: function(scope, elem, attr) {
          scope.tactic = sequentProofData.tactic;

          var combinators = ['*', '|', '&', '<'];
          var ta = elem.find('textarea');
          var textcomplete = new Textcomplete(ta, [
            // combinators
            {
              match: /\B:(\w*)$/,
              search: function (term, callback) {
                callback($.map(combinators, function (element) {
                    return element.indexOf(term) === 0 ? element : null;
                }));
              },
              index: 1,
              replace: function (element) { return element; }
            },
            // positions 1.0.tactic
            {
                match: /(((\-?[1-9]([0-9]*)\.)([0-1]\.)*)(\w*))$/,
                search: function (term, callback) {
                  var dotPos = term.lastIndexOf('.');
                  var keyword = term.substring(dotPos + 1);
                  this.position = term.substring(0, dotPos);
                  // other code for some reason uses , as separator
                  var formulaId = this.position.replace(/\./g, ',');
                  sequentProofData.formulas.highlighted = formulaId.indexOf(',') >= 0 ? formulaId : formulaId + ','; //@note top-level formula IDs end in ','
                  //console.log("Matched term " + term + ", searching for keyword " + keyword + "; position " + this.position);
                  $http.get('proofs/user/' + scope.userId + '/' + scope.proofId + '/' + scope.nodeId + '/' + formulaId + '/list')
                       .success(function(data) {
                    callback($.map(data, function (element) {
                      return element.standardDerivation.id.indexOf(keyword) === 0 ? element.standardDerivation.id : null;
                    }));
                  });
                },
                index: 2,
                replace: function (element) {
                  sequentProofData.formulas.highlighted = undefined;
                  scope.onTactic({formulaId: this.position, tacticId: element});
                  //return ['<' + element + '>', '</' + element + '>'];
                  return element + "(" + this.position + ")";
                }
            }
          ]);

          $(textcomplete).on({
            'textComplete:select': function(e, value) {
              scope.$apply(function() {
                sequentProofData.tactic.tacticText = value
              })
            },
            'textComplete:show': function(e) {
              $(this).data('autocompleting', true);
            },
            'textComplete:hide': function(e) {
              $(this).data('autocompleting', false);
            }
          });
        },
        template: '<div class="row k4-tacticeditor"><div class="col-md-12"><textarea class="k4-tacticeditor" ng-model="tactic.tacticText" type="text" rows="10"></textarea></div></div>' +
                  '<div class="row"><div class="col-md-12"><button class="btn btn-default" data-ng-click="onTacticScript({tacticText: tactic.tacticText})">Run entire tactic</button></div></div>'
    };
  }]);
