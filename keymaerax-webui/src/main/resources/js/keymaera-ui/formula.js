angular.module('formula', ['ngSanitize']);

/** Renders a formula into hierarchically structured spans */
angular.module('formula')
  .directive('k4Formula', ['$compile', '$http', function($compile, $http) {
    return {
        restrict: 'AE',
        scope: {
            userId: '=',
            proofId: '=',
            nodeId: '=',
            goalId: '=',
            formula: '=',
            highlight: '=',
            collapsed: '=?',
            onTactic: '&',     // onTactic(formulaId, tacticId)
            onInputTactic: '&' // onInputTactic(formulaId, tactic)
        },
        link: function($scope, $sce) {
            var span = function(id, content, depth) {
                if ($scope.highlight) {
                    return '<span class="hl" id="' + id + '"' +
                             'onmouseover="$(event.target).addClass(\'hlhover\');"' +
                             'onmouseout="$(event.target).removeClass(\'hlhover\');"' +
                             'ng-click="formulaClick(\'' + id + '\', $event)"' +
                             'ng-right-click="formulaRightClick(\'' + id + '\', $event)"' +
                             // initialize formulaId for popover template, use ng-repeat for scoping
                             'ng-repeat="formulaId in [\'' + id + '\']"' +
                             'uib-popover-template="\'js/keymaera-ui/axiomPopoverTemplate.html\'"' +
                             'popover-title="Apply tactic"' +
                             'popover-is-open="tacticPopover.isOpen(\'' + id + '\')"' +
                             'popover-trigger="outsideClick"' + // in upcoming angular-ui 1.0
                             'popover-append-to-body="true"' +
                             'popover-placement="bottom">' + content + '</span>';
                } else {
                    return content;
                }
            }

            var needsParens = function(parent, child) {
                var precedence =
                  [
                  //Terms.
                  "add" ,
                  "subtract" ,
                  "multiply" ,
                  "divide" ,
                  "exp" ,
                  "neg" ,
                  "function" ,
                  "programconstant" , //real-valued.
                  "number"   ,
                  //Formulas
                  "equiv" ,
                  "imply" ,
                  "or" ,
                  "and" ,
                  "not" ,
                  "boxmodality"  ,
                  "diamondmodality" ,
                  "modality" ,
                  "forall" ,
                  "exists" ,
                  "equal" ,
                  "notEqual" ,
                  "lt"  ,
                  "leq" ,
                  "geq" ,
                  "gt" ,
                  "formuladerivative" ,
                  "predicateconstant" ,
                  //Programs.
                  "Choice" ,
                  "Sequence" ,
                  "Loop" ,
                  "Assign" ,
                  "NDetAssign" ,
                  "Test" ,
                  "NFODEProduct" ,
                  "ODEProduct" ,
                  "AtomicODE" ,
                  // Atoms
                  "ProgramConstant" ,
                  "ContEvolveProgramConstant",
                  "applypredicate" ,
                  "true" ,
                  "false" ,
                  "apply",
                  "derivative" ,
                  "differentialsymbol" ,
                  "Variable",
                  "Number"].reverse()

                var childPrecedence = precedence.indexOf(child.name);
                var parentPrecedence = precedence.indexOf(parent.name);
                return childPrecedence > parentPrecedence;
            }

            var parensIfNeeded = function(parent, child, depth, collapsed) {
                var parens = [ "(", ")" ]
//                  if(child.isInstanceOf[Program]) ["{","}"]
//                  else ["(",")"]

                if(needsParens(parent, child)) {
                  return parens[0] + parseFormulaHelper(child, depth, collapsed) + parens[1]
                } else {
                  return parseFormulaHelper(child, depth, collapsed)
                }
              }

            // Recursively generate sequent HTML
            var parseFormulaHelper = function(json, depth, collapsed) {
                var items = [];
                if (json.hasOwnProperty("children") && $.isArray(json.children)) {
                    var c = json.children;
                    var content;
                    switch (json.name) {
                        case "not":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = "&not;" + left;
                            break;

                        case "and":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &#8743; " + right;
                            break;

                        case "or":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &#8744; " + right;
                            break;

                        case "imply":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + (depth === 0 && !collapsed ? "<br/>" : "") + "→" + (depth === 0 && !collapsed ? "<br/>" : "") + right;
                            break;

                        case "equiv":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &#8596 " + right;
                            break;

                        case "lt":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &lt; " + right;
                            break;

                        case "leq":
                            var left = parseFormulaHelper(c[0], depth + 1, collapsed);
                            var right = parseFormulaHelper(c[1], depth + 1, collapsed);
                            content = left + " &leq; " + right;
                            break;

                        case "equals":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " = " + right;
                            break;

                        case "notEquals":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &ne; " + right;
                            break;

                        case "geq":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &geq; " + right;
                            break;

                        case "gt":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &gt; " + right;
                            break;

                        case "neg":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = "-" + left;
                            break;

                        case "add":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " + " + right;
                            break;

                        case "subtract":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " - " + right;
                            break;

                        case "multiply":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " &middot; " + right;
                            break;

                        case "divide":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " / " + right;
                            break;

                        case "exp":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + "<sup>" + right + "</sup>";
                            break;

                        case "forall":
                            var vars = json.variables[0];
                            for (var i = 1; i < json.variables.length; i++) {
                                vars = vars + "," + json.variables[i];
                            }
                            content = "&forall;" + vars + ". (" + parseFormulaHelper(c[0], depth + 1, collapsed) + ")"
                            break;

                        case "exists":
                            var vars = json.variables[0];
                            for (var i = 1; i < json.variables.length; i++) {
                                vars = vars + "," + json.variables[i];
                            }
                            content = "&exist;" + vars + ". (" + parseFormulaHelper(c[0], depth + 1, collapsed) + ")"
                            break;

                        case "boxmodality":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = "[" + left + "] " + right;
                            break;

                        case "diamondmodality":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = "<" + left + "> " + right;
                            break;

                        case "Assign":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + " := " + right;
                            break;

                        case "NDetAssign":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = left + ":= *";
                            break;

                        case "Test":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = " ? " + left;
                            break;

                         case "IfThen":
                            var left = parseFormulaHelper(c[0], depth+1, collapsed)
                            var right = parseFormulaHelper(c[1], depth+1, collapsed)
                            content = "if (" + left + ") then {" + right + "} fi"
                            break;

                        case "IfThenElse":
                            var condT = parseFormulaHelper(c[0], depth+1, collapsed)
                            var thenT = parseFormulaHelper(c[1], depth+1, collapsed)
                            var elseT = parseFormulaHelper(c[2], depth+1, collapsed)
                            content = "if " + condT + " then {" + thenT + "} else {" + elseT + "} fi"
                            break;

                        case "Loop":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = "{" + left + "}<sup>*</sup>";
                            break;

                        case "Sequence":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + ";" + (collapsed ? " " : "<br/>") + right;
                            break;

                        case "Choice":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = left + (collapsed ? " " : "<br/>") + "&#8746;" + (collapsed ? " " : "<br/>") + right;
                            break;

                        case "AtomicODE":
                            var x = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var theta = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            content = x + " = " + theta;
                            break;

                        case "ODEProduct":
                            var left = parseFormulaHelper(c[0], depth + 1, collapsed);
                            var right = parseFormulaHelper(c[1], depth + 1, collapsed);
                            if (c[1].name != "EmptyODE") {
                              content = left + ", " + right;
                            } else {
                              content = left;
                            }
                            break;

                        case "EmptyODE":
                            content = ""
                            break;

                        case "NFODEProduct":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            var right = parensIfNeeded(json, c[1], depth + 1, collapsed);
                            if (c[1].name != "EmptyODE") {
                              if(c[1].name == "AtomicODE" || c[1].name == "ODEProduct") {
                                content = left + ", " + right;
                              } else content = left + " & " + right;
                            } else {
                              content = left;
                            }
                            break;

                        case "formuladerivative":
                            content = "(" + parseFormulaHelper(c[0], depth, collapsed) + ")'"
                            break;

                        case "derivative":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = left + "'";
                            break;

                        case "differentialsymbol":
                            var left = parensIfNeeded(json, c[0], depth + 1, collapsed);
                            content = left + "'";
                            break;

                        case "Anything": content = "?"; break;
                        case "Nothing": content = ""; break;

                        case "apply":
                            var name = c[0]
                            if (c[1].name != "Nothing") {
                              content = name + parensIfNeeded(json, c[1], depth + 1, collapsed);
                            } else {
                              content = name + "()";
                            }
                            break;

                        default:
                            var seqs = [];
                            for (var i = 0; i < c.length; i++) {
                                seqs.push(parseFormulaHelper(c[i], depth, collapsed));
                            }
                            content = json.name + "(" + seqs.join(", ") + ")";
                            break;
                    }
                    items.push(span(json.id, content, depth));
                } else {
                    items.push(span(json.id, json.name, depth));
                }
                return items.join("");
            }

            $scope.formulaAxiomsMap = {};

            $scope.formulaClick = function(formulaId, event) {
              // avoid event propagation to parent span (otherwise: multiple calls with a single click since nested spans)
              event.stopPropagation();
              $scope.onTactic({formulaId: formulaId, tacticId: "step"});
            }

            $scope.formulaRightClick = function(formulaId, event) {
              event.stopPropagation();
              // emulate hoverable popover (to come in later ui-bootstrap version) with hide on blur (need to focus for blur)
              event.target.focus();
              if ($scope.formulaAxiomsMap[formulaId] === undefined) {
                // axioms not fetched yet
                $http.get('proofs/user/' + $scope.userId + '/' + $scope.proofId + '/' + $scope.nodeId + '/' + $scope.goalId + '/' + formulaId + '/list')
                  .success(function(data) {
                    $scope.formulaAxiomsMap[formulaId] = $.map(data, function(tactic, i) {
                      if (tactic.deduction.type === 'sequentrule') {
                        return convertSequentRuleToInput(tactic);
                      } else if (tactic.deduction.type === 'axiom') {
                        return tactic;
                      } else {
                        console.log("Unknown deduction type '" + tactic.deduction.type + "'");
                      }
                    });
                    $scope.tacticPopover.open(formulaId);
                });
              } else {
                // tactic already cached
                $scope.tacticPopover.open(formulaId);
              }
            }

            $scope.applyTactic = function(formulaId, tacticId) {
              console.log("Applying tactic " + tacticId + " on formula " + formulaId);
              $scope.onTactic({formulaId: formulaId, tacticId: tacticId});
            }

            $scope.applyInputTactic = function(formulaId, tactic) {
              console.log("Applying input tactic " + tactic.id + " on formula " + formulaId);
              $scope.onInputTactic({formulaId: formulaId, tacticId: tacticId});
            }

            $scope.input = function(formula, tactic) {
              return $.grep(tactic.deduction.input, function(elem, i) { return elem.param === formula; })[0].value;
            }

            $scope.tacticPopover = {
              openFormulaId: undefined,
              isOpen: function(formulaId) { return $scope.tacticPopover.openFormulaId === formulaId; },
              open: function(formulaId) { $scope.tacticPopover.openFormulaId = formulaId; },
              close: function() { $scope.tacticPopover.openFormulaId = undefined; }
            }

            convertSequentRuleToInput = function(tactic) {
              tactic.deduction.premise = $.map(tactic.deduction.premise, function(premise, i) {
                return {ante: convertToInput(premise.ante, tactic), succ: convertToInput(premise.succ, tactic)};
              });
              return tactic;
            }

            convertToInput = function(formulas, tactic) {
              //@note double-wrap array so that it doesn't get flattened
              return $.map(formulas, function(formula, i) { return [convertFormulaToInput(formula, tactic)]; });
            }

            convertFormulaToInput = function(formula, tactic) {
              var inputs = $.grep(tactic.deduction.input, function(input, i) { return formula.indexOf(input.param) >= 0; });
              var inputBoundaries = $.map(inputs, function(input, i) {
                var inputStart = formula.indexOf(input.param);
                return {start: inputStart, end: inputStart + input.param.length };
              }).sort(function(a, b) { a.start <= b.start ? -1 : 1; });

              var result = [];
              if (inputBoundaries.length > 0) {
                result[0] = {text: formula.slice(0, inputBoundaries[0].start), isInput: false};
                result[1] = createInput(formula, tactic, inputBoundaries[0]);
                for (var i = 1; i < inputBoundaries.length; i++) {
                  result[i+1] = {text: formula.slice(inputBoundaries[i-1].end, inputBoundaries[i].start), isInput: false};
                  result[i+2] = createInput(formula, tactic, inputBoundaries[i]);
                }
                result[inputBoundaries.length+1] = {
                  text: formula.slice(inputBoundaries[inputBoundaries.length-1].end, formula.length),
                  isInput: false
                }
              } else {
                result[0] = {text: formula, isInput: false};
              }
              return result;
            }

            createInput = function(formula, tactic, inputBoundary) {
              var inputId = formula.slice(inputBoundary.start, inputBoundary.end);
              return {
                text: inputId,
                isInput: true,
                value: function(newValue) {
                  if (newValue === undefined) {
                    // get
                    return $.grep(tactic.deduction.input, function(elem, i) { return elem.param === inputId; })[0].value;
                  } else {
                    // set
                    return $.grep(tactic.deduction.input, function(elem, i) { return elem.param === inputId; })[0].value = newValue;
                  }
                }
              };
            }

            var fmlMarkup = parseFormulaHelper($scope.formula, 0, $scope.collapsed);
            var template =
              '<span ng-if="!collapsed">' + fmlMarkup + '</span>' +
              '<span ng-if="collapsed" class="k4-abbreviate">' + fmlMarkup + '</span>';
            // compile template, bind to scope, and add into DOM
            $sce.append($compile(template)($scope));
        }
    };
  }]);
