angular.module('formula', ['ngSanitize']);

/** Renders a formula into hierarchically structured spans */
angular.module('formula')
  .directive('k4Formula', ["$compile", function($compile) {
    return {
        restrict: 'AE',
        scope: {
            formula: '=',
            highlight: '=',
            collapsed: '=?'
        },
        link: function($scope, $sce) {
            var span = function(id, content, depth) {
                if ($scope.highlight) {
                    return '<span class="hl" id="' + id + '"' +
                             'onmouseover="$(event.target).addClass(\'hlhover\');"' +
                             'onmouseout="$(event.target).removeClass(\'hlhover\');"' +
                             'ng-click="formulaClick(\'' + id + '\', $event)">' + content + '</span>';
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

            $scope.formulaClick = function(formulaId, event) {
              // avoid event propagation to parent span (otherwise: multiple calls with a single click since nested spans)
              event.stopPropagation();
              console.log("Formula click " + formulaId)
            }

            // TODO: Popover menu

            var template =
              '<span ng-if="highlight">' + parseFormulaHelper($scope.formula, 0, false) + '</span>' +
              '<span ng-if="!highlight" class="k4-abbreviate">' + parseFormulaHelper($scope.formula, 0, $scope.collapsed) + '</span>';
            // compile template, bind to scope, and add into DOM
            $sce.append($compile(template)($scope));
        }
    };
  }]);
