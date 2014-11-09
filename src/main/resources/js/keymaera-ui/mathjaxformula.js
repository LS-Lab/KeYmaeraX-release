angular.module('mathjaxformula', ['ngSanitize','mathjaxbind'])
  .directive('k4Mathjaxformula', function() {
    return {
        restrict: 'AE',
        scope: {
            formula: '=',
            delimiter: '='
        },
        controller: function($scope, $sce, $attrs) {
            // Recursively generate LaTeX
            function parseFormulaHelper(json, depth) {
                var items = [];
                if (json.hasOwnProperty("children") && $.isArray(json.children)) {
                    var c = json.children;
                    var content;
                    switch (json.name) {
                        case "not":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = " \\neg " + left;
                            break;

                        case "and":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\wedge " + right;
                            break;

                        case "or":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\vee " + right;
                            break;

                        case "imply":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\rightarrow " + right;
                            break;

                        case "equiv":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\equiv " + right;
                            break;

                        case "lt":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\lt " + right;
                            break;

                        case "leq":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\le " + right;
                            break;

                        case "equals":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " = " + right;
                            break;

                        case "notEquals":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\neq " + right;
                            break;

                        case "geq":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\ge " + right;
                            break;

                        case "gt":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " \\gt " + right;
                            break;

                        case "neg":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = " -" + left;
                            break;

                        case "add":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " + " + right;
                            break;

                        case "subtract":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " - " + right;
                            break;

                        case "multiply":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " " + right;
                            break;

                        case "divide":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = "\\frac{" + left + "}{" + right + "}";
                            break;

                        case "exp":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + "^" + right;
                            break;

                        case "boxmodality":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = "\\left[" + left + "\\right]" + right;
                            break;

                        case "Assign":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " := " + right;
                            break;

                        case "NDetAssign":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = left + ":= *";
                            break;

                        case "Test":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = "?" + left;
                            break;

                        case "Loop":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = "\\left\\{" + left + "\\right\\}^*";
                            break;

                        case "Sequence":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + ";~" + right;
                            break;

                        case "Choice":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + "\\cup" + right;
                            break;

                        default:
                            var seqs = [];
                            for (var i = 0; i < c.length; i++) {
                                seqs.push(parseFormulaHelper(c[i]));
                            }
                            content = json.name + "(" + seqs.join(", ") + ")";
                            break;
                    }
                    items.push(content);
                } else {
                    items.push(json.name);
                }
                return items.join("");
            }

            $scope.parseFormula = function(json, delimiter) {
                if (delimiter == "display") { return "\\[" + parseFormulaHelper(json, 0) + "\\]"; }
                else { return "\\(" + parseFormulaHelper(json, 0) + "\\)"; }
            };
        },
        template: '<span k4-mathjaxbind="parseFormula(formula, delimiter)"></span>'
    };
  });