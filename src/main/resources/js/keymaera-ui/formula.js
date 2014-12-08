angular.module('formula', ['ngSanitize'])
  .directive('k4Formula', function() {
    return {
        restrict: 'AE',
        scope: {
            formula: '=',
            highlight: '='
        },
        controller: function($scope, $sce) {
            function span(id, content) {
                if ($scope.highlight) {
                    return '<span xmlns="http://www.w3.org/1999/xhtml"' +
                             'onmouseover="$(event.target).addClass(\'hlhover\');"' +
                             'onmouseout="$(event.target).removeClass(\'hlhover\');"' +
                             'class="hl" id="' + id + '">' + content + '</span>';
                } else {
                    return '<span xmlns="http://www.w3.org/1999/xhtml"' +
                             'class="hl" id="' + id + '">' + content + '</span>';
                }
            }

            // Recursively generate sequent HTML
            function parseFormulaHelper(json, depth) {
                var items = [];
                if (json.hasOwnProperty("children") && $.isArray(json.children)) {
                    var c = json.children;
                    var content;
                    switch (json.name) {
                        case "not":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = "&not;" + left;
                            break;

                        case "and":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &#8743; " + right;
                            break;

                        case "or":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &#8744; " + right;
                            break;

                        case "imply":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " → " + (depth === 0 ? "<br/>" : "") + right;
                            break;

                        case "equiv":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &#8596 " + right;
                            break;

                        case "lt":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &lt; " + right;
                            break;

                        case "leq":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &leq; " + right;
                            break;

                        case "equals":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " = " + right;
                            break;

                        case "notEquals":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &ne; " + right;
                            break;

                        case "geq":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &geq; " + right;
                            break;

                        case "gt":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &gt; " + right;
                            break;

                        case "neg":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = "-" + left;
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
                            content = left + " &middot; " + right;
                            break;

                        case "divide":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " / " + right;
                            break;

                        case "exp":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + "<sup>" + right + "</sup>";
                            break;

                        case "boxmodality":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = "[" + left + "] " + right;
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
                            content = " ? " + left;
                            break;

                        case "Loop":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = "{" + left + "}<sup>*</sup>";
                            break;

                        case "Sequence":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + "; " + right;
                            break;

                        case "Choice":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            var right = parseFormulaHelper(c[1], depth + 1);
                            content = left + " &#8746; " + right;
                            break;

                        case "ContEvolve":
                            content = parseFormulaHelper(c[0], depth + 1);
                            break;

                        case "derivative":
                            var left = parseFormulaHelper(c[0], depth + 1);
                            content = left + "'";
                            break;

                        default:
                            var seqs = [];
                            for (var i = 0; i < c.length; i++) {
                                seqs.push(parseFormulaHelper(c[i]));
                            }
                            content = json.name + "(" + seqs.join(", ") + ")";
                            break;
                    }
                    items.push(span(json.id, content));
                } else {
                    items.push(json.name);
                }
                return items.join("");
            }

            $scope.parseFormula = function(json) {
                return $sce.trustAsHtml(parseFormulaHelper(json, 0));
            };
        },
        template: '<span ng-bind-html="parseFormula(formula)"></span>'
    };
  });