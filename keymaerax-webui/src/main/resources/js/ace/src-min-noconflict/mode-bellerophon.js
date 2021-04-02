ace.define("ace/mode/bellerophon_highlight_rules",["require","exports","module","ace/lib/oop","ace/mode/text_highlight_rules"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;

var BellerophonHighlightRules = function() {

    //@todo
    var keywords = (
    "auto|unfold|prop|"+
    "andL|andR|orL|orR|implyL|implyR|equivL|equivR|"+
    "composeb|assignb|choiceb|loop"
    );

    var builtinConstants = ("'R|'L|'_");

    var keywordMapper = this.createKeywordMapper({
        "variable.language": "this",
        "keyword": keywords,
        "constant.language": builtinConstants
    }, "text");

    // regexp must not have capturing parentheses. Use (?:) instead.
    // regexps are ordered -> the first match is used

    this.$rules = {
        "start" : [
            {
                token : "comment", // multi line comment
                regex : "\\/\\*",
                next : "comment"
            }, {
                token : "string", // single line
                regex : '["](?:(?:[^"]))*?["]'
            }, {
                token : "string", // single line
                regex : '[`](?:(?:[^`]))*?[`]'
            }, {
                token : "constant.numeric", // hex
                regex : /0(?:[xX][0-9a-fA-F][0-9a-fA-F_]*|[bB][01][01_]*)[LlSsDdFfYy]?\b/
            }, {
                token : "constant.numeric", // float
                regex : /[+-]?\d[\d_]*(?:(?:\.[\d_]*)?(?:[eE][+-]?[\d_]+)?)?[LlSsDdFfYy]?\b/
            }, {
                token : "constant.language.boolean",
                regex : "(?:true|false)\\b"
            }, {
                regex: "(open(?:\\s+))?module(?=\\s*\\w)",
                token: "keyword",
                next: [{
                    regex: "{",
                    token: "paren.lparen",
                    next: [{
                        regex: "}",
                        token: "paren.rparen",
                        next: "start"
                    }]
                }, {
                    token : "text",
                    regex : "\\s+"
                }, {
                    token : "identifier",
                    regex : "\\w+"
                }, {
                    token : "punctuation.operator",
                    regex : "."
                }, {
                    token : "text",
                    regex : "\\s+"
                }, {
                    regex: "", // exit if there is anything else
                    next: "start"
                }]
            }, {
                token : keywordMapper,
                // TODO: Unicode escape sequences
                // TODO: Unicode identifiers
                regex : "[a-zA-Z][a-zA-Z0-9_]*\\b"
            }, {
                token : "keyword.operator",
                regex : "!|&|\\*|->|\\-|\\+|=|!=|<=|>=|<|>|\\||\\?|;"
            }, {
                token : "lparen",
                regex : "[[({]"
            }, {
                token : "rparen",
                regex : "[\\])}]"
            }, {
                token : "text",
                regex : "\\s+"
            }
        ],
        "comment" : [
            {
                token : "comment", // closing comment
                regex : "\\*\\/",
                next : "start"
            }, {
                defaultToken : "comment"
            }
        ]
    };
};

oop.inherits(BellerophonHighlightRules, TextHighlightRules);

exports.BellerophonHighlightRules = BellerophonHighlightRules;
});

ace.define("ace/mode/matching_brace_outdent",["require","exports","module","ace/range"], function(require, exports, module) {
"use strict";

var Range = require("../range").Range;

var MatchingBraceOutdent = function() {};

(function() {

    this.checkOutdent = function(line, input) {
        if (! /^\s+$/.test(line))
            return false;

        return /^\s*\}/.test(input);
    };

    this.autoOutdent = function(doc, row) {
        var line = doc.getLine(row);
        var match = line.match(/^(\s*\})/);

        if (!match) return 0;

        var column = match[1].length;
        var openBracePos = doc.findMatchingBracket({row: row, column: column});

        if (!openBracePos || openBracePos.row == row) return 0;

        var indent = this.$getIndent(doc.getLine(openBracePos.row));
        doc.replace(new Range(row, 0, row, column-1), indent);
    };

    this.$getIndent = function(line) {
        return line.match(/^\s*/)[0];
    };

}).call(MatchingBraceOutdent.prototype);

exports.MatchingBraceOutdent = MatchingBraceOutdent;
});

ace.define("ace/mode/folding/bellerophon",["require","exports","module","ace/lib/oop","ace/range","ace/mode/folding/fold_mode"], function(require, exports, module) {
"use strict";

var oop = require("../../lib/oop");
var Range = require("../../range").Range;
var BaseFoldMode = require("./fold_mode").FoldMode;

var FoldMode = exports.FoldMode = function() {};
oop.inherits(FoldMode, BaseFoldMode);

(function() {

    this.foldingStartMarker = /[~=]="([^"]*)/;
    this.foldingStopMarker = /([^"]*)"/;

    this.getFoldWidgetRange = function(session, foldStyle, row, forceMultiline) {
        var line = session.getLine(row);

        var match = line.match(this.foldingStartMarker);
        if (match) {
          return new Range(row, match.index, row, match.index + match[0].length + 1);
        }
    };

}).call(FoldMode.prototype);

});

ace.define("ace/mode/bellerophon",["require","exports","module","ace/lib/oop","ace/mode/text","ace/mode/bellerophon_highlight_rules","ace/mode/matching_brace_outdent","ace/worker/worker_client","ace/mode/behaviour/cstyle","ace/mode/folding/bellerophon"], function(require, exports, module) {
"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var BellerophonHighlightRules = require("./bellerophon_highlight_rules").BellerophonHighlightRules;
var MatchingBraceOutdent = require("./matching_brace_outdent").MatchingBraceOutdent;
var WorkerClient = require("../worker/worker_client").WorkerClient;
var CstyleBehaviour = require("./behaviour/cstyle").CstyleBehaviour;
var CStyleFoldMode = require("./folding/bellerophon").FoldMode;

var Mode = function() {
    this.HighlightRules = BellerophonHighlightRules;

    this.$outdent = new MatchingBraceOutdent();
    this.$behaviour = new CstyleBehaviour();
    this.foldingRules = new CStyleFoldMode();
};
oop.inherits(Mode, TextMode);

(function() {

    //this.lineCommentStart = "//";
    this.blockComment = {start: "/*", end: "*/"};
    this.$quotes = {'"': '"', "'": "'", "`": "`"};

    this.getNextLineIndent = function(state, line, tab) {
        var indent = this.$getIndent(line);

        var tokenizedLine = this.getTokenizer().getLineTokens(line, state);
        var tokens = tokenizedLine.tokens;
        var endState = tokenizedLine.state;

        if (tokens.length && tokens[tokens.length-1].type == "comment") {
            return indent;
        }

        if (state == "start" || state == "no_regex") {
            var match = line.match(/^.*(?:\bcase\b.*:|[\{\(\[])\s*$/);
            if (match) {
                indent += tab;
            }
        }

        return indent;
    };

    this.checkOutdent = function(state, line, input) {
        return this.$outdent.checkOutdent(line, input);
    };

    this.autoOutdent = function(state, doc, row) {
        this.$outdent.autoOutdent(doc, row);
    };

    // create worker for live syntax checking
    this.createWorker = function(session) {
        var worker = new WorkerClient(["ace"], "ace/mode/bellerophon_worker", "Worker");
        worker.attachToDocument(session.getDocument());
        worker.on("annotate", function(e) {
            session.setAnnotations(e.data);
        });
        worker.on("terminate", function(e) {
            session.clearAnnotations();
        });
        return worker;
    };

    this.$id = "ace/mode/bellerophon";
}).call(Mode.prototype);

exports.Mode = Mode;
});

(function() {
    ace.require(["ace/mode/bellerophon"], function(m) {
        if (typeof module == "object" && typeof exports == "object" && module) {
            module.exports = m;
        }
    });
})();
