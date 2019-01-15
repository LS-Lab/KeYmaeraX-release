/*
Language: dL
Description: Differential dynamic logic is a logic for describing properties of hybrid programs.
Author: Stefan Mitsch
*/

function(hljs) {
  var PROGOP = {
    begin: /:=|\+\+|\*|\?/,
    className: 'progop',
    relevance: 0
  };
  
  var LOGOP = {
    begin: /\&|->|<->|\||!/,
    className: 'logop',
    relevance: 0
  };
  
  var BOXOPENOP = {
    begin: /\[/,
    className: 'boxopenop',
    relevance: 0
  };
  
  var BOXCLOSEOP = {
    begin: /\]/,
    className: 'boxcloseop',
    relevance: 0
  }
  
  var DIAMONDOPENOP = {
    begin: /</,
    className: 'diamondopenop',
    relevance: 0
  };
  
  var DIAMONDCLOSEOP = {
    begin: />/,
    className: 'diamondcloseop',
    relevance: 0
  }
  
  return {
    case_insensitive: false,
    lexemes: '[@a-zA-Z][a-zA-Z0-9]*',
    keywords: {
      keyword: 'ArchiveEntry Theorem Lemma Exercise SharedDefinitions Functions Definitions ProgramVariables Problem Tactic End @invariant if else Link Citation Title Description Author See',
      literal: 'true false Real Bool HP'
    },
    contains: [
      PROGOP,
      LOGOP,
      BOXOPENOP,
      BOXCLOSEOP,
      DIAMONDOPENOP,
      DIAMONDCLOSEOP,
      hljs.C_NUMBER_MODE,
      hljs.C_BLOCK_COMMENT_MODE,
      hljs.QUOTE_STRING_MODE
    ]
  };
}
