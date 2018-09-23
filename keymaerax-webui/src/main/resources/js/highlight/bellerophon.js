/*
Language: Bellerophon
Description: Bellerophon is a tactic language in the theorem prover KeYmaera X.
Author: Stefan Mitsch
*/

function(hljs) {
  var INPUT = {
    begin: /\{`/,
    end: /`\}/,
    className: 'string',
    relevance: 0
  };
  
  var COMBINATOR = {
    begin: /<|\||\*/,
    className: 'keyword',
    relevance: 0
  };
  
  return {
    case_insensitive: false,
    lexemes: '[a-zA-Z][a-zA-Z0-9]*',
    keywords: 'doall nil skip done loop prop unfold master QE closeId cut fullSimplify',
    contains: [
      INPUT,
      COMBINATOR,
      hljs.C_NUMBER_MODE,
      hljs.C_BLOCK_COMMENT_MODE
    ]
  };
}
