// Therefore — Level 2: Sentential logic.
// Notation follows The Logic Book: ~ & ∨ ⊃ ≡. Always print connectives through
// SYMBOLS so the planned notation setting can swap them in one place.
(function(){
'use strict';

const SYMBOLS = {not:'~', and:'&', or:'∨', cond:'⊃', bicond:'≡'};

registerLevel({num:2, title:'Sentential logic', topics:[
  {title:'Symbolization', sub:'Translate English into symbols'},
  {title:'Truth tables', sub:'Build tables and classify sentences'},
  {title:'Derivations', sub:'Natural deduction proofs'},
]});
})();
