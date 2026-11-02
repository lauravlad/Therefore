// Therefore — Level 2: Sentential logic.
// Modules: Symbolization, Truth tables, Derivations (Fitch-style natural deduction).
// Content is original; definitions are based on forall x: Calgary (CC BY 4.0).
// Default notation: ~ & ∨ ⊃ ≡ with capital sentence letters. Always print connectives
// through SYMBOLS so the planned notation setting can swap them in one place. The parser
// also accepts common alternatives (¬ ∧ → ↔, and keyboard forms like - v -> <->).
(function(){
'use strict';

const SYM = SYMBOLS; // shared with core.js; changes with the notation setting
const BINARY = ['and','or','cond','bicond'];

// =====================================================================
// Parser
// =====================================================================
// Binary connectives need their own parentheses, except around the whole sentence.
const ALIASES = [['<->','bicond'],['<=>','bicond'],['≡','bicond'],['↔','bicond'],['⇔','bicond'],['=','bicond'],
  ['->','cond'],['=>','cond'],['⊃','cond'],['→','cond'],['⇒','cond'],['>','cond'],
  ['&','and'],['∧','and'],['^','and'],['•','and'],['·','and'],['⋅','and'],['.','and'],
  ['∨','or'],['v','or'],['|','or'],
  ['~','not'],['¬','not'],['-','not'],['!','not']].sort((a,b)=>b[0].length-a[0].length);
const OPEN='([{', CLOSE=')]}';
function ParseError(msg){ this.message=msg; }
const VARS='xyz';
function tokenize(src, ql){
  const out=[]; let i=0;
  while(i<src.length){
    const c=src[i];
    if(/\s/.test(c)){ i++; continue; }
    const o=OPEN.indexOf(c), cl=CLOSE.indexOf(c);
    if(o>=0){ out.push({k:'(', b:o}); i++; continue; }
    if(cl>=0){ out.push({k:')', b:cl}); i++; continue; }
    if(/[A-Z]/.test(c)){ out.push({k:'atom', n:c}); i++; continue; }
    if(c==='∀'||c==='∃'){ if(!ql) throw new ParseError('Quantifiers belong to predicate logic (Level 3).'); out.push({k:'q', q:c==='∀'?'all':'some'}); i++; continue; }
    if(ql && c==='\\' && /[AEae]/.test(src[i+1]||'')){ out.push({k:'q', q:/[Aa]/.test(src[i+1])?'all':'some'}); i+=2; continue; }
    const m=ALIASES.find(([s])=>src.startsWith(s,i));
    if(m){ out.push({k:m[1]}); i+=m[0].length; continue; }
    if(/[a-z]/.test(c)){
      if(ql){ out.push({k:'term', n:c}); i++; continue; }
      throw new ParseError(`Sentence letters are capitals. Try “${c.toUpperCase()}” instead of “${c}”.`);
    }
    throw new ParseError(`“${c}” isn’t a symbol I recognize.`);
  }
  return out;
}
// opts.ql: predicate logic. Atoms take lowercase terms (Fa, Rxy); quantifiers are (∀x) and (∃x).
function parse(src, opts){
  const ql=!!(opts&&opts.ql), toks=tokenize(String(src), ql); let p=0;
  if(!toks.length) throw new ParseError('Type a sentence first.');
  function unit(){
    const t=toks[p];
    if(!t) throw new ParseError('The sentence ends too soon: something is missing at the end.');
    if(t.k==='not'){ p++; return {t:'not', a:unit()}; }
    if(t.k==='atom'){ p++; const args=[]; while(toks[p] && toks[p].k==='term'){ args.push(toks[p].n); p++; } return {t:'atom', n:t.n, args}; }
    if(t.k==='q'){ p++; return quant(t.q); }
    if(t.k==='(' && toks[p+1] && toks[p+1].k==='q'){
      p+=2; const f=quant(toks[p-1].q, true); return f;
    }
    if(t.k==='term') throw new ParseError(`“${t.n}” can’t stand alone. Lowercase letters go right after a predicate, as in F${t.n}.`);
    if(t.k==='('){
      p++; const f=group(); const c=toks[p];
      if(!c || c.k!==')') throw new ParseError('A left parenthesis is never closed.');
      if(c.b!==t.b) throw new ParseError(`“${OPEN[t.b]}” is closed by “${CLOSE[c.b]}”. Brackets need to match.`);
      p++; return f;
    }
    if(t.k===')') throw new ParseError('Something is missing just before a right parenthesis.');
    throw new ParseError(`“${SYM[t.k]}” needs a sentence on its left.`);
  }
  function quant(q, paren){
    const v=toks[p];
    if(!v || v.k!=='term' || !VARS.includes(v.n)) throw new ParseError(`A quantifier needs a variable (x, y, or z), as in (${q==='all'?'∀':'∃'}x).`);
    p++;
    if(paren){ const c=toks[p]; if(!c || c.k!==')') throw new ParseError(`Close the quantifier’s parentheses, as in (${q==='all'?'∀':'∃'}${v.n}).`); p++; }
    return {t:q, v:v.n, a:unit()};
  }
  function group(){
    const l=unit(), t=toks[p];
    if(t && BINARY.includes(t.k)){
      p++; const r=unit(), t2=toks[p];
      if(t2 && BINARY.includes(t2.k)) throw new ParseError(`Add parentheses: “${SYM[t.k]}” and “${SYM[t2.k]}” can’t share a level. Each binary connective needs its own pair, as in (A & B) ∨ C.`);
      return {t:t.k, l, r};
    }
    return l;
  }
  const f=group();
  if(p<toks.length){
    const t=toks[p];
    if(t.k===')') throw new ParseError('There’s an extra right parenthesis.');
    if(t.k==='atom'||t.k==='('||t.k==='not') throw new ParseError('Two sentences sit side by side with no connective between them.');
    throw new ParseError('Something extra is at the end of the sentence.');
  }
  return f;
}
function tryParse(src, opts){ try{ return {f:parse(src, opts)}; }catch(e){ if(e instanceof ParseError) return {err:e.message}; throw e; } }

// =====================================================================
// Printing, comparing, evaluating
// =====================================================================
// Tokens for display: each connective and atom token points at its node.
const QSYM = {all:'∀', some:'∃'}; // always written (∀x) and (∃x)
function tokensOf(f, top=true, out=[]){
  if(f.t==='atom'){ out.push({s:f.n+(f.args||[]).join(''), node:f, k:'atom'}); return out; }
  if(f.t==='not'){ out.push({s:SYM.not, node:f, k:'conn'}); tokensOf(f.a,false,out); return out; }
  if(f.t==='all'||f.t==='some'){ out.push({s:`(${QSYM[f.t]}${f.v})`, node:f, k:'conn'}); tokensOf(f.a,false,out); return out; }
  if(!top) out.push({s:'(', k:'paren'});
  tokensOf(f.l,false,out); out.push({s:SYM[f.t], node:f, k:'conn'}); tokensOf(f.r,false,out);
  if(!top) out.push({s:')', k:'paren'});
  return out;
}
const joinToks = tk => tk.map(t=>t.k==='conn'&&BINARY.includes(t.node.t)?` ${t.s} `:t.s).join('');
const show = f => joinToks(tokensOf(f));          // outer parentheses dropped
const showP = f => joinToks(tokensOf(f,false));   // with outer parentheses (for parts of a sentence)
function eq(a,b){
  if(a.t!==b.t) return false;
  if(a.t==='atom') return a.n===b.n && (a.args||[]).join('')===(b.args||[]).join('');
  if(a.t==='not') return eq(a.a,b.a);
  if(a.t==='all'||a.t==='some') return a.v===b.v && eq(a.a,b.a);
  return eq(a.l,b.l) && eq(a.r,b.r);
}
function value(f,row){
  switch(f.t){
    case 'atom': return row[f.n];
    case 'not': return !value(f.a,row);
    case 'and': return value(f.l,row) && value(f.r,row);
    case 'or': return value(f.l,row) || value(f.r,row);
    case 'cond': return !value(f.l,row) || value(f.r,row);
    case 'bicond': return value(f.l,row) === value(f.r,row);
  }
}
function lettersOf(...fs){
  const s=new Set();
  const walk=f=>{ if(f.t==='atom') s.add(f.n); else if(f.t==='not') walk(f.a); else { walk(f.l); walk(f.r); } };
  fs.forEach(walk); return [...s].sort();
}
// Standard row order: first row all T; the last letter alternates every row, the one before it every two rows, and so on.
function rowsFor(letters){
  const n=letters.length, rows=[];
  for(let i=0;i<(1<<n);i++){ const row={}; letters.forEach((L,j)=>{ row[L]=((i>>(n-1-j))&1)===0; }); rows.push(row); }
  return rows;
}
function classify(f){
  const vs=rowsFor(lettersOf(f)).map(r=>value(f,r));
  return vs.every(v=>v) ? 'true' : vs.every(v=>!v) ? 'false' : 'indeterminate';
}
const equivalent = (f,g) => rowsFor(lettersOf(f,g)).every(r=>value(f,r)===value(g,r));
const consistent = fs => rowsFor(lettersOf(...fs)).some(r=>fs.every(f=>value(f,r)));
const validArg = (prem, concl) => !rowsFor(lettersOf(...prem,concl)).some(r=>prem.every(f=>value(f,r)) && !value(concl,r));
const connCount = f => f.t==='atom' ? 0 : f.t==='not' ? 1+connCount(f.a) : 1+connCount(f.l)+connCount(f.r);
const TF = b => b ? 'T' : 'F';

// =====================================================================
// Random sentences at three difficulty levels (2, 3, or 4 letters)
// =====================================================================
const POOL='ABCDEFGHJKLMNPQRSTUW'.split('');
const CONN_W=['and','and','or','or','cond','cond','bicond'];
const LV = {1:{n:2,k:[1,2]}, 2:{n:3,k:[2,3]}, 3:{n:4,k:[3,4]}};
const randLetters = n => shuffle(POOL).slice(0,n).sort();
const atom = n => ({t:'atom', n});
function randTree(leaves, k){
  let f;
  if(k===0) f=atom(leaves.pop());
  else { const kl=Math.floor(Math.random()*k); const l=randTree(leaves,kl), r=randTree(leaves,k-1-kl); f={t:pick(CONN_W), l, r}; }
  return Math.random()<0.22 ? {t:'not', a:f} : f;
}
function randSentence(letters, k){
  const leaves=shuffle(letters.concat(Array.from({length:k+1-letters.length},()=>pick(letters))));
  return randTree(leaves,k);
}
function genSentence(level, letters){
  const spec=LV[level]; letters=letters||randLetters(spec.n);
  return randSentence(letters, Math.max(letters.length-1, pick(spec.k)));
}
function substitute(f, map){
  if(f.t==='atom') return map[f.n] ? JSON.parse(JSON.stringify(map[f.n])) : f;
  if(f.t==='not') return {t:'not', a:substitute(f.a,map)};
  return {t:f.t, l:substitute(f.l,map), r:substitute(f.r,map)};
}
// Fill a template's X, Y, Z with letters (or small compounds) so that it uses exactly n letters.
function instantiate(templates, level){
  const fs=templates.map(parse), vars=lettersOf(...fs).filter(v=>'XYZ'.includes(v));
  const L=randLetters(LV[level].n), map={};
  vars.forEach((v,i)=>{ map[v]= Math.random()<.2 ? {t:'not',a:atom(L[i])} : atom(L[i]); });
  L.slice(vars.length).forEach(extra=>{ const v=pick(vars); map[v]= Math.random()<.5 ? {t:pick(['and','or','cond']), l:map[v], r:atom(extra)} : {t:pick(['and','or','cond']), l:atom(extra), r:map[v]}; });
  return fs.map(f=>substitute(f,map));
}
const varCount = ts => lettersOf(...ts.map(parse)).filter(v=>'XYZ'.includes(v)).length;
const TAUT_T=['X ⊃ (Y ⊃ X)','(X & Y) ⊃ X','X ⊃ (X ∨ Y)','(X ⊃ Y) ∨ (Y ⊃ X)','~(X & Y) ≡ (~X ∨ ~Y)'];
const CONTRA_T=['~(X ⊃ (Y ⊃ X))','(X & Y) & ~X','~(X ∨ Y) & X','(X ≡ Y) & (X & ~Y)'];
function genClassified(level){
  const want=pick(['true','false','indeterminate']);
  for(let i=0;i<250;i++){ const f=genSentence(level); if(classify(f)===want && connCount(f)>=2) return f; }
  if(want==='indeterminate') return genSentence(level);
  return instantiate([pick(want==='true'?TAUT_T:CONTRA_T)], level)[0];
}
// Templates for testing with a table. The answer always comes from the table, never from the template.
const TESTS = {
  equiv:[['X ⊃ Y','~Y ⊃ ~X'],['X ⊃ Y','~X ∨ Y'],['~(X & Y)','~X ∨ ~Y'],['~(X ∨ Y)','~X & ~Y'],['X & (Y ∨ Z)','(X & Y) ∨ (X & Z)'],
    ['X ≡ Y','(X ⊃ Y) & (Y ⊃ X)'],['(X & Y) ⊃ Z','X ⊃ (Y ⊃ Z)'],['X ∨ Y','~X ⊃ Y'],
    ['X ⊃ Y','Y ⊃ X'],['X ⊃ Y','~X ⊃ ~Y'],['~(X & Y)','~X & ~Y'],['~(X ∨ Y)','~X ∨ ~Y'],['X & (Y ∨ Z)','(X & Y) ∨ Z'],
    ['X ≡ Y','X ⊃ Y'],['(X ∨ Y) ⊃ Z','X ⊃ (Y ∨ Z)'],['X ∨ Y','X ⊃ ~Y']],
  cons:[['X ⊃ Y','X','~Y'],['X ∨ Y','~X','~Y'],['X ≡ Y','X & ~Y'],['~(X ∨ Y)','X'],['X ⊃ Y','Y ⊃ Z','X & ~Z'],
    ['X ⊃ Y','~Y'],['X ∨ Y','~X'],['X ≡ Y','~X'],['X & Y','Y ⊃ Z'],['~(X & Y)','X ∨ Y']],
  valid:[['X ⊃ Y','X','Y'],['X ⊃ Y','~Y','~X'],['X ⊃ Y','Y ⊃ Z','X ⊃ Z'],['X ∨ Y','~X','Y'],['X ≡ Y','Y','X'],['X & Y','Y ∨ Z'],
    ['X ⊃ Y','Y','X'],['X ⊃ Y','~X','~Y'],['X ∨ Y','X','~Y'],['X ⊃ Y','Y ⊃ X'],['(X & Y) ⊃ Z','X','Z'],['X ∨ Y','Y ⊃ Z','Z']],
};
function testAnswer(kind, fs){
  if(kind==='equiv') return equivalent(fs[0],fs[1]);
  if(kind==='cons') return consistent(fs);
  return validArg(fs.slice(0,-1), fs[fs.length-1]);
}
function genTest(kind, level){
  const want=Math.random()<.5, temps=TESTS[kind].filter(t=>varCount(t)<=LV[level].n);
  let fs;
  for(let i=0;i<300;i++){
    if(Math.random()<.7) fs=instantiate(pick(temps), level);
    else { const L=randLetters(LV[level].n), m=kind==='equiv'?2:kind==='cons'?pick([2,3]):3; fs=Array.from({length:m},()=>genSentence(Math.max(1,level-1), L)); }
    if(testAnswer(kind,fs)===want) return fs;
  }
  return fs;
}

// =====================================================================
// Shared UI: symbol keys, inputs, tables
// =====================================================================
const KEYNAMES={not:'negation',and:'conjunction',or:'disjunction',cond:'conditional',bicond:'biconditional'};
function symKeys(target, ql){
  let keys=['not','and','or','cond','bicond'].map(k=>[BINARY.includes(k)?` ${SYM[k]} `:SYM[k], SYM[k], KEYNAMES[k]]).concat([['(','(','left parenthesis'],[')',')','right parenthesis']]);
  if(ql) keys=keys.concat([['(∀x)','(∀x)','for all x'],['(∃x)','(∃x)','there is an x'],['(∀y)','(∀y)','for all y'],['(∃y)','(∃y)','there is a y'],['x','x','variable x'],['y','y','variable y']]);
  return `<div class="keys" role="group" aria-label="Insert a symbol">${keys.map(([ins,lab,name])=>`<button type="button" data-ins="${esc(ins)}" data-target="${target}" aria-label="${name}">${lab}</button>`).join('')}</div>`;
}
const typingTip = ql => `<p class="hint muted" style="margin-top:6px">On a keyboard you can also type <b class="kbd">-</b> for ${SYM.not}, <b class="kbd">&amp;</b> for ${SYM.and}, <b class="kbd">v</b> for ${SYM.or}, <b class="kbd">&gt;</b> or <b class="kbd">-&gt;</b> for ${SYM.cond}, and <b class="kbd">=</b> or <b class="kbd">&lt;-&gt;</b> for ${SYM.bicond}${ql?', and <b class="kbd">\\A</b> for ∀ or <b class="kbd">\\E</b> for ∃':''}.</p>`;
function insertAt(id, text, replace){
  const el=document.getElementById(id); if(!el) return;
  if(replace){ el.value=text; }
  else { const s=el.selectionStart!=null?el.selectionStart:el.value.length, e=el.selectionEnd!=null?el.selectionEnd:s;
    el.value=el.value.slice(0,s)+text+el.value.slice(e); const p=s+text.length; el.focus(); el.setSelectionRange(p,p); }
  if(replace){ el.focus(); el.setSelectionRange(el.value.length, el.value.length); }
  el.dispatchEvent(new Event('input',{bubbles:true}));
}
function focusAfter(){ const e=App.ex; if(e && e.focus){ const el=document.getElementById(e.focus); if(el && el.focus) el.focus(); e.focus=null; } }
const level = () => getSetting('tfLevel','1');
const levelSeg = () => seg('tfLevel','Difficulty',[['1','2 letters'],['2','3 letters'],['3','4 letters']], level());

function tableModel(f){
  const tk=tokensOf(f), letters=lettersOf(f), rows=rowsFor(letters);
  const cols=tk.map((t,i)=>t.k==='conn'?i:-1).filter(i=>i>=0);
  const main=tk.findIndex(t=>t.k==='conn' && t.node===f);
  return {f, tk, letters, rows, cols, main, val:(r,c)=>value(tk[c].node, rows[r])};
}
// Full table: letter columns, then one column per symbol of the sentence. cell(r,c) renders connective cells.
function renderTable(m, cell, rowClass){
  const head=`<tr><th class="rn"></th>${m.letters.map((L,i)=>`<th class="${i===m.letters.length-1?'sep':''}">${L}</th>`).join('')}${m.tk.map((t,c)=>`<th class="${c===m.main?'main':''}">${esc(t.s)}</th>`).join('')}</tr>`;
  const body=m.rows.map((row,r)=>`<tr class="${rowClass?rowClass(r):''}"><td class="rn">${r+1}</td>${m.letters.map((L,i)=>`<td class="${i===m.letters.length-1?'sep':''}">${TF(row[L])}</td>`).join('')}${m.tk.map((t,c)=>{
    const cls=c===m.main?' class="main"':'';
    if(t.k==='atom') return `<td${cls}><span class="ro atomv">${TF(row[t.s])}</span></td>`;
    if(t.k==='paren') return `<td></td>`;
    return `<td${cls}>${cell(r,c)}</td>`; }).join('')}</tr>`).join('');
  return `<div class="tt-wrap"><table class="tt"><thead>${head}</thead><tbody>${body}</tbody></table></div>`;
}
const RULE_TEXT = {
  not:'A negation has the opposite value of the sentence it negates.',
  and:'A conjunction is true only when both conjuncts are true.',
  or:'A disjunction is false only when both disjuncts are false.',
  cond:'A conditional is false only when its antecedent is true and its consequent is false.',
  bicond:'A biconditional is true exactly when both sides have the same value.',
};
function cellWhy(m, r, c){
  const node=m.tk[c].node, row=m.rows[r], v=x=>TF(value(x,row));
  if(node.t==='not') return `In row ${r+1}, ${esc(showP(node.a))} is ${v(node.a)}, so ${esc(show(node))} is ${v(node)}. ${RULE_TEXT.not}`;
  return `In row ${r+1}, ${esc(showP(node.l))} is ${v(node.l)} and ${esc(showP(node.r))} is ${v(node.r)}, so ${esc(showP(node))} is ${v(node)}. ${RULE_TEXT[node.t]}`;
}
const CLASS_LABEL = {true:'Truth-functionally true (a tautology)', false:'Truth-functionally false (a contradiction)', indeterminate:'Truth-functionally indeterminate (contingent)'};

// =====================================================================
// Key definitions (original wording, based on forall x: Calgary)
// =====================================================================
function charTables(){
  const one=(cap, f)=>{ const m=tableModel(parse(f)); return renderTable(m,(r,c)=>`<span class="ro">${TF(m.val(r,c))}</span>`).replace('<div class="tt-wrap">','<div class="tt-wrap" style="margin:0" aria-label="'+cap+'">'); };
  return `<div class="char-tables">${one('negation','~A')}${one('conjunction','A & B')}${one('disjunction','A ∨ B')}${one('conditional','A ⊃ B')}${one('biconditional','A ≡ B')}</div>`;
}
const TD = () => ({
  letter:['Sentence letter',`A capital letter that stands for a simple sentence. Its inner structure doesn’t matter to sentential logic.`,'Let R mean “It’s raining.”'],
  conn:['Connectives',`Symbols that build longer sentences from shorter ones: ${SYM.not} (not), ${SYM.and} (and), ${SYM.or} (or), ${SYM.cond} (if…then), and ${SYM.bicond} (if and only if). ${SYM.not} attaches to one sentence. The other four join two sentences and come with their own parentheses.`,`R ${SYM.and} ${SYM.not}S says “It’s raining and it isn’t snowing.”`],
  main:['Main connective','The connective added last when the sentence was built. It governs the whole sentence and isn’t inside any parentheses (ignoring a pair around the whole thing).',`In ${SYM.not}(A ${SYM.and} B) the main connective is ${SYM.not}. In ${SYM.not}A ${SYM.and} B it’s ${SYM.and}.`],
  table:['Truth table','A table with one row for each way of assigning T and F to the sentence letters. It shows the sentence’s value in each row. With n letters there are 2ⁿ rows. Rows start with every letter T; the last letter alternates every row, the one before it every two rows, and so on.',`A ${SYM.or} B needs four rows: TT, TF, FT, FF.`],
  taut:['Tautology (truth-functionally true)','A sentence that’s true in every row of its truth table.',`A ${SYM.or} ${SYM.not}A`],
  contra:['Contradiction (truth-functionally false)','A sentence that’s false in every row.',`A ${SYM.and} ${SYM.not}A`],
  contingent:['Contingent (truth-functionally indeterminate)','A sentence that’s true in at least one row and false in at least one row.',`A ${SYM.cond} B`],
  equiv:['Equivalence','Two sentences are equivalent when they have the same value in every row of a truth table that covers both.',`${SYM.not}(A ${SYM.and} B) and ${SYM.not}A ${SYM.or} ${SYM.not}B`],
  cons:['Consistency','A set of sentences is consistent when at least one row makes every sentence in it true. Otherwise it’s inconsistent.',`{A ${SYM.or} B, ${SYM.not}A} is consistent: the row with A false and B true makes both true.`],
  valid:['Validity','An argument is valid when no row makes all the premises true and the conclusion false. A row like that is a counterexample.',`A ${SYM.cond} B, A, therefore B is valid. A ${SYM.cond} B, B, therefore A is not: the row with A false and B true is a counterexample.`],
});
const ttDefs = () => keyDefs([{items:[TD().letter,TD().conn,TD().main,TD().table]},{h:'Kinds of sentences',items:[TD().taut,TD().contra,TD().contingent]},{h:'Relations between sentences',items:[TD().equiv,TD().cons,TD().valid]},
  {h:'Characteristic truth tables',items:[['How each connective works', charTables()]]}]);

registerLevel({num:2, title:'Sentential logic', topics:[
  {title:'Symbolization', sub:'Translate English into symbols', go:'sym'},
  {title:'Truth tables', sub:'Build tables and classify sentences', go:'tt'},
  {title:'Derivations', sub:'Natural deduction proofs', go:'der'},
]});
const soFar = k => { const s=score(k); return s.done?` ${s.right} of ${s.done} correct so far.`:''; };

// =====================================================================
// Truth tables module
// =====================================================================
function ttView(){
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Truth tables</h2>
  <p class="muted">Work out a sentence’s truth value in every possible situation.</p>
  ${ttDefs()}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-go="ttmain"><span>Main connective<small>Find the connective that governs the whole sentence.${soFar('mc')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="ttfull"><span>Complete a truth table<small>Fill in every column, then classify the sentence.${soFar('tt')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="ttspot"><span>Spot the error<small>Is this completed table right? If not, find the wrong entry.${soFar('spot')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="tttest"><span>Test with a table<small>Equivalence, consistency, and validity.${soFar('test')}</small></span><span class="go">Practice</span></button></li>
  </ul>
  ${levelSeg()}`;
}
const newOnLevel = name => { if(name==='tfLevel'||name==='testKind') App.ex=VIEWS[App.view].init(); };

// ----- Main connective -----
function newMain(){
  let f; do{ f=genSentence(+level()); } while(connCount(f)<2 || f.t==='atom');
  return {f, tk:tokensOf(f), pick:null};
}
function mainWhy(f){
  if(f.t==='not') return `The ${SYM.not} at the very front applies to everything after it, so the whole sentence is a negation of ${esc(showP(f.a))}.`;
  return `The ${SYM[f.t]} joins ${esc(showP(f.l))} and ${esc(showP(f.r))}, and it isn’t inside any parentheses.`;
}
function mainView(){
  const e=App.ex, main=e.tk.findIndex(t=>t.k==='conn'&&t.node===e.f);
  const toks=e.tk.map((t,i)=>{
    if(t.k!=='conn') return `<span>${esc(t.s)}</span>`;
    let c='tok'; if(e.pick!==null){ if(i===main) c+=' right'; else if(i===e.pick) c+=' wrong'; }
    const sp = t.node.t!=='not';
    return `${sp?' ':''}<button class="${c}" data-mc="${i}" ${e.pick!==null?'disabled':''} aria-label="${KEYNAMES[t.node.t]}">${esc(t.s)}</button>${sp?' ':''}`;
  }).join('');
  let fb='';
  if(e.pick!==null){
    const ok=e.pick===main, node=e.tk[e.pick].node;
    const wrongWhy = ok ? '' : (node.t==='not' ? `That ${SYM.not} only applies to ${esc(showP(node.a))}, which is part of a bigger sentence. ` : `That ${SYM[node.t]} only joins ${esc(showP(node.l))} and ${esc(showP(node.r))}, inside parentheses. `);
    fb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'}</strong>${wrongWhy}${mainWhy(e.f)}</div>`;
  }
  const sc=score('mc');
  return `<button class="back" data-go="tt">‹ Truth tables</button>
  <div class="ex-head"><h2>Main connective</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([{items:[TD().conn,TD().main]}])}
  ${levelSeg()}
  <section class="step"><h3>Tap the main connective</h3><div class="mc">${toks}</div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}

// ----- Complete a table -----
function newFull(){ const f=genClassified(+level()); return {m:tableModel(f), vals:{}, checked:false, cls:null}; }
function fullView(){
  const e=App.ex, m=e.m, key=(r,c)=>r+','+c;
  const wrong=[]; if(e.checked) m.rows.forEach((_,r)=>m.cols.forEach(c=>{ if(e.vals[key(r,c)]!==TF(m.val(r,c))) wrong.push([r,c]); }));
  const cell=(r,c)=>{ const v=e.vals[key(r,c)]||''; let cls='cell';
    if(e.checked) cls+= v===TF(m.val(r,c)) ? ' right' : ' wrong';
    return `<button class="${cls}" data-cell="${r},${c}" aria-label="Row ${r+1}, ${KEYNAMES[m.tk[c].node.t]} column: ${v||'blank'}">${v}</button>`; };
  let tfb='';
  if(e.checked){
    tfb = !wrong.length ? `<div class="fb good"><strong>Every entry is right.</strong></div>`
      : `<div class="fb bad"><strong>${wrong.length===1?'One entry is':wrong.length+' entries are'} wrong or blank (marked red).</strong><ol>${wrong.slice(0,3).map(([r,c])=>`<li>${cellWhy(m,r,c)}</li>`).join('')}</ol>${wrong.length>3?'<p class="muted">Fix these, then check again.</p>':''}</div>`;
  }
  const truth=classify(m.f);
  const cbtn=k=>{ let c='choice'; if(e.cls){ if(k===truth) c+=' right'; else if(k===e.cls) c+=' wrong'; } return `<button class="${c}" data-cls="${k}" ${e.cls?'disabled':''}>${CLASS_LABEL[k]}</button>`; };
  let cfb='';
  if(e.cls){
    const why={true:'The main column has T in every row.', false:'The main column has F in every row.', indeterminate:'The main column has at least one T and at least one F.'}[truth];
    cfb=`<div class="fb ${e.cls===truth?'good':'bad'}"><strong>${e.cls===truth?'Correct.':'Not quite.'}</strong>${why} So the sentence is ${CLASS_LABEL[truth].toLowerCase()}.</div>`;
  }
  const sc=score('tt');
  return `<button class="back" data-go="tt">‹ Truth tables</button>
  <div class="ex-head"><h2>Complete a truth table</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([{items:[TD().table,TD().taut,TD().contra,TD().contingent]},{h:'Characteristic truth tables',items:[['How each connective works', charTables()]]}])}
  ${levelSeg()}
  <p class="sentence">${esc(show(m.f))}</p>
  <section class="step"><h3>Fill in the table</h3><p class="hint">Tap a cell to cycle through T, F, and blank. Work from the inside out; the shaded column is the main connective.</p>
    ${renderTable(m,cell)}
    <div class="actions"><button class="btn" data-act="check-tt">Check table</button><button class="btn ghost" data-act="clear-tt">Clear</button></div>${tfb}</section>
  <section class="step"><h3>Classify the sentence</h3><div class="choices one">${['true','false','indeterminate'].map(cbtn).join('')}</div>${cfb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}

// ----- Spot the error -----
function newSpot(){
  let f; do{ f=genSentence(+level()); } while(connCount(f)<2);
  const m=tableModel(f), err = Math.random()<.5 ? {r:Math.floor(Math.random()*m.rows.length), c:pick(m.cols)} : null;
  return {m, err, sel:null, ans:null};
}
function spotView(){
  const e=App.ex, m=e.m, isErr=(r,c)=>e.err&&e.err.r===r&&e.err.c===c;
  const shown=(r,c)=>{ const v=m.val(r,c); return TF(isErr(r,c)?!v:v); };
  const cell=(r,c)=>{ let cls='cell'; const sel=e.sel&&e.sel.r===r&&e.sel.c===c;
    if(e.ans){ if(isErr(r,c)) cls+=' wrong'; else if(sel) cls+=' sel'; } else if(sel) cls+=' sel';
    return `<button class="${cls}" data-pickcell="${r},${c}" ${e.ans?'disabled':''} aria-label="Row ${r+1}, ${KEYNAMES[m.tk[c].node.t]} column: ${shown(r,c)}">${shown(r,c)}</button>`; };
  let fb='';
  if(e.ans){
    const fix = e.err ? `${cellWhy(m,e.err.r,e.err.c)} The table shows ${TF(!m.val(e.err.r,e.err.c))} there.` : '';
    if(e.ans==='ok') fb = e.err ? `<div class="fb bad"><strong>There’s one wrong entry (marked red).</strong>${fix}</div>` : `<div class="fb good"><strong>Correct: every entry checks out.</strong></div>`;
    else {
      const hit=e.err && e.sel.r===e.err.r && e.sel.c===e.err.c;
      if(hit) fb=`<div class="fb good"><strong>Correct: that’s the wrong entry.</strong>${fix}</div>`;
      else fb=`<div class="fb bad"><strong>That entry is actually right.</strong>${cellWhy(m,e.sel.r,e.sel.c)} ${e.err?`The mistake is elsewhere (marked red). ${fix}`:'In fact, the whole table is correct.'}</div>`;
    }
  }
  const sc=score('spot');
  return `<button class="back" data-go="tt">‹ Truth tables</button>
  <div class="ex-head"><h2>Spot the error</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([{items:[TD().table]},{h:'Characteristic truth tables',items:[['How each connective works', charTables()]]}])}
  ${levelSeg()}
  <p class="sentence">${esc(show(m.f))}</p>
  <section class="step"><h3>Is this table correct?</h3><p class="hint">Some tables are right; others have exactly one wrong entry. If you find one, tap it, then press “This entry is wrong.”</p>
    ${renderTable(m,cell)}
    <div class="actions"><button class="btn" data-act="spot-ok" ${e.ans?'disabled':''}>The table is correct</button><button class="btn ghost" data-act="spot-cell" ${e.ans||!e.sel?'disabled':''}>This entry is wrong</button></div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next table</button></div>`;
}

// ----- Test with a table -----
const TEST_Q = {equiv:'Are the two sentences equivalent?', cons:'Is the set consistent?', valid:'Is the argument valid?'};
function newTest(){
  let kind=getSetting('testKind','mix'); if(kind==='mix') kind=pick(['equiv','cons','valid']);
  const fs=genTest(kind, +level()), letters=lettersOf(...fs);
  return {kind, fs, letters, rows:rowsFor(letters), vals:{}, checked:false, ans:null};
}
function testView(){
  const e=App.ex, key=(r,i)=>r+','+i, truth=testAnswer(e.kind,e.fs);
  const n=e.fs.length, rowsTrue=e.rows.map(row=>e.fs.map(f=>value(f,row)));
  let witness=[];
  if(e.kind==='equiv') witness=e.rows.map((_,r)=>r).filter(r=>rowsTrue[r][0]!==rowsTrue[r][1]);
  if(e.kind==='cons') witness=e.rows.map((_,r)=>r).filter(r=>rowsTrue[r].every(v=>v));
  if(e.kind==='valid') witness=e.rows.map((_,r)=>r).filter(r=>rowsTrue[r].slice(0,-1).every(v=>v)&&!rowsTrue[r][n-1]);
  const label=i=> e.kind==='valid' ? (i===n-1?'∴ ':'')+show(e.fs[i]) : show(e.fs[i]);
  const head=`<tr><th class="rn"></th>${e.letters.map((L,i)=>`<th class="${i===e.letters.length-1?'sep':''}">${L}</th>`).join('')}${e.fs.map((_,i)=>`<th class="main">${esc(label(i))}</th>`).join('')}</tr>`;
  const body=e.rows.map((row,r)=>`<tr class="${e.ans!==null&&witness.includes(r)?(e.kind==='cons'?'hl':'badrow'):''}"><td class="rn">${r+1}</td>${e.letters.map((L,i)=>`<td class="${i===e.letters.length-1?'sep':''}">${TF(row[L])}</td>`).join('')}${e.fs.map((f,i)=>{
    const v=e.vals[key(r,i)]||''; let cls='cell'; if(e.checked) cls+= v===TF(value(f,row))?' right':' wrong';
    return `<td class="main"><button class="${cls}" data-tcell="${r},${i}" aria-label="Row ${r+1}, sentence ${i+1}: ${v||'blank'}">${v}</button></td>`; }).join('')}</tr>`).join('');
  let tfb='';
  if(e.checked){
    const bad=[]; e.rows.forEach((row,r)=>e.fs.forEach((f,i)=>{ if(e.vals[key(r,i)]!==TF(value(f,row))) bad.push([r,i]); }));
    tfb = bad.length ? `<div class="fb bad"><strong>${bad.length===1?'One entry is':bad.length+' entries are'} wrong or blank (marked red).</strong>For example, in row ${bad[0][0]+1}, ${esc(show(e.fs[bad[0][1]]))} is ${TF(value(e.fs[bad[0][1]],e.rows[bad[0][0]]))}.</div>` : `<div class="fb good"><strong>Every entry is right.</strong></div>`;
  }
  let afb='';
  if(e.ans!==null){
    const ok=e.ans===truth, rl=rs=>rs.slice(0,4).map(r=>r+1).join(', ')+(rs.length>4?', …':'');
    const why = {
      equiv: truth ? 'The two columns match in every row.' : `The columns differ in row${witness.length>1?'s':''} ${rl(witness)} (highlighted), so they’re not equivalent.`,
      cons: truth ? `Row${witness.length>1?'s':''} ${rl(witness)} (highlighted) make${witness.length>1?'':'s'} every sentence true, so the set is consistent.` : 'No row makes every sentence true, so the set is inconsistent.',
      valid: truth ? 'No row has all the premises true and the conclusion false, so the argument is valid.' : `Row${witness.length>1?'s':''} ${rl(witness)} (highlighted) make${witness.length>1?'':'s'} every premise true and the conclusion false. That’s a counterexample, so the argument is invalid.`,
    }[e.kind];
    afb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'}</strong>${why}</div>`;
  }
  const yn=(v,l)=>{ let c='choice'; if(e.ans!==null){ if(v===truth) c+=' right'; else if(v===e.ans) c+=' wrong'; } return `<button class="${c}" data-tans="${v}" ${e.ans!==null?'disabled':''}>${l}</button>`; };
  const words={equiv:['Equivalent','Not equivalent'],cons:['Consistent','Inconsistent'],valid:['Valid','Invalid']}[e.kind];
  const shown = e.kind==='equiv' ? `${esc(show(e.fs[0]))}<br>${esc(show(e.fs[1]))}` : e.kind==='cons' ? `{ ${e.fs.map(f=>esc(show(f))).join(', ')} }`
    : `${e.fs.slice(0,-1).map(f=>esc(show(f))).join('<br>')}<br>∴ ${esc(show(e.fs[n-1]))}`;
  const sc=score('test');
  return `<button class="back" data-go="tt">‹ Truth tables</button>
  <div class="ex-head"><h2>Test with a table</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([{items:[TD().equiv,TD().cons,TD().valid]},{h:'Characteristic truth tables',items:[['How each connective works', charTables()]]}])}
  ${seg('testKind','Test for',[['mix','Mixed'],['equiv','Equivalence'],['cons','Consistency'],['valid','Validity']], getSetting('testKind','mix'))}
  ${levelSeg()}
  <p class="args">${shown}</p>
  <section class="step"><h3>Fill in the main columns</h3><p class="hint">Tap a cell to cycle through T, F, and blank.</p>
    <div class="tt-wrap"><table class="tt"><thead>${head}</thead><tbody>${body}</tbody></table></div>
    <div class="actions"><button class="btn" data-act="check-test">Check table</button></div>${tfb}</section>
  <section class="step"><h3>${TEST_Q[e.kind]}</h3><div class="choices">${yn(true,words[0])}${yn(false,words[1])}</div>${afb}</section>
  <div class="next"><button class="btn" data-act="next">Next problem</button></div>`;
}
const cycle = v => v===''||v==null ? 'T' : v==='T' ? 'F' : '';
function ttClick(ev){
  const e=App.ex, view=App.view, d=x=>ev.target.closest(x);
  let el;
  if((el=d('[data-mc]')) && e.pick===null){ e.pick=+el.dataset.mc; tally('mc', e.tk[e.pick].node===e.f); render(); return; }
  if((el=d('[data-cell]'))){ const k=el.dataset.cell; e.vals[k]=cycle(e.vals[k]); e.checked=false; render(); return; }
  if((el=d('[data-cls]')) && !e.cls){ e.cls=el.dataset.cls; tally('tt', e.cls===classify(e.m.f)); render(); return; }
  if((el=d('[data-pickcell]')) && !e.ans){ const [r,c]=el.dataset.pickcell.split(',').map(Number); e.sel={r,c}; render(); return; }
  if((el=d('[data-tcell]'))){ const k=el.dataset.tcell; e.vals[k]=cycle(e.vals[k]); e.checked=false; render(); return; }
  if((el=d('[data-tans]')) && e.ans===null){ e.ans=el.dataset.tans==='true'; tally('test', e.ans===testAnswer(e.kind,e.fs)); render(); return; }
  const a=d('[data-act]'); if(!a) return;
  const act=a.dataset.act;
  if(act==='check-tt'||act==='check-test'){ e.checked=true; render(); }
  if(act==='clear-tt'){ e.vals={}; e.checked=false; render(); }
  if(act==='spot-ok' && !e.ans){ e.ans='ok'; tally('spot', !e.err); render(); }
  if(act==='spot-cell' && !e.ans && e.sel){ e.ans='cell'; tally('spot', !!e.err && e.sel.r===e.err.r && e.sel.c===e.err.c); render(); }
}
registerView('tt',     {render: ttView, onSetting: ()=>{}});
registerView('ttmain', {init: newMain, render: mainView, click: ttClick, onSetting: newOnLevel});
registerView('ttfull', {init: newFull, render: fullView, click: ttClick, onSetting: newOnLevel});
registerView('ttspot', {init: newSpot, render: spotView, click: ttClick, onSetting: newOnLevel});
registerView('tttest', {init: newTest, render: testView, click: ttClick, onSetting: newOnLevel});

// =====================================================================
// Symbolization module
// =====================================================================
// [level, English, key, model answer]. Any truth-functionally equivalent answer is accepted.
const SYMS = [
 [1,'Maya is not home.',{M:'Maya is home'},'~M'],
 [1,'The library is open and the café is open.',{L:'The library is open',C:'The café is open'},'L & C'],
 [1,'Either the bus is late or Tom missed it.',{B:'The bus is late',T:'Tom missed the bus'},'B ∨ T'],
 [1,'If it rains, the game is canceled.',{R:'It rains',G:'The game is canceled'},'R ⊃ G'],
 [1,'The game is canceled if it rains.',{R:'It rains',G:'The game is canceled'},'R ⊃ G'],
 [1,'The store is open if and only if the lights are on.',{S:'The store is open',L:'The lights are on'},'S ≡ L'],
 [1,'Priya plays guitar, but she doesn’t sing.',{P:'Priya plays guitar',S:'Priya sings'},'P & ~S'],
 [1,'The printer works only if it has paper.',{W:'The printer works',P:'The printer has paper'},'W ⊃ P'],
 [1,'Sam will pass provided that he studies.',{P:'Sam passes',S:'Sam studies'},'S ⊃ P'],
 [1,'Neither Ana nor Ben came to the party.',{A:'Ana came to the party',B:'Ben came to the party'},'~A & ~B'],
 [1,'The soup is hot unless the stove is off.',{H:'The soup is hot',O:'The stove is off'},'H ∨ O'],
 [1,'The first train and the second train are not both late.',{F:'The first train is late',S:'The second train is late'},'~(F & S)'],
 [1,'Jo didn’t win, but she had fun.',{W:'Jo won',F:'Jo had fun'},'~W & F'],
 [1,'If the alarm doesn’t ring, Kai oversleeps.',{A:'The alarm rings',K:'Kai oversleeps'},'~A ⊃ K'],
 [1,'The cookies are ready when the timer beeps.',{C:'The cookies are ready',T:'The timer beeps'},'T ⊃ C'],
 [1,'Lena will order pizza or tacos.',{P:'Lena orders pizza',T:'Lena orders tacos'},'P ∨ T'],
 [1,'Rosa runs every morning, and so does Ivan.',{R:'Rosa runs every morning',I:'Ivan runs every morning'},'R & I'],
 [1,'The plant dies unless someone waters it.',{D:'The plant dies',W:'Someone waters the plant'},'D ∨ W'],
 [1,'Omar is happy if and only if his team wins.',{O:'Omar is happy',T:'Omar’s team wins'},'O ≡ T'],
 [1,'The phone charges only if it’s plugged in.',{C:'The phone charges',P:'The phone is plugged in'},'C ⊃ P'],
 [1,'Ella isn’t tired, and she isn’t hungry.',{T:'Ella is tired',H:'Ella is hungry'},'~T & ~H'],
 [1,'Either the store is closed or it’s out of milk.',{C:'The store is closed',M:'The store has milk'},'C ∨ ~M'],
 [2,'If it’s sunny and warm, we’ll go to the beach.',{S:'It’s sunny',W:'It’s warm',B:'We go to the beach'},'(S & W) ⊃ B'],
 [2,'We’ll go to the beach only if it’s sunny and warm.',{S:'It’s sunny',W:'It’s warm',B:'We go to the beach'},'B ⊃ (S & W)'],
 [2,'Neither the bakery nor the bank is open, but the pharmacy is.',{K:'The bakery is open',N:'The bank is open',P:'The pharmacy is open'},'(~K & ~N) & P'],
 [2,'If Mia doesn’t call, Jon will worry and won’t sleep.',{M:'Mia calls',J:'Jon worries',S:'Jon sleeps'},'~M ⊃ (J & ~S)'],
 [2,'The team wins only if both the goalie and the striker play well.',{W:'The team wins',G:'The goalie plays well',S:'The striker plays well'},'W ⊃ (G & S)'],
 [2,'Either Ava or Noah will drive, but not both.',{A:'Ava drives',N:'Noah drives'},'(A ∨ N) & ~(A & N)'],
 [2,'The concert goes ahead unless it storms or the singer is sick.',{C:'The concert goes ahead',T:'It storms',S:'The singer is sick'},'C ∨ (T ∨ S)'],
 [2,'If the oven is on, then the kitchen is warm and the window is fogged up.',{O:'The oven is on',K:'The kitchen is warm',F:'The window is fogged up'},'O ⊃ (K & F)'],
 [2,'You’ll get a refund provided that you have a receipt and the item is unused.',{R:'You get a refund',H:'You have a receipt',U:'The item is unused'},'(H & U) ⊃ R'],
 [2,'The movie is good if and only if it isn’t too long.',{G:'The movie is good',L:'The movie is too long'},'G ≡ ~L'],
 [2,'Dev and Rana didn’t both pass the test, but at least one of them did.',{D:'Dev passed the test',R:'Rana passed the test'},'~(D & R) & (D ∨ R)'],
 [2,'If the bus is late, then if Tara is waiting, she’ll be annoyed.',{B:'The bus is late',T:'Tara is waiting',A:'Tara is annoyed'},'B ⊃ (T ⊃ A)'],
 [2,'Kim plays piano only if she doesn’t play violin.',{P:'Kim plays piano',N:'Kim plays violin'},'P ⊃ ~N'],
 [2,'Unless the wifi comes back, Leo can’t finish his homework.',{W:'The wifi comes back',F:'Leo finishes his homework'},'W ∨ ~F'],
 [2,'The garden floods if it rains hard and the drain is blocked.',{F:'The garden floods',R:'It rains hard',D:'The drain is blocked'},'(R & D) ⊃ F'],
 [2,'The keys are either in the car or in the house, and they aren’t in the car.',{C:'The keys are in the car',H:'The keys are in the house'},'(C ∨ H) & ~C'],
 [2,'If Zoe wins, Max doesn’t, and if Max wins, Zoe doesn’t.',{Z:'Zoe wins',M:'Max wins'},'(Z ⊃ ~M) & (M ⊃ ~Z)'],
 [2,'The trip is on provided that neither the car breaks down nor the road closes.',{T:'The trip is on',C:'The car breaks down',R:'The road closes'},'(~C & ~R) ⊃ T'],
 [2,'Ivy studies if and only if she has a test, and she has a test.',{S:'Ivy studies',T:'Ivy has a test'},'(S ≡ T) & T'],
 [2,'If the milk is sour, then either it’s old or the fridge broke.',{S:'The milk is sour',O:'The milk is old',F:'The fridge broke'},'S ⊃ (O ∨ F)'],
 [2,'Dan will cook only if Eve buys groceries.',{D:'Dan cooks',E:'Eve buys groceries'},'D ⊃ E'],
 [2,'The dog barks whenever someone knocks.',{B:'The dog barks',K:'Someone knocks'},'K ⊃ B'],
 [3,'If the meeting runs late, then Ana misses her train only if she doesn’t leave early.',{M:'The meeting runs late',T:'Ana misses her train',L:'Ana leaves early'},'M ⊃ (T ⊃ ~L)'],
 [3,'Neither Raj nor Sita will come unless the party is on Saturday.',{R:'Raj comes',S:'Sita comes',P:'The party is on Saturday'},'(~R & ~S) ∨ P'],
 [3,'The team wins if and only if both the defense holds and the offense scores.',{W:'The team wins',D:'The defense holds',O:'The offense scores'},'W ≡ (D & O)'],
 [3,'If the printer and the copier don’t both work, the report will be late.',{P:'The printer works',C:'The copier works',L:'The report is late'},'~(P & C) ⊃ L'],
 [3,'Either Bea takes the job and moves, or she stays and keeps studying.',{J:'Bea takes the job',M:'Bea moves',S:'Bea stays',K:'Bea keeps studying'},'(J & M) ∨ (S & K)'],
 [3,'Traffic will be heavy only if the bridge is open and the ferry isn’t running.',{T:'Traffic is heavy',B:'The bridge is open',F:'The ferry is running'},'T ⊃ (B & ~F)'],
 [3,'If Carl studies, he passes; and if he doesn’t study, he fails unless the test is easy.',{S:'Carl studies',P:'Carl passes',E:'The test is easy'},'(S ⊃ P) & (~S ⊃ (~P ∨ E))'],
 [3,'It’s not the case that if the shop is open, it has bread.',{O:'The shop is open',B:'The shop has bread'},'~(O ⊃ B)'],
 [3,'If either the coach or the captain objects, the plan won’t go ahead unless the principal approves.',{C:'The coach objects',K:'The captain objects',G:'The plan goes ahead',P:'The principal approves'},'(C ∨ K) ⊃ (~G ∨ P)'],
 [3,'Nora will travel only if she saves enough and her boss approves, and she’ll save enough only if she skips the concert.',{T:'Nora travels',S:'Nora saves enough',B:'Nora’s boss approves',K:'Nora skips the concert'},'(T ⊃ (S & B)) & (S ⊃ K)'],
 [3,'Neither the heat nor the humidity bothers Eli, but the noise does if he’s tired.',{H:'The heat bothers Eli',U:'The humidity bothers Eli',N:'The noise bothers Eli',T:'Eli is tired'},'(~H & ~U) & (T ⊃ N)'],
 [3,'Either the store is open and has milk, or we’ll make pancakes without milk.',{O:'The store is open',M:'The store has milk',P:'We make pancakes without milk'},'(O & M) ∨ P'],
 [3,'If the river rises, then the road closes if and only if the bridge is down.',{R:'The river rises',C:'The road closes',B:'The bridge is down'},'R ⊃ (C ≡ B)'],
 [3,'Provided that the understudy is unavailable, the show is canceled if the lead actor is sick.',{C:'The show is canceled',L:'The lead actor is sick',U:'The understudy is available'},'~U ⊃ (L ⊃ C)'],
 [3,'It’s not true that Ben will go only if Ana goes.',{B:'Ben goes',A:'Ana goes'},'~(B ⊃ A)'],
 [3,'Jess will play tennis unless it rains, and if it rains, she’ll read.',{T:'Jess plays tennis',R:'It rains',D:'Jess reads'},'(T ∨ R) & (R ⊃ D)'],
 [3,'If neither the bus nor the train runs, Omar works from home unless his manager says no.',{B:'The bus runs',T:'The train runs',H:'Omar works from home',N:'Omar’s manager says no'},'(~B & ~T) ⊃ (H ∨ N)'],
 [3,'Paul and Quinn will both win only if neither of them gets injured.',{P:'Paul wins',Q:'Quinn wins',I:'Paul gets injured',J:'Quinn gets injured'},'(P & Q) ⊃ (~I & ~J)'],
 [3,'The cake is done or the toothpick comes out wet, but not both.',{C:'The cake is done',W:'The toothpick comes out wet'},'(C ∨ W) & ~(C & W)'],
 [3,'If the team wins, the fans celebrate, and if the team loses, the fans go home; and the team either wins or loses.',{W:'The team wins',C:'The fans celebrate',L:'The team loses',H:'The fans go home'},'((W ⊃ C) & (L ⊃ H)) & (W ∨ L)'],
 [3,'The lights stay on only if the generator works, and the generator works if and only if it has fuel.',{L:'The lights stay on',G:'The generator works',F:'The generator has fuel'},'(L ⊃ G) & (G ≡ F)'],
 [3,'Unless both the cat and the dog are fed, someone will be woken up early.',{C:'The cat is fed',D:'The dog is fed',W:'Someone is woken up early'},'(C & D) ∨ W'],
 [3,'Mira will apply to the program if and only if it’s affordable or it offers her a scholarship.',{A:'Mira applies to the program',F:'The program is affordable',S:'The program offers Mira a scholarship'},'A ≡ (F ∨ S)'],
].map(([lv,en,key,ans],i)=>({id:i, lv, en, key, ans}));

// Small changes to the model answer that match common mistakes.
function mutations(f){
  const out=[];
  const rec=(node, rebuild)=>{
    if(node.t==='cond'){ out.push({kind:'reverse', f:rebuild({t:'cond',l:node.r,r:node.l})}); out.push({kind:'cond2bicond', f:rebuild({t:'bicond',l:node.l,r:node.r})}); }
    if(node.t==='bicond'){ out.push({kind:'bicond2cond', f:rebuild({t:'cond',l:node.l,r:node.r})}); out.push({kind:'bicond2cond', f:rebuild({t:'cond',l:node.r,r:node.l})}); }
    if(node.t==='and') out.push({kind:'andor', f:rebuild({t:'or',l:node.l,r:node.r})});
    if(node.t==='or'){
      out.push({kind:'andor', f:rebuild({t:'and',l:node.l,r:node.r})});
      out.push({kind:'unless', f:rebuild({t:'cond',l:node.r,r:node.l})});
      out.push({kind:'unless', f:rebuild({t:'cond',l:node.r,r:{t:'not',a:node.l}})});
      out.push({kind:'unlessExcl', f:rebuild({t:'bicond',l:node.l,r:{t:'not',a:node.r}})});
    }
    if(node.t==='not'){
      out.push({kind:'dropneg', f:rebuild(node.a)});
      const a=node.a; if(a.t==='and'||a.t==='or') out.push({kind:'demorgan', f:rebuild({t:a.t,l:{t:'not',a:a.l},r:{t:'not',a:a.r}})});
      rec(node.a, n=>rebuild({t:'not',a:n}));
    } else if(node.t!=='atom'){ rec(node.l, n=>rebuild({t:node.t,l:n,r:node.r})); rec(node.r, n=>rebuild({t:node.t,l:node.l,r:n})); }
  };
  rec(f, n=>n);
  return out;
}
function mistakeMsg(kind, en){
  en=en.toLowerCase();
  switch(kind){
    case 'reverse':
      if(/only if/.test(en) && !/if and only if/.test(en)) return `You reversed the conditional. In “P only if Q,” the part after “only if” is a necessary condition, so it goes on the right: P ${SYM.cond} Q. “Only if” doesn’t introduce the antecedent, the way plain “if” does.`;
      if(/provided that|whenever|\bwhen\b|\bif\b/.test(en)) return `You reversed the conditional. The clause after “if” (or “provided that,” “when,” “whenever”) is the antecedent, so it goes on the left of ${SYM.cond}, even when it comes second in the English sentence.`;
      return 'The antecedent and consequent are swapped. Ask which part is the condition and which part follows from it.';
    case 'cond2bicond': return `You used ${SYM.bicond}, but the sentence only goes one way. ${SYM.cond} is enough; ${SYM.bicond} would also claim the reverse.`;
    case 'bicond2cond': return `That captures only one direction. “If and only if” says each side requires the other, so use ${SYM.bicond}.`;
    case 'andor':
      if(/neither/.test(en)) return `“Neither P nor Q” says both are false: ${SYM.not}P ${SYM.and} ${SYM.not}Q, or equivalently ${SYM.not}(P ${SYM.or} Q). Check your ${SYM.and} and ${SYM.or}.`;
      return `Check your ${SYM.and} and ${SYM.or}: one of them is swapped. “And” and “but” mean both; “or” means at least one.`;
    case 'demorgan':
      if(/neither/.test(en)) return `“Neither P nor Q” means ${SYM.not}P ${SYM.and} ${SYM.not}Q, or ${SYM.not}(P ${SYM.or} Q). Your answer only says at least one is false.`;
      if(/both/.test(en)) return `“Not both” leaves room for one of them to be true: ${SYM.not}(P ${SYM.and} Q). Your answer says neither is true.`;
      return `Careful with a negation in front of parentheses: it applies to the whole group. ${SYM.not}(P ${SYM.and} Q) isn’t ${SYM.not}P ${SYM.and} ${SYM.not}Q, and ${SYM.not}(P ${SYM.or} Q) isn’t ${SYM.not}P ${SYM.or} ${SYM.not}Q.`;
    case 'dropneg': return `You’re missing a negation (${SYM.not}) somewhere, or have one too many. Look for “not,” “n’t,” and “neither.”`;
    case 'unless': return `“P unless Q” means that if Q doesn’t happen, P does: P ${SYM.or} Q, or equivalently ${SYM.not}Q ${SYM.cond} P. Your answer reads “unless” the wrong way around.`;
    case 'unlessExcl': return `This app reads “unless” inclusively: “P unless Q” is P ${SYM.or} Q, which allows both to be true. Your answer rules that out.`;
  }
}
const SYM_TIPS = () => [
  [/if and only if/, `“P if and only if Q” → P ${SYM.bicond} Q.`],
  [/only if/, `“P only if Q” → P ${SYM.cond} Q. Q is necessary for P.`],
  [/unless/, `“P unless Q” → P ${SYM.or} Q (equivalently, ${SYM.not}Q ${SYM.cond} P).`],
  [/neither/, `“Neither P nor Q” → ${SYM.not}P ${SYM.and} ${SYM.not}Q.`],
  [/provided that/, `“P provided that Q” → Q ${SYM.cond} P.`],
  [/not both|n’t both|but not both/, `“Not both P and Q” → ${SYM.not}(P ${SYM.and} Q). An exclusive “or” is (P ${SYM.or} Q) ${SYM.and} ${SYM.not}(P ${SYM.and} Q).`],
  [/whenever|\bwhen\b/, `“P when Q” and “P whenever Q” → Q ${SYM.cond} P.`],
  [/\bbut\b/, `“But” works like “and” → ${SYM.and}.`],
];
function symTips(en){
  // "if and only if" shouldn't also trigger the "only if" tip.
  const lo=en.toLowerCase(), noIff=lo.replace(/if and only if/g,''), out=[];
  SYM_TIPS().forEach(([re,t])=>{ if(re.test(re.source==='only if'?noIff:lo)) out.push(t); });
  return out.slice(0,3);
}
function checkSym(item, src){
  const p=tryParse(src); if(p.err) return {err:p.err};
  const keyL=Object.keys(item.key), used=lettersOf(p.f), bad=used.filter(l=>!keyL.includes(l));
  if(bad.length) return {err:`${bad.join(', ')} ${bad.length>1?'aren’t':'isn’t'} in the symbolization key. Use ${keyL.join(', ')}.`};
  const model=parse(item.ans);
  if(equivalent(p.f, model)) return {ok:true, exact:eq(p.f,model), f:p.f};
  const m=mutations(model).find(x=>!equivalent(x.f,model) && equivalent(p.f,x.f));
  const missing=lettersOf(model).filter(l=>!used.includes(l));
  return {ok:false, f:p.f, mistake: m ? mistakeMsg(m.kind, item.en) : null, missing};
}
let symRecent=[];
function newSym(){
  const lv=getSetting('symLevel','1'), list=SYMS.filter(s=>lv==='mix'||s.lv===+lv);
  const fresh=list.filter(s=>!symRecent.includes(s.id)), it=pick(fresh.length?fresh:list);
  symRecent.push(it.id); if(symRecent.length>Math.min(15,list.length-1)) symRecent.shift();
  return {it, input:'', res:null, counted:false, focus:'sym-in'};
}
const symDefsGroups = () => [
  {items:[['Symbolization key','A list that assigns each sentence letter an English sentence. A good key uses simple sentences with no “not,” “and,” “or,” or “if” inside them.','P: Pat plays the drums. Q: Quinn sings.']]},
  {h:'English words and their connectives', items:[
    ['Not',`“not,” “it’s not the case that,” “-n’t” → ${SYM.not}`,`“Pat doesn’t play the drums” → ${SYM.not}P`],
    ['And',`“and,” “but,” “although,” “yet,” “also” → ${SYM.and}. Words like “but” add contrast, but the logic is the same.`,`“Pat plays, but Quinn doesn’t sing” → P ${SYM.and} ${SYM.not}Q`],
    ['Or',`“or,” “either…or” → ${SYM.or}. This is inclusive: at least one, possibly both. For “but not both,” add ${SYM.and} ${SYM.not}(P ${SYM.and} Q).`,`“Pat plays or Quinn sings” → P ${SYM.or} Q`],
    ['Neither…nor',`Both parts are false: ${SYM.not}P ${SYM.and} ${SYM.not}Q, or equivalently ${SYM.not}(P ${SYM.or} Q).`,`“Neither Pat nor Quinn performs” → ${SYM.not}P ${SYM.and} ${SYM.not}Q`],
    ['If…then',`“If P, Q,” “Q if P,” “Q when P,” “Q whenever P,” “Q provided that P” → P ${SYM.cond} Q. The clause after “if” is the antecedent, wherever it sits in the sentence.`,`“Quinn sings if Pat plays” → P ${SYM.cond} Q`],
    ['Only if',`“P only if Q” → P ${SYM.cond} Q. The clause after “only if” is a necessary condition, so it’s the consequent. This is the one students reverse most often.`,`“You can vote only if you’re registered” → V ${SYM.cond} R. Registering doesn’t guarantee you vote, but voting requires it.`],
    ['Provided that',`“P provided that Q” works like “P if Q” → Q ${SYM.cond} P.`,`“The picnic is on provided that it’s sunny” → S ${SYM.cond} N`],
    ['Unless',`“P unless Q” → P ${SYM.or} Q. If Q fails, P must hold. It’s equivalent to ${SYM.not}Q ${SYM.cond} P.`,`“Pat plays unless it rains” → P ${SYM.or} R`],
    ['If and only if',`“P if and only if Q,” “P just in case Q” → P ${SYM.bicond} Q.`,`“Quinn sings if and only if Pat plays” → Q ${SYM.bicond} P`],
  ]},
];
function symHub(){
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Symbolization</h2>
  <p class="muted">Translate English sentences into sentential logic.</p>
  ${keyDefs(symDefsGroups())}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-go="symq"><span>Symbolize a sentence<small>${SYMS.length} sentences at three levels. Any equivalent answer counts.${soFar('sym')}</small></span><span class="go">Practice</span></button></li>
  </ul>`;
}
function symView(){
  const e=App.ex, it=e.it, sc=score('sym');
  let fb='';
  if(e.res){
    if(e.res.err) fb=`<div class="fb bad"><strong>I can’t read that yet.</strong>${esc(e.res.err)}</div>`;
    else {
      const tips=symTips(it.en), model=show(parse(it.ans));
      const tipHtml = tips.length ? `<p class="muted" style="margin-top:8px">${tips.map(esc).join('<br>')}</p>` : '';
      if(e.res.ok) fb=`<div class="fb good"><strong>Correct.</strong>${e.res.exact?'That’s the model answer.':`Your answer is equivalent to the model answer, <span class="sent">${esc(model)}</span>.`}${tipHtml}</div>`;
      else {
        const parts=[];
        if(e.res.mistake) parts.push(esc(e.res.mistake));
        if(e.res.missing && e.res.missing.length) parts.push(`Your answer leaves out ${e.res.missing.join(', ')}.`);
        if(!parts.length) parts.push('Your answer isn’t equivalent to the sentence: some row of the truth table gives it a different value.');
        fb=`<div class="fb bad"><strong>Not quite.</strong>${parts.join(' ')}<p style="margin-top:8px">Model answer: <span class="sent"><b>${esc(model)}</b></span></p>${tipHtml}</div>`;
      }
    }
  }
  const answered = e.res && !e.res.err;
  return `<button class="back" data-go="sym">‹ Symbolization</button>
  <div class="ex-head"><h2>Symbolize</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs(symDefsGroups())}
  ${seg('symLevel','Level',[['1','1'],['2','2'],['3','3'],['mix','Mixed']], getSetting('symLevel','1'))}
  <p class="prop">${esc(it.en)}</p>
  <ul class="symkey">${Object.entries(it.key).map(([k,v])=>`<li><b>${k}</b>: ${esc(v)}</li>`).join('')}</ul>
  <section class="step"><h3>Your symbolization</h3>
    <input id="sym-in" class="sym-input" autocomplete="off" autocapitalize="characters" spellcheck="false" value="${esc(e.input)}" aria-label="Your symbolization" ${answered?'disabled':''}>
    ${answered?'':symKeys('sym-in')}${answered?'':typingTip()}
    <div class="actions"><button class="btn" data-act="check-sym" ${answered?'disabled':''}>Check</button></div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}
function symCheck(){
  const e=App.ex; if(e.res && !e.res.err) return;
  e.res=checkSym(e.it, e.input);
  if(!e.res.err && !e.counted){ e.counted=true; tally('sym', e.res.ok); }
  if(e.res.err) e.focus='sym-in';
  render();
}
function insClick(ev){
  const b=ev.target.closest('[data-ins]'); if(!b) return false;
  insertAt(b.dataset.target, b.dataset.ins, b.dataset.replace==='1'); return true;
}
registerView('sym',  {render: symHub});
registerView('symq', {init:newSym, render:symView, after:focusAfter,
  click:ev=>{ if(insClick(ev)) return; const a=ev.target.closest('[data-act="check-sym"]'); if(a) symCheck(); },
  input:ev=>{ if(ev.target.id==='sym-in') App.ex.input=ev.target.value; },
  keydown:ev=>{ if(ev.target.id==='sym-in' && ev.key==='Enter'){ ev.preventDefault(); symCheck(); } },
  onSetting:name=>{ if(name==='symLevel'){ symRecent=[]; App.ex=newSym(); } }});

// =====================================================================
// Derivations: Fitch-style proof checker
// =====================================================================
// A proof state holds lines {f, rule, cites, stack, asm, prem}. `stack` lists the line numbers of the
// assumptions whose subproofs contain the line. A line is in scope from line n when its stack is a prefix of n's.
const RULES = ['R','&I','&E','∨I','∨E','⊃I','⊃E','~I','~E','≡I','≡E'];
const SHAPES = { // n = a line, s = a subproof range
  'R':['n','R cites one line, like “R 2”.'],
  '&I':['nn','&I cites two lines, one for each conjunct, like “&I 1, 3”.'],
  '&E':['n','&E cites one line, the conjunction, like “&E 2”.'],
  '∨I':['n','∨I cites one line, the disjunct you have, like “∨I 4”.'],
  '∨E':['nss','∨E cites the disjunction and two subproofs, like “∨E 1, 2–4, 5–7”.'],
  '⊃I':['s','⊃I cites one subproof as a range, like “⊃I 3–6”.'],
  '⊃E':['nn','⊃E cites two lines, the conditional and its antecedent, like “⊃E 1, 3”.'],
  '~I':['s','~I cites one subproof as a range, like “~I 2–5”.'],
  '~E':['s','~E cites one subproof as a range, like “~E 2–5”.'],
  '≡I':['ss','≡I cites two subproofs, like “≡I 2–4, 5–7”.'],
  '≡E':['nn','≡E cites two lines, the biconditional and one side of it, like “≡E 1, 4”.'],
};
// Extra rules registered by later levels (the quantifier rules in Level 3).
// RULE_EXT[name] = {shape, msg, check(ctx) -> {} or {err}}
const RULE_EXT = {};
function registerRule(name, def){ RULE_EXT[name]=def; }
function normRule(s){
  let r=s.replace(/\s+/g,'');
  const q=r.match(/^(∀|\\A|A|U)([IiEe])$/), x=r.match(/^(∃|\\E|E)([IiEe])$/);
  if(q) return '∀'+q[2].toUpperCase();
  if(x) return '∃'+x[2].toUpperCase();
  r=r.replace(/<->|<=>|↔|⇔|=/g,'≡').replace(/->|=>|→|⇒|>/g,'⊃').replace(/∧|\^|•|·|⋅|\./g,'&').replace(/¬|-|!/g,'~').replace(/\|/g,'∨');
  r=r.replace(/^[vV](?=[IiEe]$)/,'∨').replace(/[ie]$/,c=>c.toUpperCase());
  if(/^(r|re|reit|reiteration)$/i.test(r)) r='R';
  return r;
}
function parseJust(src){
  const m=String(src).trim().match(/^([^\d]*?)\s*(\d[\d\s,\-–—]*)?$/);
  if(!m || !m[1]) return {err:'Start the justification with a rule name, like “&E 1” or “⊃I 3–5”.'};
  if(/^(a|assume|assumption)$/i.test(m[1].trim())) return {err:'To make an assumption, type the sentence and press “Assume.” That starts a new subproof.'};
  if(/^(p|pr|premise)$/i.test(m[1].trim())) return {err:'Premises are given at the top. Every new line needs a rule.'};
  const rule=normRule(m[1]);
  if(!RULES.includes(rule) && !RULE_EXT[rule]) return {err:`“${m[1].trim()}” isn’t one of the rules. Use one of: ${RULES.concat(Object.keys(RULE_EXT)).join(', ')}.`};
  const cites=[];
  if(m[2]) for(const part of m[2].split(/[,\s]+/).filter(Boolean)){
    const r=part.match(/^(\d+)(?:[-–—](\d+))?$/);
    if(!r) return {err:`I can’t read the citation “${part}”. Cite lines like “3” and subproofs like “3–5”.`};
    cites.push(r[2]!==undefined ? {a:+r[1], b:+r[2]} : {n:+r[1]});
  }
  return {rule, cites};
}
const citeStr = cs => cs.map(c=>c.n!==undefined?c.n:`${c.a}–${c.b}`).join(', ');
const isPrefix = (a,b) => a.length<=b.length && a.every((x,i)=>x===b[i]);
const NOT = a => ({t:'not', a});

// opts.ql: predicate logic (lines may use predicates and quantifiers, and must be sentences).
function newProof(premSrcs, opts){
  const ql=!!(opts&&opts.ql);
  return {ql, lines:premSrcs.map(s=>({f:parse(s,{ql}), rule:'P', cites:[], stack:[], asm:false, prem:true})), stack:[], hist:[]};
}
function freeVars(f, bound=[], out=new Set()){
  if(f.t==='atom') (f.args||[]).forEach(a=>{ if(VARS.includes(a) && !bound.includes(a)) out.add(a); });
  else if(f.t==='not') freeVars(f.a,bound,out);
  else if(f.t==='all'||f.t==='some') freeVars(f.a,bound.concat(f.v),out);
  else { freeVars(f.l,bound,out); freeVars(f.r,bound,out); }
  return out;
}
function parseLine(st, src){
  const p=tryParse(src,{ql:st.ql}); if(p.err) return p;
  const fv=[...freeVars(p.f)];
  if(fv.length) return {err:`${show(p.f)} has a free variable (${fv.join(', ')}), so it isn’t a sentence. Every line must be a sentence: use a constant instead, or add a quantifier.`};
  return p;
}
function snapshot(st){ st.hist.push({n:st.lines.length, stack:st.stack.slice()}); }
function undo(st){ const h=st.hist.pop(); if(!h) return false; st.lines.length=h.n; st.stack=h.stack; return true; }
function endSub(st){
  if(!st.stack.length) return {err:'You’re not inside a subproof, so there’s nothing to close.'};
  snapshot(st); st.stack=st.stack.slice(0,-1); return {ok:true};
}
function assume(st, src){
  const p=parseLine(st, src); if(p.err) return p;
  snapshot(st);
  const n=st.lines.length+1; st.stack=st.stack.concat(n);
  st.lines.push({f:p.f, rule:'A', cites:[], stack:st.stack.slice(), asm:true});
  return {ok:true};
}
function subEnd(st, start){ let e=start; for(let k=start+1;k<=st.lines.length;k++){ if(st.lines[k-1].stack.includes(start)) e=k; else break; } return e; }
function closedWhere(st, stack){ // the outermost closed subproof among `stack`, relative to the current scope
  let i=0; while(i<stack.length && stack[i]===st.stack[i]) i++;
  const start=stack[i]; return {start, end:subEnd(st,start)};
}
function addLine(st, src, just){
  const p=parseLine(st, src); if(p.err) return {err:p.err};
  const J=parseJust(just); if(J.err) return {err:J.err};
  const res=checkRule(st, p.f, J); if(res.err) return res;
  snapshot(st);
  st.lines.push({f:p.f, rule:J.rule, cites:J.cites, stack:st.stack.slice(), asm:false});
  return {ok:true};
}
function checkRule(st, f, J){
  const n=st.lines.length+1, L=k=>st.lines[k-1], pr=x=>show(x);
  const ext=RULE_EXT[J.rule], shape=ext?[ext.shape,ext.msg]:SHAPES[J.rule];
  const kinds=J.cites.map(c=>c.n!==undefined?'n':'s').join('');
  if(kinds!==shape[0]) return {err:shape[1]};
  function line(k){
    if(k>=n) return {err:`Line ${k} doesn’t exist yet. You can only cite earlier lines.`};
    if(k<1) return {err:`There’s no line ${k}.`};
    const l=L(k);
    if(!isPrefix(l.stack, st.stack)){
      const w=closedWhere(st, l.stack);
      return {err:`Line ${k} is inside the subproof on lines ${w.start}–${w.end}, which has already closed. Lines in a closed subproof are out of scope. You can cite the whole subproof (${w.start}–${w.end}) with a rule like ⊃I, but not its individual lines.`};
    }
    return {f:l.f};
  }
  function sub(c){
    const {a,b}=c;
    if(a<1 || a>=n) return {err:`Line ${a} ${a>=n?'doesn’t exist yet':'doesn’t exist'}.`};
    if(b<a) return {err:`A subproof range runs forward, like “${a}–${Math.max(a,b)+1}”.`};
    const la=L(a);
    if(!la.asm) return {err:`Line ${a} isn’t an assumption, so ${a}–${b} isn’t a subproof. A subproof range starts at the assumption that opens it.`};
    if(st.stack.includes(a)) return {err:`The subproof that starts at line ${a} is still open. Close it with “End subproof” first; then you can cite it as a whole.`};
    const parent=la.stack.slice(0,-1);
    if(!isPrefix(parent, st.stack)){ const w=closedWhere(st, parent); return {err:`Lines ${a}–${b} are inside the subproof on lines ${w.start}–${w.end}, which has already closed, so they’re out of scope.`}; }
    const end=subEnd(st,a);
    if(b!==end) return {err:`The subproof that starts at line ${a} ends at line ${end}, so cite it as ${a}–${end}.`};
    if(L(end).stack.length!==la.stack.length) return {err:`The subproof ${a}–${end} ends inside a smaller subproof nested within it, so it has no last line of its own. Bring the result out to the subproof’s own level first.`};
    const body=[]; for(let k=a;k<=end;k++) if(L(k).stack.length===la.stack.length) body.push(L(k).f);
    return {asm:la.f, last:L(end).f, body, a, b:end};
  }
  const got=[];
  for(const c of J.cites){ const r=c.n!==undefined?line(c.n):sub(c); if(r.err) return r; got.push(r); }
  const contradiction = body => body.some(x=>body.some(y=>y.t==='not' && eq(y.a,x)));
  // Sentences in premises and open assumptions (the undischarged assumptions at this line).
  const undischarged=()=>st.lines.filter(l=>l.prem).map(l=>l.f).concat(st.stack.map(k=>L(k).f));
  if(ext) return ext.check({st, f, got, J, pr, undischarged}) || {};
  const [g1,g2,g3]=got;
  switch(J.rule){
    case 'R':
      return eq(f,g1.f) ? {} : {err:`R repeats a line exactly. Line ${J.cites[0].n} is ${pr(g1.f)}, not ${pr(f)}.`};
    case '&I':
      if(f.t!=='and') return {err:`&I produces a conjunction, but ${pr(f)} isn’t one.`};
      if((eq(f.l,g1.f)&&eq(f.r,g2.f)) || (eq(f.l,g2.f)&&eq(f.r,g1.f))) return {};
      return {err:`&I joins the cited sentences. Lines ${J.cites[0].n} and ${J.cites[1].n} give ${pr(g1.f)} and ${pr(g2.f)}, so &I would give ${pr({t:'and',l:g1.f,r:g2.f})}.`};
    case '&E':
      if(g1.f.t!=='and') return {err:`&E needs a conjunction, but line ${J.cites[0].n} is ${pr(g1.f)}.`};
      return eq(f,g1.f.l)||eq(f,g1.f.r) ? {} : {err:`From ${pr(g1.f)}, &E gives either ${pr(g1.f.l)} or ${pr(g1.f.r)}.`};
    case '∨I':
      if(f.t!=='or') return {err:`∨I produces a disjunction, but ${pr(f)} isn’t one.`};
      return eq(f.l,g1.f)||eq(f.r,g1.f) ? {} : {err:`∨I adds a disjunct to the cited sentence, so one side of your disjunction must be ${pr(g1.f)}.`};
    case '∨E': {
      const D=g1.f;
      if(D.t!=='or') return {err:`∨E starts from a disjunction, but line ${J.cites[0].n} is ${pr(D)}.`};
      const ok=(eq(g2.asm,D.l)&&eq(g3.asm,D.r)) || (eq(g2.asm,D.r)&&eq(g3.asm,D.l));
      if(!ok) return {err:`For ∨E on ${pr(D)}, one subproof must assume ${pr(D.l)} and the other must assume ${pr(D.r)}. Yours assume ${pr(g2.asm)} and ${pr(g3.asm)}.`};
      if(!eq(g2.last,f)||!eq(g3.last,f)) return {err:`Both subproofs must end with the sentence you’re concluding, ${pr(f)}. They end with ${pr(g2.last)} and ${pr(g3.last)}.`};
      return {};
    }
    case '⊃I':
      if(f.t!=='cond') return {err:`⊃I produces a conditional, but ${pr(f)} isn’t one.`};
      if(!eq(f.l,g1.asm)) return {err:`With ⊃I, the antecedent must be the subproof’s assumption, ${pr(g1.asm)}. So you’d get ${pr({t:'cond',l:g1.asm,r:g1.last})}.`};
      if(!eq(f.r,g1.last)) return {err:`With ⊃I, the consequent must be the subproof’s last line, ${pr(g1.last)}. So you’d get ${pr({t:'cond',l:g1.asm,r:g1.last})}.`};
      return {};
    case '⊃E': {
      const pairs=[[g1,g2,0],[g2,g1,1]];
      const cands=pairs.filter(([c])=>c.f.t==='cond');
      if(!cands.length) return {err:'⊃E needs a conditional and its antecedent, but neither cited line is a conditional.'};
      for(const [c,o] of cands) if(eq(o.f,c.f.l)) return eq(f,c.f.r) ? {} : {err:`⊃E gives the consequent of ${pr(c.f)}, which is ${pr(c.f.r)}.`};
      const [c,o]=cands[0];
      if(eq(o.f,c.f.r)) return {err:`To use ${pr(c.f)} with ⊃E you need its antecedent, ${pr(c.f.l)}. The other line is the consequent, and reasoning from the consequent is the fallacy of affirming the consequent.`};
      return {err:`To use ${pr(c.f)} with ⊃E you need its antecedent, ${pr(c.f.l)}, but the other line is ${pr(o.f)}.`};
    }
    case '~I':
      if(!(f.t==='not' && eq(f.a,g1.asm))) return {err:`~I concludes the negation of the subproof’s assumption: ${pr(NOT(g1.asm))}.`};
      return contradiction(g1.body) ? {} : {err:`The subproof ${g1.a}–${g1.b} needs to contain some sentence and its negation at its own level, and it doesn’t yet. Use R to bring in a line from outside if you need it.`};
    case '~E':
      if(g1.asm.t!=='not') return {err:`~E needs a subproof that assumes a negation. This one assumes ${pr(g1.asm)}, so use ~I to conclude ${pr(NOT(g1.asm))} instead.`};
      if(!eq(f,g1.asm.a)) return {err:`~E concludes the sentence whose negation was assumed: ${pr(g1.asm.a)}.`};
      return contradiction(g1.body) ? {} : {err:`The subproof ${g1.a}–${g1.b} needs to contain some sentence and its negation at its own level, and it doesn’t yet. Use R to bring in a line from outside if you need it.`};
    case '≡I':
      if(f.t!=='bicond') return {err:`≡I produces a biconditional, but ${pr(f)} isn’t one.`};
      if((eq(g1.asm,f.l)&&eq(g1.last,f.r)&&eq(g2.asm,f.r)&&eq(g2.last,f.l)) || (eq(g2.asm,f.l)&&eq(g2.last,f.r)&&eq(g1.asm,f.r)&&eq(g1.last,f.l))) return {};
      return {err:`≡I needs one subproof that assumes ${pr(f.l)} and ends with ${pr(f.r)}, and another that assumes ${pr(f.r)} and ends with ${pr(f.l)}.`};
    case '≡E': {
      const pairs=[[g1,g2],[g2,g1]].filter(([b])=>b.f.t==='bicond');
      if(!pairs.length) return {err:'≡E needs a biconditional and one of its sides, but neither cited line is a biconditional.'};
      for(const [b,o] of pairs){
        if(eq(o.f,b.f.l)) return eq(f,b.f.r)?{}:{err:`From ${pr(b.f)} and ${pr(o.f)}, ≡E gives ${pr(b.f.r)}.`};
        if(eq(o.f,b.f.r)) return eq(f,b.f.l)?{}:{err:`From ${pr(b.f)} and ${pr(o.f)}, ≡E gives ${pr(b.f.l)}.`};
      }
      return {err:`To use ${pr(pairs[0][0].f)} with ≡E, the other line must be one of its sides, ${pr(pairs[0][0].f.l)} or ${pr(pairs[0][0].f.r)}.`};
    }
  }
}
function isComplete(st, concl){
  return st.stack.length===0 && st.lines.some(l=>!l.prem && l.stack.length===0 && eq(l.f,concl));
}
// Run a model proof written as "depth|sentence|justification" lines; "A" marks an assumption.
function runModel(prem, proof, opts){
  const st=newProof(prem, opts);
  for(const line of proof){
    const [d,s,j]=line.split('|').map(x=>x.trim()), depth=+d;
    if(j==='A'){ while(st.stack.length>depth-1) endSub(st); if(st.stack.length!==depth-1) return {err:`bad depth before “${s}”`, st}; const r=assume(st,s); if(r.err) return {err:r.err, st}; }
    else { while(st.stack.length>depth) endSub(st); if(st.stack.length!==depth) return {err:`bad depth at “${s}”`, st}; const r=addLine(st,s,j); if(r.err) return {err:`line ${st.lines.length+1} (${s}, ${j}): ${r.err}`, st}; }
  }
  return {st};
}

// ----- Exercises: [level, premises, conclusion, model proof] -----
const DERS = [
 [1,['A & B'],'A',['0|A|&E 1']],
 [1,['A','B'],'A & B',['0|A & B|&I 1, 2']],
 [1,['A ⊃ B','A'],'B',['0|B|⊃E 1, 2']],
 [1,['A'],'A ∨ B',['0|A ∨ B|∨I 1']],
 [1,['A & B'],'B & A',['0|B|&E 1','0|A|&E 1','0|B & A|&I 2, 3']],
 [1,['A ≡ B','A'],'B',['0|B|≡E 1, 2']],
 [1,['A ≡ B','B'],'A',['0|A|≡E 1, 2']],
 [1,['A ⊃ B','B ⊃ C','A'],'C',['0|B|⊃E 1, 3','0|C|⊃E 2, 4']],
 [1,['(A & B) ⊃ C','A','B'],'C',['0|A & B|&I 2, 3','0|C|⊃E 1, 4']],
 [1,['A & B'],'A ∨ C',['0|A|&E 1','0|A ∨ C|∨I 2']],
 [1,['A ⊃ (B & C)','A'],'C',['0|B & C|⊃E 1, 2','0|C|&E 3']],
 [1,['~A ⊃ B','~A'],'B ∨ C',['0|B|⊃E 1, 2','0|B ∨ C|∨I 3']],
 [1,['(A ∨ B) ⊃ C','A'],'C',['0|A ∨ B|∨I 2','0|C|⊃E 1, 3']],
 [1,['A ≡ B','B ≡ C','A'],'C',['0|B|≡E 1, 3','0|C|≡E 2, 4']],
 [2,['B'],'A ⊃ B',['1|A|A','1|B|R 1','0|A ⊃ B|⊃I 2–3']],
 [2,['A ⊃ B','B ⊃ C'],'A ⊃ C',['1|A|A','1|B|⊃E 1, 3','1|C|⊃E 2, 4','0|A ⊃ C|⊃I 3–5']],
 [2,['A ⊃ B','~B'],'~A',['1|A|A','1|B|⊃E 1, 3','1|~B|R 2','0|~A|~I 3–5']],
 [2,['A ∨ B'],'B ∨ A',['1|A|A','1|B ∨ A|∨I 2','1|B|A','1|B ∨ A|∨I 4','0|B ∨ A|∨E 1, 2–3, 4–5']],
 [2,['A & B'],'A ≡ B',['1|A|A','1|B|&E 1','1|B|A','1|A|&E 1','0|A ≡ B|≡I 2–3, 4–5']],
 [2,['A ∨ B','~A'],'B',['1|A|A','2|~B|A','2|A|R 3','2|~A|R 2','1|B|~E 4–6','1|B|A','1|B|R 8','0|B|∨E 1, 3–7, 8–9']],
 [2,['A ⊃ (B ⊃ C)'],'(A & B) ⊃ C',['1|A & B|A','1|A|&E 2','1|B|&E 2','1|B ⊃ C|⊃E 1, 3','1|C|⊃E 5, 4','0|(A & B) ⊃ C|⊃I 2–6']],
 [2,['(A & B) ⊃ C'],'A ⊃ (B ⊃ C)',['1|A|A','2|B|A','2|A & B|&I 2, 3','2|C|⊃E 1, 4','1|B ⊃ C|⊃I 3–5','0|A ⊃ (B ⊃ C)|⊃I 2–6']],
 [2,['A'],'~~A',['1|~A|A','1|A|R 1','0|~~A|~I 2–3']],
 [2,['~~A'],'A',['1|~A|A','1|~~A|R 1','0|A|~E 2–3']],
 [2,['A ⊃ B','A ⊃ C'],'A ⊃ (B & C)',['1|A|A','1|B|⊃E 1, 3','1|C|⊃E 2, 3','1|B & C|&I 4, 5','0|A ⊃ (B & C)|⊃I 3–6']],
 [2,['A ≡ B'],'B ≡ A',['1|B|A','1|A|≡E 1, 2','1|A|A','1|B|≡E 1, 4','0|B ≡ A|≡I 2–3, 4–5']],
 [2,['A ∨ B','A ⊃ C','B ⊃ C'],'C',['1|A|A','1|C|⊃E 2, 4','1|B|A','1|C|⊃E 3, 6','0|C|∨E 1, 4–5, 6–7']],
 [2,['~A'],'A ⊃ B',['1|A|A','2|~B|A','2|A|R 2','2|~A|R 1','1|B|~E 3–5','0|A ⊃ B|⊃I 2–6']],
 [2,['A'],'B ⊃ (A & B)',['1|B|A','1|A & B|&I 1, 2','0|B ⊃ (A & B)|⊃I 2–3']],
 [2,['(A ∨ B) ⊃ C'],'A ⊃ C',['1|A|A','1|A ∨ B|∨I 2','1|C|⊃E 1, 3','0|A ⊃ C|⊃I 2–4']],
 [2,[],'A ⊃ A',['1|A|A','1|A|R 1','0|A ⊃ A|⊃I 1–2']],
 [2,[],'~(A & ~A)',['1|A & ~A|A','1|A|&E 1','1|~A|&E 1','0|~(A & ~A)|~I 1–3']],
 [2,['A ≡ B','~A'],'~B',['1|B|A','1|A|≡E 1, 3','1|~A|R 2','0|~B|~I 3–5']],
 [3,['A ⊃ B'],'~B ⊃ ~A',['1|~B|A','2|A|A','2|B|⊃E 1, 3','2|~B|R 2','1|~A|~I 3–5','0|~B ⊃ ~A|⊃I 2–6']],
 [3,['~(A ∨ B)'],'~A',['1|A|A','1|A ∨ B|∨I 2','1|~(A ∨ B)|R 1','0|~A|~I 2–4']],
 [3,['~(A ∨ B)'],'~A & ~B',['1|A|A','1|A ∨ B|∨I 2','1|~(A ∨ B)|R 1','0|~A|~I 2–4','1|B|A','1|A ∨ B|∨I 6','1|~(A ∨ B)|R 1','0|~B|~I 6–8','0|~A & ~B|&I 5, 9']],
 [3,['~A & ~B'],'~(A ∨ B)',['1|A ∨ B|A','2|A|A','3|A ∨ B|A','3|A|R 3','3|~A|&E 1','2|~(A ∨ B)|~I 4–6','2|B|A','3|A ∨ B|A','3|B|R 8','3|~B|&E 1','2|~(A ∨ B)|~I 9–11','1|~(A ∨ B)|∨E 2, 3–7, 8–12','0|~(A ∨ B)|~I 2–13']],
 [3,['A ⊃ B','B ⊃ A'],'A ≡ B',['1|A|A','1|B|⊃E 1, 3','1|B|A','1|A|⊃E 2, 5','0|A ≡ B|≡I 3–4, 5–6']],
 [3,['A ∨ B','~B'],'A',['1|A|A','1|A|R 3','1|B|A','2|~A|A','2|B|R 5','2|~B|R 2','1|A|~E 6–8','0|A|∨E 1, 3–4, 5–9']],
 [3,['A ⊃ (B ⊃ C)'],'B ⊃ (A ⊃ C)',['1|B|A','2|A|A','2|B ⊃ C|⊃E 1, 3','2|B|R 2','2|C|⊃E 4, 5','1|A ⊃ C|⊃I 3–6','0|B ⊃ (A ⊃ C)|⊃I 2–7']],
 [3,['A & (B ∨ C)'],'(A & B) ∨ (A & C)',['0|A|&E 1','0|B ∨ C|&E 1','1|B|A','1|A & B|&I 2, 4','1|(A & B) ∨ (A & C)|∨I 5','1|C|A','1|A & C|&I 2, 7','1|(A & B) ∨ (A & C)|∨I 8','0|(A & B) ∨ (A & C)|∨E 3, 4–6, 7–9']],
 [3,['A ⊃ B'],'~A ∨ B',['1|~(~A ∨ B)|A','2|A|A','2|B|⊃E 1, 3','2|~A ∨ B|∨I 4','2|~(~A ∨ B)|R 2','1|~A|~I 3–6','1|~A ∨ B|∨I 7','0|~A ∨ B|~E 2–8']],
 [3,[],'A ∨ ~A',['1|~(A ∨ ~A)|A','2|A|A','2|A ∨ ~A|∨I 2','2|~(A ∨ ~A)|R 1','1|~A|~I 2–4','1|A ∨ ~A|∨I 5','0|A ∨ ~A|~E 1–6']],
 [3,['~A ∨ ~B'],'~(A & B)',['1|A & B|A','2|~A|A','3|A & B|A','3|A|&E 2','3|~A|R 3','2|~(A & B)|~I 4–6','2|~B|A','3|A & B|A','3|B|&E 2','3|~B|R 8','2|~(A & B)|~I 9–11','1|~(A & B)|∨E 1, 3–7, 8–12','0|~(A & B)|~I 2–13']],
 [3,['(A ⊃ B) & (C ⊃ D)','A ∨ C'],'B ∨ D',['0|A ⊃ B|&E 1','0|C ⊃ D|&E 1','1|A|A','1|B|⊃E 3, 5','1|B ∨ D|∨I 6','1|C|A','1|D|⊃E 4, 8','1|B ∨ D|∨I 9','0|B ∨ D|∨E 2, 5–7, 8–10']],
 [3,['A ⊃ (B & C)'],'(A ⊃ B) & (A ⊃ C)',['1|A|A','1|B & C|⊃E 1, 2','1|B|&E 3','0|A ⊃ B|⊃I 2–4','1|A|A','1|B & C|⊃E 1, 6','1|C|&E 7','0|A ⊃ C|⊃I 6–8','0|(A ⊃ B) & (A ⊃ C)|&I 5, 9']],
 [3,['~A ⊃ A'],'A',['1|~A|A','1|A|⊃E 1, 2','0|A|~E 2–3']],
 [3,['A ⊃ B','~A ⊃ B'],'B',['1|~B|A','2|A|A','2|B|⊃E 1, 4','2|~B|R 3','1|~A|~I 4–6','1|B|⊃E 2, 7','0|B|~E 3–8']],
].map(([lv,p,c,proof],i)=>({id:i, lv, p, c, proof}));

// ----- Hints: first a strategy for the current goal, then a concrete next step from a model proof -----
function hintFor(ex, tier){
  const d=ex.d, st=ex.st, M=runModel(d.p,d.proof,{ql:d.ql}).st, concl=parse(d.c,{ql:d.ql});
  const avail=f=>st.lines.some(l=>isPrefix(l.stack,st.stack)&&eq(l.f,f));
  const consumerOf=a=>{ const end=subEnd(M,a), depth=M.lines[a-1].stack.length; for(let k=end+1;k<=M.lines.length;k++) if(M.lines[k-1].stack.length<depth) return M.lines[k-1]; return null; };
  const purpose=(rule, cons)=>{
    if(rule==='⊃I') return ` That sets up ⊃I: derive ${show(cons.f.r)} inside, then close the subproof to get ${show(cons.f)}.`;
    if(rule==='~I'||rule==='~E') return ` Then aim for a contradiction inside (a sentence and its negation); ${rule} will give ${show(cons.f)}.`;
    if(rule==='∨E') return ` This is one case for ∨E: derive ${show(cons.f)} inside it.`;
    if(rule==='≡I') return ` This is one half of ≡I for ${show(cons.f)}.`;
    if(rule==='∃E') return ` This is the instance for ∃E. Its constant must be new; derive ${show(cons.f)} inside, then close the subproof.`;
    return '';
  };
  if(tier===1){
    if(st.stack.length){
      const asm=st.lines[st.stack[st.stack.length-1]-1].f;
      const mk=M.lines.findIndex(l=>l.asm&&eq(l.f,asm));
      if(mk>=0){
        const a=mk+1, cons=consumerOf(a), last=M.lines[subEnd(M,a)-1].f;
        if(cons && (cons.rule==='~I'||cons.rule==='~E')) return `You assumed ${show(asm)} to reach a contradiction. Look for a sentence you can derive here along with its negation. R brings in lines from outside the subproof.`;
        if(cons && cons.rule==='∨E') return `This subproof is one case of ∨E. In this case, aim for ${show(last)}, the same sentence the other case needs to reach.`;
        if(cons && cons.rule==='∃E') return `You’re reasoning from an instance, ${show(asm)}, for ∃E. Aim for ${show(last)}, which must not contain the new constant, then close the subproof.`;
        if(cons && cons.rule==='≡I') return `This subproof is half of ≡I. Aim for ${show(last)}, then close it.`;
        return `You’re assuming ${show(asm)}. Aim for ${show(last)} inside this subproof; then close it and use ⊃I.`;
      }
      return `You’re inside a subproof that assumes ${show(asm)}. Decide what it’s for: ⊃I needs its last line to be the consequent you want, and ~I or ~E need a contradiction inside it.`;
    }
    const G=concl, disj=st.lines.some(l=>l.stack.length===0&&l.f.t==='or');
    const extra = disj && G.t!=='or' ? ' One of your lines is a disjunction, so ∨E (reasoning by cases) may be the way in.' : '';
    if(G.t==='cond') return `Your goal, ${show(G)}, is a conditional. Assume its antecedent, ${show(G.l)}, derive the consequent, ${show(G.r)}, then close the subproof and use ⊃I.`;
    if(G.t==='and') return `Your goal is a conjunction. Derive ${show(G.l)} and ${show(G.r)} separately, then combine them with &I.`+extra;
    if(G.t==='bicond') return `Your goal is a biconditional. Use ≡I: one subproof that assumes ${show(G.l)} and reaches ${show(G.r)}, and another that assumes ${show(G.r)} and reaches ${show(G.l)}.`;
    if(G.t==='not') return `Your goal is a negation. Assume ${show(G.a)}, derive a contradiction (some sentence and its negation), then use ~I.`+extra;
    if(G.t==='all') return `Your goal is universal. Derive an instance of it using a constant that appears in no premise, no open assumption, and not in the goal itself; then ∀I generalizes it.`+extra;
    if(G.t==='some') return `Your goal is existential. Derive one instance of it, with any constant, then use ∃I.`+extra;
    if(st.lines.some(l=>l.stack.length===0&&l.f.t==='some')) return `One of your lines is existential. Use ∃E: assume an instance with a brand-new constant, derive ${show(G)} inside the subproof, then close it.`;
    if(G.t==='or') return `Your goal is a disjunction. If you can get ${show(G.l)} or ${show(G.r)} on its own, finish with ∨I. If one of your lines is a disjunction, try ∨E instead. If neither works, assume ${show(NOT(G))} and aim for a contradiction (~E).`;
    return `Look for ${show(G)} inside what you have: break up conjunctions with &E, use conditionals with ⊃E and biconditionals with ≡E.${extra} As a last resort, assume ${show(NOT(G))} and aim for a contradiction (~E).`;
  }
  const subs=M.lines.map((l,i)=>l.asm?i+1:0).filter(Boolean);
  const done=a=>{ const c=consumerOf(a); return c && avail(c.f); };
  for(let k=1;k<=M.lines.length;k++){
    const ml=M.lines[k-1]; if(ml.prem) continue;
    if(ml.stack.some(a=>subs.includes(a)&&done(a))) continue;
    if(ml.asm){
      if(st.stack.some(a=>eq(st.lines[a-1].f,ml.f))) continue;
      const cons=consumerOf(k);
      const close = st.stack.length>ml.stack.length-1 ? 'First close the current subproof (End subproof). Then press' : 'Press';
      return `${close} “Assume” with ${show(ml.f)}.${cons?purpose(cons.rule,cons):''}`;
    }
    if(avail(ml.f)) continue;
    const close = st.stack.length>ml.stack.length ? 'First close the current subproof (End subproof). Then write' : 'Next, write';
    const from = ml.cites.map(c=>c.n!==undefined?show(M.lines[c.n-1].f):`the subproof that assumes ${show(M.lines[c.a-1].f)}`);
    return `${close} ${show(ml.f)} using ${ml.rule}${from.length?` (from ${from.join(' and ')})`:''}.`;
  }
  return `You have what you need. Write ${show(concl)} at the outermost level (close any open subproofs first).`;
}

// ----- Key definitions -----
const DD = {
  deriv:['Derivation','A numbered list of sentences that starts from the premises. Each later line is either an assumption or follows from earlier lines by a rule, and the last line is the conclusion.','From line 1, A & B, line 2 can be “A &E 1.”'],
  asm:['Assumption','A sentence you suppose for the sake of argument. Making an assumption opens a new subproof.','To show A ⊃ C, assume A and see whether C follows.'],
  sub:['Subproof','The lines that depend on an assumption. They’re indented with their own vertical line, and the assumption is underlined. Closing the subproof steps back out to the outer line.',''],
  scope:['Scope','A line is in scope (available to cite) only if it isn’t inside a subproof that has already closed. After a subproof closes, you can cite it as a whole range, like 3–6, but not its individual lines.','If lines 3–6 form a closed subproof, line 8 can’t cite line 4, but “⊃I 3–6” is fine.'],
};
const RULE_DEFS = [
  ['R (Reiteration)','Repeat a line that’s in scope. This is how you bring an outside line into a subproof.','Line 1 is A. Inside a subproof, “A R 1.”'],
  ['&I (conjunction introduction)','From P and Q, conclude P & Q.','Line 1: A. Line 2: B. Then “A & B &I 1, 2.”'],
  ['&E (conjunction elimination)','From P & Q, conclude P, or conclude Q.','Line 4: C & D. Then “D &E 4.”'],
  ['∨I (disjunction introduction)','From P, conclude P ∨ Q or Q ∨ P, for any sentence Q.','Line 2: A. Then “A ∨ Z ∨I 2.”'],
  ['∨E (disjunction elimination)','From P ∨ Q, a subproof that assumes P and reaches R, and a subproof that assumes Q and reaches R, conclude R. You reason by cases: either way, R.','“C ∨E 1, 2–4, 5–7.”'],
  ['⊃I (conditional introduction)','If a subproof that assumes P ends with Q, close it and conclude P ⊃ Q.','Lines 3–6 assume A and end with C. Then “A ⊃ C ⊃I 3–6.”'],
  ['⊃E (conditional elimination)','From P ⊃ Q and P, conclude Q.','Line 1: A ⊃ B. Line 2: A. Then “B ⊃E 1, 2.”'],
  ['~I (negation introduction)','If a subproof that assumes P contains some sentence and its negation, close it and conclude ~P. The assumption led to a contradiction, so it must be false.','Lines 2–5 assume A and contain both B and ~B. Then “~A ~I 2–5.”'],
  ['~E (negation elimination)','If a subproof that assumes ~P contains some sentence and its negation, close it and conclude P.','Lines 2–5 assume ~A and contain both B and ~B. Then “A ~E 2–5.”'],
  ['≡I (biconditional introduction)','From a subproof that assumes P and reaches Q, and a subproof that assumes Q and reaches P, conclude P ≡ Q.','“A ≡ B ≡I 2–3, 4–5.”'],
  ['≡E (biconditional elimination)','From P ≡ Q and either side, conclude the other side.','Line 1: A ≡ B. Line 3: B. Then “A ≡E 1, 3.”'],
];
const symItems = items => items.map(it=>it.map(x=>sym(x)));
const derDefs = () => keyDefs([{items:symItems([DD.deriv,DD.asm,DD.sub,DD.scope])},{h:'Rules',items:symItems(RULE_DEFS)},
  {h:'Entering a proof here',items:symItems([['One line at a time','Type the sentence and its justification (for example, “⊃E 1, 3”) and press “Add line.” To start a subproof, type the assumption and press “Assume.” To close the current subproof, press “End subproof”; your next line goes one level out. Cite subproofs as ranges like 3–6.','']])}]);

// ----- Views: a derivation module (reused by Level 3 with the quantifier rules) -----
// cfg: {key, title, back, backLabel, exercises, levelNames, defs, intro, ql}
function makeDerivationModule(cfg){
  const K=cfg.key, EXS=cfg.exercises, doneKey=K+'Done';
  const done = () => progress[doneKey] || (progress[doneKey]=[]);
  const P = s => parse(s,{ql:cfg.ql});
  let idx=0;
  function hub(){
    const list=lv=>`<h3 class="section-title">${cfg.levelNames[lv]}</h3><ul class="der-list">${EXS.filter(d=>d.lv===lv).map(d=>{
      const ok=done().includes(d.id);
      return `<li><button class="${ok?'done':''}" data-der="${d.id}"><small>#${d.id+1}${ok?' · done':''}</small>${esc(d.p.map(s=>show(P(s))).join(', '))} ⊢ ${esc(show(P(d.c)))}</button></li>`; }).join('')}</ul>`;
    return `<button class="back" data-go="${cfg.back}">‹ ${cfg.backLabel}</button>
    <h2>${cfg.title}</h2>
    <p class="muted">${cfg.intro} ${done().length} of ${EXS.length} exercises done.</p>
    ${cfg.defs()}
    ${Object.keys(cfg.levelNames).map(lv=>list(+lv)).join('')}`;
  }
  function init(){ const d=EXS[idx]; return {d, st:newProof(d.p,{ql:cfg.ql}), sent:'', just:'', msg:null, hint:null, hints:0, done:false, focus:null}; }
  function view(){
    const e=App.ex, d=e.d, concl=P(d.c);
    const rules=RULES.concat(cfg.ql?Object.keys(RULE_EXT):[]);
    const ruleKeys=`<div class="keys rules" role="group" aria-label="Insert a rule">${rules.map(r=>`<button type="button" data-ins="${esc(sym(r))} " data-target="der-j" data-replace="1">${esc(sym(r))}</button>`).join('')}</div>`;
    const msg = e.msg ? `<div class="fb ${e.msg.ok?'good':'bad'}">${e.msg.ok?'':'<strong>That line doesn’t check out.</strong>'}${esc(sym(e.msg.text))}</div>` : '';
    const prev = d.id>0 ? `<button class="btn ghost" data-der="${d.id-1}">‹ Previous</button>` : '<span></span>';
    const next = d.id<EXS.length-1 ? `<button class="btn" data-der="${d.id+1}">Next exercise ›</button>` : '';
    const input = e.done ? `${confetti()}<div class="fb good"><strong>Proof complete!</strong>Every line checks out, and ${esc(show(concl))} is on the outermost level.</div>` : `
      <label class="field-label" for="der-s">Sentence</label>
      <input id="der-s" class="sym-input" autocomplete="off" autocapitalize="off" spellcheck="false" value="${esc(e.sent)}">
      ${symKeys('der-s', cfg.ql)}
      <label class="field-label" for="der-j">Justification</label>
      <input id="der-j" class="sym-input" autocomplete="off" spellcheck="false" value="${esc(e.just)}" placeholder="for example, ${esc(sym('⊃E 1, 3'))}">
      ${ruleKeys}
      <div class="actions">
        <button class="btn" data-act="der-add">Add line</button>
        <button class="btn ghost" data-act="der-asm">Assume</button>
        <button class="btn ghost" data-act="der-end" ${e.st.stack.length?'':'disabled'}>End subproof</button>
        <button class="btn ghost" data-act="der-undo" ${e.st.hist.length?'':'disabled'}>Undo</button>
        <button class="btn ghost" data-act="der-hint">${e.hints?'Another hint':'Hint'}</button>
      </div>${msg}${e.hint?`<div class="hint-box"><b>Hint:</b> ${esc(sym(e.hint))}</div>`:''}`;
    return `<button class="back" data-go="${K}">‹ ${cfg.title}</button>
    <div class="ex-head"><h2>Exercise ${d.id+1}</h2><span class="score">Level ${d.lv}</span></div>
    ${cfg.defs()}
    <p class="args">${d.p.length?`From ${d.p.map(s=>esc(show(P(s)))).join(', ')}, derive`:'With no premises, derive'} <b>${esc(show(concl))}</b>.</p>
    ${renderProof(e.st, e.done)}
    <section class="step" style="margin-top:12px">${input}</section>
    <div class="next" style="justify-content:space-between">${prev}${next}</div>`;
  }
  function act(a){
    const e=App.ex, d=e.d; let r;
    e.hint=null;
    if(a==='der-add'){ r=addLine(e.st, e.sent, e.just); if(!r.err){ e.msg={ok:true, text:`Line ${e.st.lines.length} checks out.`}; e.sent=''; e.just=''; } e.focus='der-s'; }
    if(a==='der-asm'){ r=assume(e.st, e.sent); if(!r.err){ e.msg={ok:true, text:`Line ${e.st.lines.length} opens a new subproof.`}; e.sent=''; e.just=''; } e.focus='der-s'; }
    if(a==='der-end'){ r=endSub(e.st); if(!r.err) e.msg=null; e.focus='der-s'; }
    if(a==='der-undo'){ undo(e.st); e.msg=null; }
    if(a==='der-hint'){ e.hints++; e.hint=hintFor(e, e.hints); }
    if(r && r.err) e.msg={ok:false, text:r.err};
    if(!e.done && isComplete(e.st, P(d.c))){ e.done=true; e.msg=null; if(!done().includes(d.id)){ done().push(d.id); save(); } }
    render();
  }
  function click(ev){
    const pickD=ev.target.closest('[data-der]');
    if(pickD){ idx=+pickD.dataset.der; go(K+'q'); return; }
    if(insClick(ev)) return;
    const a=ev.target.closest('[data-act]'); if(a && a.dataset.act.startsWith('der-')) act(a.dataset.act);
  }
  registerView(K, {render: hub, click});
  registerView(K+'q', {init, render: view, click, after: focusAfter,
    input: ev=>{ if(ev.target.id==='der-s') App.ex.sent=ev.target.value; if(ev.target.id==='der-j') App.ex.just=ev.target.value; },
    keydown: ev=>{ if(ev.key!=='Enter') return;
      if(ev.target.id==='der-s'){ ev.preventDefault(); const j=document.getElementById('der-j'); if(j) j.focus(); }
      if(ev.target.id==='der-j'){ ev.preventDefault(); act('der-add'); } }});
}
function renderProof(st, done){
  const nPrem=st.lines.filter(l=>l.prem).length;
  const bars=(depth, openAt)=>Array.from({length:depth+1},(_,j)=>`<span class="bar${j===openAt?' open':''}"></span>`).join('');
  const rows=st.lines.map((l,i)=>{
    const k=i+1, d=l.stack.length;
    const just=l.prem?'P':l.asm?'A':`${sym(l.rule)} ${citeStr(l.cites)}`;
    const cls=['pl']; if(l.asm) cls.push('asm'); if(l.prem&&k===nPrem) cls.push('lastprem');
    return `<div class="${cls.join(' ')}"><span class="ln">${k}</span>${bars(d, l.asm?d:-1)}<span class="body"><span class="s">${esc(show(l.f))}</span><span class="j">${esc(just)}</span></span></div>`;
  }).join('');
  const ghost = done ? '' : `<div class="pl ghost"><span class="ln">${st.lines.length+1}</span>${bars(st.stack.length,-1)}<span class="body"><span class="s">next line ${st.stack.length?`(inside ${st.stack.length===1?'a subproof':st.stack.length+' subproofs'})`:''}</span></span></div>`;
  return `<div class="proof" aria-label="Proof so far">${rows}${ghost}</div>`;
}
makeDerivationModule({key:'der', title:'Derivations', back:'home', backLabel:'All levels', exercises:DERS, defs:derDefs, ql:false,
  intro:'Fitch-style natural deduction. The checker verifies each line as you enter it.',
  levelNames:{1:'Level 1 · Basic rules',2:'Level 2 · Subproofs',3:'Level 3 · Strategy'}});

// Building blocks shared with Levels 3 and 4.
Shared.logic = {SYM, BINARY, VARS, parse, tryParse, show, showP, eq, tokensOf, lettersOf, value, rowsFor, freeVars, genSentence, randLetters, symKeys, typingTip, insertAt, insClick, focusAfter, ParseError};
Shared.derivations = {makeDerivationModule, registerRule, renderProof, symItems, RULE_DEFS, DD};

// Exposed for tests/.
Engines.sentential = {SYMBOLS, parse, tryParse, show, showP, eq, value, lettersOf, rowsFor, classify, equivalent, consistent, validArg,
  tokensOf, tableModel, genSentence, genClassified, genTest, testAnswer, instantiate, connCount, LV};
Engines.symbolization = {SYMS, checkSym, mutations, symTips};
Engines.derivations = {DERS, RULES, newProof, addLine, assume, endSub, undo, isComplete, runModel, parseJust, hintFor, freeVars};
})();
