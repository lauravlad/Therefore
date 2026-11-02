// Therefore — Level 4: Beyond two values (three-valued and fuzzy logic).
// Kleene's strong logic (K3), Łukasiewicz's three-valued logic (Ł3), and fuzzy logic with
// values in [0, 1] (~ = 1 − x, & = min, ∨ = max, ⊃ = Łukasiewicz implication).
// Content is original; definitions are based on the Open Logic Project (CC BY 4.0).
(function(){
'use strict';
const L = Shared.logic, DV = Shared.derivations, SYM = L.SYM;
const P = s => L.parse(s);
const show = L.show, showP = L.showP;

// =====================================================================
// Semantics
// =====================================================================
// Values are numbers: 1 = T, 0.5 = U, 0 = F (and anything in between for fuzzy logic).
const r3 = x => Math.round(x*1000)/1000;
const SYSTEMS = {
  K3:{short:'K3', name:'Kleene’s strong logic (K3)', cond:(a,b)=>Math.max(1-a,b), bicond:(a,b)=>Math.min(Math.max(1-a,b),Math.max(1-b,a))},
  L3:{short:'Ł3', name:'Łukasiewicz’s three-valued logic (Ł3)', cond:(a,b)=>Math.min(1,1-a+b), bicond:(a,b)=>1-Math.abs(a-b)},
};
SYSTEMS.fuzzy = {short:'fuzzy', name:'Fuzzy logic', cond:SYSTEMS.L3.cond, bicond:SYSTEMS.L3.bicond};
function mv(f, row, sys){
  const S=SYSTEMS[sys];
  switch(f.t){
    case 'atom': return row[f.n];
    case 'not': return r3(1-mv(f.a,row,sys));
    case 'and': return Math.min(mv(f.l,row,sys), mv(f.r,row,sys));
    case 'or': return Math.max(mv(f.l,row,sys), mv(f.r,row,sys));
    case 'cond': return r3(S.cond(mv(f.l,row,sys), mv(f.r,row,sys)));
    case 'bicond': return r3(S.bicond(mv(f.l,row,sys), mv(f.r,row,sys)));
  }
}
const V3 = [1, 0.5, 0];
const NAME3 = v => v===1?'T':v===0?'F':v===0.5?'U':String(v);
// Rows in T, U, F order; the first letter changes slowest.
function rows3(letters){
  const n=letters.length, rows=[];
  for(let i=0;i<Math.pow(3,n);i++){ const row={}; let r=i; for(let j=n-1;j>=0;j--){ row[letters[j]]=V3[r%3]; r=(r/3)|0; } rows.push(row); }
  return rows;
}
// Fuzzy rows: every letter takes the values 0, 0.05, …, 1.
function fuzzyRows(letters, steps=20){
  let rows=[{}];
  letters.forEach(Lt=>{ const next=[]; rows.forEach(row=>{ for(let k=0;k<=steps;k++) next.push(Object.assign({},row,{[Lt]:r3(k/steps)})); }); rows=next; });
  return rows;
}
// A tautology in a many-valued logic always takes a designated value. Here only T (1) is designated.
function tautIn(f, sys){
  const letters=L.lettersOf(f), rows = sys==='fuzzy' ? fuzzyRows(letters) : rows3(letters);
  const bad=rows.find(row=>mv(f,row,sys)<1);
  return {holds:!bad, counter:bad||null, value:bad?mv(f,bad,sys):1};
}
const fmt = v => { const s=(Math.round(v*100)/100).toFixed(2).replace(/0$/,'').replace(/\.0$/,''); return s; };
const rowText = (row, three) => Object.keys(row).map(k=>`${k} = ${three?NAME3(row[k]):fmt(row[k])}`).join(', ');

// How each connective is computed, in words.
function ruleText(t, sys){
  if(t==='not') return `${SYM.not} gives 1 minus the value: T and F swap, and U stays U.`;
  if(t==='and') return `${SYM.and} takes the lower of the two values.`;
  if(t==='or') return `${SYM.or} takes the higher of the two values.`;
  if(t==='cond') return sys==='K3' ? `In K3, P ${SYM.cond} Q works like ${SYM.not}P ${SYM.or} Q: the higher of 1 − P and Q.` : `In ${SYSTEMS[sys].short}, P ${SYM.cond} Q is the smaller of 1 and 1 − P + Q, so it’s T whenever P is no truer than Q.`;
  if(t==='bicond') return sys==='K3' ? `In K3, P ${SYM.bicond} Q is (P ${SYM.cond} Q) ${SYM.and} (Q ${SYM.cond} P).` : `In ${SYSTEMS[sys].short}, P ${SYM.bicond} Q is 1 minus the difference between the values, so it’s T when they match.`;
}

// =====================================================================
// Content
// =====================================================================
const SHOWCASE = ['P ∨ ~P','P ⊃ P','~(P & ~P)','P ≡ P','(P & Q) ⊃ P','P ⊃ (Q ⊃ P)','(P ⊃ Q) ∨ (Q ⊃ P)','~(P ∨ Q) ≡ (~P & ~Q)','P ⊃ Q','~P ∨ Q','(P ≡ Q) ⊃ (P ⊃ Q)','~P ⊃ (P ⊃ Q)','(P ∨ Q) & ~P','P & (Q ∨ ~Q)'];
const TAUTS = ['P ∨ ~P','~(P & ~P)','P ⊃ P','P ≡ P','~~P ≡ P','(P & Q) ⊃ P','P ⊃ (P ∨ Q)','P ⊃ (Q ⊃ P)','(P ⊃ Q) ≡ (~Q ⊃ ~P)','((P ⊃ Q) & P) ⊃ Q','(P ⊃ Q) ∨ (Q ⊃ P)','~(P & Q) ≡ (~P ∨ ~Q)','(P & Q) ≡ (Q & P)','~P ⊃ (P ⊃ Q)','(P ⊃ (Q ⊃ R)) ⊃ ((P ⊃ Q) ⊃ (P ⊃ R))'];

const MD = () => [
  {items:[
    ['Three-valued logic','A logic in which a sentence can take a third value besides true and false. Here the third value is U, which you can read as “unknown” or “half true.” In calculations, T = 1, U = ½, and F = 0.','“The 2050 election will be close” might get U today.'],
    ['Designated values','The values that count as “true enough.” A sentence is a tautology when it always takes a designated value, and an argument is valid when designated premises guarantee a designated conclusion. In K3 and Ł3, only T is designated. (Other logics, such as LP, designate both T and U.)',''],
    ['Kleene’s strong logic (K3)','~ swaps T and F and leaves U alone. & takes the lower value and ∨ the higher. P ⊃ Q works like ~P ∨ Q. A compound is U whenever the U parts could tip the answer either way.','T ∨ U = T, T & U = U, U ⊃ U = U.'],
    ['Łukasiewicz’s three-valued logic (Ł3)','The same ~, &, and ∨ as K3, but a different conditional: P ⊃ Q is the smaller of 1 and 1 − P + Q. So P ⊃ Q is T whenever P is no truer than Q, including U ⊃ U. P ≡ Q is 1 minus the difference between the values.','U ⊃ U = T, T ⊃ U = U, U ⊃ F = U.'],
    ['Fuzzy logic','Truth comes in degrees, from 0 (completely false) to 1 (completely true). ~P = 1 − P, P & Q = the lower value, P ∨ Q = the higher, and P ⊃ Q = the smaller of 1 and 1 − P + Q (Łukasiewicz implication).','If “the soup is hot” has degree 0.7 and “the soup is salty” 0.4, then their conjunction has degree 0.4, and “hot ⊃ salty” has degree 0.7.'],
  ]},
];
function charTable3(sys){
  const conns=[['~P','not'],['P & Q','and'],['P ∨ Q','or'],['P ⊃ Q','cond'],['P ≡ Q','bicond']];
  const rows=rows3(['P','Q']);
  const head=`<tr><th>P</th><th class="sep">Q</th>${conns.map(([s])=>`<th>${esc(show(P(s)))}</th>`).join('')}</tr>`;
  const body=rows.map(row=>`<tr><td>${NAME3(row.P)}</td><td class="sep">${NAME3(row.Q)}</td>${conns.map(([s])=>`<td>${NAME3(mv(P(s),row,sys))}</td>`).join('')}</tr>`).join('');
  return `<p style="margin:8px 0 4px"><b>${SYSTEMS[sys].short}</b></p><div class="tt-wrap" style="margin:0"><table class="tt"><thead>${head}</thead><tbody>${body}</tbody></table></div>`;
}
const mvDefs = () => keyDefs([{items:DV.symItems(MD()[0].items)}, {h:'Truth tables (rows in T, U, F order)', items:[[sym('K3 and Ł3 differ only in ⊃ and ≡'), charTable3('K3')+charTable3('L3')]]}]);

registerLevel({num:4, title:'Beyond two values', topics:[
  {title:'Multi-valued and fuzzy logic', sub:'Kleene, Łukasiewicz, and fuzzy truth values', go:'mv'},
]});
const soFar = k => { const s=score(k); return s.done?` ${s.right} of ${s.done} correct so far.`:''; };
const sysNow = () => getSetting('mvSys','K3');
const sysSeg = () => seg('mvSys','System',[['K3','Kleene (K3)'],['L3','Łukasiewicz (Ł3)']], sysNow());
function mvHub(){
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Multi-valued and fuzzy logic</h2>
  <p class="muted">What happens when sentences can be more than just true or false?</p>
  ${mvDefs()}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-go="mvtab"><span>Three-valued truth tables<small>Fill in a table in K3 or Ł3, then decide whether the sentence is a tautology.${soFar('mvtab')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="fuzzy"><span>Fuzzy truth values<small>Compute a sentence’s degree of truth.${soFar('fuzzy')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="mvtaut"><span>Which tautologies survive?<small>Check classical tautologies in K3, Ł3, and fuzzy logic.${soFar('mvtaut')}</small></span><span class="go">Practice</span></button></li>
  </ul>`;
}

// ----- Three-valued tables -----
function newTab(){
  const f = Math.random()<.6 ? P(pick(SHOWCASE)) : L.genSentence(1);
  const tk=L.tokensOf(f), letters=L.lettersOf(f);
  return {f, tk, letters, rows:rows3(letters), cols:tk.map((t,i)=>t.k==='conn'?i:-1).filter(i=>i>=0), main:tk.findIndex(t=>t.k==='conn'&&t.node===f), vals:{}, checked:false, ans:null, sys:sysNow()};
}
const cycle3 = v => v==null||v==='' ? 'T' : v==='T' ? 'U' : v==='U' ? 'F' : '';
function cellWhy3(e, r, c){
  const node=e.tk[c].node, row=e.rows[r], v=x=>NAME3(mv(x,row,e.sys));
  const parts = node.t==='not' ? `${esc(showP(node.a))} is ${v(node.a)}` : `${esc(showP(node.l))} is ${v(node.l)} and ${esc(showP(node.r))} is ${v(node.r)}`;
  return `In row ${r+1}, ${parts}, so ${esc(showP(node))} is ${v(node)}. ${esc(ruleText(node.t,e.sys))}`;
}
function tabView(){
  const e=App.ex, key=(r,c)=>r+','+c, truth=(r,c)=>NAME3(mv(e.tk[c].node,e.rows[r],e.sys));
  const wrong=[]; if(e.checked) e.rows.forEach((_,r)=>e.cols.forEach(c=>{ if(e.vals[key(r,c)]!==truth(r,c)) wrong.push([r,c]); }));
  const head=`<tr><th class="rn"></th>${e.letters.map((Lt,i)=>`<th class="${i===e.letters.length-1?'sep':''}">${Lt}</th>`).join('')}${e.tk.map((t,c)=>`<th class="${c===e.main?'main':''}">${esc(t.s)}</th>`).join('')}</tr>`;
  const body=e.rows.map((row,r)=>`<tr><td class="rn">${r+1}</td>${e.letters.map((Lt,i)=>`<td class="${i===e.letters.length-1?'sep':''}">${NAME3(row[Lt])}</td>`).join('')}${e.tk.map((t,c)=>{
    const cls=c===e.main?' class="main"':'';
    if(t.k==='atom') return `<td${cls}><span class="ro atomv">${NAME3(row[t.s])}</span></td>`;
    if(t.k==='paren') return '<td></td>';
    const v=e.vals[key(r,c)]||''; let b='cell'; if(e.checked) b+= v===truth(r,c)?' right':' wrong';
    return `<td${cls}><button class="${b}" data-c3="${r},${c}" aria-label="Row ${r+1}: ${v||'blank'}">${v}</button></td>`; }).join('')}</tr>`).join('');
  let tfb='';
  if(e.checked) tfb = !wrong.length ? `<div class="fb good"><strong>Every entry is right.</strong></div>`
    : `<div class="fb bad"><strong>${wrong.length===1?'One entry is':wrong.length+' entries are'} wrong or blank (marked red).</strong><ol>${wrong.slice(0,3).map(([r,c])=>`<li>${cellWhy3(e,r,c)}</li>`).join('')}</ol></div>`;
  const t=tautIn(e.f,e.sys);
  let afb='';
  if(e.ans!==null){
    const ok=e.ans===t.holds;
    afb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'}</strong>${t.holds?`The main column is T in every row, so it’s a tautology in ${SYSTEMS[e.sys].short}.`:`With ${rowText(t.counter,true)}, the sentence is ${NAME3(t.value)}, not T. Only T is designated, so it isn’t a tautology in ${SYSTEMS[e.sys].short}.`}</div>`;
  }
  const yn=(v,l)=>{ let c='choice'; if(e.ans!==null){ if(v===t.holds) c+=' right'; else if(v===e.ans) c+=' wrong'; } return `<button class="${c}" data-t3="${v}" ${e.ans!==null?'disabled':''}>${l}</button>`; };
  const sc=score('mvtab');
  return `<button class="back" data-go="mv">‹ Multi-valued logic</button>
  <div class="ex-head"><h2>Three-valued tables</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${mvDefs()}
  ${sysSeg()}
  <p class="sentence">${esc(show(e.f))}</p>
  <section class="step"><h3>Fill in the table in ${SYSTEMS[e.sys].short}</h3><p class="hint">Tap a cell to cycle through T, U, F, and blank.</p>
    <div class="tt-wrap"><table class="tt"><thead>${head}</thead><tbody>${body}</tbody></table></div>
    <div class="actions"><button class="btn" data-act="check-3">Check table</button><button class="btn ghost" data-act="clear-3">Clear</button></div>${tfb}</section>
  <section class="step"><h3>Is it a tautology in ${SYSTEMS[e.sys].short}?</h3><div class="choices">${yn(true,'Yes, always T')}${yn(false,'No')}</div>${afb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}

// ----- Fuzzy values -----
const DEG=[0,0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9,1];
function newFuzzy(){
  let f; do{ f=L.genSentence(pick([1,1,2])); } while(f.t==='atom');
  const row={}; L.lettersOf(f).forEach(Lt=>row[Lt]=pick(DEG));
  return {f, row, input:'', res:null, focus:'fz-in'};
}
function fuzzySteps(f, row){
  const out=[], seen=new Set();
  const walk=n=>{
    if(n.t==='atom') return;
    if(n.t==='not') walk(n.a); else { walk(n.l); walk(n.r); }
    const k=show(n); if(seen.has(k)) return; seen.add(k);
    const v=x=>fmt(mv(x,row,'fuzzy'));
    const how = n.t==='not' ? `1 − ${v(n.a)}` : n.t==='and' ? `min(${v(n.l)}, ${v(n.r)})` : n.t==='or' ? `max(${v(n.l)}, ${v(n.r)})`
      : n.t==='cond' ? `min(1, 1 − ${v(n.l)} + ${v(n.r)})` : `1 − |${v(n.l)} − ${v(n.r)}|`;
    out.push(`${esc(show(n))} = ${how} = <b>${v(n)}</b>`);
  };
  walk(f); return out;
}
function fuzzyView(){
  const e=App.ex, truth=mv(e.f,e.row,'fuzzy'), sc=score('fuzzy');
  let fb='';
  if(e.res){
    if(e.res.err) fb=`<div class="fb bad"><strong>Enter a number from 0 to 1.</strong>${esc(e.res.err)}</div>`;
    else fb=`<div class="fb ${e.res.ok?'good':'bad'}"><strong>${e.res.ok?'Correct':'Not quite'}: the value is ${fmt(truth)}.</strong><ol>${fuzzySteps(e.f,e.row).map(s=>`<li>${s}</li>`).join('')}</ol></div>`;
  }
  const answered=e.res && !e.res.err;
  return `<button class="back" data-go="mv">‹ Multi-valued logic</button>
  <div class="ex-head"><h2>Fuzzy truth values</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${mvDefs()}
  <p class="sentence">${esc(show(e.f))}</p>
  <ul class="symkey">${Object.keys(e.row).map(k=>`<li><b>${k}</b> = ${fmt(e.row[k])}</li>`).join('')}</ul>
  <p class="hint muted" style="margin-top:8px">${SYM.not}x = 1 − x · ${SYM.and} = min · ${SYM.or} = max · x ${SYM.cond} y = min(1, 1 − x + y) · x ${SYM.bicond} y = 1 − |x − y|</p>
  <section class="step"><h3>What is its truth value?</h3>
    <input id="fz-in" class="sym-input" inputmode="decimal" autocomplete="off" value="${esc(e.input)}" aria-label="Truth value" placeholder="for example, 0.6" ${answered?'disabled':''}>
    <div class="actions"><button class="btn" data-act="check-fz" ${answered?'disabled':''}>Check</button></div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}
function fuzzyCheck(){
  const e=App.ex; if(e.res && !e.res.err) return;
  const x=parseFloat(String(e.input).replace(',','.'));
  if(!isFinite(x) || x<0 || x>1){ e.res={err:'For example, 0.6 or 1.'}; e.focus='fz-in'; render(); return; }
  e.res={ok:Math.abs(x-mv(e.f,e.row,'fuzzy'))<0.006}; tally('fuzzy', e.res.ok); render();
}

// ----- Which tautologies survive? -----
const TSYS=['K3','L3','fuzzy'];
function newTaut(){ return {f:P(pick(TAUTS)), picks:{}, checked:false}; }
function tautView(){
  const e=App.ex, sc=score('mvtaut');
  const rows=TSYS.map(sys=>{
    const t=tautIn(e.f,sys), mine=e.picks[sys];
    const btn=(v,l)=>{ let c='choice'; if(e.checked){ if(v===t.holds) c+=' right'; else if(v===mine) c+=' wrong'; } else if(v===mine) c+=' picked';
      return `<button class="${c}" data-ts="${sys}" data-v="${v}" ${e.checked?'disabled':''}>${l}</button>`; };
    const three=sys!=='fuzzy';
    const why = t.holds ? (three?'It’s T in every row.':'It has value 1 for every assignment of degrees.')
      : `With ${rowText(t.counter,three)}, its value is ${three?NAME3(t.value):fmt(t.value)}, not ${three?'T':'1'}.`;
    const fb=e.checked?`<div class="fb ${mine===t.holds?'good':'bad'}"><strong>${t.holds?'Still a tautology.':'Not a tautology here.'}</strong>${why}</div>`:'';
    return `<div class="sq-row"><b>${SYSTEMS[sys].name}</b><div class="tri">${btn(true,'Still a tautology')}${btn(false,'Fails')}</div>${fb}</div>`;
  }).join('');
  const all=TSYS.every(s=>e.picks[s]!==undefined);
  return `<button class="back" data-go="mv">‹ Multi-valued logic</button>
  <div class="ex-head"><h2>Which tautologies survive?</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${mvDefs()}
  <p class="sentence">${esc(show(e.f))}</p>
  <p class="hint muted">This is a tautology in classical logic. Is it still one in each system? (Only T, or 1, counts as designated.)</p>
  <div class="sq-rows">${rows}</div>
  <div class="actions"><button class="btn" data-act="check-ts" ${all&&!e.checked?'':'disabled'}>Check</button></div>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}

function mvClick(ev){
  const e=App.ex, d=x=>ev.target.closest(x); let el;
  if((el=d('[data-c3]'))){ const k=el.dataset.c3; e.vals[k]=cycle3(e.vals[k]); e.checked=false; render(); return; }
  if((el=d('[data-t3]')) && e.ans===null){ e.ans=el.dataset.t3==='true'; tally('mvtab', e.ans===tautIn(e.f,e.sys).holds); render(); return; }
  if((el=d('[data-ts]')) && !e.checked){ e.picks[el.dataset.ts]=el.dataset.v==='true'; render(); return; }
  const a=d('[data-act]'); if(!a) return;
  const act=a.dataset.act;
  if(act==='check-3'){ e.checked=true; render(); }
  if(act==='clear-3'){ e.vals={}; e.checked=false; render(); }
  if(act==='check-fz') fuzzyCheck();
  if(act==='check-ts'){ e.checked=true; tally('mvtaut', TSYS.every(s=>e.picks[s]===tautIn(e.f,s).holds)); render(); }
}
registerView('mv', {render: mvHub});
registerView('mvtab', {init:newTab, render:tabView, click:mvClick, onSetting:name=>{ if(name==='mvSys') App.ex=newTab(); }});
registerView('fuzzy', {init:newFuzzy, render:fuzzyView, click:mvClick, after:L.focusAfter,
  input:ev=>{ if(ev.target.id==='fz-in') App.ex.input=ev.target.value; },
  keydown:ev=>{ if(ev.target.id==='fz-in' && ev.key==='Enter'){ ev.preventDefault(); fuzzyCheck(); } }});
registerView('mvtaut', {init:newTaut, render:tautView, click:mvClick});

Engines.manyvalued = {SYSTEMS, mv, rows3, tautIn, fuzzySteps, TAUTS, SHOWCASE, NAME3};
})();
