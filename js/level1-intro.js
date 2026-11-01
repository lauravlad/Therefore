// Therefore — Level 1: Intro to logic.
// Categorical logic: statement forms, Venn diagrams, syllogisms. Diagrams use the
// Boolean (modern) reading by default; Aristotelian-only forms are flagged as such.
(function(){
'use strict';

// ===== Categorical logic engine =====
const BITS = { S: 1, P: 2, M: 4 };
const has = (r, t) => !!(r & BITS[t]);
const regionList = (three) => (three ? [1, 2, 3, 4, 5, 6, 7] : [1, 2, 3]);

function propEffect(type, a, b, three) {
  const R = regionList(three);
  if (type === 'A') return { kind: 'shade', regions: R.filter(r => has(r, a) && !has(r, b)) };
  if (type === 'E') return { kind: 'shade', regions: R.filter(r => has(r, a) && has(r, b)) };
  if (type === 'I') return { kind: 'x', regions: R.filter(r => has(r, a) && has(r, b)) };
  return { kind: 'x', regions: R.filter(r => has(r, a) && !has(r, b)) };
}

const FIGURES = {
  1: [['M', 'P'], ['S', 'M']],
  2: [['P', 'M'], ['S', 'M']],
  3: [['M', 'P'], ['M', 'S']],
  4: [['P', 'M'], ['M', 'S']],
};

function syllogismParts(mood, fig) {
  const [maj, min] = FIGURES[fig];
  return [
    { type: mood[0], a: maj[0], b: maj[1] },
    { type: mood[1], a: min[0], b: min[1] },
    { type: mood[2], a: 'S', b: 'P' },
  ];
}

// Diagram the premises: universals first, then each particular's X.
function diagramPremises(premises, three) {
  const shaded = new Set();
  premises.forEach(p => {
    const e = propEffect(p.type, p.a, p.b, three);
    if (e.kind === 'shade') e.regions.forEach(r => shaded.add(r));
  });
  const xGroups = [];
  for (const p of premises) {
    const e = propEffect(p.type, p.a, p.b, three);
    if (e.kind === 'x') {
      const cands = e.regions.filter(r => !shaded.has(r));
      if (cands.length === 0) return null; // inconsistent premises
      xGroups.push({ premise: p, all: e.regions, cands });
    }
  }
  return { shaded, xGroups };
}

// Boolean (modern) standpoint
function isValid(diagram, conclusion) {
  const e = propEffect(conclusion.type, conclusion.a, conclusion.b, true);
  if (e.kind === 'shade') return e.regions.every(r => diagram.shaded.has(r));
  return diagram.xGroups.some(g => g.cands.every(r => e.regions.includes(r)));
}

const VALID_BOOLEAN = ['AAA-1','EAE-1','AII-1','EIO-1','AEE-2','EAE-2','AOO-2','EIO-2',
  'IAI-3','AII-3','OAO-3','EIO-3','AEE-4','IAI-4','EIO-4'];

// ===== Content (original) =====
const TERMS = [
  {S:'violinists', P:'night owls', M:'musicians'},
  {S:'sharks', P:'predators', M:'fish'},
  {S:'novelists', P:'early risers', M:'writers'},
  {S:'tomatoes', P:'fruits', M:'garden plants'},
  {S:'chess players', P:'patient people', M:'strategists'},
  {S:'electric cars', P:'quiet vehicles', M:'hybrids'},
  {S:'senators', P:'lawyers', M:'politicians'},
  {S:'owls', P:'hunters', M:'birds'},
  {S:'poets', P:'dreamers', M:'artists'},
  {S:'surgeons', P:'careful people', M:'doctors'},
  {S:'bakers', P:'early risers', M:'shop owners'},
  {S:'ferns', P:'flowering plants', M:'shade plants'},
];
const FORMS = {
  A:{name:'A', label:'All S are P', say:(a,b)=>`All ${a} are ${b}.`},
  E:{name:'E', label:'No S are P', say:(a,b)=>`No ${a} are ${b}.`},
  I:{name:'I', label:'Some S are P', say:(a,b)=>`Some ${a} are ${b}.`},
  O:{name:'O', label:'Some S are not P', say:(a,b)=>`Some ${a} are not ${b}.`},
};
// Traditional names. needs = the term that must refer to something (Aristotelian-only forms)
const NAMES = {
  'AAA-1':{name:'Barbara'},'EAE-1':{name:'Celarent'},'AII-1':{name:'Darii'},'EIO-1':{name:'Ferio'},
  'AEE-2':{name:'Camestres'},'EAE-2':{name:'Cesare'},'AOO-2':{name:'Baroko',alt:'Baroco'},'EIO-2':{name:'Festino'},
  'IAI-3':{name:'Disamis'},'AII-3':{name:'Datisi'},'OAO-3':{name:'Bokardo',alt:'Bocardo'},'EIO-3':{name:'Ferison'},
  'AEE-4':{name:'Camenes',alt:'Calemes'},'IAI-4':{name:'Dimaris'},'EIO-4':{name:'Fresison'},
  'AAI-1':{name:'Barbari',needs:'S'},'EAO-1':{name:'Celaront',needs:'S'},
  'AEO-2':{name:'Camestros',needs:'S'},'EAO-2':{name:'Cesaro',needs:'S'},
  'AAI-3':{name:'Darapti',needs:'M'},'EAO-3':{name:'Felapton',needs:'M'},
  'AEO-4':{name:'Camenos',needs:'S',alt:'Calemos'},'AAI-4':{name:'Bramantip',needs:'P'},'EAO-4':{name:'Fesapo',needs:'M'},
};
const formKey = e => `${e.mood}-${e.fig}`;
const nameTag = e => NAMES[formKey(e)] ? `, ${NAMES[formKey(e)].name}` : '';
function nameNote(e){
  const n=NAMES[formKey(e)];
  if(!n) return ' This form has no traditional name.';
  if(!n.needs) return ` This form is <em>${n.name}</em>, valid on either reading.`;
  return ` This form is <em>${n.name}</em>. It’s valid only on the Aristotelian reading, which assumes at least one ${esc(e.t[n.needs])} (${n.needs}) exists.`;
}

// ===== Venn geometry =====
const GEO = {
  2:{w:300,h:190,c:{S:[115,100,70],P:[185,100,70]},lab:{S:[48,30],P:[252,30]}},
  3:{w:300,h:292,c:{S:[113,108,72],P:[187,108,72],M:[150,174,72]},lab:{S:[38,36],P:[262,36],M:[150,282]}},
};
// Find a comfortable interior point for each region (farthest from any edge)
function computeAnchors(n){
  const g=GEO[n], terms=Object.keys(g.c), best={};
  for(let x=0;x<g.w;x+=2) for(let y=0;y<g.h;y+=2){
    let r=0, d=Infinity;
    terms.forEach(t=>{ const [cx,cy,rad]=g.c[t]; const dist=Math.hypot(x-cx,y-cy); if(dist<rad) r|=BITS[t]; d=Math.min(d,Math.abs(dist-rad)); });
    if(!r) continue;
    if(!best[r]||d>best[r].d) best[r]={x,y,d};
  }
  g.anchor=best;
}
computeAnchors(2); computeAnchors(3);
function regionAt(n,x,y){ const g=GEO[n]; let r=0; Object.keys(g.c).forEach(t=>{const [cx,cy,rad]=g.c[t]; if(Math.hypot(x-cx,y-cy)<rad) r|=BITS[t];}); return r; }

let uid=0;
function vennSVG(n, opts){
  // opts: state {region:0|1|2}, xPoints [[x,y]], wrong Set, live bool
  const g=GEO[n], id='v'+(uid++), terms=Object.keys(g.c), W=g.w, H=g.h;
  let defs=`<pattern id="${id}h" width="7" height="7" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="7" style="stroke:var(--hatch)" stroke-width="2.6"/></pattern>`;
  terms.forEach(t=>{const [cx,cy,r]=g.c[t];
    defs+=`<mask id="${id}in${t}" maskUnits="userSpaceOnUse" x="0" y="0" width="${W}" height="${H}"><rect width="${W}" height="${H}" fill="black"/><circle cx="${cx}" cy="${cy}" r="${r}" fill="white"/></mask>`;
    defs+=`<mask id="${id}out${t}" maskUnits="userSpaceOnUse" x="0" y="0" width="${W}" height="${H}"><rect width="${W}" height="${H}" fill="white"/><circle cx="${cx}" cy="${cy}" r="${r}" fill="black"/></mask>`;
  });
  const region=(r,fill)=>{ let s=`<rect width="${W}" height="${H}" style="fill:${fill}"/>`; terms.forEach(t=>{ s=`<g mask="url(#${id}${has(r,t)?'in':'out'}${t})">${s}</g>`; }); return s; };
  let body='';
  const regs = n===3?[1,2,3,4,5,6,7]:[1,2,3];
  if(opts.wrong) opts.wrong.forEach(r=>{ body+=region(r,'var(--bad-tint)'); });
  regs.forEach(r=>{ if(opts.state&&opts.state[r]===1) body+=region(r,`url(#${id}h)`); });
  terms.forEach(t=>{const [cx,cy,r]=g.c[t]; body+=`<circle cx="${cx}" cy="${cy}" r="${r}" fill="none" style="stroke:var(--ink)" stroke-width="1.8"/>`;});
  terms.forEach(t=>{const [x,y]=g.lab[t]; body+=`<text x="${x}" y="${y}" text-anchor="middle" style="fill:var(--ink);font-family:var(--serif);font-size:20px;font-weight:600">${t}</text>`;});
  const pts = [];
  if(opts.state) regs.forEach(r=>{ if(opts.state[r]===2){ const a=g.anchor[r]; pts.push([a.x,a.y]); } });
  if(opts.xPoints) pts.push(...opts.xPoints);
  pts.forEach(([x,y])=>{ body+=`<g style="stroke:var(--mark)" stroke-width="3" stroke-linecap="round"><line x1="${x-7}" y1="${y-7}" x2="${x+7}" y2="${y+7}"/><line x1="${x+7}" y1="${y-7}" x2="${x-7}" y2="${y+7}"/></g>`; });
  const label = opts.live ? 'Venn diagram. Tap an area once to shade it, twice to mark an X, three times to clear.' : 'Venn diagram showing the answer.';
  return `<svg class="venn${opts.live?' live':''}" data-n="${n}" viewBox="0 0 ${W} ${H}" role="img" aria-label="${label}"><defs>${defs}</defs>${body}</svg>`;
}
// Answer diagram: X on the line = midpoint of the two candidate anchors
function answerPoints(n, xGroups){
  const g=GEO[n];
  return xGroups.map(gr=>{ const ps=gr.cands.map(r=>g.anchor[r]); return [ps.reduce((s,p)=>s+p.x,0)/ps.length, ps.reduce((s,p)=>s+p.y,0)/ps.length]; });
}
function regionName(r, three){
  const ts = three?['S','P','M']:['S','P'];
  const ins=ts.filter(t=>has(r,t)), outs=ts.filter(t=>!has(r,t));
  let s='inside '+ins.join(' and ');
  if(outs.length) s+=', outside '+outs.join(' and ');
  return s;
}
const legend = `<div class="legend"><span><svg width="18" height="14" aria-hidden="true"><defs><pattern id="lg" width="5" height="5" patternUnits="userSpaceOnUse" patternTransform="rotate(45)"><line x1="0" y1="0" x2="0" y2="5" style="stroke:var(--hatch)" stroke-width="2"/></pattern></defs><rect x="1" y="1" width="16" height="12" rx="2" fill="url(#lg)" style="stroke:var(--ink)" stroke-width="1.2"/></svg>1 tap: shade (empty)</span><span><b style="font-family:var(--serif)">X</b>&nbsp;2 taps: something exists here</span><span>3 taps: clear</span></div>`;

// ===== Level card and home icon =====
registerLevel({num:1, title:'Intro to logic', topics:[
  {title:'Categorical logic', sub:'Statements, Venn diagrams, syllogisms', go:'cat'},
  {title:'Fallacies', sub:'Spot the mistake in everyday arguments'},
]});
App.heroIcon = () => vennSVG(3,{state:{3:1,7:1}}).replace('class="venn"','class="venn" aria-hidden="true"');

function catView(){
  const s=score('stmt'), y=score('syl');
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Categorical logic</h2>
  <p class="muted">Diagrams use the modern (Boolean) reading: a universal statement says nothing about whether anything exists.</p>
  <ul class="topics" style="margin-top:18px">
    <li><button class="topic open" data-go="stmt"><span>Diagram a statement<small>Name the form (A, E, I, O), then draw it. ${s.done?`${s.right} of ${s.done} correct so far.`:''}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="syl"><span>Test a syllogism<small>Mood and figure, diagram, valid or invalid. ${y.done?`${y.right} of ${y.done} correct so far.`:''}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="names"><span>Named forms<small>Barbara, Celarent, Darii, Ferio, and the rest</small></span><span class="go">View</span></button></li>
  </ul>`;
}

// ===== Named forms reference =====
function namesView(){
  const row=k=>{ const n=NAMES[k]; return `<tr><td><b>${n.name}</b>${n.alt?`<small>also ${n.alt}</small>`:''}</td><td>${k}</td>${n.needs?`<td>${n.needs}</td>`:''}</tr>`; };
  const valid=Object.keys(NAMES).filter(k=>!NAMES[k].needs), cond=Object.keys(NAMES).filter(k=>NAMES[k].needs);
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <h2>Named forms</h2>
  <p class="muted">Medieval students memorized valid syllogisms by name. The three vowels in each name give the mood: <b>B<u>a</u>rb<u>a</u>r<u>a</u></b> is AAA, <b>F<u>e</u>r<u>i</u><u>o</u></b> is EIO.</p>
  <h3 style="margin-top:22px">Valid on either reading</h3>
  <p class="hint muted">These 15 forms are valid whether or not the terms refer to anything.</p>
  <div class="forms"><table><thead><tr><th>Name</th><th>Form</th></tr></thead><tbody>${valid.map(row).join('')}</tbody></table></div>
  <h3 style="margin-top:26px">Valid only on the Aristotelian reading</h3>
  <p class="hint muted">These 9 forms are valid only if the listed term refers to at least one thing. On the modern (Boolean) reading they’re invalid.</p>
  <div class="forms"><table><thead><tr><th>Name</th><th>Form</th><th>Must exist</th></tr></thead><tbody>${cond.map(row).join('')}</tbody></table></div>`;
}

// ===== Statement exercise =====
function newStmt(){
  const t=pick(TERMS), type=pick('AEIO'.split(''));
  return {t, type, form:null, state:{1:0,2:0,3:0}, checked:null, counted:false};
}
function stmtView(){
  const e=App.ex, text=FORMS[e.type].say(e.t.S,e.t.P);
  const formBtns='AEIO'.split('').map(k=>{
    let cls='choice'; if(e.form){ if(k===e.type) cls+=' right'; else if(k===e.form) cls+=' wrong'; }
    return `<button class="${cls}" data-form="${k}" ${e.form?'disabled':''}><b>${k}</b>${FORMS[k].label}</button>`; }).join('');
  let formFb='';
  if(e.form) formFb = e.form===e.type ? `<div class="fb good"><strong>Correct.</strong>${formWhy(e.type)}</div>` : `<div class="fb bad"><strong>It’s an ${e.type} statement.</strong>${formWhy(e.type)}</div>`;
  const correct=correctStmt(e);
  let diag='', dfb='';
  if(e.checked){
    const wrong=diffRegions(e.state, correct, [1,2,3]);
    diag = vennSVG(2,{state:e.state, wrong:new Set(wrong), live:!wrong.length?false:true});
    if(!wrong.length) dfb=`<div class="fb good"><strong>Correct diagram.</strong>${stmtExplain(e)}</div>`;
    else dfb=`<div class="fb bad"><strong>${wrong.length===1?'One area doesn’t match':wrong.length+' areas don’t match'} (tinted red).</strong>${stmtExplain(e)}</div>
      <p class="answer-title">Correct diagram</p><div class="venn-wrap">${vennSVG(2,{state:correctState(correct,[1,2,3]), xPoints:[]})}</div>`;
  } else diag = vennSVG(2,{state:e.state, live:true});
  const sc=score('stmt');
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <div class="ex-head"><h2>Diagram a statement</h2><span class="score">${sc.right}/${sc.done}</span></div>
  <p class="prop">${esc(text)}</p>
  <div class="key"><span><b>S</b> = ${esc(e.t.S)}</span><span><b>P</b> = ${esc(e.t.P)}</span></div>
  <section class="step"><h3>Which form is it?</h3><div class="choices">${formBtns}</div>${formFb}</section>
  <section class="step"><h3>Draw it</h3><p class="hint">Shade areas that must be empty. Put an X where something must exist.</p>
    <div class="venn-wrap" data-venn="stmt">${diag}</div>${legend}
    <div class="actions"><button class="btn" data-act="check-stmt">Check diagram</button><button class="btn ghost" data-act="clear">Clear</button></div>${dfb}</section>
  <div class="next"><button class="btn" data-act="next">Next statement</button></div>`;
}
function formWhy(t){
  return {A:' Universal affirmative: every S is a P.',E:' Universal negative: no S is a P.',I:' Particular affirmative: at least one S is a P.',O:' Particular negative: at least one S is not a P.'}[t];
}
function correctStmt(e){
  const d=diagramPremises([{type:e.type,a:'S',b:'P'}], false);
  return d;
}
function correctState(d, regs){
  const st={}; regs.forEach(r=>st[r]=0); d.shaded.forEach(r=>st[r]=1); d.xGroups.forEach(g=>g.cands.forEach(r=>st[r]=2)); return st;
}
function diffRegions(state, d, regs){ const want=correctState(d,regs); return regs.filter(r=>(state[r]||0)!==want[r]); }
function stmtExplain(e){
  return {A:' Every S is inside P, so the part of S outside P is empty: shade it.',
          E:' Nothing is both S and P, so shade where the circles overlap.',
          I:' At least one thing is both S and P, so put an X in the overlap.',
          O:' At least one S is outside P, so put an X in S outside the overlap.'}[e.type];
}

// ===== Syllogism exercise =====
function newSyl(){
  let mood, fig, d;
  do{
    const roll=Math.random();
    if(roll<.45){ const f=pick(VALID_BOOLEAN); mood=f.slice(0,3); fig=+f[4]; }
    else if(roll<.6){ const f=pick(Object.keys(NAMES).filter(k=>NAMES[k].needs)); mood=f.slice(0,3); fig=+f[4]; }
    else { mood=[0,0,0].map(()=>pick('AEIO'.split(''))).join(''); fig=1+Math.floor(Math.random()*4); }
    d=diagramPremises(syllogismParts(mood,fig).slice(0,2), true);
  } while(!d);
  return {t:pick(TERMS), mood, fig, d, pickMood:['','',''], pickFig:'', mfChecked:false, state:{1:0,2:0,3:0,4:0,5:0,6:0,7:0}, checked:false, valid:null, counted:false};
}
function sylView(){
  const e=App.ex, parts=syllogismParts(e.mood,e.fig), T=e.t;
  const say=p=>FORMS[p.type].say(T[p.a],T[p.b]);
  const correctValid=isValid(e.d,parts[2]);
  const opt=(v,cur)=>['','A','E','I','O'].map(k=>`<option value="${k}" ${k===cur?'selected':''}>${k||'–'}</option>`).join('');
  const figOpt=['','1','2','3','4'].map(k=>`<option value="${k}" ${k===e.pickFig?'selected':''}>${k||'–'}</option>`).join('');
  let mfFb='';
  if(e.mfChecked){
    const ok=e.pickMood.join('')===e.mood && +e.pickFig===e.fig;
    mfFb = ok ? `<div class="fb good"><strong>Correct: ${e.mood}-${e.fig}${nameTag(e)}.</strong>${figHint(e.fig)}</div>`
              : `<div class="fb bad"><strong>It’s ${e.mood}-${e.fig}${nameTag(e)}.</strong>Mood lists the forms of the major premise, minor premise, and conclusion. ${figHint(e.fig)}</div>`;
  }
  const regs=[1,2,3,4,5,6,7];
  let diag, dfb='';
  if(e.checked){
    const wrong=diffRegions(e.state,e.d,regs);
    diag=vennSVG(3,{state:e.state, wrong:new Set(wrong), live:true});
    const steps=`<ol>${sylSteps(e)}</ol>`;
    if(!wrong.length) dfb=`<div class="fb good"><strong>Correct diagram.</strong>${steps}</div>`;
    else dfb=`<div class="fb bad"><strong>${wrong.length===1?'One area doesn’t match':wrong.length+' areas don’t match'} (tinted red).</strong>${steps}</div>
      <p class="answer-title">Correct diagram</p><div class="venn-wrap">${vennSVG(3,{state:{...correctState({shaded:e.d.shaded,xGroups:[]},regs)}, xPoints:answerPoints(3,e.d.xGroups)})}</div>`;
  } else diag=vennSVG(3,{state:e.state, live:true});
  let vfb='';
  if(e.valid!==null){
    const ok=e.valid===correctValid;
    vfb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'} It’s ${correctValid?'valid':'invalid'}.</strong>${validWhy(e,parts[2],correctValid)}${nameNote(e)}</div>`;
  }
  const vbtn=(v,l)=>{ let c='choice'; if(e.valid!==null){ if(v===correctValid) c+=' right'; else if(v===e.valid) c+=' wrong'; } return `<button class="${c}" data-valid="${v}" ${e.valid!==null?'disabled':''}>${l}</button>`; };
  const sc=score('syl');
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <div class="ex-head"><h2>Test a syllogism</h2><span class="score">${sc.right}/${sc.done}</span></div>
  <div class="argument">
    <div class="line"><span class="lab">1.</span><span>${esc(say(parts[0]))}</span></div>
    <div class="line"><span class="lab">2.</span><span>${esc(say(parts[1]))}</span></div>
    <div class="line concl"><span class="lab">∴</span><span>${esc(say(parts[2]))}</span></div>
  </div>
  <div class="key"><span><b>S</b> = ${esc(T.S)}</span><span><b>P</b> = ${esc(T.P)}</span><span><b>M</b> = ${esc(T.M)}</span></div>
  <section class="step"><h3>Mood and figure</h3><p class="hint">Premise 1 is the major premise (it has P). Premise 2 is the minor (it has S).</p>
    <div class="selects">
      <label>Major<select data-mood="0" ${e.mfChecked?'disabled':''}>${opt(0,e.pickMood[0])}</select></label>
      <label>Minor<select data-mood="1" ${e.mfChecked?'disabled':''}>${opt(1,e.pickMood[1])}</select></label>
      <label>Conclusion<select data-mood="2" ${e.mfChecked?'disabled':''}>${opt(2,e.pickMood[2])}</select></label>
      <label>Figure<select data-fig ${e.mfChecked?'disabled':''}>${figOpt}</select></label>
    </div>
    <div class="actions"><button class="btn" data-act="check-mf" ${e.mfChecked?'disabled':''}>Check</button></div>${mfFb}</section>
  <section class="step"><h3>Diagram the premises</h3><p class="hint">Diagram universal premises first. If an X could go in either of two areas, mark both: that puts the X on the line.</p>
    <div class="venn-wrap" data-venn="syl">${diag}</div>${legend}
    <div class="actions"><button class="btn" data-act="check-syl">Check diagram</button><button class="btn ghost" data-act="clear">Clear</button></div>${dfb}</section>
  <section class="step"><h3>Valid or invalid?</h3><p class="hint">Valid means the premise diagram already shows the conclusion.</p>
    <div class="choices">${vbtn(true,'Valid')}${vbtn(false,'Invalid')}</div>${vfb}</section>
  <div class="next"><button class="btn" data-act="next">Next syllogism</button></div>`;
}
function figHint(f){ return ` Figure ${f}: the middle term is ${{1:'the subject of the major premise and the predicate of the minor',2:'the predicate of both premises',3:'the subject of both premises',4:'the predicate of the major premise and the subject of the minor'}[f]}.`; }
function sylSteps(e){
  const parts=syllogismParts(e.mood,e.fig).slice(0,2), out=[];
  const q=p=>`“${FORMS[p.type].say(p.a,p.b).slice(0,-1)}”`;
  parts.filter(p=>p.type==='A'||p.type==='E').forEach(p=>{
    out.push(`${q(p)} is universal: shade ${p.type==='A'?`the part of ${p.a} outside ${p.b}`:`where ${p.a} and ${p.b} overlap`}.`);
  });
  e.d.xGroups.forEach(g=>{
    const p=g.premise, where=p.type==='I'?`where ${p.a} and ${p.b} overlap`:`in ${p.a} outside ${p.b}`;
    let s=`${q(p)} is particular: put an X ${where}`;
    if(g.cands.length===2) s+=`. Neither part is shaded, so the X goes on the line (${regionName(g.cands[0],true)} or ${regionName(g.cands[1],true)}).`;
    else if(g.all.length>g.cands.length) s+=`. One part is already shaded, so the X goes in the other (${regionName(g.cands[0],true)}).`;
    else s+='.';
    out.push(s);
  });
  return out.map(s=>`<li>${s}</li>`).join('');
}
function validWhy(e, c, valid){
  const eff=propEffect(c.type,c.a,c.b,true);
  if(eff.kind==='shade'){
    if(valid) return ` The conclusion needs ${eff.regions.length===1?'one area':'two areas'} shaded, and the premises already shade ${eff.regions.length===1?'it':'them'}.`;
    const open=eff.regions.filter(r=>!e.d.shaded.has(r));
    return ` The conclusion needs ${open.length>1?'the areas':'the area'} ${open.map(r=>regionName(r,true)).join(' and the area ')} shaded, but the premises leave ${open.length>1?'them':'it'} open.`;
  }
  if(valid) return ' The conclusion needs an X definitely in its area, and the premises put one there.';
  const touching=e.d.xGroups.some(g=>g.cands.some(r=>eff.regions.includes(r)));
  if(touching) return ' The conclusion needs an X definitely in its area, but the X sits on a line, so the thing might be on the other side.';
  return ' The conclusion needs an X in its area, but the premises put no X there.';
}

// ===== Events for the exercise views =====
function exerciseClick(ev){
  const ex=App.ex, view=App.view;
  const f=ev.target.closest('[data-form]');
  if(f && view==='stmt' && !ex.form){ ex.form=f.dataset.form; tally('stmt', ex.form===ex.type); render(); return; }
  const v=ev.target.closest('[data-valid]');
  if(v && view==='syl' && ex.valid===null){ ex.valid=v.dataset.valid==='true'; tally('syl', ex.valid===isValid(ex.d,syllogismParts(ex.mood,ex.fig)[2])); render(); return; }
  const a=ev.target.closest('[data-act]');
  if(a){
    const act=a.dataset.act;
    if(act==='clear'){ Object.keys(ex.state).forEach(k=>ex.state[k]=0); ex.checked=false; render(); return; }
    if(act==='check-stmt'||act==='check-syl'){
      ex.checked=true;
      if(!ex.counted){ ex.counted=true; const regs=view==='stmt'?[1,2,3]:[1,2,3,4,5,6,7]; const d=view==='stmt'?correctStmt(ex):ex.d; tally(view, diffRegions(ex.state,d,regs).length===0); }
      render(); return;
    }
    if(act==='check-mf'){ ex.mfChecked=true; render(); return; }
  }
  const svg=ev.target.closest('svg.venn.live');
  if(svg){
    const n=+svg.dataset.n, pt=svg.createSVGPoint(); pt.x=ev.clientX; pt.y=ev.clientY;
    const p=pt.matrixTransform(svg.getScreenCTM().inverse());
    const r=regionAt(n,p.x,p.y); if(!r) return;
    ex.state[r]=((ex.state[r]||0)+1)%3; ex.checked=false; render();
  }
}
function sylChange(ev){
  const ex=App.ex;
  if(ev.target.dataset.mood!==undefined) ex.pickMood[+ev.target.dataset.mood]=ev.target.value;
  if(ev.target.dataset.fig!==undefined) ex.pickFig=ev.target.value;
}

registerView('cat',   {render: catView});
registerView('names', {render: namesView});
registerView('stmt',  {init: newStmt, render: stmtView, click: exerciseClick});
registerView('syl',   {init: newSyl,  render: sylView,  click: exerciseClick, change: sylChange});
})();
