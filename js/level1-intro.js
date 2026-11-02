// Therefore — Level 1: Intro to logic.
// Modules: Categorical logic (statements, square of opposition, immediate inferences,
// syllogisms) and Fallacies. Content is original; based on Knachel, Fundamental Methods
// of Logic (2017, CC BY 4.0), chapters 2 and 3.
// Categorical diagrams use the Boolean reading by default; the "reading" setting switches
// the square of opposition and syllogism exercises to the Aristotelian reading.
(function(){
'use strict';

// =====================================================================
// Categorical logic engine
// =====================================================================
// Regions are bitmasks: bit 1 = inside S, 2 = inside P, 4 = inside M. Region 0 is outside every circle.
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

// Boolean validity read off the Venn diagram (used for the step-by-step feedback).
function isValid(diagram, conclusion) {
  const e = propEffect(conclusion.type, conclusion.a, conclusion.b, true);
  if (e.kind === 'shade') return e.regions.every(r => diagram.shaded.has(r));
  return diagram.xGroups.some(g => g.cands.every(r => e.regions.includes(r)));
}

// Model checking: a "model" says which regions have members (bit r of occ set = region r is nonempty).
// A term is a letter, optionally prefixed with "!" for its complement (non-S).
const inTerm = (r, term) => term[0]==='!' ? !has(r, term[1]) : has(r, term);
function holds(type, a, b, occ, regions){
  const occupied = regions.filter(r => occ & (1<<r));
  if(type==='A') return !occupied.some(r => inTerm(r,a) && !inTerm(r,b));
  if(type==='E') return !occupied.some(r => inTerm(r,a) && inTerm(r,b));
  if(type==='I') return occupied.some(r => inTerm(r,a) && inTerm(r,b));
  return occupied.some(r => inTerm(r,a) && !inTerm(r,b));
}
const ALL3=[0,1,2,3,4,5,6,7], ALL2=[0,1,2,3];
const termExists = (t, occ, regions) => regions.some(r => (occ & (1<<r)) && inTerm(r,t));

// Syllogism validity by checking every model. `mustExist` lists terms assumed to have members.
function validWith(mood, fig, mustExist){
  const parts=syllogismParts(mood, fig);
  for(let occ=0; occ<256; occ++){
    if(mustExist.some(t => !termExists(t, occ, ALL3))) continue;
    if(parts.slice(0,2).every(p => holds(p.type,p.a,p.b,occ,ALL3)) && !holds(parts[2].type,'S','P',occ,ALL3)) return false;
  }
  return true;
}
// Aristotelian reading of a syllogism: every term (S, P, M) has members.
const validFor = (mood, fig, reading) => validWith(mood, fig, reading==='aristotelian' ? ['S','P','M'] : []);

// Square of opposition: given statement `g` (A/E/I/O about S and P) has truth value gv.
// Returns 'T', 'F', or '?' (undetermined) for statement t. Aristotelian: S has members.
function squareTruth(g, gv, t, reading){
  const seen=new Set();
  for(let occ=0; occ<16; occ++){
    if(reading==='aristotelian' && !termExists('S', occ, ALL2)) continue;
    if(holds(g,'S','P',occ,ALL2)!==gv) continue;
    seen.add(holds(t,'S','P',occ,ALL2));
  }
  return seen.size===2 ? '?' : (seen.has(true) ? 'T' : 'F');
}
function relation(a, b){
  const k=[a,b].sort().join('');
  return {AO:'contradictories', EI:'contradictories', AE:'contraries', IO:'subcontraries', AI:'subalternation', EO:'subalternation'}[k];
}

// Immediate inferences. Returns {type, a, b} for the converse, obverse, or contrapositive.
const comp = t => t[0]==='!' ? t.slice(1) : '!'+t;
const OBV = {A:'E', E:'A', I:'O', O:'I'};
function transform(type, op, a='S', b='P'){
  if(op==='converse') return {type, a:b, b:a};
  if(op==='obverse') return {type:OBV[type], a, b:comp(b)};
  if(op==='contrapositive') return {type, a:comp(b), b:comp(a)};
  if(op==='inverse') return {type, a:comp(a), b:comp(b)}; // a common wrong answer, used as a distractor
}
function equivalentStatements(s1, s2){
  for(let occ=0; occ<16; occ++) if(holds(s1.type,s1.a,s1.b,occ,ALL2)!==holds(s2.type,s2.a,s2.b,occ,ALL2)) return false;
  return true;
}

const VALID_BOOLEAN = ['AAA-1','EAE-1','AII-1','EIO-1','AEE-2','EAE-2','AOO-2','EIO-2',
  'IAI-3','AII-3','OAO-3','EIO-3','AEE-4','IAI-4','EIO-4'];

// =====================================================================
// Categorical content (original)
// =====================================================================
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
// Traditional names. needs = the term that must have members (forms valid only on the Aristotelian reading)
const NAMES = {
  'AAA-1':{name:'Barbara'},'EAE-1':{name:'Celarent'},'AII-1':{name:'Darii'},'EIO-1':{name:'Ferio'},
  'AEE-2':{name:'Camestres'},'EAE-2':{name:'Cesare'},'AOO-2':{name:'Baroco',alt:'Baroko'},'EIO-2':{name:'Festino'},
  'IAI-3':{name:'Disamis'},'AII-3':{name:'Datisi'},'OAO-3':{name:'Bocardo',alt:'Bokardo'},'EIO-3':{name:'Ferison'},
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
const reading = () => getSetting('reading','boolean');
const readingSeg = () => seg('reading','Reading',[['boolean','Boolean'],['aristotelian','Aristotelian']], reading());

// ----- Key definitions (original wording; topics follow Knachel ch. 3) -----
const D = {
  prop:['Categorical proposition','A statement about how two classes relate: it says that all or some members of one class are, or are not, members of another.','“Some volcanoes are islands.”'],
  terms:['Subject and predicate terms','The subject term names the class the statement is about. The predicate term names the class it’s being compared with.','In “No cacti are trees,” the subject term is “cacti” and the predicate term is “trees.”'],
  qq:['Quantity and quality','Quantity is whether the statement covers every member of the subject class (universal) or at least one (particular). Quality is whether it includes members in the predicate class (affirmative) or excludes them (negative).','“Some coats are not raincoats” is particular and negative.'],
  forms:['The four forms','<b>A</b>: All S are P (universal affirmative). <b>E</b>: No S are P (universal negative). <b>I</b>: Some S are P (particular affirmative). <b>O</b>: Some S are not P (particular negative). “Some” means at least one.','“No comets are planets” is an E statement.'],
  dist:['Distribution','A term is distributed when the statement says something about every member of its class. A distributes the subject. E distributes both terms. I distributes neither. O distributes the predicate.','In “Some coats are not raincoats,” only “raincoats” is distributed: those coats are shut out of the entire class of raincoats.'],
  venn:['Venn diagram','Each circle stands for a class. Shading an area says it’s empty. An X says at least one thing is there. An X on a line means something is in one of the two areas, but we don’t know which.','For “No comets are planets,” shade the overlap of the two circles.'],
  syl:['Standard-form syllogism','An argument with exactly two premises and a conclusion. All three are categorical statements, it uses exactly three terms, each term appears in two of the statements, and the major premise comes first.','All violas are string instruments. Some heirlooms are violas. So, some heirlooms are string instruments.'],
  mmm:['Major, minor, and middle terms','The major term (P) is the predicate of the conclusion, and the minor term (S) is its subject. The middle term (M) appears in both premises but not in the conclusion. The major premise is the one containing the major term.','In the viola argument, “string instruments” is major, “heirlooms” is minor, and “violas” is middle.'],
  mood:['Mood','The letters of the major premise, minor premise, and conclusion, in that order.','The viola argument has mood AII.'],
  figure:['Figure','A number from 1 to 4 that records where the middle term sits. 1: subject of the major premise, predicate of the minor. 2: predicate of both. 3: subject of both. 4: predicate of the major, subject of the minor.','The viola argument is in figure 1, so its form is AII-1.'],
  valid:['Validity','An argument is valid when its conclusion must be true whenever its premises are. Validity depends on the form, not on whether the premises are actually true.','“All dragons are reptiles. All reptiles are cold-blooded animals. So, all dragons are cold-blooded animals” is valid, even though dragons don’t exist.'],
  readings:['Boolean and Aristotelian readings','The Boolean (modern) reading doesn’t assume that classes have members, so a universal statement makes no claim that anything exists. The Aristotelian reading assumes the classes being discussed have at least one member. This app uses the Boolean reading unless you switch.','On the Boolean reading, “All unicorns are white” doesn’t imply “Some unicorns are white.” On the Aristotelian reading, it does.'],
  square:['Square of opposition','A diagram of the logical relations among the A, E, I, and O statements that share a subject and predicate. A and E sit at the top corners, I and O at the bottom.',''],
  contradictories:['Contradictories','A and O, and E and I. They always have opposite truth values. This holds on both readings.','If “All tulips are red” is false, then “Some tulips are not red” is true.'],
  contraries:['Contraries (Aristotelian only)','A and E. They can’t both be true, but they can both be false.','“All rivers are long” and “No rivers are long” are both false.'],
  subcontraries:['Subcontraries (Aristotelian only)','I and O. They can’t both be false, but they can both be true.','“Some apples are sour” and “Some apples are not sour” are both true.'],
  subalternation:['Subalternation (Aristotelian only)','A to I and E to O. Truth passes down from the universal to the particular, and falsity passes up from the particular to the universal.','If “All kites are light” is true, so is “Some kites are light.”'],
  boolsq:['The Boolean square','On the Boolean reading only the contradictories hold. If there were no S at all, “All S are P” and “No S are P” would both be true, while “Some S are P” and “Some S are not P” would both be false.',''],
  undet:['Undetermined','A statement’s truth value is undetermined when what you know is consistent both with its being true and with its being false.',''],
  immediate:['Immediate inference','An inference from one categorical statement straight to another, with no second premise.','From “No owls are reptiles” to “No reptiles are owls.”'],
  complement:['Complement','The complement of a class is everything that isn’t in it. We name it with “non-”.','The complement of “metals” is “non-metals.”'],
  conversion:['Conversion','Swap the subject and predicate terms. The converse is equivalent to the original for E and I statements only.','“Some poets are bakers” converts to “Some bakers are poets.”'],
  obversion:['Obversion','Change the quality (affirmative to negative, or negative to affirmative) and replace the predicate with its complement. The obverse is equivalent to the original for all four forms.','“All metals are conductors” obverts to “No metals are non-conductors.”'],
  contraposition:['Contraposition','Swap the subject and predicate terms and replace each with its complement. The contrapositive is equivalent to the original for A and O statements only.','“All metals are conductors” becomes “All non-conductors are non-metals.”'],
  equivalent:['Equivalent statements','Two statements are equivalent when they must have the same truth value. Their Venn diagrams look exactly alike.',''],
};
const G_STMT={h:'Statements', items:[D.prop,D.terms,D.qq,D.forms,D.dist,D.venn]};
const G_SYL={h:'Syllogisms', items:[D.syl,D.mmm,D.mood,D.figure,D.valid]};
const G_READ={h:'Readings', items:[D.readings]};
const G_SQ={h:'Square of opposition', items:[D.square,D.contradictories,D.contraries,D.subcontraries,D.subalternation,D.boolsq,D.undet]};
const G_INF={h:'Immediate inferences', items:[D.immediate,D.complement,D.conversion,D.obversion,D.contraposition,D.equivalent]};

// =====================================================================
// Venn geometry
// =====================================================================
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

// =====================================================================
// Level card, home icon, module hub
// =====================================================================
registerLevel({num:1, title:'Intro to logic', topics:[
  {title:'Categorical logic', sub:'Statements, the square of opposition, immediate inferences, syllogisms', go:'cat'},
  {title:'Fallacies', sub:'Spot the mistake in everyday arguments', go:'fal'},
]});
App.heroIcon = () => vennSVG(3,{state:{3:1,7:1}}).replace('class="venn"','class="venn" aria-hidden="true"');

const soFar = k => { const s=score(k); return s.done?` ${s.right} of ${s.done} correct so far.`:''; };
function catView(){
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Categorical logic</h2>
  <p class="muted">Statements about classes, and the arguments built from them.</p>
  ${keyDefs([G_STMT,G_SQ,G_INF,G_SYL,G_READ])}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-go="stmt"><span>Diagram a statement<small>Name the form (A, E, I, O), then draw it.${soFar('stmt')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="square"><span>Square of opposition<small>Given one statement’s truth value, work out the others.${soFar('sq')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="infer"><span>Immediate inferences<small>Converse, obverse, contrapositive: which is which, and which are equivalent?${soFar('inf')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="syl"><span>Test a syllogism<small>Mood and figure, diagram, valid or invalid.${soFar('syl')}</small></span><span class="go">Practice</span></button></li>
    <li><button class="topic open" data-go="names"><span>Named forms<small>Barbara, Celarent, Darii, Ferio, and the rest</small></span><span class="go">View</span></button></li>
  </ul>
  ${readingSeg()}
  <p class="muted" style="font-size:.9rem">Diagrams use the Boolean reading. The reading setting affects the square of opposition and syllogism validity.</p>`;
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
  <p class="hint muted">These 9 forms are valid only if the listed term refers to at least one thing. On the Boolean reading they’re invalid.</p>
  <div class="forms"><table><thead><tr><th>Name</th><th>Form</th><th>Must exist</th></tr></thead><tbody>${cond.map(row).join('')}</tbody></table></div>`;
}

// =====================================================================
// Statement exercise
// =====================================================================
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
  ${keyDefs([G_STMT])}
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
function correctStmt(e){ return diagramPremises([{type:e.type,a:'S',b:'P'}], false); }
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

// =====================================================================
// Square of opposition exercise
// =====================================================================
function squareSVG(r){
  const ar=r==='aristotelian';
  const P={A:[50,36],E:[270,36],I:[50,184],O:[270,184]};
  const ln=(a,b,on)=>`<line x1="${P[a][0]}" y1="${P[a][1]}" x2="${P[b][0]}" y2="${P[b][1]}" style="stroke:${on?'var(--ink)':'var(--line)'}" stroke-width="${on?2:1.6}" ${on?'':'stroke-dasharray="5 5"'}/>`;
  const lab=(x,y,t,on,rot)=>`<text x="${x}" y="${y}" text-anchor="middle" ${rot?`transform="rotate(-90 ${x} ${y})"`:''} style="fill:${on?'var(--ink)':'var(--muted)'};font-family:var(--sans);font-size:12px">${t}</text>`;
  const corner=k=>`<circle cx="${P[k][0]}" cy="${P[k][1]}" r="17" style="fill:var(--surface);stroke:var(--ink)" stroke-width="1.8"/><text x="${P[k][0]}" y="${P[k][1]+7}" text-anchor="middle" style="fill:var(--ink);font-family:var(--serif);font-size:20px;font-weight:600">${k}</text>`;
  return `<svg viewBox="0 0 320 220" role="img" aria-label="Square of opposition. ${ar?'All four relations hold on the Aristotelian reading.':'Only the contradictories (the diagonals) hold on the Boolean reading.'}">
    ${ln('A','E',ar)}${ln('I','O',ar)}${ln('A','I',ar)}${ln('E','O',ar)}${ln('A','O',true)}${ln('E','I',true)}
    ${lab(160,28,'contraries',ar)}${lab(160,206,'subcontraries',ar)}${lab(30,110,'subalternation',ar,true)}${lab(298,110,'subalternation',ar,true)}
    <rect x="112" y="99" width="96" height="20" rx="4" style="fill:var(--surface)"/>${lab(160,113,'contradictories',true)}
    ${corner('A')}${corner('E')}${corner('I')}${corner('O')}</svg>`;
}
function newSquare(){
  return {t:pick(TERMS), g:pick('AEIO'.split('')), gv:Math.random()<.5, picks:{}, checked:false, reading:reading()};
}
const TV = {T:'True', F:'False', '?':'Undetermined'};
const vword = b => b?'true':'false';
function squareWhy(e, t){
  const g=e.g, gv=e.gv, rel=relation(g,t), S=esc(e.t.S);
  if(rel==='contradictories') return `${g} and ${t} are contradictories: they always have opposite truth values. Since ${g} is ${vword(gv)}, ${t} is ${vword(!gv)}.`;
  if(e.reading==='boolean'){
    const ar=squareTruth(g,gv,t,'aristotelian');
    if(ar!=='?'){
      const emptyVal = t==='A'||t==='E';
      return `On the Aristotelian reading ${t} would be ${ar==='T'?'true':'false'}, but that depends on there being at least one of the ${S}. The Boolean reading doesn’t assume that. If there were no ${S} at all, ${g} would still be ${vword(gv)}, but ${t} would be ${vword(emptyVal)}. So ${t} is undetermined.`;
    }
    return `Only contradictories hold on the Boolean reading, and ${g} and ${t} aren’t contradictories. (Even on the Aristotelian reading, knowing ${g} is ${vword(gv)} leaves ${t} undetermined.)`;
  }
  if(rel==='contraries') return gv ? `${g} and ${t} are contraries: they can’t both be true. Since ${g} is true, ${t} is false.`
    : `${g} and ${t} are contraries: they can’t both be true, but both can be false. Knowing ${g} is false leaves ${t} undetermined.`;
  if(rel==='subcontraries') return gv ? `${g} and ${t} are subcontraries: they can’t both be false, but both can be true. Knowing ${g} is true leaves ${t} undetermined.`
    : `${g} and ${t} are subcontraries: they can’t both be false. Since ${g} is false, ${t} is true.`;
  const up = g==='A'||g==='E'; // given is the universal (superaltern)
  if(up) return gv ? `${g} implies ${t} by subalternation: truth passes down. If ${g} is true (and there are ${S}), ${t} is true.`
    : `Subalternation passes falsity up, not down. ${g} being false leaves ${t} undetermined.`;
  return gv ? `Subalternation passes truth down, not up. ${g} being true leaves ${t} undetermined.`
    : `Falsity passes up by subalternation: if ${g} is false, the universal ${t} above it is false too.`;
}
function squareView(){
  const e=App.ex, T=e.t, others='AEIO'.split('').filter(k=>k!==e.g);
  const rows=others.map(k=>{
    const ans=squareTruth(e.g,e.gv,k,e.reading), mine=e.picks[k];
    const btn=v=>{ let c='choice'; if(e.checked){ if(v===ans) c+=' right'; else if(v===mine) c+=' wrong'; } else if(v===mine) c+=' picked';
      return `<button class="${c}" data-sq="${k}" data-val="${v}" ${e.checked?'disabled':''}>${TV[v]}</button>`; };
    const fb = e.checked ? `<div class="fb ${mine===ans?'good':'bad'}"><strong>${mine===ans?'Correct':'It’s '+TV[ans].toLowerCase()}.</strong>${squareWhy(e,k)}</div>` : '';
    return `<div class="sq-row"><span class="fam-tag">${k}</span> <span class="sent">${esc(FORMS[k].say(T.S,T.P))}</span><div class="tri">${btn('T')}${btn('F')}${btn('?')}</div>${fb}</div>`;
  }).join('');
  const all=others.every(k=>e.picks[k]);
  const sc=score('sq');
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <div class="ex-head"><h2>Square of opposition</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([G_SQ,G_READ])}
  ${readingSeg()}
  <div class="square">${squareSVG(e.reading)}</div>
  <p class="prop">Suppose “${esc(FORMS[e.g].say(T.S,T.P)).slice(0,-1)}” is <b>${vword(e.gv)}</b>.</p>
  <p class="hint muted">That’s an ${e.g} statement. Mark each statement below as true, false, or undetermined on the ${e.reading==='boolean'?'Boolean':'Aristotelian'} reading.</p>
  <div class="sq-rows">${rows}</div>
  <div class="actions"><button class="btn" data-act="check-sq" ${all&&!e.checked?'':'disabled'}>Check</button></div>
  <div class="next"><button class="btn" data-act="next">Next statement</button></div>`;
}

// =====================================================================
// Immediate inference exercise
// =====================================================================
const OPS = {converse:'converse', obverse:'obverse', contrapositive:'contrapositive'};
const OP_EQUIV = {converse:'EI', obverse:'AEIO', contrapositive:'AO'};
const termLabel = (T, x) => x[0]==='!' ? 'non-'+T[x[1]] : T[x];
const saySt = (T, s) => FORMS[s.type].say(termLabel(T,s.a), termLabel(T,s.b));
function newInfer(){
  const type=pick('AEIO'.split('')), op=pick(Object.keys(OPS));
  const choices=shuffle(['converse','obverse','contrapositive','inverse']);
  return {t:pick(TERMS), type, op, choices, pick:null, eq:null, counted:false};
}
function inferWhy(e){
  const T=e.t, S=esc(T.S), P=esc(T.P), ty=e.type, op=e.op;
  if(op==='obverse') return `Obversion flips the quality and swaps ${P} for non-${P}. Being outside ${P} is the same as being inside non-${P}, so the obverse always says the same thing as the original.`;
  if(op==='converse'){
    if(ty==='E') return `“No ${S} are ${P}” and “No ${P} are ${S}” both say the overlap of the two circles is empty. Swapping the terms changes nothing, so they’re equivalent.`;
    if(ty==='I') return `“Some ${S} are ${P}” and “Some ${P} are ${S}” both put an X in the overlap. Swapping the terms changes nothing, so they’re equivalent.`;
    if(ty==='A') return `“All ${S} are ${P}” says nothing is in ${S} outside ${P}. The converse says nothing is in ${P} outside ${S}, which is a different area. All the ${S} could be among the ${P} while plenty of ${P} aren’t ${S}, so they’re not equivalent.`;
    return `“Some ${S} are not ${P}” puts an X in ${S} outside ${P}. The converse puts it in ${P} outside ${S}, a different area, so they’re not equivalent.`;
  }
  if(ty==='A') return `Both “All ${S} are ${P}” and “All non-${P} are non-${S}” rule out the same thing: something that’s one of the ${S} but not one of the ${P}. So they’re equivalent.`;
  if(ty==='O') return `Both “Some ${S} are not ${P}” and its contrapositive say there’s something that’s one of the ${S} but not one of the ${P}. So they’re equivalent.`;
  if(ty==='E') return `“No ${S} are ${P}” says the overlap is empty. Its contrapositive, “No non-${P} are non-${S},” says nothing is outside both circles, which is a different area. So they’re not equivalent.`;
  return `“Some ${S} are ${P}” puts an X in the overlap. Its contrapositive, “Some non-${P} are non-${S},” puts an X outside both circles, a different area. So they’re not equivalent.`;
}
const OP_HOW = {converse:'Swap the subject and predicate.', obverse:'Change the quality and replace the predicate with its complement.', contrapositive:'Swap the subject and predicate, and replace each with its complement.', inverse:''};
function inferView(){
  const e=App.ex, T=e.t, orig={type:e.type,a:'S',b:'P'};
  const correctEq = OP_EQUIV[e.op].includes(e.type);
  const opts=e.choices.map((c,i)=>{ let cls='choice'; if(e.pick){ if(c===e.op) cls+=' right'; else if(c===e.pick) cls+=' wrong'; }
    return `<button class="${cls}" data-inf="${c}" ${e.pick?'disabled':''}>${esc(saySt(T,transform(e.type,c)))}</button>`; }).join('');
  let pfb='';
  if(e.pick){
    const ok=e.pick===e.op;
    const what = e.pick==='inverse' ? 'That one complements both terms without swapping them, which isn’t any of the three standard inferences.'
      : `That one is the ${e.pick}.`;
    pfb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'}</strong>${ok?'':what+' '}To form the ${e.op}: ${OP_HOW[e.op].toLowerCase()}</div>`;
  }
  let efb='';
  if(e.eq!==null){
    const ok=e.eq===correctEq;
    efb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'} The ${e.op} ${correctEq?'is':'isn’t'} equivalent.</strong>${inferWhy(e)} <span class="muted">Rule of thumb: conversion works for E and I, contraposition for A and O, obversion for all four.</span></div>`;
  }
  const yn=(v,l)=>{ let c='choice'; if(e.eq!==null){ if(v===correctEq) c+=' right'; else if(v===e.eq) c+=' wrong'; } return `<button class="${c}" data-eq="${v}" ${e.eq!==null?'disabled':''}>${l}</button>`; };
  const sc=score('inf');
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <div class="ex-head"><h2>Immediate inferences</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([G_INF])}
  <p class="prop">${esc(saySt(T,orig))}</p>
  <section class="step"><h3>Which statement is its ${e.op}?</h3><div class="choices one">${opts}</div>${pfb}</section>
  <section class="step"><h3>Is the ${e.op} equivalent to the original?</h3><div class="choices">${yn(true,'Yes, equivalent')}${yn(false,'No, not equivalent')}</div>${efb}</section>
  <div class="next"><button class="btn" data-act="next">Next statement</button></div>`;
}

// =====================================================================
// Syllogism exercise
// =====================================================================
function newSyl(){
  let mood, fig, d;
  do{
    const roll=Math.random();
    if(roll<.45){ const f=pick(VALID_BOOLEAN); mood=f.slice(0,3); fig=+f[4]; }
    else if(roll<.6){ const f=pick(Object.keys(NAMES).filter(k=>NAMES[k].needs)); mood=f.slice(0,3); fig=+f[4]; }
    else { mood=[0,0,0].map(()=>pick('AEIO'.split(''))).join(''); fig=1+Math.floor(Math.random()*4); }
    d=diagramPremises(syllogismParts(mood,fig).slice(0,2), true);
  } while(!d);
  return {t:pick(TERMS), mood, fig, d, pickMood:['','',''], pickFig:'', mfChecked:false, state:{1:0,2:0,3:0,4:0,5:0,6:0,7:0}, checked:false, valid:null, counted:false, reading:reading()};
}
function sylView(){
  const e=App.ex, parts=syllogismParts(e.mood,e.fig), T=e.t;
  const say=p=>FORMS[p.type].say(T[p.a],T[p.b]);
  const correctValid=validFor(e.mood,e.fig,e.reading);
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
    vfb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct.':'Not quite.'} It’s ${correctValid?'valid':'invalid'} on the ${e.reading==='boolean'?'Boolean':'Aristotelian'} reading.</strong>${validWhy(e,parts[2],correctValid)}${nameNote(e)}</div>`;
  }
  const vbtn=(v,l)=>{ let c='choice'; if(e.valid!==null){ if(v===correctValid) c+=' right'; else if(v===e.valid) c+=' wrong'; } return `<button class="${c}" data-valid="${v}" ${e.valid!==null?'disabled':''}>${l}</button>`; };
  const sc=score('syl');
  return `<button class="back" data-go="cat">‹ Categorical logic</button>
  <div class="ex-head"><h2>Test a syllogism</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${keyDefs([G_SYL,G_READ])}
  ${readingSeg()}
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
  <section class="step"><h3>Valid or invalid?</h3><p class="hint">${e.reading==='boolean'?'Valid means the premise diagram already shows the conclusion.':'Valid means the conclusion must be true if the premises are, assuming each of S, P, and M has at least one member.'}</p>
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
function booleanWhy(e, c, valid){
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
function validWhy(e, c, valid){
  const boolValid=isValid(e.d,c);
  if(e.reading==='boolean' || boolValid) return booleanWhy(e,c,boolValid);
  if(!valid) return booleanWhy(e,c,false)+' Assuming each term has members doesn’t change that.';
  const n=NAMES[formKey(e)], need=n&&n.needs;
  if(!need) return ' Once we assume every term has members, the conclusion follows.';
  const open=regionList(true).filter(r=>has(r,need)&&!e.d.shaded.has(r));
  const where=open.length===1?` Only one area of ${need} is left unshaded (${regionName(open[0],true)}), so something must be there.`:'';
  return ` The diagram alone doesn’t show the conclusion, but the Aristotelian reading assumes there’s at least one ${esc(e.t[need])} (${need}).${where} That supplies the X the conclusion needs.`;
}

// =====================================================================
// Events for the categorical exercises
// =====================================================================
function catClick(ev){
  const ex=App.ex, view=App.view;
  const f=ev.target.closest('[data-form]');
  if(f && view==='stmt' && !ex.form){ ex.form=f.dataset.form; tally('stmt', ex.form===ex.type); render(); return; }
  const v=ev.target.closest('[data-valid]');
  if(v && view==='syl' && ex.valid===null){ ex.valid=v.dataset.valid==='true'; tally('syl', ex.valid===validFor(ex.mood,ex.fig,ex.reading)); render(); return; }
  const sq=ev.target.closest('[data-sq]');
  if(sq && view==='square' && !ex.checked){ ex.picks[sq.dataset.sq]=sq.dataset.val; render(); return; }
  const inf=ev.target.closest('[data-inf]');
  if(inf && view==='infer' && !ex.pick){ ex.pick=inf.dataset.inf; inferTally(ex); render(); return; }
  const eq=ev.target.closest('[data-eq]');
  if(eq && view==='infer' && ex.eq===null){ ex.eq=eq.dataset.eq==='true'; inferTally(ex); render(); return; }
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
    if(act==='check-sq'){ ex.checked=true; tally('sq','AEIO'.split('').filter(k=>k!==ex.g).every(k=>ex.picks[k]===squareTruth(ex.g,ex.gv,k,ex.reading))); render(); return; }
  }
  const svg=ev.target.closest('svg.venn.live');
  if(svg){
    const n=+svg.dataset.n, pt=svg.createSVGPoint(); pt.x=ev.clientX; pt.y=ev.clientY;
    const p=pt.matrixTransform(svg.getScreenCTM().inverse());
    const r=regionAt(n,p.x,p.y); if(!r) return;
    ex.state[r]=((ex.state[r]||0)+1)%3; ex.checked=false; render();
  }
}
function inferTally(ex){
  if(ex.counted || !ex.pick || ex.eq===null) return;
  ex.counted=true; tally('inf', ex.pick===ex.op && ex.eq===OP_EQUIV[ex.op].includes(ex.type));
}
function sylChange(ev){
  const ex=App.ex;
  if(ev.target.dataset.mood!==undefined) ex.pickMood[+ev.target.dataset.mood]=ev.target.value;
  if(ev.target.dataset.fig!==undefined) ex.pickFig=ev.target.value;
}
// Switching the reading mid-exercise: keep an unanswered exercise, start fresh if it was already graded.
function onReading(answered){
  return (name)=>{ if(name!=='reading') return; const ex=App.ex; if(answered(ex)) App.ex=VIEWS[App.view].init(); else ex.reading=reading(); };
}

registerView('cat',    {render: catView});
registerView('names',  {render: namesView});
registerView('stmt',   {init: newStmt,   render: stmtView,   click: catClick});
registerView('square', {init: newSquare, render: squareView, click: catClick, onSetting: onReading(ex=>ex.checked)});
registerView('infer',  {init: newInfer,  render: inferView,  click: catClick});
registerView('syl',    {init: newSyl,    render: sylView,    click: catClick, change: sylChange, onSetting: onReading(ex=>ex.valid!==null)});

// =====================================================================
// Fallacies (original passages; families follow Knachel ch. 2)
// =====================================================================
const FAMILIES = {
  distraction:{name:'Fallacies of distraction', short:'Distraction', def:'The premises pull attention away from the real question, toward feelings, people, threats, or a different topic.'},
  weak:{name:'Fallacies of weak induction', short:'Weak induction', def:'The premises are about the right topic, but they’re far too weak to support the conclusion.'},
  presumption:{name:'Fallacies of illicit presumption', short:'Illicit presumption', def:'The argument quietly depends on an assumption that hasn’t been earned.'},
  linguistic:{name:'Fallacies of linguistic emphasis', short:'Linguistic emphasis', def:'The argument works by exploiting or slanting language: a word used two ways, a quote with its context cut away, or loaded phrasing.'},
  formal:{name:'Formal fallacies', short:'Formal', def:'The mistake is in the argument’s logical form, so any argument with the same form fails the same way.'},
};
// near: closest wrong answers, each with why it doesn't fit (these are the distractors offered).
const FALLACIES = [
 {id:'emotion', name:'Appeal to emotion', fam:'distraction', def:'Trying to win agreement by stirring up feelings such as pity, fear, or pride instead of giving reasons that bear on the claim.',
  near:{force:'An appeal to force threatens a consequence for disagreeing. Nobody is threatened here; the passage just works on your feelings.', bandwagon:'Bandwagon points to how many people believe something. Here the pull is emotional, not popularity.', redherring:'A red herring switches to another topic. Here the topic stays the same, but feelings take the place of evidence.', framing:'Manipulative framing slants how a fact is described. Here no fact is reworded; the passage paints an emotional picture instead.'},
  ex:[
   {p:'Please don’t give me a C on this essay, Professor. I stayed up all night, my cat is sick, and my parents will be so disappointed. I really deserve at least a B.', why:'Every reason is about how sad the situation is. None of them is about the quality of the essay, which is what the grade should depend on.'},
   {p:'Picture your little brother walking home alone after dark. Now ask yourself whether you can really vote against more streetlights on Elm Road.', why:'Instead of evidence that streetlights help or are worth the cost, the passage asks you to imagine a frightening scene.'},
   {p:'This phone was designed by people who believe in you. Buy it, and find out what it feels like to finally be the person you were meant to be.', why:'Nothing is said about the phone’s features or price. The ad tries to attach good feelings to buying it.'},
  ]},
 {id:'force', name:'Appeal to force', fam:'distraction', def:'Pressuring someone to accept a claim by hinting at harm or loss if they don’t, instead of showing that the claim is true.',
  near:{emotion:'An appeal to emotion stirs up feelings in general. This passage specifically threatens a consequence for disagreeing.', abusive:'Ad hominem attacks the person making an argument. Here the speaker threatens the listener rather than insulting anyone.', redherring:'A red herring changes the subject. Here the subject stays the same, but the only “reason” is a threat.'},
  ex:[
   {p:'I think you’ll agree the new schedule is a great idea, Dana. After all, performance reviews are next week.', why:'The only “reason” is a hint that Dana’s review could suffer, which has nothing to do with whether the schedule is good.'},
   {p:'Of course the club should keep me as treasurer. Remember, I’m the one with the keys to the equipment room.', why:'The speaker hints that the club could lose its equipment. That’s a threat, not a reason they’re a good treasurer.'},
   {p:'You might want to rethink that one-star review of my bakery. My cousin writes for the local paper, and people pay attention to what he says about businesses in town.', why:'The baker hints that bad press will follow. That threatens the reviewer instead of answering the review.'},
  ]},
 {id:'abusive', name:'Ad hominem (abusive)', fam:'distraction', def:'Rejecting an argument by insulting or attacking the character of the person who gives it.',
  near:{circumstantial:'A circumstantial ad hominem points to what the person stands to gain. Here the attack is on their character or habits, not their interests.', tuquoque:'Tu quoque accuses the person of hypocrisy. There’s no claim here that they fail to practice what they preach.', strawman:'A straw man distorts the argument. Here the argument isn’t described at all; only the person is attacked.'},
  ex:[
   {p:'Why would anyone listen to Jordan’s plan for the parking lot? He can’t even keep his own car clean.', why:'The plan is dismissed because of a personal flaw that has nothing to do with whether the plan is any good.'},
   {p:'The new coach says we need more conditioning drills, but she’s a know-it-all who never smiles, so I’m not buying it.', why:'The coach’s personality is attacked instead of her reasons for more drills.'},
   {p:'My neighbor thinks the town should start recycling glass. Then again, he’s the guy who wears socks with sandals, so I wouldn’t take him seriously.', why:'A jab at the neighbor’s fashion is offered as a reason to doubt his view on recycling.'},
  ]},
 {id:'circumstantial', name:'Ad hominem (circumstantial)', fam:'distraction', def:'Rejecting an argument by pointing to the arguer’s circumstances, such as what they stand to gain, instead of assessing their reasons.',
  near:{abusive:'Abusive ad hominem insults someone’s character. Here the point is the arguer’s situation or interests, not their character.', tuquoque:'Tu quoque says the arguer doesn’t follow their own advice. Here the point is that they’d benefit, not that they’re inconsistent.', authority:'Appeal to unqualified authority relies on a source. Here a source is being dismissed, not relied on.'},
  ex:[
   {p:'Of course the dentist says we should floss every day. She makes money when people care about their teeth.', why:'The advice is rejected because of the dentist’s interests, without checking whether flossing actually helps.'},
   {p:'The student council president says the school needs a longer lunch break. Well, naturally. He’s a student.', why:'Being a student is treated as a reason to dismiss the argument, but a student could still have good reasons.'},
   {p:'That study showing bike lanes reduce accidents was written by researchers who ride bikes to work. I’d ignore it.', why:'The researchers’ circumstances are used to dismiss the study instead of examining its evidence.'},
  ]},
 {id:'tuquoque', name:'Tu quoque (“you too”)', fam:'distraction', def:'Rejecting someone’s argument or advice because they don’t act consistently with it themselves.',
  near:{abusive:'Abusive ad hominem insults character in general. This passage specifically points out that the person doesn’t follow their own advice.', circumstantial:'Circumstantial ad hominem points to what the arguer gains. This passage points to their inconsistent behavior instead.', redherring:'A red herring moves to an unrelated issue. Here the reply turns the advice back on the person who gave it.'},
  ex:[
   {p:'My dad told me I should stop drinking so much soda. But he drinks two cans a day, so why should I listen?', why:'Dad’s habits don’t change whether soda is bad for you. His advice could be good even if he ignores it.'},
   {p:'You’re telling me to put my phone away during dinner? You were texting all through my recital last week!', why:'The speaker points out the other person’s inconsistency instead of responding to the request.'},
   {p:'The mayor wants everyone to save water, but I’ve seen her sprinklers running at noon. The water restrictions are obviously pointless.', why:'The mayor’s hypocrisy doesn’t show anything about whether the restrictions are needed.'},
  ]},
 {id:'strawman', name:'Straw man', fam:'distraction', def:'Misrepresenting someone’s position as weaker or more extreme than it is, then attacking that distorted version.',
  near:{redherring:'A red herring changes the subject. A straw man stays on topic but attacks a distorted version of the other person’s view.', slipperyslope:'A slippery slope predicts an unsupported chain of consequences. A straw man changes what the opponent actually said.', abusive:'Ad hominem attacks the person. A straw man attacks a misstated version of their view.', quoting:'Quoting out of context uses the person’s real words with the context cut away. A straw man restates their view in a distorted way.'},
  ex:[
   {p:'Maya suggested the cafeteria offer one vegetarian option each day. So apparently she wants to ban meat and make everyone eat lettuce.', why:'Maya asked for one option a day, but her view is replaced by an extreme one that’s easy to mock.'},
   {p:'My roommate says we should split the chores more evenly. I guess he thinks I’m his personal servant who should do whatever he says.', why:'A request for fairness is twisted into a demand for servitude, and that distorted version is what gets rejected.'},
   {p:'The council member wants to study whether the park needs more lighting. So she thinks our town is a crime-ridden wasteland? Ridiculous.', why:'A proposal to study lighting is turned into a claim that the town is dangerous, and that distortion is what gets attacked.'},
  ]},
 {id:'redherring', name:'Red herring', fam:'distraction', def:'Shifting attention to a different issue, so the original question gets dropped without being answered.',
  near:{strawman:'A straw man attacks a distorted version of the other side’s view. A red herring leaves the view alone and changes the topic.', emotion:'An appeal to emotion stays on the topic but swaps evidence for feelings. A red herring moves to a different topic.', tuquoque:'Tu quoque shifts to the critic’s own behavior. A red herring shifts to an unrelated issue.'},
  ex:[
   {p:'Some parents say the school bus leaves too early. But what about the students who skip breakfast entirely? That’s the real problem we should be talking about.', why:'The question about the bus schedule is dropped, and attention moves to a different issue.'},
   {p:'Critics say our restaurant’s prices went up too much. But have you seen our new patio? It’s the nicest outdoor seating in town.', why:'The patio has nothing to do with whether the price increase is fair. It pulls attention elsewhere.'},
   {p:'Yes, my essay was late, but think about how much the library hours have been cut this year. Somebody should write to the administration about that.', why:'The late essay is the issue. The library hours are a different topic, used to steer away from it.'},
  ]},
 {id:'bandwagon', name:'Appeal to the people (bandwagon)', fam:'distraction', def:'Arguing that a claim is true, or a choice is good, because lots of people believe it or do it.',
  near:{authority:'Appeal to unqualified authority relies on one person’s say-so. Bandwagon relies on popularity.', emotion:'A general appeal to emotion works on feelings like pity or fear. Bandwagon specifically uses the pull of what everyone else thinks.', hasty:'A hasty generalization draws a conclusion from too few cases. Bandwagon treats popularity itself as the evidence.'},
  ex:[
   {p:'Everyone at school is getting these sneakers, so they must be the best ones out there.', why:'Popularity is offered as proof of quality, but lots of people can like something that isn’t the best.'},
   {p:'Millions of people use this sleep app, so it must really work.', why:'The number of users doesn’t show the app improves sleep. That takes evidence about results.'},
   {p:'Most of the people in my group chat think the moon landing was staged, so there’s probably something to it.', why:'How many people believe a claim isn’t evidence that it’s true.'},
  ]},
 {id:'ignorance', name:'Appeal to ignorance', fam:'weak', def:'Concluding that a claim is true because it hasn’t been proven false, or false because it hasn’t been proven true.',
  near:{hasty:'A hasty generalization uses too little evidence. An appeal to ignorance uses no evidence at all, only the lack of a disproof.', begging:'Begging the question assumes the conclusion. An appeal to ignorance rests on the absence of evidence against it.', falsedilemma:'A false dilemma offers too few options. An appeal to ignorance treats “not disproven” as “proven.”'},
  ex:[
   {p:'Nobody has ever proven that my lucky socks don’t help me win games, so I’m going to keep wearing them.', why:'The lack of a disproof is treated as support, but no evidence shows the socks help.'},
   {p:'No one has shown that the new cafeteria pizza is unhealthy, so it must be good for you.', why:'Having no evidence that something is unhealthy doesn’t show that it’s healthy.'},
   {p:'Scientists haven’t found life on any other planet, so we know for sure that we’re alone in the universe.', why:'Not having found life yet doesn’t prove there is none. The search is nowhere near complete.'},
  ]},
 {id:'authority', name:'Appeal to unqualified authority', fam:'weak', def:'Accepting a claim because someone says so, when that person has no special expertise on the topic.',
  near:{bandwagon:'Bandwagon relies on how many people believe something. This passage relies on one person who isn’t an expert on the topic.', circumstantial:'Circumstantial ad hominem dismisses a source because of their interests. This passage leans on a source rather than dismissing one.', hasty:'A hasty generalization generalizes from a few cases. This passage takes one person’s word on a topic outside their field.'},
  ex:[
   {p:'My favorite pop star says vitamin C cures colds, and she’s sold millions of albums, so I’m taking it.', why:'Being a successful singer doesn’t make someone an expert on medicine.'},
   {p:'The guy who runs my favorite gaming channel says the stock market will crash next month, so I’m selling everything.', why:'A gaming streamer isn’t a qualified source on financial forecasts.'},
   {p:'A famous quarterback says this mattress is the best thing for your back, so it must be.', why:'Football skill isn’t expertise in spinal health, and he’s likely being paid to say it.'},
  ]},
 {id:'hasty', name:'Hasty generalization', fam:'weak', def:'Drawing a broad conclusion about a group from a sample that’s too small or unrepresentative.',
  near:{posthoc:'Post hoc assumes one event caused another because it came first. A hasty generalization draws a broad conclusion from a few cases.', accident:'Accident applies a general rule to an exception. A hasty generalization goes the other way, from a few cases to a general rule.', analogy:'A weak analogy compares two different things. A hasty generalization stretches a few examples to cover a whole group.'},
  ex:[
   {p:'I’ve been to that pizza chain twice, and both times the service was slow. Every one of their restaurants must have terrible service.', why:'Two visits to one location are far too few to judge every restaurant in the chain.'},
   {p:'My two cousins who went to that college both hated it, so it’s obviously a bad school.', why:'Two students’ experiences are a tiny sample of everyone who goes there.'},
   {p:'The first three songs on this album were boring. This band has never made a good song.', why:'A few songs from one album don’t represent everything the band has made.'},
  ]},
 {id:'posthoc', name:'False cause (post hoc)', fam:'weak', def:'Concluding that one event caused another just because it happened first.',
  near:{hasty:'A hasty generalization stretches a few examples into a rule. Post hoc claims a cause just because of the order of events.', slipperyslope:'A slippery slope predicts a future chain of events. Post hoc claims something already happened because of what came before it.', ignorance:'An appeal to ignorance relies on the lack of a disproof. Post hoc relies on timing.'},
  ex:[
   {p:'I washed my car this morning, and this afternoon it rained. Washing my car makes it rain.', why:'Rain after a car wash is a coincidence. The order of events doesn’t make one cause the other.'},
   {p:'After the school painted the hallways blue, test scores went up. The blue paint must have helped students focus.', why:'Scores could have risen for many reasons. Coming after the paint job doesn’t show the paint caused it.'},
   {p:'I started drinking green tea in January, and I haven’t had a cold since. Green tea must prevent colds.', why:'Staying healthy might be luck or the season. Timing alone doesn’t establish a cause.'},
  ]},
 {id:'slipperyslope', name:'Slippery slope', fam:'weak', def:'Claiming that a small first step will lead, through a chain of events, to an extreme result, without good reason to think each link will happen.',
  near:{strawman:'A straw man distorts what someone actually proposed. A slippery slope accepts the proposal as stated but predicts a runaway chain of consequences.', posthoc:'Post hoc says an earlier event caused a later one. A slippery slope predicts a future chain of events.', falsedilemma:'A false dilemma offers only two options. A slippery slope claims one small step will snowball.'},
  ex:[
   {p:'If we let students use calculators on this quiz, next they’ll want them on every test, then nobody will learn arithmetic, and soon no one will be able to make change at a store.', why:'Each step is just asserted. Nothing shows that allowing calculators once leads to the extreme outcome.'},
   {p:'If I let my little sister borrow my sweater, she’ll start taking my shoes, then my phone, and before long she’ll have moved into my room.', why:'Lending one sweater doesn’t make the rest of the chain likely. Each link is assumed, not shown.'},
   {p:'If the town allows one food truck downtown, soon the streets will be packed with them, every restaurant will close, and downtown will be one big parking lot.', why:'The passage jumps from one food truck to the end of downtown without support for any of the steps.'},
  ]},
 {id:'analogy', name:'Weak analogy', fam:'weak', def:'Arguing that because two things are alike in some ways, they must be alike in another way, when the similarities don’t matter for that conclusion.',
  near:{hasty:'A hasty generalization draws a rule from too few cases. A weak analogy compares two things that differ in the ways that matter.', composition:'Composition reasons from parts to the whole. A weak analogy reasons from one thing to a different thing that’s only superficially similar.', equivocation:'Equivocation uses one word in two senses. A weak analogy compares two things that aren’t really alike.'},
  ex:[
   {p:'Employees are like nails: you have to hit them on the head to get them to work. So managers should be harsh.', why:'People and nails have almost nothing relevant in common, so the comparison gives no reason to think harshness works.'},
   {p:'A school is like a business, and businesses fire workers who don’t produce. So schools should expel students with low grades.', why:'Schools and businesses differ in exactly the way that matters here: students are there to learn, not to produce.'},
   {p:'My old phone and this new one are both black and made by the same company. My old phone lasted five years, so this one will too.', why:'Color and brand aren’t the features that decide how long a phone lasts.'},
  ]},
 {id:'begging', name:'Begging the question', fam:'presumption', def:'Assuming the very thing the argument is supposed to prove, often by restating the conclusion in different words.',
  near:{loaded:'A loaded question smuggles an assumption into a question. Begging the question builds the conclusion into the premises of an argument.', ignorance:'An appeal to ignorance leans on the lack of evidence against a claim. Begging the question leans on the claim itself.', falsedilemma:'A false dilemma limits the options. Begging the question assumes the answer.'},
  ex:[
   {p:'This website is trustworthy, because it says right on the homepage that all of its information is reliable.', why:'Using the site to vouch for itself assumes it’s trustworthy, which is the very point in question.'},
   {p:'Taking naps is good for you, because resting during the day is healthy.', why:'The premise just restates the conclusion in other words, so it gives no independent support.'},
   {p:'Our team is the best in the league, because no other team is as good as we are.', why:'“No team is as good as us” is the same claim as “we’re the best,” so nothing has been shown.'},
  ]},
 {id:'falsedilemma', name:'False dilemma', fam:'presumption', def:'Presenting two options as if they were the only possibilities, when others exist.',
  near:{slipperyslope:'A slippery slope predicts a chain of consequences. A false dilemma pretends there are only two options.', begging:'Begging the question assumes the conclusion. A false dilemma assumes that the options on the table are the only ones.', loaded:'A loaded question presupposes something unproven. A false dilemma leaves out options.'},
  ex:[
   {p:'Either you play on the varsity team or you don’t really care about soccer.', why:'Plenty of people care about soccer without playing varsity. The two options leave out many others.'},
   {p:'We either cancel the field trip completely or we risk someone getting lost. Those are our only choices.', why:'There are middle options, like more chaperones or a buddy system.'},
   {p:'If you don’t buy the most expensive laptop, you’ll end up with one that’s useless.', why:'There are lots of good laptops between “most expensive” and “useless.”'},
  ]},
 {id:'loaded', name:'Loaded question', fam:'presumption', def:'Asking a question that presupposes something unproven, so any direct answer seems to grant it.',
  near:{begging:'Begging the question builds the conclusion into an argument’s premises. A loaded question hides an assumption inside a question.', falsedilemma:'A false dilemma offers only two options. A loaded question makes every direct answer admit something.', strawman:'A straw man misstates someone’s view. A loaded question presupposes something about them that hasn’t been shown.'},
  ex:[
   {p:'Have you stopped copying your friends’ homework?', why:'Whether you answer yes or no, you admit you copied homework, which hasn’t been established.'},
   {p:'Why is our mayor so bad at managing money?', why:'The question takes for granted that the mayor manages money badly.'},
   {p:'How much did you pay the referee to win that game?', why:'The question presupposes the referee was paid off.'},
  ]},
 {id:'composition', name:'Composition', fam:'presumption', def:'Concluding that a whole has a property because its parts have it.',
  near:{division:'Division goes from the whole to its parts. Composition goes from the parts to the whole.', hasty:'A hasty generalization goes from a few members to the whole group. Composition goes from the parts of one thing to that thing as a whole.', analogy:'A weak analogy compares two separate things. Composition reasons from parts to the whole they make up.'},
  ex:[
   {p:'Every player on our team is a great athlete, so our team is definitely going to be great.', why:'Great individuals don’t guarantee a great team. Teamwork and fit matter too.'},
   {p:'Each ingredient in this recipe tastes good on its own, so the dish will taste amazing.', why:'Good ingredients can make a bad combination. The whole doesn’t simply inherit the flavor of its parts.'},
   {p:'Every brick in this wall is light, so the whole wall must be light.', why:'Lots of light bricks together can be very heavy.'},
  ]},
 {id:'division', name:'Division', fam:'presumption', def:'Concluding that each part has a property because the whole has it.',
  near:{composition:'Composition goes from the parts to the whole. Division goes from the whole to its parts.', accident:'Accident applies a general rule to an exceptional case. Division assumes each part shares a property of the whole.', hasty:'A hasty generalization goes from a few cases to a whole group, the opposite direction.'},
  ex:[
   {p:'Our school is huge, so every classroom in it must be huge.', why:'A big school can have small rooms. The size of the whole doesn’t pass down to its parts.'},
   {p:'That orchestra is world-famous, so its second-chair violinist must be world-famous too.', why:'An orchestra can be famous without each of its members being famous.'},
   {p:'This city is very wealthy, so everyone who lives there must be rich.', why:'A city’s total wealth says little about each resident. It can be unevenly spread.'},
  ]},
 {id:'accident', name:'Accident', fam:'presumption', def:'Applying a general rule to a special case that the rule wasn’t meant to cover.',
  near:{hasty:'A hasty generalization creates a rule from too few cases. Accident takes a sensible rule and applies it where it doesn’t fit.', division:'Division assumes the parts share a property of the whole. Accident misapplies a rule to an exception.', equivocation:'Equivocation shifts the meaning of a word. Accident keeps the rule’s meaning but ignores an obvious exception.'},
  ex:[
   {p:'You’re supposed to be quiet in the library, so the librarian shouldn’t shout “Fire!” even if the building is burning.', why:'The quiet rule is a general guideline. An emergency is an exception it was never meant to cover.'},
   {p:'People should always keep their promises. I promised to drive my friend home, so I should drive even though my medicine makes me drowsy.', why:'Promise-keeping is a good general rule, but not when keeping the promise would be dangerous.'},
   {p:'Exercise is good for you, so my brother should go running even with a broken ankle.', why:'“Exercise is good for you” assumes normal health. A broken ankle is the kind of exception the rule ignores.'},
  ]},
 {id:'equivocation', name:'Equivocation', fam:'linguistic', def:'Using a word or phrase in two different senses within one argument, so the reasoning only seems to work.',
  near:{quoting:'Quoting out of context cuts away what surrounds someone’s words. Equivocation shifts the meaning of a single word.', framing:'Manipulative framing picks slanted words to describe facts. Equivocation uses one word in two different senses.', analogy:'A weak analogy compares two things that aren’t alike. Equivocation trades on two meanings of one word.'},
  ex:[
   {p:'The sign says “Fine for parking here,” so it must be fine to park here.', why:'On the sign, “fine” means a penalty. In the conclusion it means “okay.”'},
   {p:'The newspaper said the senator’s speech was critical of the new highway plan. “Critical” means extremely important, so the senator thinks the plan is extremely important.', why:'“Critical of” means disapproving. The conclusion switches to the other sense, “crucial.”'},
   {p:'Everyone has a right to free speech, so it’s always right to say whatever you want.', why:'The first “right” means a legal entitlement. The second means morally correct.'},
  ]},
 {id:'quoting', name:'Quoting out of context', fam:'linguistic', def:'Presenting a quotation stripped of the words around it so that it seems to say something the speaker didn’t mean.',
  near:{strawman:'A straw man restates someone’s view in a distorted way. Quoting out of context uses their actual words but cuts away what gave them meaning.', equivocation:'Equivocation shifts the meaning of one word. Quoting out of context removes the surrounding words.', framing:'Manipulative framing describes facts in slanted language. Quoting out of context trims a quotation.'},
  ex:[
   {p:'A review said, “The special effects are amazing, but everything else about the movie is a disaster.” The poster outside the theater reads: “Amazing!”', why:'One word is lifted from a negative review, making it look like praise.'},
   {p:'My brother told Mom I said, “I hate school.” What I actually said was, “I hate school when the cafeteria runs out of pizza.”', why:'Dropping the second half turns a small complaint into a sweeping one.'},
   {p:'The principal said, “Phones are a problem only when students use them during tests.” The school paper’s headline: “Principal: Phones Are a Problem.”', why:'The headline cuts the qualifier that limited the principal’s point.'},
  ]},
 {id:'framing', name:'Manipulative framing', fam:'linguistic', def:'Describing facts in slanted language, or from a carefully chosen angle, to push the audience toward a conclusion.',
  near:{emotion:'An appeal to emotion paints a moving picture. Manipulative framing rewords the same facts to make them look better or worse.', equivocation:'Equivocation uses one word in two senses. Manipulative framing picks wording to slant how facts look.', quoting:'Quoting out of context trims someone’s words. Manipulative framing chooses how to describe facts.'},
  ex:[
   {p:'Which would you rather have: a surgery with a 90% survival rate, or one with a 10% death rate? Our clinic only offers the first kind!', why:'Those are the same statistic. The clinic makes its surgery sound better just by how the fact is phrased.'},
   {p:'Don’t think of it as spending $40 on concert tickets. Think of it as investing in memories that will last a lifetime.', why:'Calling a purchase an “investment” slants the description to make the spending sound wise.'},
   {p:'This ice cream is 80% fat-free, so it’s practically a health food.', why:'“80% fat-free” means 20% fat, which is a lot. The framing makes a high number sound healthy.'},
  ]},
 {id:'affirming', name:'Affirming the consequent', fam:'formal', def:'Reasoning “If P, then Q. Q. So, P.” The conclusion doesn’t follow, because Q could be true for some other reason.',
  near:{denying:'Denying the antecedent reasons “If P, then Q. Not P. So, not Q.” This argument affirms the “then” part instead.', posthoc:'Post hoc reasons from the order of events. This argument has a conditional premise and reasons backward from its “then” part.', hasty:'A hasty generalization stretches a few cases into a rule. This argument’s problem is its form.'},
  ex:[
   {p:'If it snowed last night, the roads are slippery. The roads are slippery. So it snowed last night.', why:'Slippery roads could come from rain or ice. The “then” part being true doesn’t show the “if” part is.'},
   {p:'If Sam studied, he passed the exam. Sam passed. So he must have studied.', why:'Sam might have passed for other reasons, like already knowing the material.'},
   {p:'If my phone is broken, it won’t turn on. It won’t turn on. So it’s broken.', why:'A dead battery would also keep it from turning on.'},
  ]},
 {id:'denying', name:'Denying the antecedent', fam:'formal', def:'Reasoning “If P, then Q. Not P. So, not Q.” The conclusion doesn’t follow, because Q could still be true for some other reason.',
  near:{affirming:'Affirming the consequent reasons “If P, then Q. Q. So, P.” This argument denies the “if” part instead.', falsedilemma:'A false dilemma limits the options to two. This argument’s problem is its form: it assumes the “if” part is the only route to the “then” part.', hasty:'A hasty generalization draws a rule from too few cases. This argument’s problem is its form.'},
  ex:[
   {p:'If you run a red light, you’ll get a ticket. Lena didn’t run a red light, so she won’t get a ticket.', why:'Lena could still get a ticket for speeding or parking. The rule only names one way to get a ticket.'},
   {p:'If it’s a holiday, the library is closed. Today isn’t a holiday, so the library is open.', why:'The library might be closed for other reasons, like repairs or late hours.'},
   {p:'If I eat dessert, I’ll feel full. I’m not eating dessert, so I won’t feel full.', why:'Plenty of other food could still make you full.'},
  ]},
];
const FBY = Object.fromEntries(FALLACIES.map(f=>[f.id,f]));

const DF = {
  argument:['Argument','A set of statements in which some (the premises) are offered as reasons to believe another (the conclusion).','“The bus is late every Monday, and today is Monday, so the bus will probably be late.”'],
  fallacy:['Fallacy','A common pattern of bad reasoning: an argument whose premises don’t give the support they seem to.',''],
  formal:['Formal fallacy','A mistake in the argument’s structure. You can spot it from the form alone, whatever the argument is about.','“If it’s a cat, it has fur. It has fur. So it’s a cat.”'],
  informal:['Informal fallacy','A mistake you can only spot by looking at what the argument says, such as irrelevant premises, weak evidence, or a hidden assumption.','“You can’t trust her opinion on movies. She failed algebra.”'],
};
function falDefs(){
  const fams=['distraction','weak','presumption','linguistic'].map(k=>[FAMILIES[k].name, FAMILIES[k].def]);
  return keyDefs([{items:[DF.argument,DF.fallacy,DF.formal,DF.informal]},{h:'The four families of informal fallacies', items:fams}]);
}
function falGuide(){
  const body=Object.keys(FAMILIES).map(k=>`<h4>${FAMILIES[k].name}</h4><dl>${FALLACIES.filter(f=>f.fam===k).map(f=>`<dt>${f.name}</dt><dd>${f.def}</dd>`).join('')}</dl>`).join('');
  return `<details class="defs"><summary>Fallacy guide</summary><div class="defs-body">${body}</div></details>`;
}
function falView(){
  const famBtn=k=>{ const n=FALLACIES.filter(f=>f.fam===k).length;
    return `<li><button class="topic open" data-fam="${k}"><span>${FAMILIES[k].short}<small>${n} fallacies. ${FAMILIES[k].def}</small></span><span class="go">Study</span></button></li>`; };
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Fallacies</h2>
  <p class="muted">Read a short passage and name the mistake in its reasoning.</p>
  ${falDefs()}
  ${falGuide()}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-fam="all"><span>Mixed practice<small>All ${FALLACIES.length} fallacies.${soFar('fal')}</small></span><span class="go">Practice</span></button></li>
  </ul>
  <h3 class="section-title">Study by family</h3>
  <ul class="topics" style="margin-top:10px">${Object.keys(FAMILIES).map(famBtn).join('')}</ul>`;
}
let falFamily='all', falRecent=[];
function falChoices(f){
  const near=Object.keys(f.near);
  let ds=shuffle(near).slice(0,3);
  const pool=shuffle(FALLACIES.filter(x=>x.id!==f.id && !ds.includes(x.id)));
  pool.sort((a,b)=>(b.fam===f.fam)-(a.fam===f.fam));
  while(ds.length<3) ds.push(pool.shift().id);
  return shuffle([f.id,...ds]);
}
function newFal(){
  const list=FALLACIES.filter(f=>falFamily==='all'||f.fam===falFamily);
  const all=[]; list.forEach(f=>f.ex.forEach((_,i)=>all.push([f.id,i])));
  const fresh=all.filter(([id,i])=>!falRecent.includes(id+i));
  const [id,i]=pick(fresh.length?fresh:all);
  falRecent.push(id+i); if(falRecent.length>Math.min(12, all.length-1)) falRecent.shift();
  return {f:FBY[id], i, choices:falChoices(FBY[id]), pick:null};
}
function falWhyNot(f, otherId){
  const o=FBY[otherId];
  return f.near[otherId] || `${o.name} means ${o.def.charAt(0).toLowerCase()+o.def.slice(1)} That isn’t what this passage does.`;
}
function falqView(){
  const e=App.ex, f=e.f, x=f.ex[e.i];
  const btns=e.choices.map(id=>{ let c='choice'; if(e.pick){ if(id===f.id) c+=' right'; else if(id===e.pick) c+=' wrong'; }
    return `<button class="${c}" data-fal="${id}" ${e.pick?'disabled':''}>${FBY[id].name}</button>`; }).join('');
  let fb='';
  if(e.pick){
    const ok=e.pick===f.id;
    const other = ok ? e.choices.find(id=>id!==f.id && f.near[id]) || e.choices.find(id=>id!==f.id) : e.pick;
    fb=`<div class="fb ${ok?'good':'bad'}"><strong>${ok?'Correct':'It’s '+f.name.charAt(0).toLowerCase()+f.name.slice(1)}${ok?`: ${f.name}.`:'.'}</strong>${x.why}
      <p style="margin-top:8px"><b>Why not ${FBY[other].name.charAt(0).toLowerCase()+FBY[other].name.slice(1)}?</b> ${falWhyNot(f,other)}</p>
      <p class="muted" style="margin-top:8px">${f.name}: ${f.def}</p></div>`;
  }
  const sc=score('fal');
  const label = falFamily==='all' ? 'Mixed practice' : FAMILIES[falFamily].short;
  return `<button class="back" data-go="fal">‹ Fallacies</button>
  <div class="ex-head"><h2>Name the fallacy</h2><span class="score">${sc.right}/${sc.done}</span></div>
  <span class="fam-tag">${label}</span>
  <blockquote class="passage">${esc(x.p)}</blockquote>
  <section class="step"><h3>Which fallacy is this?</h3><div class="choices one">${btns}</div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next passage</button></div>`;
}
function falClick(ev){
  const fam=ev.target.closest('[data-fam]');
  if(fam){ falFamily=fam.dataset.fam; falRecent=[]; go('falq'); return; }
  const c=ev.target.closest('[data-fal]'), e=App.ex;
  if(c && e && !e.pick){ e.pick=c.dataset.fal; tally('fal', e.pick===e.f.id); render(); }
}
registerView('fal',  {render: falView, click: falClick});
registerView('falq', {init: newFal, render: falqView, click: falClick});

// Exposed for tests/ (pure logic and content checks).
Engines.categorical = {syllogismParts, diagramPremises, isValid, validFor, validWith, squareTruth, relation, transform, equivalentStatements,
  correctStmt:type=>correctStmt({type}), correctState, diffRegions, VALID_BOOLEAN, NAMES, OP_EQUIV};
Engines.fallacies = {FALLACIES, FAMILIES, falChoices};
})();
