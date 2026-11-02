// Therefore — Level 3: Predicate logic.
// Modules: Quantifiers (symbolization) and Quantifier derivations (∀E, ∀I, ∃I, ∃E added to the
// Level 2 proof checker). Quantifiers are always written (∀x) and (∃x).
// Content is original; definitions are based on forall x: Calgary (CC BY 4.0).
(function(){
'use strict';
const L = Shared.logic, DV = Shared.derivations, SYM = L.SYM, VARS = L.VARS;
const P = s => L.parse(s, {ql:true});
const show = L.show;

// =====================================================================
// Semantics: interpretations with small finite domains
// =====================================================================
// An interpretation: domain {0..n-1}; each predicate's extension is a bitmask over tuples
// (tuple (d1,...,dk) has index d1 + d2*n + ...); each constant names an element.
function signature(f, out={preds:{}, consts:new Set(), clash:null}){
  if(f.t==='atom'){
    const k=(f.args||[]).length;
    if(f.n in out.preds && out.preds[f.n]!==k) out.clash=f.n; else out.preds[f.n]=k;
    (f.args||[]).forEach(a=>{ if(!VARS.includes(a)) out.consts.add(a); });
  } else if(f.t==='not'||f.t==='all'||f.t==='some') signature(f.a,out);
  else { signature(f.l,out); signature(f.r,out); }
  return out;
}
function evalQ(f, I, env){
  switch(f.t){
    case 'atom': { let idx=0, m=1; for(const a of (f.args||[])){ idx+=(VARS.includes(a)?env[a]:I.c[a])*m; m*=I.n; } return ((I.ext[f.n]/Math.pow(2,idx))|0)%2===1; }
    case 'not': return !evalQ(f.a,I,env);
    case 'and': return evalQ(f.l,I,env) && evalQ(f.r,I,env);
    case 'or': return evalQ(f.l,I,env) || evalQ(f.r,I,env);
    case 'cond': return !evalQ(f.l,I,env) || evalQ(f.r,I,env);
    case 'bicond': return evalQ(f.l,I,env) === evalQ(f.r,I,env);
    case 'all': for(let d=0;d<I.n;d++) if(!evalQ(f.a,I,Object.assign({},env,{[f.v]:d}))) return false; return true;
    case 'some': for(let d=0;d<I.n;d++) if(evalQ(f.a,I,Object.assign({},env,{[f.v]:d}))) return true; return false;
  }
}
// Calls cb(I) for every interpretation of the given predicates and constants, domain sizes 1..maxN.
// Stops early (returning that interpretation) when cb returns true.
function forEachInterp(preds, consts, maxN, cb){
  const pl=Object.entries(preds);
  for(let n=1;n<=maxN;n++){
    const radices=pl.map(([,k])=>Math.pow(2,Math.pow(n,k))).concat(consts.map(()=>n));
    const idx=radices.map(()=>0);
    for(;;){
      const I={n, ext:{}, c:{}};
      pl.forEach(([p],i)=>I.ext[p]=idx[i]); consts.forEach((c,j)=>I.c[c]=idx[pl.length+j]);
      if(cb(I)) return I;
      let k=0; while(k<radices.length){ idx[k]++; if(idx[k]<radices[k]) break; idx[k]=0; k++; }
      if(k===radices.length) break;
    }
  }
  return null;
}
// Equivalence on every interpretation with a domain of 1 to 3 objects.
function qlCompare(f, g, maxN=3){
  const s1=signature(f), s2=signature(g), preds=Object.assign({}, s1.preds, s2.preds), consts=[...new Set([...s1.consts, ...s2.consts])].sort();
  const counter=forEachInterp(preds, consts, maxN, I=>evalQ(f,I,{})!==evalQ(g,I,{}));
  return {equiv:!counter, counter, preds, consts};
}
function describeInterp(I, preds, consts){
  const D=[...Array(I.n).keys()].map(d=>d+1);
  const parts=[`domain {${D.join(', ')}}`];
  Object.entries(preds).sort().forEach(([p,k])=>{
    if(k===0){ parts.push(`${p} is ${(I.ext[p]&1)?'true':'false'}`); return; }
    const members=[]; const total=Math.pow(I.n,k);
    for(let t=0;t<total;t++) if(((I.ext[p]/Math.pow(2,t))|0)%2===1){ const tup=[]; let r=t; for(let i=0;i<k;i++){ tup.push(r%I.n+1); r=(r/I.n)|0; } members.push(k===1?tup[0]:`⟨${tup.join(',')}⟩`); }
    parts.push(`${p} = {${members.join(', ')}}`);
  });
  consts.forEach(c=>parts.push(`${c} = ${I.c[c]+1}`));
  return parts.join('; ');
}

// =====================================================================
// Symbolization content (original). Key: predicates "Fx: …", constants "a: …"
// =====================================================================
// [level, English, domain, key, model answer]
const QS = [
 [1,'Everything is fragile.','things',{F:'x is fragile'},'(∀x)Fx'],
 [1,'Something is broken.','things',{B:'x is broken'},'(∃x)Bx'],
 [1,'Nothing is perfect.','things',{P:'x is perfect'},'~(∃x)Px'],
 [1,'Not everything is free.','things',{F:'x is free'},'~(∀x)Fx'],
 [1,'All dogs are loyal.','animals',{D:'x is a dog',L:'x is loyal'},'(∀x)(Dx ⊃ Lx)'],
 [1,'Some cats are orange.','animals',{C:'x is a cat',O:'x is orange'},'(∃x)(Cx & Ox)'],
 [1,'No snakes are friendly.','animals',{S:'x is a snake',F:'x is friendly'},'(∀x)(Sx ⊃ ~Fx)'],
 [1,'Some birds can’t fly.','animals',{B:'x is a bird',F:'x can fly'},'(∃x)(Bx & ~Fx)'],
 [1,'Not all fish swim in schools.','animals',{F:'x is a fish',S:'x swims in a school'},'~(∀x)(Fx ⊃ Sx)'],
 [1,'Ana is a pilot.','people',{P:'x is a pilot',a:'Ana'},'Pa'],
 [1,'If Ben is late, everyone waits.','people',{L:'x is late',W:'x waits',b:'Ben'},'Lb ⊃ (∀x)Wx'],
 [1,'Only members can vote.','people',{M:'x is a member',V:'x can vote'},'(∀x)(Vx ⊃ Mx)'],
 [1,'Every student passed.','people',{S:'x is a student',P:'x passed'},'(∀x)(Sx ⊃ Px)'],
 [1,'Someone in the class speaks Spanish.','people in the class',{S:'x speaks Spanish'},'(∃x)Sx'],
 [1,'Everything in the box is red or blue.','things in the box',{R:'x is red',B:'x is blue'},'(∀x)(Rx ∨ Bx)'],
 [1,'Some apples aren’t ripe.','fruit',{A:'x is an apple',R:'x is ripe'},'(∃x)(Ax & ~Rx)'],
 [1,'Not every athlete is fast.','people',{A:'x is an athlete',F:'x is fast'},'~(∀x)(Ax ⊃ Fx)'],
 [1,'There are no free lunches.','meals',{L:'x is a lunch',F:'x is free'},'~(∃x)(Lx & Fx)'],
 [2,'All red apples are sweet.','fruit',{R:'x is red',A:'x is an apple',S:'x is sweet'},'(∀x)((Rx & Ax) ⊃ Sx)'],
 [2,'Some students are tired but happy.','people',{S:'x is a student',T:'x is tired',H:'x is happy'},'(∃x)(Sx & (Tx & Hx))'],
 [2,'Every dog that barks is awake.','animals',{D:'x is a dog',B:'x barks',A:'x is awake'},'(∀x)((Dx & Bx) ⊃ Ax)'],
 [2,'Only teachers and staff may enter.','people',{T:'x is a teacher',S:'x is on the staff',E:'x may enter'},'(∀x)(Ex ⊃ (Tx ∨ Sx))'],
 [2,'If anyone cheats, everyone loses.','players',{C:'x cheats',L:'x loses'},'(∃x)Cx ⊃ (∀x)Lx'],
 [2,'If Dana is a chef, then some chefs are tall.','people',{C:'x is a chef',T:'x is tall',d:'Dana'},'Cd ⊃ (∃x)(Cx & Tx)'],
 [2,'Every bike is either new or repaired.','things',{B:'x is a bike',N:'x is new',R:'x is repaired'},'(∀x)(Bx ⊃ (Nx ∨ Rx))'],
 [2,'No singer is both shy and famous.','people',{S:'x is a singer',Y:'x is shy',F:'x is famous'},'(∀x)(Sx ⊃ ~(Yx & Fx))'],
 [2,'Some movies are long and boring, but not every long movie is boring.','things',{M:'x is a movie',L:'x is long',B:'x is boring'},'(∃x)(Mx & (Lx & Bx)) & ~(∀x)((Mx & Lx) ⊃ Bx)'],
 [2,'Everyone who studies passes, and Eli studies.','people',{S:'x studies',P:'x passes',e:'Eli'},'(∀x)(Sx ⊃ Px) & Se'],
 [2,'Neither Ann nor Bo is a doctor, but someone is.','people',{D:'x is a doctor',a:'Ann',b:'Bo'},'(~Da & ~Db) & (∃x)Dx'],
 [2,'All plants need water or sunlight.','living things',{P:'x is a plant',W:'x needs water',S:'x needs sunlight'},'(∀x)(Px ⊃ (Wx ∨ Sx))'],
 [2,'A ticket is valid only if it’s stamped.','things',{T:'x is a ticket',V:'x is valid',S:'x is stamped'},'(∀x)((Tx & Vx) ⊃ Sx)'],
 [2,'Nobody who is late gets a seat.','people',{L:'x is late',S:'x gets a seat'},'(∀x)(Lx ⊃ ~Sx)'],
 [2,'Every cat is a mammal, but some mammals aren’t cats.','animals',{C:'x is a cat',M:'x is a mammal'},'(∀x)(Cx ⊃ Mx) & (∃x)(Mx & ~Cx)'],
 [2,'Everything is a plant or an animal, but nothing is both.','living things',{P:'x is a plant',A:'x is an animal'},'(∀x)(Px ∨ Ax) & ~(∃x)(Px & Ax)'],
 [2,'Some pies are made with apples, and all of those are delicious.','food',{P:'x is a pie',A:'x is made with apples',D:'x is delicious'},'(∃x)(Px & Ax) & (∀x)((Px & Ax) ⊃ Dx)'],
 [3,'Ana knows everyone.','people',{K:'x knows y',a:'Ana'},'(∀x)Kax'],
 [3,'Everyone knows Ana.','people',{K:'x knows y',a:'Ana'},'(∀x)Kxa'],
 [3,'Someone knows everyone.','people',{K:'x knows y'},'(∃x)(∀y)Kxy'],
 [3,'Everyone knows someone.','people',{K:'x knows y'},'(∀x)(∃y)Kxy'],
 [3,'There’s someone whom everyone knows.','people',{K:'x knows y'},'(∃y)(∀x)Kxy'],
 [3,'Nobody knows everyone.','people',{K:'x knows y'},'~(∃x)(∀y)Kxy'],
 [3,'Every student respects some teacher.','people',{S:'x is a student',T:'x is a teacher',R:'x respects y'},'(∀x)(Sx ⊃ (∃y)(Ty & Rxy))'],
 [3,'Some teacher is respected by every student.','people',{S:'x is a student',T:'x is a teacher',R:'x respects y'},'(∃y)(Ty & (∀x)(Sx ⊃ Rxy))'],
 [3,'No student respects every teacher.','people',{S:'x is a student',T:'x is a teacher',R:'x respects y'},'~(∃x)(Sx & (∀y)(Ty ⊃ Rxy))'],
 [3,'Bo likes everyone who likes him.','people',{L:'x likes y',b:'Bo'},'(∀x)(Lxb ⊃ Lbx)'],
 [3,'Everyone likes someone who doesn’t like them back.','people',{L:'x likes y'},'(∀x)(∃y)(Lxy & ~Lyx)'],
 [3,'Every dog chases some cat.','animals',{D:'x is a dog',C:'x is a cat',H:'x chases y'},'(∀x)(Dx ⊃ (∃y)(Cy & Hxy))'],
 [3,'Some cat chases every dog.','animals',{D:'x is a dog',C:'x is a cat',H:'x chases y'},'(∃x)(Cx & (∀y)(Dy ⊃ Hxy))'],
 [3,'No dog chases itself.','animals',{D:'x is a dog',H:'x chases y'},'(∀x)(Dx ⊃ ~Hxx)'],
 [3,'Anyone who helps everyone is helped by someone.','people',{H:'x helps y'},'(∀x)((∀y)Hxy ⊃ (∃y)Hyx)'],
 [3,'If Cal trusts anyone, he trusts Dee.','people',{T:'x trusts y',c:'Cal',d:'Dee'},'(∃x)Tcx ⊃ Tcd'],
 [3,'Everybody admires somebody who admires them.','people',{A:'x admires y'},'(∀x)(∃y)(Axy & Ayx)'],
 [3,'There’s a book that every student has read.','people and books',{B:'x is a book',S:'x is a student',R:'x has read y'},'(∃y)(By & (∀x)(Sx ⊃ Rxy))'],
 [3,'Every student has read some book.','people and books',{B:'x is a book',S:'x is a student',R:'x has read y'},'(∀x)(Sx ⊃ (∃y)(By & Rxy))'],
 [3,'Ana is older than everyone who is older than Bo.','people',{O:'x is older than y',a:'Ana',b:'Bo'},'(∀x)(Oxb ⊃ Oax)'],
 [3,'Some people don’t trust anyone.','people',{T:'x trusts y'},'(∃x)~(∃y)Txy'],
].map(([lv,en,domain,key,ans],id)=>({id, lv, en, domain, key, ans}));
const arity = desc => new Set(desc.match(/\b[xyz]\b/g)||[]).size;
function keyInfo(item){
  const preds={}, consts=[];
  Object.entries(item.key).forEach(([k,v])=>{ if(/[A-Z]/.test(k)) preds[k]=arity(v); else consts.push(k); });
  return {preds, consts};
}

// Small changes to the model answer that match common mistakes.
function qMutations(f){
  const out=[], clone=x=>JSON.parse(JSON.stringify(x));
  const rec=(node, rebuild)=>{
    const add=(kind, g)=>out.push({kind, f:rebuild(g)});
    if(node.t==='all'){
      add('quantType', {t:'some', v:node.v, a:node.a});
      if(node.a.t==='cond'){ add('allAnd', {t:'all', v:node.v, a:{t:'and', l:node.a.l, r:node.a.r}}); }
      if((node.a.t==='all'||node.a.t==='some') && node.a.t!==node.t) add('order', {t:node.a.t, v:node.a.v, a:{t:node.t, v:node.v, a:node.a.a}});
      if(node.a.t==='not') add('negScope', {t:'not', a:{t:'all', v:node.v, a:node.a.a}});
    }
    if(node.t==='some'){
      add('quantType', {t:'all', v:node.v, a:node.a});
      if(node.a.t==='and') add('someCond', {t:'some', v:node.v, a:{t:'cond', l:node.a.l, r:node.a.r}});
      if((node.a.t==='all'||node.a.t==='some') && node.a.t!==node.t) add('order', {t:node.a.t, v:node.a.v, a:{t:node.t, v:node.v, a:node.a.a}});
      if(node.a.t==='not') add('negScope', {t:'not', a:{t:'some', v:node.v, a:node.a.a}});
    }
    if(node.t==='not' && (node.a.t==='all'||node.a.t==='some')) add('negScope', {t:node.a.t, v:node.a.v, a:{t:'not', a:node.a.a}});
    // "Not every F is G" misread as "every F is not G" (and the same for "not some")
    if(node.t==='not' && node.a.t==='all' && node.a.a.t==='cond') add('negScope', {t:'all', v:node.a.v, a:{t:'cond', l:node.a.a.l, r:{t:'not', a:node.a.a.r}}});
    if(node.t==='not' && node.a.t==='some' && node.a.a.t==='and') add('negScope', {t:'some', v:node.a.v, a:{t:'and', l:node.a.a.l, r:{t:'not', a:node.a.a.r}}});
    if(node.t==='cond') add('reverse', {t:'cond', l:node.r, r:node.l});
    if(node.t==='not') add('dropneg', node.a);
    if(node.t==='not'||node.t==='all'||node.t==='some') rec(node.a, n=>rebuild(Object.assign(clone(node),{a:n})));
    else if(node.t!=='atom'){ rec(node.l, n=>rebuild({t:node.t,l:n,r:node.r})); rec(node.r, n=>rebuild({t:node.t,l:node.l,r:n})); }
  };
  rec(f, n=>n);
  return out;
}
function qMistakeMsg(kind, en){
  const lo=en.toLowerCase(), A='(∀x)', E='(∃x)';
  switch(kind){
    case 'allAnd': return `With “all” or “every,” use ${SYM.cond} inside the quantifier: ${A}(Fx ${SYM.cond} Gx) says every F is G. ${A}(Fx ${SYM.and} Gx) says everything is both F and G.`;
    case 'someCond': return `With “some,” use ${SYM.and} inside the quantifier: ${E}(Fx ${SYM.and} Gx). ${E}(Fx ${SYM.cond} Gx) is true as soon as anything at all isn’t F, so it says almost nothing.`;
    case 'quantType': return 'Check your quantifier: one of your ∀s and ∃s should be the other kind. “All,” “every,” and “any” usually mean ∀; “some” and “a” usually mean ∃.';
    case 'order': return 'The order of the quantifiers matters. (∀x)(∃y)Rxy says each x has its own y. (∃y)(∀x)Rxy says one single y works for every x.';
    case 'negScope': return `Watch where the negation goes. “Not all F are G” is ${SYM.not}${A}(Fx ${SYM.cond} Gx), but “no F are G” is ${A}(Fx ${SYM.cond} ${SYM.not}Gx).`;
    case 'reverse':
      if(/\bonly\b/.test(lo)) return `You reversed the conditional. “Only F are G” means every G is an F: ${A}(Gx ${SYM.cond} Fx). The word after “only” goes on the right.`;
      return `You reversed a conditional. In “All F are G,” the F part is the antecedent: ${A}(Fx ${SYM.cond} Gx).`;
    case 'dropneg': return `You’re missing a negation (${SYM.not}) somewhere, or have an extra one. Look for “no,” “not,” “n’t,” and “nobody.”`;
  }
}
function checkQ(item, src){
  const p=L.tryParse(src,{ql:true}); if(p.err) return {err:p.err};
  const fv=[...DV_freeVars(p.f)];
  if(fv.length) return {err:`The variable ${fv.join(', ')} isn’t bound by any quantifier. Add a quantifier, like (∀${fv[0]}), or use a constant.`};
  const k=keyInfo(item), s=signature(p.f);
  if(s.clash) return {err:`${s.clash} is used with different numbers of terms.`};
  for(const [pr,ar] of Object.entries(s.preds)){
    if(!(pr in k.preds)) return {err:`${pr} isn’t in the symbolization key.`};
    if(k.preds[pr]!==ar) return {err:`${pr} takes ${k.preds[pr]} term${k.preds[pr]===1?'':'s'} (like ${pr}${'xyz'.slice(0,k.preds[pr])}), but you gave it ${ar}.`};
  }
  for(const c of s.consts) if(!k.consts.includes(c)) return {err:`“${c}” isn’t a constant in the key. ${k.consts.length?`Use ${k.consts.join(', ')}.`:'This sentence doesn’t need any names.'}`};
  const model=P(item.ans), cmp=qlCompare(p.f, model);
  if(cmp.equiv) return {ok:true, exact:L.eq(p.f,model), f:p.f};
  const m=qMutations(model).find(x=>!qlCompare(x.f,model).equiv && qlCompare(p.f,x.f).equiv);
  const I=cmp.counter, yours=evalQ(p.f,I,{});
  return {ok:false, f:p.f, mistake:m?qMistakeMsg(m.kind,item.en):null,
    counter:`In this situation — ${describeInterp(I,cmp.preds,cmp.consts)} — the English sentence is ${yours?'false':'true'}, but your answer is ${yours?'true':'false'}.`};
}
const DV_freeVars = f => Engines.derivations.freeVars(f);

// ----- Key definitions (original wording, based on forall x: Calgary) -----
const QD = () => [
  {items:[
    ['Predicate','A capital letter that says something about one or more objects. The key shows how many by using variables.','Fx: x is fragile. Rxy: x respects y.'],
    ['Constant','A lowercase letter (a through w) that names exactly one object in the domain.','a: Ana. Then Pa says “Ana is a pilot.”'],
    ['Variable','x, y, or z. A variable doesn’t name anything by itself; it’s a placeholder that a quantifier gives meaning to.',''],
    ['Domain','The collection of things the quantifiers range over. Every symbolization key says what the domain is.','If the domain is people, (∀x)Hx says everyone is happy.'],
    ['Universal quantifier (∀x)','“For every x in the domain.” (∀x)Fx is true when every object in the domain is F.','(∀x)(Dx ⊃ Lx): every dog is loyal.'],
    ['Existential quantifier (∃x)','“There is at least one x in the domain such that.” (∃x)Fx is true when at least one object is F.','(∃x)(Cx & Ox): some cat is orange.'],
    ['Scope','The part of a sentence a quantifier governs: the shortest complete formula right after it.',`In (∀x)Fx ⊃ Ga, the scope of (∀x) is just Fx. In (∀x)(Fx ⊃ Gx), it’s the whole parenthesized part.`],
    ['Bound and free variables','A variable is bound when it falls within the scope of a quantifier using the same variable; otherwise it’s free. A sentence has no free variables.','In (∃x)Rxy, x is bound and y is free, so it isn’t a sentence yet.'],
  ]},
  {h:'Common patterns', items:[
    ['All F are G',`(∀x)(Fx ⊃ Gx). Use ⊃, not &, with “all.”`,''],
    ['Some F are G',`(∃x)(Fx & Gx). Use &, not ⊃, with “some.”`,''],
    ['No F are G',`(∀x)(Fx ⊃ ~Gx), or equivalently ~(∃x)(Fx & Gx).`,''],
    ['Not all F are G',`~(∀x)(Fx ⊃ Gx), or equivalently (∃x)(Fx & ~Gx).`,''],
    ['Only F are G',`(∀x)(Gx ⊃ Fx). Anything that’s G must be F.`,''],
  ]},
];
const qDefs = () => keyDefs(QD().map(g=>({h:g.h, items:DV.symItems(g.items)})));

registerLevel({num:3, title:'Predicate logic', topics:[
  {title:'Quantifiers', sub:'Symbolize with (∀x) and (∃x)', go:'ql'},
  {title:'Derivations', sub:'Proofs with quantifier rules', go:'qder'},
]});
const soFar = k => { const s=score(k); return s.done?` ${s.right} of ${s.done} correct so far.`:''; };
function qlHub(){
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Quantifiers</h2>
  <p class="muted">Symbolize English sentences about objects and their properties and relations.</p>
  ${qDefs()}
  <h3 class="section-title">Practice</h3>
  <ul class="topics" style="margin-top:10px">
    <li><button class="topic open" data-go="qlq"><span>Symbolize a sentence<small>${QS.length} sentences at three levels. Any equivalent answer counts.${soFar('qsym')}</small></span><span class="go">Practice</span></button></li>
  </ul>`;
}
let qRecent=[];
function newQ(){
  const lv=getSetting('qLevel','1'), list=QS.filter(s=>lv==='mix'||s.lv===+lv);
  const fresh=list.filter(s=>!qRecent.includes(s.id)), it=pick(fresh.length?fresh:list);
  qRecent.push(it.id); if(qRecent.length>Math.min(15,list.length-1)) qRecent.shift();
  return {it, input:'', res:null, counted:false, focus:'ql-in'};
}
function qView(){
  const e=App.ex, it=e.it, sc=score('qsym');
  let fb='';
  if(e.res){
    if(e.res.err) fb=`<div class="fb bad"><strong>I can’t check that yet.</strong>${esc(e.res.err)}</div>`;
    else {
      const model=show(P(it.ans));
      if(e.res.ok) fb=`<div class="fb good"><strong>Correct.</strong>${e.res.exact?'That’s the model answer.':`Your answer is equivalent to the model answer, <span class="sent">${esc(model)}</span>, on every interpretation with up to 3 objects.`}</div>`;
      else fb=`<div class="fb bad"><strong>Not quite.</strong>${e.res.mistake?esc(e.res.mistake)+' ':''}<p style="margin-top:6px">${esc(e.res.counter)}</p><p style="margin-top:8px">Model answer: <span class="sent"><b>${esc(model)}</b></span></p></div>`;
    }
  }
  const answered=e.res && !e.res.err;
  const keyList=Object.entries(it.key).map(([k,v])=>`<li><b>${k}${/[A-Z]/.test(k)?'xyz'.slice(0,arity(v)):''}</b>: ${esc(v)}</li>`).join('');
  return `<button class="back" data-go="ql">‹ Quantifiers</button>
  <div class="ex-head"><h2>Symbolize</h2><span class="score">${sc.right}/${sc.done}</span></div>
  ${qDefs()}
  ${seg('qLevel','Level',[['1','1'],['2','2'],['3','3'],['mix','Mixed']], getSetting('qLevel','1'))}
  <p class="prop">${esc(it.en)}</p>
  <ul class="symkey"><li><b>Domain</b>: ${esc(it.domain)}</li>${keyList}</ul>
  <section class="step"><h3>Your symbolization</h3>
    <input id="ql-in" class="sym-input" autocomplete="off" autocapitalize="off" spellcheck="false" value="${esc(e.input)}" aria-label="Your symbolization" ${answered?'disabled':''}>
    ${answered?'':L.symKeys('ql-in', true)}${answered?'':L.typingTip(true)}
    <div class="actions"><button class="btn" data-act="check-ql" ${answered?'disabled':''}>Check</button></div>${fb}</section>
  <div class="next"><button class="btn" data-act="next">Next sentence</button></div>`;
}
function qCheck(){
  const e=App.ex; if(e.res && !e.res.err) return;
  e.res=checkQ(e.it, e.input);
  if(!e.res.err && !e.counted){ e.counted=true; tally('qsym', e.res.ok); }
  if(e.res.err) e.focus='ql-in';
  render();
}
registerView('ql', {render: qlHub});
registerView('qlq', {init:newQ, render:qView, after:L.focusAfter,
  click:ev=>{ if(L.insClick(ev)) return; if(ev.target.closest('[data-act="check-ql"]')) qCheck(); },
  input:ev=>{ if(ev.target.id==='ql-in') App.ex.input=ev.target.value; },
  keydown:ev=>{ if(ev.target.id==='ql-in' && ev.key==='Enter'){ ev.preventDefault(); qCheck(); } },
  onSetting:name=>{ if(name==='qLevel'){ qRecent=[]; App.ex=newQ(); } }});

// =====================================================================
// Quantifier rules for the proof checker
// =====================================================================
// subst(f, v, c): replace the free occurrences of variable v in f with the constant c.
function subst(f, v, c){
  if(f.t==='atom') return {t:'atom', n:f.n, args:(f.args||[]).map(a=>a===v?c:a)};
  if(f.t==='not') return {t:'not', a:subst(f.a,v,c)};
  if(f.t==='all'||f.t==='some') return f.v===v ? f : {t:f.t, v:f.v, a:subst(f.a,v,c)};
  return {t:f.t, l:subst(f.l,v,c), r:subst(f.r,v,c)};
}
const constantsOf = f => [...signature(f).consts];
const hasConst = (f, c) => constantsOf(f).includes(c);
// Constants c such that subst(body, v, c) equals target. A fresh constant covers the vacuous case.
function instanceConstants(body, v, target){
  const cands=[...new Set(constantsOf(target).concat(['∘']))];
  return cands.filter(c=>L.eq(subst(body,v,c), target));
}
const EX_C = f => constantsOf(f)[0] || 'a';
DV.registerRule('∀E', {shape:'n', msg:'∀E cites one line, the universal sentence, like “∀E 2”.', check:({f, got, J, pr})=>{
  const U=got[0].f;
  if(U.t!=='all') return {err:`∀E needs a universal sentence, (∀x)…, but line ${J.cites[0].n} is ${pr(U)}.`};
  if(instanceConstants(U.a,U.v,f).length) return {};
  return {err:`∀E drops the (∀${U.v}) and puts one constant in place of every ${U.v} it bound. From ${pr(U)} you can get, for example, ${pr(subst(U.a,U.v,EX_C(f)))}.`};
}});
DV.registerRule('∃I', {shape:'n', msg:'∃I cites one line, the instance you have, like “∃I 3”.', check:({f, got, pr})=>{
  if(f.t!=='some') return {err:`∃I produces an existential sentence, (∃x)…, but ${pr(f)} isn’t one.`};
  const Q=got[0].f;
  if(instanceConstants(f.a,f.v,Q).length) return {};
  return {err:`∃I replaces a constant in the cited line with the new quantifier’s variable. ${pr(Q)} isn’t an instance of ${pr(f)}: putting a constant for ${f.v} in ${pr(f.a)} doesn’t give it.`};
}});
DV.registerRule('∀I', {shape:'n', msg:'∀I cites one line, the instance you’re generalizing, like “∀I 5”.', check:({f, got, pr, undischarged})=>{
  if(f.t!=='all') return {err:`∀I produces a universal sentence, (∀x)…, but ${pr(f)} isn’t one.`};
  const Q=got[0].f, cs=instanceConstants(f.a,f.v,Q);
  if(!cs.length) return {err:`${pr(Q)} isn’t an instance of ${pr(f)}. ∀I replaces every occurrence of one constant with the quantifier’s variable.`};
  let why='';
  for(const c of cs){
    if(c==='∘') return {};
    if(hasConst(f,c)){ why=why||`The constant ${c} still appears in ${pr(f)}. ∀I must replace every occurrence of ${c}, so ${c} can’t remain in the sentence you conclude.`; continue; }
    const bad=undischarged().find(u=>hasConst(u,c));
    if(bad){ why=why||`The constant ${c} appears in ${pr(bad)}, which is a premise or an undischarged assumption. ∀I needs a constant you know nothing special about, so ${c} can’t appear in any premise or open assumption.`; continue; }
    return {};
  }
  return {err:why};
}});
DV.registerRule('∃E', {shape:'ns', msg:'∃E cites the existential sentence and a subproof, like “∃E 1, 2–5”.', check:({f, got, J, pr, undischarged})=>{
  const X=got[0].f, S=got[1];
  if(X.t!=='some') return {err:`∃E starts from an existential sentence, (∃x)…, but line ${J.cites[0].n} is ${pr(X)}.`};
  const cs=instanceConstants(X.a,X.v,S.asm).filter(c=>c!=='∘');
  if(!cs.length) return {err:`The subproof must assume an instance of ${pr(X)}: drop the (∃${X.v}) and put a new constant in place of ${X.v}. ${pr(S.asm)} isn’t one.`};
  if(!L.eq(f,S.last)) return {err:`∃E concludes the subproof’s last line, ${pr(S.last)}.`};
  let why='';
  for(const c of cs){
    if(hasConst(X,c)){ why=why||`The constant ${c} already appears in ${pr(X)}. The instance for ∃E needs a brand-new constant.`; continue; }
    if(hasConst(f,c)){ why=why||`The constant ${c} appears in the conclusion, ${pr(f)}. With ∃E, the new constant must not appear in what you conclude, since all you know is that something or other fits.`; continue; }
    const bad=undischarged().find(u=>hasConst(u,c));
    if(bad){ why=why||`The constant ${c} appears in ${pr(bad)}, which is a premise or an undischarged assumption. The instance for ∃E needs a constant that appears nowhere else.`; continue; }
    return {};
  }
  return {err:why};
}});

// ----- Exercises: [level, premises, conclusion, model proof] -----
const QDERS = [
 [1,['(∀x)Fx'],'Fa',['0|Fa|∀E 1']],
 [1,['Fa'],'(∃x)Fx',['0|(∃x)Fx|∃I 1']],
 [1,['(∀x)(Fx ⊃ Gx)','Fa'],'Ga',['0|Fa ⊃ Ga|∀E 1','0|Ga|⊃E 3, 2']],
 [1,['(∀x)(Fx & Gx)'],'Gb',['0|Fb & Gb|∀E 1','0|Gb|&E 2']],
 [1,['Fa & Ga'],'(∃x)(Fx & Gx)',['0|(∃x)(Fx & Gx)|∃I 1']],
 [1,['(∀x)Fx'],'(∃x)Fx',['0|Fa|∀E 1','0|(∃x)Fx|∃I 2']],
 [1,['(∀x)Fx','(∀x)Gx'],'Fa & Ga',['0|Fa|∀E 1','0|Ga|∀E 2','0|Fa & Ga|&I 3, 4']],
 [1,['(∀x)(Fx ⊃ Gx)','~Ga'],'~Fa',['0|Fa ⊃ Ga|∀E 1','1|Fa|A','1|Ga|⊃E 3, 4','1|~Ga|R 2','0|~Fa|~I 4–6']],
 [1,['Rab'],'(∃x)Rxb',['0|(∃x)Rxb|∃I 1']],
 [1,['(∀x)Rxx'],'Raa',['0|Raa|∀E 1']],
 [1,['Raa'],'(∃x)Rxa',['0|(∃x)Rxa|∃I 1']],
 [2,['(∀x)(Fx & Gx)'],'(∀x)Fx',['0|Fa & Ga|∀E 1','0|Fa|&E 2','0|(∀x)Fx|∀I 3']],
 [2,['(∀x)(Fx ⊃ Gx)','(∀x)Fx'],'(∀x)Gx',['0|Fa ⊃ Ga|∀E 1','0|Fa|∀E 2','0|Ga|⊃E 3, 4','0|(∀x)Gx|∀I 5']],
 [2,['(∃x)(Fx & Gx)'],'(∃x)Fx',['1|Fa & Ga|A','1|Fa|&E 2','1|(∃x)Fx|∃I 3','0|(∃x)Fx|∃E 1, 2–4']],
 [2,['(∀x)(Fx ⊃ Gx)','(∃x)Fx'],'(∃x)Gx',['1|Fa|A','1|Fa ⊃ Ga|∀E 1','1|Ga|⊃E 4, 3','1|(∃x)Gx|∃I 5','0|(∃x)Gx|∃E 2, 3–6']],
 [2,['(∀x)(Fx & Gx)'],'(∀x)(Gx & Fx)',['0|Fa & Ga|∀E 1','0|Fa|&E 2','0|Ga|&E 2','0|Ga & Fa|&I 4, 3','0|(∀x)(Gx & Fx)|∀I 5']],
 [2,['(∀x)Fx','(∀x)Gx'],'(∀x)(Fx & Gx)',['0|Fa|∀E 1','0|Ga|∀E 2','0|Fa & Ga|&I 3, 4','0|(∀x)(Fx & Gx)|∀I 5']],
 [2,['(∃x)Fx'],'(∃x)(Fx ∨ Gx)',['1|Fa|A','1|Fa ∨ Ga|∨I 2','1|(∃x)(Fx ∨ Gx)|∃I 3','0|(∃x)(Fx ∨ Gx)|∃E 1, 2–4']],
 [2,['(∀x)(Fx ⊃ Gx)','(∀x)(Gx ⊃ Hx)'],'(∀x)(Fx ⊃ Hx)',['1|Fa|A','1|Fa ⊃ Ga|∀E 1','1|Ga|⊃E 4, 3','1|Ga ⊃ Ha|∀E 2','1|Ha|⊃E 6, 5','0|Fa ⊃ Ha|⊃I 3–7','0|(∀x)(Fx ⊃ Hx)|∀I 8']],
 [2,['(∃x)(Fx & Gx)'],'(∃x)(Gx & Fx)',['1|Fa & Ga|A','1|Fa|&E 2','1|Ga|&E 2','1|Ga & Fa|&I 4, 3','1|(∃x)(Gx & Fx)|∃I 5','0|(∃x)(Gx & Fx)|∃E 1, 2–6']],
 [2,['(∀x)Fx'],'(∀y)Fy',['0|Fa|∀E 1','0|(∀y)Fy|∀I 2']],
 [2,['(∀x)~Fx'],'~(∃x)Fx',['1|(∃x)Fx|A','2|Fa|A','3|(∃x)Fx|A','3|Fa|R 3','3|~Fa|∀E 1','2|~(∃x)Fx|~I 4–6','1|~(∃x)Fx|∃E 2, 3–7','0|~(∃x)Fx|~I 2–8']],
 [2,['~(∃x)Fx'],'(∀x)~Fx',['1|Fa|A','1|(∃x)Fx|∃I 2','1|~(∃x)Fx|R 1','0|~Fa|~I 2–4','0|(∀x)~Fx|∀I 5']],
 [2,['(∀x)(Fx ∨ Gx)','(∀x)~Fx'],'(∀x)Gx',['0|Fa ∨ Ga|∀E 1','0|~Fa|∀E 2','1|Fa|A','2|~Ga|A','2|Fa|R 5','2|~Fa|R 4','1|Ga|~E 6–8','1|Ga|A','1|Ga|R 10','0|Ga|∨E 3, 5–9, 10–11','0|(∀x)Gx|∀I 12']],
 [3,['(∀x)(∀y)Rxy'],'Rab',['0|(∀y)Ray|∀E 1','0|Rab|∀E 2']],
 [3,['(∀x)(∀y)Rxy'],'(∀y)(∀x)Rxy',['0|(∀y)Ray|∀E 1','0|Rab|∀E 2','0|(∀x)Rxb|∀I 3','0|(∀y)(∀x)Rxy|∀I 4']],
 [3,['(∃x)(∀y)Rxy'],'(∀y)(∃x)Rxy',['1|(∀y)Ray|A','1|Rab|∀E 2','1|(∃x)Rxb|∃I 3','1|(∀y)(∃x)Rxy|∀I 4','0|(∀y)(∃x)Rxy|∃E 1, 2–5']],
 [3,['(∀x)(Fx ⊃ Gx)'],'(∀x)Fx ⊃ (∀x)Gx',['1|(∀x)Fx|A','1|Fa|∀E 2','1|Fa ⊃ Ga|∀E 1','1|Ga|⊃E 4, 3','1|(∀x)Gx|∀I 5','0|(∀x)Fx ⊃ (∀x)Gx|⊃I 2–6']],
 [3,['(∃x)Fx ⊃ Ga'],'(∀x)(Fx ⊃ Ga)',['1|Fb|A','1|(∃x)Fx|∃I 2','1|Ga|⊃E 1, 3','0|Fb ⊃ Ga|⊃I 2–4','0|(∀x)(Fx ⊃ Ga)|∀I 5']],
 [3,['(∀x)(Fx ⊃ Ga)'],'(∃x)Fx ⊃ Ga',['1|(∃x)Fx|A','2|Fb|A','2|Fb ⊃ Ga|∀E 1','2|Ga|⊃E 4, 3','1|Ga|∃E 2, 3–5','0|(∃x)Fx ⊃ Ga|⊃I 2–6']],
 [3,['(∃x)(Fx ∨ Gx)'],'(∃x)Fx ∨ (∃x)Gx',['1|Fa ∨ Ga|A','2|Fa|A','2|(∃x)Fx|∃I 3','2|(∃x)Fx ∨ (∃x)Gx|∨I 4','2|Ga|A','2|(∃x)Gx|∃I 6','2|(∃x)Fx ∨ (∃x)Gx|∨I 7','1|(∃x)Fx ∨ (∃x)Gx|∨E 2, 3–5, 6–8','0|(∃x)Fx ∨ (∃x)Gx|∃E 1, 2–9']],
 [3,['~(∀x)Fx'],'(∃x)~Fx',['1|~(∃x)~Fx|A','2|~Fa|A','2|(∃x)~Fx|∃I 3','2|~(∃x)~Fx|R 2','1|Fa|~E 3–5','1|(∀x)Fx|∀I 6','1|~(∀x)Fx|R 1','0|(∃x)~Fx|~E 2–8']],
 [3,['(∀x)(Fx ⊃ (∃y)Rxy)','Fa'],'(∃y)Ray',['0|Fa ⊃ (∃y)Ray|∀E 1','0|(∃y)Ray|⊃E 3, 2']],
 [3,['(∀x)(∃y)Rxy','(∀x)(∀y)(Rxy ⊃ Ryx)'],'(∀x)(∃y)Ryx',['0|(∃y)Ray|∀E 1','1|Rab|A','1|(∀y)(Ray ⊃ Rya)|∀E 2','1|Rab ⊃ Rba|∀E 5','1|Rba|⊃E 6, 4','1|(∃y)Rya|∃I 7','0|(∃y)Rya|∃E 3, 4–8','0|(∀x)(∃y)Ryx|∀I 9']],
 [3,['(∃x)(Fx & Gx)','(∀x)(Gx ⊃ Hx)'],'(∃x)(Fx & Hx)',['1|Fa & Ga|A','1|Fa|&E 3','1|Ga|&E 3','1|Ga ⊃ Ha|∀E 2','1|Ha|⊃E 6, 5','1|Fa & Ha|&I 4, 7','1|(∃x)(Fx & Hx)|∃I 8','0|(∃x)(Fx & Hx)|∃E 1, 3–9']],
 [3,['(∀x)(Fx ≡ Gx)','(∃x)Gx'],'(∃x)Fx',['1|Ga|A','1|Fa ≡ Ga|∀E 1','1|Fa|≡E 4, 3','1|(∃x)Fx|∃I 5','0|(∃x)Fx|∃E 2, 3–6']],
].map(([lv,p,c,proof],id)=>({id, lv, p, c, proof, ql:true}));

const QRULE_DEFS = [
  ['∀E (universal elimination)','From (∀x)P, conclude any instance: drop the quantifier and put one constant in place of every x it bound.','From (∀x)(Fx ⊃ Gx), conclude Fb ⊃ Gb.'],
  ['∃I (existential introduction)','From a sentence about a constant, conclude that something fits: replace one or more occurrences of the constant with a variable, and put (∃x) in front.','From Raa, conclude (∃x)Rxa or (∃x)Rxx.'],
  ['∀I (universal introduction)','From an instance P(a), conclude (∀x)P(x), where x replaces every occurrence of a. Restriction: a must not appear in any premise or undischarged assumption, or in the sentence you conclude. Then a really was “any object at all.”','From Fa & Ga (with no premise about a), conclude (∀x)(Fx & Gx).'],
  ['∃E (existential elimination)','From (∃x)P, open a subproof assuming an instance P(a) with a new constant a. If the subproof reaches Q, close it and conclude Q. Restriction: a must not appear in (∃x)P, in Q, or in any premise or undischarged assumption.','From (∃x)Fx, assume Fa, derive (∃x)(Fx ∨ Gx), and conclude it by “∃E 1, 2–4.”'],
];
const qderDefs = () => keyDefs([
  {items:DV.symItems([
    ['Instance','The result of dropping a quantifier and putting a constant in place of the variable it bound.','Fa ⊃ Ga is an instance of (∀x)(Fx ⊃ Gx).'],
    ['Undischarged assumption','A premise, or an assumption whose subproof is still open at the line you’re writing.',''],
    ['New constant','A constant that hasn’t appeared anywhere relevant: not in a premise, an open assumption, or the sentence being concluded. ∀I and ∃E need one.',''],
  ])},
  {h:'Quantifier rules', items:DV.symItems(QRULE_DEFS)},
  {h:'Rules from sentential logic', items:DV.symItems(DV.RULE_DEFS)},
]);
DV.makeDerivationModule({key:'qder', title:'Quantifier derivations', back:'home', backLabel:'All levels', exercises:QDERS, defs:qderDefs, ql:true,
  intro:'Natural deduction with ∀E, ∀I, ∃I, and ∃E, plus every rule from sentential logic.',
  levelNames:{1:'Level 1 · Instances',2:'Level 2 · ∀I and ∃E',3:'Level 3 · Several quantifiers'}});

Engines.predicate = {QS, QDERS, checkQ, qlCompare, evalQ, signature, keyInfo, subst, forEachInterp, qMutations};
})();
