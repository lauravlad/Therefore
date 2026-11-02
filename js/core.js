// Therefore — shared app shell: helpers, saved progress and settings, level registry,
// routing, delegated events, shared UI pieces (key definitions, setting toggles),
// the home page and the credits page.
// Loaded before the level files. Each js/levelN-*.js calls registerLevel() for its
// home-page card and registerView() for each screen it owns.
'use strict';

// ===== Helpers =====
const pick = arr => arr[Math.floor(Math.random()*arr.length)];
const esc = s => String(s).replace(/[&<>"]/g, c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
function shuffle(arr){ const a=arr.slice(); for(let i=a.length-1;i>0;i--){ const j=Math.floor(Math.random()*(i+1)); [a[i],a[j]]=[a[j],a[i]]; } return a; }

// ===== Saved progress and settings (this browser only, no accounts) =====
const KEY='therefore-v1';
function load(){ try{ const p=JSON.parse(localStorage.getItem(KEY)); return p&&typeof p==='object'?p:{}; }catch(e){ return {}; } }
function save(){ try{ localStorage.setItem(KEY, JSON.stringify(progress)); }catch(e){} }
const progress = load();
function score(kind){ return progress[kind] || (progress[kind]={done:0,right:0}); }
function tally(kind, ok){ const s=score(kind); s.done++; if(ok) s.right++; save(); }
function getSetting(name, dflt){ const s=progress.settings||{}; return name in s ? s[name] : dflt; }
function setSetting(name, value){ (progress.settings||(progress.settings={}))[name]=value; save(); if(name==='notation') applyNotation(); }

// ===== Notation (Settings page). Everything displays connectives through SYMBOLS. =====
// Text written in the default Logic Book symbols (rule names like "⊃E", definitions) goes through sym().
const NOTATIONS = {
  logicbook:{label:'The Logic Book style', not:'~', and:'&', or:'∨', cond:'⊃', bicond:'≡'},
  hurley:{label:'Hurley style', not:'~', and:'•', or:'∨', cond:'⊃', bicond:'≡'},
  modern:{label:'Modern style', not:'¬', and:'∧', or:'∨', cond:'→', bicond:'↔'},
};
const SYMBOLS = {};
function applyNotation(){ const n=NOTATIONS[getSetting('notation','logicbook')]||NOTATIONS.logicbook; ['not','and','or','cond','bicond'].forEach(k=>SYMBOLS[k]=n[k]); }
applyNotation();
const sym = s => String(s).replace(/[~&⊃≡]/g, c=>({'~':SYMBOLS.not,'&':SYMBOLS.and,'⊃':SYMBOLS.cond,'≡':SYMBOLS.bicond})[c]);

// Building blocks one level shares with later ones (Level 2's parser and proof checker are reused by Levels 3 and 4).
const Shared = {};
// Pure logic engines, registered by the level files so tests/ can exercise them with node.
const Engines = {notation:{NOTATIONS, SYMBOLS, sym, use:name=>setSetting('notation',name)}};

// ===== Registry =====
// Level: {num, title, topics:[{title, sub, go?, action?}]}. A topic without `go` shows "Coming soon".
// View:  {render() -> html, init?() -> new exercise state, click?(ev), change?(ev), input?(ev),
//         keydown?(ev), onSetting?(name, value), after?() (runs after each render)}
const LEVELS=[], VIEWS={};
const App={view:'home', ex:null, heroIcon:null};
function registerLevel(def){ LEVELS.push(def); LEVELS.sort((a,b)=>a.num-b.num); }
function registerView(name, def){ VIEWS[name]=def; }

// ===== Shared UI pieces =====
// Collapsible "Key definitions". groups: [{h?, items:[[term, definition, example?], ...]}]
function keyDefs(groups, open){
  const body=groups.map(g=>`${g.h?`<h4>${g.h}</h4>`:''}<dl>${g.items.map(([t,d,x])=>
    `<dt>${t}</dt><dd>${d}${x?`<span class="ex">Example: ${x}</span>`:''}</dd>`).join('')}</dl>`).join('');
  return `<details class="defs"${open?' open':''}><summary>Key definitions</summary><div class="defs-body">${body}</div></details>`;
}
// A row of toggle buttons bound to a saved setting. options: [[value, label], ...]
function seg(name, label, options, current){
  return `<div class="seg" role="group" aria-label="${label}"><span class="seg-label">${label}</span>${options.map(([v,l])=>
    `<button class="${v===current?'on':''}" data-setting="${name}" data-value="${v}" aria-pressed="${v===current}">${l}</button>`).join('')}</div>`;
}

// ===== Routing (the URL hash mirrors the view, so the back button and links work) =====
const app=document.getElementById('app');
function render(){
  const v=VIEWS[App.view];
  app.innerHTML = v ? v.render() : '';
  if(v && v.after) v.after();
}
function go(name){
  if(!VIEWS[name]) name='home';
  App.view=name;
  if(VIEWS[name].init) App.ex=VIEWS[name].init();
  render(); window.scrollTo(0,0);
  try{ if(location.hash.slice(1)!==name) location.hash=name; }catch(e){}
}
window.addEventListener('hashchange', ()=>{ const h=location.hash.slice(1)||'home'; if(h!==App.view) go(h); });

// ===== Home =====
function homeView(){
  const icon = App.heroIcon ? App.heroIcon() : '';
  const topic = t => t.go
    ? `<li><button class="topic open" data-go="${t.go}"><span>${t.title}<small>${t.sub}</small></span><span class="go">${t.action||'Start'}</span></button></li>`
    : `<li><button class="topic" disabled><span>${t.title}<small>${t.sub}</small></span><span class="pill">Coming soon</span></button></li>`;
  const level = l => `<li class="level"><div class="level-head"><h2>${l.title}</h2><span class="level-num">Level ${l.num}</span></div>
      <ul class="topics">${l.topics.map(topic).join('')}</ul></li>`;
  return `
  <div class="hero">${icon}<div><h1>Therefore</h1><p class="tagline">Practice logic one step at a time, with feedback on every answer.</p></div></div>
  <ol class="levels">${LEVELS.map(level).join('')}</ol>
  <footer class="foot"><p>Free to use, with no accounts. Your progress is saved in this browser only.</p>
    <p><a href="#settings" data-go="settings">Settings</a> · <a href="#credits" data-go="credits">Credits and sources</a></p></footer>`;
}
registerView('home', {render: homeView});

// ===== Settings =====
function settingsView(){
  const cur=getSetting('notation','logicbook');
  const opt=([k,n])=>`<button class="choice${k===cur?' picked':''}" data-setting="notation" data-value="${k}" aria-pressed="${k===cur}">
      <b>${n.label}</b><small class="sent">${n.not} ${n.and} ${n.or} ${n.cond} ${n.bicond}  ·  ${n.not}(A ${n.and} B) ${n.cond} (C ${n.or} D)</small></button>`;
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Settings</h2>
  <h3 class="section-title">Notation</h3>
  <p class="muted">How connectives are shown everywhere in the app. Whichever you pick, you can type answers in any of these styles, or use keyboard forms: <b class="kbd">-</b> for not, <b class="kbd">&amp;</b> for and, <b class="kbd">v</b> for or, <b class="kbd">-&gt;</b> for if…then, <b class="kbd">&lt;-&gt;</b> for if and only if.</p>
  <div class="choices one" style="margin-top:10px">${Object.entries(NOTATIONS).map(opt).join('')}</div>
  <h3 class="section-title">Categorical logic</h3>
  ${seg('reading','Reading',[['boolean','Boolean'],['aristotelian','Aristotelian']], getSetting('reading','boolean'))}
  <p class="muted" style="font-size:.92rem">Boolean (the default) doesn’t assume classes have members. Aristotelian does, which adds the traditional square of opposition and nine more valid syllogisms.</p>
  <p class="muted" style="margin-top:22px">Settings and progress are saved in this browser only.</p>`;
}
registerView('settings', {render: settingsView});

// ===== Credits (CC BY 4.0 requires title, author, license, and a link for each source) =====
const CC_BY = '<a href="https://creativecommons.org/licenses/by/4.0/" target="_blank" rel="noopener">CC BY 4.0</a>';
function creditsView(){
  const src=(title, by, url, used)=>`<li><h3><cite>${title}</cite></h3><p>${by}</p>
    <p>License: ${CC_BY} · <a href="${url}" target="_blank" rel="noopener">${url.replace(/^https:\/\//,'').replace(/\/$/,'')}</a></p>
    <p class="muted">Used for: ${used}</p></li>`;
  return `<button class="back" data-go="home">‹ All levels</button>
  <h2>Credits</h2>
  <p>All definitions, explanations, examples, and exercises in Therefore are written in our own words. They're based on the openly licensed books below, used under the Creative Commons Attribution 4.0 International license (CC BY 4.0). No text from these books is reproduced, and their authors haven't reviewed or endorsed this app.</p>
  <ul class="credits">
    ${src('Fundamental Methods of Logic (original 2017 edition)','Matthew Knachel','https://wisconsin.pressbooks.pub/logicfundamentals/','Level 1: categorical logic and fallacies.')}
    ${src('forall x: Calgary','P. D. Magnus and Tim Button, with additions by J. Robert Loftis and Robert Trueman; remixed and revised by Aaron Thomas-Bolduc and Richard Zach','https://forallx.openlogicproject.org/','Levels 2 and 3: symbolization, truth tables, derivations, and quantifiers.')}
    ${src('The Open Logic Project','Richard Zach and the Open Logic Project contributors','https://openlogicproject.org/','Level 4 (three-valued and fuzzy logic), and background for the formal definitions throughout.')}
  </ul>
  <h3>Fonts</h3>
  <p>Atkinson Hyperlegible (Braille Institute of America) and Literata (TypeTogether), both under the SIL Open Font License, served by Google Fonts.</p>
  <h3>This app</h3>
  <p>Therefore is free, with no accounts and no tracking. Your progress and settings stay in this browser.</p>`;
}
registerView('credits', {render: creditsView});

// ===== Events (delegated; level-specific handling goes to the current view) =====
app.addEventListener('click', ev=>{
  const goEl=ev.target.closest('[data-go]'); if(goEl){ ev.preventDefault(); go(goEl.dataset.go); return; }
  if(ev.target.closest('[data-act="next"]')){ go(App.view); return; }
  const v=VIEWS[App.view];
  const s=ev.target.closest('[data-setting]');
  if(s){ setSetting(s.dataset.setting, s.dataset.value); if(v && v.onSetting) v.onSetting(s.dataset.setting, s.dataset.value); render(); return; }
  if(v && v.click) v.click(ev);
});
['change','input','keydown'].forEach(type=>app.addEventListener(type, ev=>{ const v=VIEWS[App.view]; if(v && v[type]) v[type](ev); }));

// All level scripts have run by the time this fires.
document.addEventListener('DOMContentLoaded', ()=>{ const h=location.hash.slice(1); if(VIEWS[h] && h!=='home') go(h); else render(); });
