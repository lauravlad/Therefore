// Therefore — shared app shell: helpers, saved progress, level registry, routing, events.
// Loaded before the level files. Each js/levelN-*.js calls registerLevel() for its
// home-page card and registerView() for each screen it owns.
'use strict';

// ===== Helpers =====
const pick = arr => arr[Math.floor(Math.random()*arr.length)];
const esc = s => String(s).replace(/[&<>"]/g, c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));

// ===== Saved progress (this browser only, no accounts) =====
const KEY='therefore-v1';
function load(){ try{ return JSON.parse(localStorage.getItem(KEY))||{}; }catch(e){ return {}; } }
function save(){ try{ localStorage.setItem(KEY, JSON.stringify(progress)); }catch(e){} }
const progress = load();
function score(kind){ return progress[kind] || (progress[kind]={done:0,right:0}); }
function tally(kind, ok){ const s=score(kind); s.done++; if(ok) s.right++; save(); }

// ===== Registry =====
// Level: {num, title, topics:[{title, sub, go?, action?}]}. A topic without `go` shows "Coming soon".
// View:  {render() -> html, init?() -> new exercise state, click?(ev), change?(ev)}
const LEVELS=[], VIEWS={};
const App={view:'home', ex:null, heroIcon:null};
function registerLevel(def){ LEVELS.push(def); LEVELS.sort((a,b)=>a.num-b.num); }
function registerView(name, def){ VIEWS[name]=def; }

// ===== Routing =====
const app=document.getElementById('app');
function render(){ const v=VIEWS[App.view]; app.innerHTML = v ? v.render() : ''; }
function go(name){
  if(!VIEWS[name]) name='home';
  App.view=name;
  if(VIEWS[name].init) App.ex=VIEWS[name].init();
  render(); window.scrollTo(0,0);
}

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
  <ol class="levels">${LEVELS.map(level).join('')}</ol>`;
}
registerView('home', {render: homeView});

// ===== Events (delegated; level-specific handling goes to the current view) =====
app.addEventListener('click', ev=>{
  const goEl=ev.target.closest('[data-go]'); if(goEl){ go(goEl.dataset.go); return; }
  if(ev.target.closest('[data-act="next"]')){ go(App.view); return; }
  const v=VIEWS[App.view]; if(v && v.click) v.click(ev);
});
app.addEventListener('change', ev=>{ const v=VIEWS[App.view]; if(v && v.change) v.change(ev); });

// All level scripts have run by the time this fires.
document.addEventListener('DOMContentLoaded', render);
