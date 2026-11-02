// Therefore test runner. Usage: node tests/run.js
// Loads the app's own script files into a sandbox (with a tiny fake DOM) and runs every
// tests/*.test.js file against the logic engines they register on `Engines`.
'use strict';
const fs = require('fs'), path = require('path'), vm = require('vm');
const root = path.join(__dirname, '..');
const APP_FILES = ['js/core.js', 'js/level1-intro.js', 'js/level2-sentential.js', 'js/level3-predicate.js', 'js/level4-multivalued.js'];

function loadEngines(){
  const el = {innerHTML:'', addEventListener(){}};
  const store = {};
  const sandbox = {
    console,
    document: {getElementById: () => el, addEventListener(){}},
    window: {scrollTo(){}, addEventListener(){}},
    location: {hash:''},
    localStorage: {getItem: k => (k in store ? store[k] : null), setItem: (k, v) => { store[k] = String(v); }},
    Event: function Event(){},
  };
  const ctx = vm.createContext(sandbox);
  for (const f of APP_FILES) vm.runInContext(fs.readFileSync(path.join(root, f), 'utf8'), ctx, {filename: f});
  return vm.runInContext('Engines', ctx);
}

let passed = 0, failed = 0, current = '';
const fmt = v => { try { return JSON.stringify(v); } catch (e) { return String(v); } };
const t = {
  test(name, fn){
    current = name;
    try { fn(); passed++; }
    catch (e) { failed++; console.log(`  ✗ ${name}\n      ${e && e.message ? e.message : e}`); }
  },
  eq(actual, expected, msg){
    if (fmt(actual) !== fmt(expected)) throw new Error(`${msg ? msg + ': ' : ''}expected ${fmt(expected)}, got ${fmt(actual)}`);
  },
  ok(cond, msg){ if (!cond) throw new Error(msg || 'expected a true value'); },
};

const E = loadEngines();
const files = fs.readdirSync(__dirname).filter(f => f.endsWith('.test.js')).sort();
for (const f of files){
  const before = failed;
  console.log(f);
  require(path.join(__dirname, f))(t, E);
  if (failed === before) console.log('  all passed');
}
console.log(`\n${passed} passed, ${failed} failed`);
if (failed) process.exitCode = 1;
