// Fallacies: content checks (coverage, examples, distractor explanations).
module.exports = (t, E) => {
  const {FALLACIES, FAMILIES, falChoices} = E.fallacies;
  const ids = new Set(FALLACIES.map(f => f.id));
  t.test('about 20 informal fallacies plus the two formal ones', () => {
    t.ok(FALLACIES.filter(f => f.fam !== 'formal').length >= 20, 'at least 20 informal');
    t.ok(ids.has('affirming') && ids.has('denying'), 'affirming the consequent and denying the antecedent');
  });
  t.test('ids are unique and families are known', () => {
    t.eq(ids.size, FALLACIES.length);
    FALLACIES.forEach(f => t.ok(FAMILIES[f.fam], `${f.id} family`));
  });
  t.test('every informal family has fallacies', () => {
    ['distraction', 'weak', 'presumption', 'linguistic'].forEach(k => t.ok(FALLACIES.some(f => f.fam === k), k));
  });
  t.test('every fallacy has a definition and at least 3 passages with explanations', () => {
    FALLACIES.forEach(f => {
      t.ok(f.name && f.def, f.id);
      t.ok(f.ex.length >= 3, `${f.id} has ${f.ex.length} passages`);
      f.ex.forEach((x, i) => t.ok(x.p.length > 20 && x.why.length > 20, `${f.id} #${i}`));
    });
  });
  t.test('no passage is repeated', () => {
    const all = FALLACIES.flatMap(f => f.ex.map(x => x.p));
    t.eq(new Set(all).size, all.length);
  });
  t.test('every fallacy has at least 3 close alternatives, each explained', () => {
    FALLACIES.forEach(f => {
      const near = Object.keys(f.near);
      t.ok(near.length >= 3, `${f.id} has ${near.length}`);
      near.forEach(n => { t.ok(ids.has(n) && n !== f.id, `${f.id} → ${n}`); t.ok(f.near[n].length > 20, `${f.id} → ${n} text`); });
    });
  });
  t.test('choices: 4 distinct options including the right answer', () => {
    FALLACIES.forEach(f => { for (let i = 0; i < 20; i++) {
      const c = falChoices(f);
      t.eq(c.length, 4, f.id); t.eq(new Set(c).size, 4, f.id); t.ok(c.includes(f.id), f.id);
    } });
  });
};
