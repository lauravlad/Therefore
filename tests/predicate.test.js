// Predicate logic: parsing, semantics on small domains, the symbolization checker,
// and the quantifier rules with their restrictions on constants.
module.exports = (t, E) => {
  const Q = E.predicate, S = E.sentential, D = E.derivations;
  const P = s => S.parse(s, {ql: true});

  t.test('quantified sentences parse and print as (∀x) and (∃x)', () => {
    [['(∀x)(Fx ⊃ Gx)', '(∀x)(Fx ⊃ Gx)'], ['∀x Fx', '(∀x)Fx'], ['\\Ax Fx', '(∀x)Fx'], ['\\Ey(Ty & Rxy)', '(∃y)(Ty & Rxy)'],
     ['~(∃x)(∀y)Kxy', '~(∃x)(∀y)Kxy'], ['(∀x)Fx ⊃ Ga', '(∀x)Fx ⊃ Ga'], ['Rab', 'Rab']]
      .forEach(([src, out]) => t.eq(S.show(P(src)), out, src));
  });
  t.test('predicate-logic syntax errors', () => {
    t.ok(S.tryParse('(∀)Fx', {ql: true}).err.includes('variable'));
    t.ok(S.tryParse('(∀x Fx', {ql: true}).err.includes('Close'));
    t.ok(S.tryParse('a & Fb', {ql: true}).err.includes('can’t stand alone'));
    t.ok(S.tryParse('(∀x)Fx', {}).err.includes('predicate logic'), 'quantifiers are rejected in sentential mode');
  });
  t.test('evaluation on a small interpretation', () => {
    // domain {0,1}; F = {0}; R = {(0,1)}; a = 0
    const I = {n: 2, ext: {F: 1, R: 1 << (0 + 1 * 2)}, c: {a: 0}};
    t.ok(Q.evalQ(P('(∃x)Fx'), I, {})); t.ok(!Q.evalQ(P('(∀x)Fx'), I, {}));
    t.ok(Q.evalQ(P('Fa'), I, {}));
    t.ok(Q.evalQ(P('(∃x)(∃y)Rxy'), I, {})); t.ok(!Q.evalQ(P('(∀x)(∃y)Rxy'), I, {}));
    t.ok(Q.evalQ(P('(∃y)Ray'), I, {}));
  });
  t.test('equivalence on domains up to 3', () => {
    t.ok(Q.qlCompare(P('~(∃x)(Fx & Gx)'), P('(∀x)(Fx ⊃ ~Gx)')).equiv);
    t.ok(Q.qlCompare(P('~(∀x)Fx'), P('(∃x)~Fx')).equiv);
    t.ok(Q.qlCompare(P('(∀x)(Fx & Gx)'), P('(∀x)Fx & (∀x)Gx')).equiv);
    t.ok(!Q.qlCompare(P('(∀x)(∃y)Rxy'), P('(∃y)(∀x)Rxy')).equiv);
    t.ok(!Q.qlCompare(P('(∀x)(Fx ⊃ Gx)'), P('(∀x)(Fx & Gx)')).equiv);
    const c = Q.qlCompare(P('(∃x)Fx'), P('(∀x)Fx'));
    t.ok(!c.equiv && c.counter.n === 2, 'smallest counterexample has 2 objects');
  });
  t.test('at least 50 sentences across three levels', () => {
    t.ok(Q.QS.length >= 50, `${Q.QS.length}`);
    [1, 2, 3].forEach(lv => t.ok(Q.QS.filter(s => s.lv === lv).length >= 12, `level ${lv}`));
  });
  t.test('every model answer is a sentence matching its key exactly', () => {
    Q.QS.forEach(s => {
      const f = P(s.ans), sig = Q.signature(f), k = Q.keyInfo(s);
      t.eq([...D.freeVars(f)], [], s.en);
      const sorted = o => Object.keys(o).sort().map(x => [x, o[x]]);
      t.eq(sorted(sig.preds), sorted(k.preds), s.en);
      t.eq([...sig.consts].sort(), k.consts.slice().sort(), s.en);
    });
  });
  t.test('every model answer is accepted', () => {
    Q.QS.forEach(s => t.ok(Q.checkQ(s, s.ans).ok, s.en));
  });
  const item = en => Q.QS.find(s => s.en === en);
  t.test('equivalent answers are accepted', () => {
    t.ok(Q.checkQ(item('No snakes are friendly.'), '~(∃x)(Sx & Fx)').ok);
    t.ok(Q.checkQ(item('Not all fish swim in schools.'), '(∃x)(Fx & ~Sx)').ok);
    t.ok(Q.checkQ(item('Nobody knows everyone.'), '(∀x)(∃y)~Kxy').ok);
    t.ok(Q.checkQ(item('A ticket is valid only if it’s stamped.'), '(∀x)(Tx ⊃ (Vx ⊃ Sx))').ok);
    t.ok(Q.checkQ(item('Everything is fragile.'), '(∀y)Fy').ok, 'a different variable');
  });
  t.test('common mistakes get specific feedback and a counterexample', () => {
    const a = Q.checkQ(item('All dogs are loyal.'), '(∀x)(Dx & Lx)');
    t.ok(!a.ok && a.mistake.includes('use ⊃'), a.mistake); t.ok(a.counter.includes('domain'), a.counter);
    t.ok(Q.checkQ(item('Some cats are orange.'), '(∃x)(Cx ⊃ Ox)').mistake.includes('use &'));
    t.ok(Q.checkQ(item('Someone knows everyone.'), '(∀y)(∃x)Kxy').mistake.includes('order'));
    t.ok(Q.checkQ(item('Only members can vote.'), '(∀x)(Mx ⊃ Vx)').mistake.includes('Only'));
    t.ok(Q.checkQ(item('Not every athlete is fast.'), '(∀x)(Ax ⊃ ~Fx)').mistake.includes('negation'));
  });
  t.test('answers that don’t fit the key are rejected without grading', () => {
    t.ok(Q.checkQ(item('All dogs are loyal.'), '(∀x)(Dx ⊃ Qx)').err.includes('isn’t in the symbolization key'));
    t.ok(Q.checkQ(item('Ana knows everyone.'), '(∀x)Ka').err.includes('takes 2 terms'));
    t.ok(Q.checkQ(item('All dogs are loyal.'), 'Dx ⊃ Lx').err.includes('isn’t bound'));
    t.ok(Q.checkQ(item('All dogs are loyal.'), '(∀x)(Dx ⊃ Lb)').err.includes('constant'));
  });

  // ----- Quantifier rules -----
  const setup = (prem, model, closeAll) => {
    const r = D.runModel(prem, model || [], {ql: true});
    if (r.err) throw new Error('setup failed: ' + r.err);
    if (closeAll) while (r.st.stack.length) D.endSub(r.st);
    return r.st;
  };
  const ok = (st, s, j) => { const r = D.addLine(st, s, j); t.ok(!r.err, `“${s}  ${j}” should be accepted: ${r.err}`); };
  const bad = (st, s, j, frag) => {
    const r = D.addLine(st, s, j);
    t.ok(r.err, `“${s}  ${j}” should be rejected`);
    if (frag) t.ok(r.err.includes(frag), `error should mention “${frag}”: ${r.err}`);
  };
  t.test('rule names: ∀E, ∀I, ∃I, ∃E and keyboard forms', () => {
    t.eq(D.parseJust('∀E 1').rule, '∀E'); t.eq(D.parseJust('AE 1').rule, '∀E'); t.eq(D.parseJust('\\AI 2').rule, '∀I');
    t.eq(D.parseJust('EI 1').rule, '∃I'); t.eq(D.parseJust('∃E 1, 2-4').rule, '∃E');
  });
  t.test('every line must be a sentence (no free variables)', () => {
    bad(setup(['(∀x)Fx']), 'Fx', '∀E 1', 'free variable');
    const st = setup(['(∀x)Fx']); t.ok(D.assume(st, 'Gy').err.includes('free variable'));
  });
  t.test('∀E: any constant, replacing every occurrence', () => {
    ok(setup(['(∀x)Fx']), 'Fa', '∀E 1');
    ok(setup(['(∀x)Rxx']), 'Rbb', '∀E 1');
    ok(setup(['(∀x)(Fx ⊃ (∃y)Rxy)']), 'Fc ⊃ (∃y)Rcy', '∀E 1');
    bad(setup(['(∀x)Rxx']), 'Rab', '∀E 1', 'every x');
    bad(setup(['(∃x)Fx']), 'Fa', '∀E 1', 'universal');
    bad(setup(['(∀x)Fx']), 'Ga', '∀E 1');
  });
  t.test('∃I: some or all occurrences of a constant', () => {
    ok(setup(['Raa']), '(∃x)Rxa', '∃I 1');
    ok(setup(['Raa']), '(∃x)Rxx', '∃I 1');
    ok(setup(['Fa & Ga']), '(∃x)(Fx & Gx)', '∃I 1');
    bad(setup(['Fa & Gb']), '(∃x)(Fx & Gx)', '∃I 1', 'isn’t an instance');
    bad(setup(['Fa']), '(∀x)Fx', '∃I 1', 'existential');
  });
  t.test('∀I: allowed with a constant that appears in no premise or open assumption', () => {
    ok(setup(['(∀x)(Fx & Gx)'], ['0|Fa & Ga|∀E 1', '0|Fa|&E 2']), '(∀x)Fx', '∀I 3');
    ok(setup(['(∀x)Fx'], ['0|Fa|∀E 1']), '(∀y)Fy', '∀I 2');
  });
  t.test('∀I restriction: the constant may not appear in a premise', () => {
    bad(setup(['Fa']), '(∀x)Fx', '∀I 1', 'premise or an undischarged assumption');
  });
  t.test('∀I restriction: the constant may not appear in an open assumption', () => {
    const st = setup(['(∀x)Gx'], ['1|Fa|A', '1|Ga|∀E 1']);
    bad(st, '(∀x)Gx', '∀I 3', 'undischarged assumption');
  });
  t.test('∀I is fine once the assumption with the constant is discharged', () => {
    const st = setup([], ['1|Fa|A', '1|Fa|R 1', '0|Fa ⊃ Fa|⊃I 1–2']);
    ok(st, '(∀x)(Fx ⊃ Fx)', '∀I 3');
  });
  t.test('∀I restriction: the constant may not remain in the conclusion', () => {
    bad(setup(['(∀x)Rxx'], ['0|Raa|∀E 1']), '(∀x)Rxa', '∀I 2', 'still appears');
  });
  t.test('∀I: the line must be an instance of the result', () => {
    bad(setup(['(∀x)Fx'], ['0|Fa|∀E 1']), '(∀x)Gx', '∀I 2', 'isn’t an instance');
  });
  const exSub = (prem, inner) => setup(prem, inner, true);
  t.test('∃E: a new constant, a conclusion without it', () => {
    ok(exSub(['(∃x)Fx'], ['1|Fa|A', '1|Fa ∨ Ga|∨I 2', '1|(∃x)(Fx ∨ Gx)|∃I 3']), '(∃x)(Fx ∨ Gx)', '∃E 1, 2–4');
  });
  t.test('∃E restriction: the constant may not appear in the conclusion', () => {
    bad(exSub(['(∃x)Fx'], ['1|Fa|A', '1|Fa|R 2']), 'Fa', '∃E 1, 2–3', 'appears in the conclusion');
  });
  t.test('∃E restriction: the constant may not appear in the existential sentence', () => {
    bad(exSub(['(∃x)Rxa'], ['1|Raa|A', '1|(∃x)Rxx|∃I 2']), '(∃x)Rxx', '∃E 1, 2–3', 'already appears');
  });
  t.test('∃E restriction: the constant may not appear in a premise', () => {
    bad(exSub(['(∃x)Fx', 'Ga'], ['1|Fa|A', '1|Fa & Ga|&I 3, 2', '1|(∃x)(Fx & Gx)|∃I 4']), '(∃x)(Fx & Gx)', '∃E 1, 3–5', 'premise or an undischarged assumption');
  });
  t.test('∃E restriction: the constant may not appear in an open assumption', () => {
    const st = setup(['(∃x)Fx'], ['1|Ga|A', '2|Fa|A', '2|Fa & Ga|&I 3, 2', '2|(∃x)(Fx & Gx)|∃I 4']);
    D.endSub(st);
    bad(st, '(∃x)(Fx & Gx)', '∃E 1, 3–5', 'undischarged assumption');
  });
  t.test('∃E: the subproof must assume an instance, and end with the conclusion', () => {
    bad(exSub(['(∃x)Fx'], ['1|Ga|A', '1|Ga|R 2']), 'Ga', '∃E 1, 2–3', 'must assume an instance');
    bad(exSub(['(∃x)Fx'], ['1|Fa|A', '1|(∃x)Fx|∃I 2']), '(∃y)Fy', '∃E 1, 2–3', 'last line');
    bad(exSub(['(∀x)Fx'], ['1|Fa|A', '1|(∃x)Fx|∃I 2']), '(∃x)Fx', '∃E 1, 2–3', 'existential');
  });
  t.test('quantifier rule citation shapes', () => {
    bad(setup(['(∀x)Fx', 'Fa']), 'Fa', '∀E 1, 2', 'one line');
    bad(setup(['(∃x)Fx']), 'Fa', '∃E 1', 'subproof');
  });
  t.test('at least 30 exercises; every model proof checks and completes', () => {
    t.ok(Q.QDERS.length >= 30, `${Q.QDERS.length}`);
    [1, 2, 3].forEach(lv => t.ok(Q.QDERS.filter(d => d.lv === lv).length >= 8, `level ${lv}`));
    Q.QDERS.forEach(d => {
      const r = D.runModel(d.p, d.proof, {ql: true});
      t.ok(!r.err, `#${d.id + 1}: ${r.err}`);
      t.ok(D.isComplete(r.st, P(d.c)), `#${d.id + 1} complete`);
    });
  });
  t.test('every exercise is valid on all interpretations up to 3 objects', () => {
    Q.QDERS.forEach(d => {
      const prem = d.p.map(P), concl = P(d.c);
      const sig = [...prem, concl].reduce((s, f) => Q.signature(f, s), {preds: {}, consts: new Set()});
      const counter = Q.forEachInterp(sig.preds, [...sig.consts], 2, I => prem.every(f => Q.evalQ(f, I, {})) && !Q.evalQ(concl, I, {}));
      t.ok(!counter, `#${d.id + 1}`);
    });
  });
  t.test('hints work for every quantifier exercise at every step', () => {
    Q.QDERS.forEach(d => {
      for (let k = 0; k < d.proof.length; k++) {
        const r = D.runModel(d.p, d.proof.slice(0, k), {ql: true});
        [1, 2].forEach(tier => { const h = D.hintFor({d, st: r.st}, tier); t.ok(typeof h === 'string' && h.length > 10, `#${d.id + 1} step ${k}`); });
      }
    });
  });
};
