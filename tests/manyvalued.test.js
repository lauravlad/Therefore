// Many-valued logic: K3 and Ł3 truth tables, fuzzy values, and which tautologies survive.
module.exports = (t, E) => {
  const M = E.manyvalued, S = E.sentential, P = S.parse;
  const T = 1, U = 0.5, F = 0;
  const table = (src, sys) => M.rows3(['P', 'Q']).map(r => M.mv(P(src), r, sys));
  // rows: TT TU TF UT UU UF FT FU FF
  t.test('three-valued rows come in T, U, F order', () => {
    t.eq(M.rows3(['P', 'Q']).map(r => M.NAME3(r.P) + M.NAME3(r.Q)), ['TT', 'TU', 'TF', 'UT', 'UU', 'UF', 'FT', 'FU', 'FF']);
  });
  t.test('negation, conjunction, disjunction (same in K3 and Ł3)', () => {
    ['K3', 'L3'].forEach(sys => {
      t.eq(M.rows3(['P']).map(r => M.mv(P('~P'), r, sys)), [F, U, T], sys);
      t.eq(table('P & Q', sys), [T, U, F, U, U, F, F, F, F], sys);
      t.eq(table('P ∨ Q', sys), [T, T, T, T, U, U, T, U, F], sys);
    });
  });
  t.test('K3 conditional and biconditional', () => {
    t.eq(table('P ⊃ Q', 'K3'), [T, U, F, T, U, U, T, T, T]);
    t.eq(table('P ≡ Q', 'K3'), [T, U, F, U, U, U, F, U, T]);
  });
  t.test('Ł3 conditional and biconditional', () => {
    t.eq(table('P ⊃ Q', 'L3'), [T, U, F, T, T, U, T, T, T]);
    t.eq(table('P ≡ Q', 'L3'), [T, U, F, U, T, U, F, U, T]);
  });
  t.test('fuzzy values: min, max, 1 − x, Łukasiewicz implication', () => {
    const row = {A: 0.7, B: 0.4};
    t.eq(M.mv(P('A & B'), row, 'fuzzy'), 0.4);
    t.eq(M.mv(P('A ∨ B'), row, 'fuzzy'), 0.7);
    t.eq(M.mv(P('~A'), row, 'fuzzy'), 0.3);
    t.eq(M.mv(P('A ⊃ B'), row, 'fuzzy'), 0.7);
    t.eq(M.mv(P('B ⊃ A'), row, 'fuzzy'), 1);
    t.eq(M.mv(P('A ≡ B'), row, 'fuzzy'), 0.7);
    t.eq(M.mv(P('~(A & ~B)'), row, 'fuzzy'), 0.4);
  });
  t.test('fuzzy worked steps end with the right value', () => {
    const steps = M.fuzzySteps(P('~(A & ~B)'), {A: 0.7, B: 0.4});
    t.eq(steps.length, 3);
    t.ok(steps[2].includes('<b>0.4</b>'), steps[2]);
  });
  t.test('P ∨ ~P fails in K3, Ł3, and fuzzy logic', () => {
    ['K3', 'L3', 'fuzzy'].forEach(s => t.ok(!M.tautIn(P('P ∨ ~P'), s).holds, s));
    t.eq(M.tautIn(P('P ∨ ~P'), 'K3').counter, {P: 0.5});
  });
  t.test('P ⊃ P fails in K3 but holds in Ł3 and fuzzy logic', () => {
    t.ok(!M.tautIn(P('P ⊃ P'), 'K3').holds);
    t.ok(M.tautIn(P('P ⊃ P'), 'L3').holds);
    t.ok(M.tautIn(P('P ⊃ P'), 'fuzzy').holds);
  });
  t.test('more survivors and failures', () => {
    t.ok(M.tautIn(P('P ⊃ (Q ⊃ P)'), 'L3').holds);
    t.ok(!M.tautIn(P('((P ⊃ Q) & P) ⊃ Q'), 'L3').holds, 'modus ponens as a sentence fails in Ł3');
    t.ok(M.tautIn(P('~(P & Q) ≡ (~P ∨ ~Q)'), 'L3').holds, 'De Morgan survives in Ł3');
    t.ok(!M.tautIn(P('~(P & ~P)'), 'K3').holds);
  });
  t.test('no sentence is a K3 tautology (all-U row)', () => {
    M.TAUTS.forEach(s => t.ok(!M.tautIn(P(s), 'K3').holds, s));
  });
  t.test('every practice sentence in the tautology list is a classical tautology', () => {
    M.TAUTS.forEach(s => t.eq(S.classify(P(s)), 'true', s));
  });
  t.test('three-valued logic agrees with classical logic on T/F rows', () => {
    M.SHOWCASE.forEach(s => {
      const f = P(s);
      S.rowsFor(S.lettersOf(f)).forEach(row => {
        const num = Object.fromEntries(Object.entries(row).map(([k, v]) => [k, v ? 1 : 0]));
        ['K3', 'L3'].forEach(sys => t.eq(M.mv(f, num, sys), S.value(f, row) ? 1 : 0, `${s} ${sys}`));
      });
    });
  });
};
