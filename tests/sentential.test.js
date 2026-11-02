// Sentential logic: parser, printer, evaluator, truth tables, classification,
// equivalence/consistency/validity, and the random generators.
module.exports = (t, E) => {
  const S = E.sentential, P = S.parse;
  const throws = (src, frag) => {
    const r = S.tryParse(src);
    t.ok(r.err, `“${src}” should not parse`);
    if (frag) t.ok(r.err.includes(frag), `error for “${src}” should mention “${frag}”: ${r.err}`);
  };

  t.test('parse and print round-trip, dropping only the outer parentheses', () => {
    [['A', 'A'], ['~A', '~A'], ['A & B', 'A & B'], ['~(A & B)', '~(A & B)'], ['(A & B) ∨ C', '(A & B) ∨ C'],
     ['~~A', '~~A'], ['((A ⊃ B) ≡ (~C ∨ D))', '(A ⊃ B) ≡ (~C ∨ D)'], ['(A)', 'A'], ['~(~A)', '~~A']]
      .forEach(([src, out]) => t.eq(S.show(P(src)), out, src));
  });
  t.test('keyboard and alternative symbols are accepted', () => {
    const same = (a, b) => t.ok(S.eq(P(a), P(b)), `${a} vs ${b}`);
    same('A -> B', 'A ⊃ B'); same('A > B', 'A ⊃ B'); same('A => B', 'A ⊃ B'); same('A → B', 'A ⊃ B');
    same('A <-> B', 'A ≡ B'); same('A = B', 'A ≡ B'); same('A ↔ B', 'A ≡ B');
    same('-A v B', '~A ∨ B'); same('¬A ∧ B', '~A & B'); same('!A | B', '~A ∨ B');
    same('[A & B] ∨ {C}', '(A & B) ∨ C');
  });
  t.test('malformed sentences give helpful errors', () => {
    throws('', 'Type a sentence');
    throws('A & B ∨ C', 'parentheses');
    throws('A &', 'ends too soon');
    throws('(A & B', 'never closed');
    throws('A B', 'no connective');
    throws('a & b', 'capitals');
    throws('(A & B]', 'match');
    throws('A & B)', 'extra right');
    throws('& A', 'needs a sentence on its left');
    throws('A # B', 'recognize');
  });
  t.test('rows come in standard order, starting with all T', () => {
    const rows = S.rowsFor(['A', 'B', 'C']);
    t.eq(rows.length, 8);
    t.eq(rows[0], {A: true, B: true, C: true});
    t.eq(rows[7], {A: false, B: false, C: false});
    t.eq(rows.map(r => r.C), [true, false, true, false, true, false, true, false]);
    t.eq(rows.map(r => r.A), [true, true, true, true, false, false, false, false]);
  });
  t.test('characteristic truth tables', () => {
    const col = src => S.rowsFor(['A', 'B']).map(r => S.value(P(src), r));
    t.eq(col('A & B'), [true, false, false, false]);
    t.eq(col('A ∨ B'), [true, true, true, false]);
    t.eq(col('A ⊃ B'), [true, false, true, true]);
    t.eq(col('A ≡ B'), [true, false, false, true]);
    t.eq(S.rowsFor(['A']).map(r => S.value(P('~A'), r)), [false, true]);
  });
  t.test('classification', () => {
    t.eq(S.classify(P('A ∨ ~A')), 'true');
    t.eq(S.classify(P('((A ⊃ B) & A) ⊃ B')), 'true');
    t.eq(S.classify(P('A & ~A')), 'false');
    t.eq(S.classify(P('~(A ⊃ (B ⊃ A))')), 'false');
    t.eq(S.classify(P('A ⊃ B')), 'indeterminate');
  });
  t.test('equivalence', () => {
    t.ok(S.equivalent(P('~(A & B)'), P('~A ∨ ~B')));
    t.ok(S.equivalent(P('A ⊃ B'), P('~B ⊃ ~A')));
    t.ok(S.equivalent(P('A'), P('A & (B ∨ ~B)')), 'different letters still compared on a joint table');
    t.ok(!S.equivalent(P('A ⊃ B'), P('B ⊃ A')));
  });
  t.test('consistency', () => {
    t.ok(S.consistent([P('A ∨ B'), P('~A')]));
    t.ok(!S.consistent([P('A ⊃ B'), P('A'), P('~B')]));
    t.ok(!S.consistent([P('A & ~A')]));
  });
  t.test('validity', () => {
    t.ok(S.validArg([P('A ⊃ B'), P('A')], P('B')), 'modus ponens');
    t.ok(S.validArg([P('A ⊃ B'), P('~B')], P('~A')), 'modus tollens');
    t.ok(!S.validArg([P('A ⊃ B'), P('B')], P('A')), 'affirming the consequent');
    t.ok(!S.validArg([P('A ⊃ B'), P('~A')], P('~B')), 'denying the antecedent');
    t.ok(S.validArg([P('A & ~A')], P('B')), 'inconsistent premises');
  });
  t.test('table model: one column per connective, main column is the root', () => {
    const m = S.tableModel(P('~(A & B) ⊃ C'));
    t.eq(m.cols.length, 3);
    t.eq(m.tk[m.main].s, '⊃');
    t.eq(m.rows.length, 8);
  });
  t.test('random sentences use exactly 2, 3, or 4 letters and print/parse cleanly', () => {
    [1, 2, 3].forEach(lv => { for (let i = 0; i < 200; i++) {
      const f = S.genSentence(lv);
      t.eq(S.lettersOf(f).length, S.LV[lv].n, S.show(f));
      t.ok(S.eq(P(S.show(f)), f), `round trip ${S.show(f)}`);
      t.ok(S.connCount(f) >= 1);
    } });
  });
  t.test('classification practice produces all three kinds at every level', () => {
    [1, 2, 3].forEach(lv => {
      const seen = new Set();
      for (let i = 0; i < 150; i++) seen.add(S.classify(S.genClassified(lv)));
      t.eq([...seen].sort(), ['false', 'indeterminate', 'true'], `level ${lv}`);
    });
  });
  t.test('table-test problems produce both answers for each kind and level', () => {
    ['equiv', 'cons', 'valid'].forEach(kind => [1, 2, 3].forEach(lv => {
      const seen = new Set();
      for (let i = 0; i < 40; i++) {
        const fs = S.genTest(kind, lv);
        fs.forEach(f => t.ok(S.eq(P(S.show(f)), f)));
        seen.add(S.testAnswer(kind, fs));
      }
      t.eq(seen.size, 2, `${kind} level ${lv}`);
    }));
  });
};
