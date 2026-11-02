// Notation setting: display follows the chosen style; input is accepted in every style.
module.exports = (t, E) => {
  const N = E.notation, S = E.sentential, D = E.derivations;
  const withNotation = (name, fn) => { N.use(name); try { fn(); } finally { N.use('logicbook'); } };
  t.test('the default is The Logic Book style', () => t.eq([N.SYMBOLS.not, N.SYMBOLS.and, N.SYMBOLS.cond, N.SYMBOLS.bicond], ['~', '&', '⊃', '≡']));
  t.test('sentences display in each style', () => {
    const f = S.parse('~(A & B) ⊃ (C ≡ D)');
    withNotation('hurley', () => t.eq(S.show(f), '~(A • B) ⊃ (C ≡ D)'));
    withNotation('modern', () => t.eq(S.show(f), '¬(A ∧ B) → (C ↔ D)'));
    t.eq(S.show(f), '~(A & B) ⊃ (C ≡ D)');
  });
  t.test('fixed text (rule names, examples) is translated by sym()', () => {
    withNotation('modern', () => t.eq(N.sym('&I, ⊃E, ~I, ≡E, ∨E'), '∧I, →E, ¬I, ↔E, ∨E'));
    withNotation('hurley', () => t.eq(N.sym('A & B ⊃ ~C'), 'A • B ⊃ ~C'));
  });
  t.test('input in any style parses the same, whatever the setting', () => {
    const want = S.parse('~(A & B) ⊃ (C ≡ D)');
    ['logicbook', 'hurley', 'modern'].forEach(n => withNotation(n, () => {
      ['~(A & B) ⊃ (C ≡ D)', '~(A • B) ⊃ (C ≡ D)', '~(A · B) ⊃ (C ≡ D)', '¬(A ∧ B) → (C ↔ D)', '-(A & B) -> (C <-> D)']
        .forEach(src => t.ok(S.eq(S.parse(src), want), `${n}: ${src}`));
    }));
  });
  t.test('rule names are accepted in any style', () => {
    t.eq(D.parseJust('∧I 1, 2').rule, '&I'); t.eq(D.parseJust('•E 1').rule, '&E');
    t.eq(D.parseJust('→E 1, 2').rule, '⊃E'); t.eq(D.parseJust('¬I 2–4').rule, '~I');
    t.eq(D.parseJust('↔I 2–3, 4–5').rule, '≡I');
  });
  t.test('proofs check the same way under every notation', () => {
    ['hurley', 'modern'].forEach(n => withNotation(n, () => D.DERS.forEach(d => t.ok(!D.runModel(d.p, d.proof).err, `${n} #${d.id + 1}`))));
  });
};
