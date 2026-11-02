// Symbolization: content checks and the answer checker (equivalence + mistake feedback).
module.exports = (t, E) => {
  const {SYMS, checkSym, symTips} = E.symbolization, S = E.sentential;
  const item = en => SYMS.find(s => s.en === en);
  t.test('at least 60 sentences across three levels', () => {
    t.ok(SYMS.length >= 60, `${SYMS.length}`);
    [1, 2, 3].forEach(lv => t.ok(SYMS.filter(s => s.lv === lv).length >= 15, `level ${lv}`));
  });
  t.test('every model answer parses and uses exactly the letters in its key', () => {
    SYMS.forEach(s => {
      const f = S.parse(s.ans);
      t.eq(S.lettersOf(f), Object.keys(s.key).sort(), s.en);
    });
  });
  t.test('the model answer is always accepted', () => {
    SYMS.forEach(s => { const r = checkSym(s, s.ans); t.ok(r.ok && r.exact, s.en); });
  });
  t.test('equivalent answers are accepted', () => {
    t.ok(checkSym(item('The soup is hot unless the stove is off.'), '~O ⊃ H').ok);
    t.ok(checkSym(item('Neither Ana nor Ben came to the party.'), '~(A ∨ B)').ok);
    t.ok(checkSym(item('The printer works only if it has paper.'), '~P ⊃ ~W').ok);
    t.ok(checkSym(item('Either Ava or Noah will drive, but not both.'), '~(A ≡ N)').ok);
  });
  t.test('reversed "only if" gets the only-if explanation', () => {
    const r = checkSym(item('The printer works only if it has paper.'), 'P ⊃ W');
    t.ok(!r.ok); t.ok(r.mistake && r.mistake.includes('only if'), r.mistake);
    const r2 = checkSym(item('We’ll go to the beach only if it’s sunny and warm.'), '(S & W) ⊃ B');
    t.ok(r2.mistake && r2.mistake.includes('only if'), r2.mistake);
  });
  t.test('reversed "if" (antecedent second) is explained', () => {
    const r = checkSym(item('The game is canceled if it rains.'), 'G ⊃ R');
    t.ok(r.mistake && r.mistake.includes('antecedent'), r.mistake);
  });
  t.test('neither/nor, not both, iff, and unless mistakes are recognized', () => {
    t.ok(checkSym(item('Neither Ana nor Ben came to the party.'), '~A ∨ ~B').mistake.includes('Neither'));
    t.ok(checkSym(item('The first train and the second train are not both late.'), '~F & ~S').mistake.includes('Not both'));
    t.ok(checkSym(item('Omar is happy if and only if his team wins.'), 'O ⊃ T').mistake.includes('one direction'));
    t.ok(checkSym(item('The soup is hot unless the stove is off.'), 'H ≡ ~O').mistake.includes('inclusively'));
    t.ok(checkSym(item('The soup is hot unless the stove is off.'), 'O ⊃ H').mistake.includes('unless'));
  });
  t.test('letters outside the key and unreadable input are rejected without grading', () => {
    t.ok(checkSym(item('Maya is not home.'), '~Q').err.includes('key'));
    t.ok(checkSym(item('Maya is not home.'), '~').err);
  });
  t.test('a missing letter is pointed out', () => {
    const r = checkSym(item('The library is open and the café is open.'), 'L');
    t.ok(!r.ok); t.eq(r.missing, ['C']);
  });
  t.test('"if and only if" does not trigger the "only if" tip', () => {
    const tips = symTips('Omar is happy if and only if his team wins.');
    t.ok(tips.some(x => x.includes('if and only if')) && !tips.some(x => x.startsWith('“P only if')));
  });
};
