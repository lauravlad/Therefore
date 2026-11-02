// Derivations: every rule (accepting and rejecting), scope errors, citation parsing,
// proof bookkeeping, all exercise model proofs, and hints.
module.exports = (t, E) => {
  const D = E.derivations, S = E.sentential;
  const setup = (prem, model, closeAll) => {
    const r = D.runModel(prem, model || []);
    if (r.err) throw new Error('setup failed: ' + r.err);
    if (closeAll) while (r.st.stack.length) D.endSub(r.st);
    return r.st;
  };
  const ok = (st, s, j) => { const r = D.addLine(st, s, j); t.ok(!r.err, `“${s}  ${j}” should be accepted: ${r.err}`); };
  const bad = (st, s, j, frag) => {
    const n = st.lines.length, r = D.addLine(st, s, j);
    t.ok(r.err, `“${s}  ${j}” should be rejected`);
    if (frag) t.ok(r.err.includes(frag), `error should mention “${frag}”: ${r.err}`);
    t.eq(st.lines.length, n, 'a rejected line is not added');
  };

  // ----- Citation parsing -----
  t.test('justifications: symbols, keyboard forms, and ranges', () => {
    t.eq(D.parseJust('⊃E 1, 3'), {rule: '⊃E', cites: [{n: 1}, {n: 3}]});
    t.eq(D.parseJust('>E 1,3').rule, '⊃E');
    t.eq(D.parseJust('->E 1 3').rule, '⊃E');
    t.eq(D.parseJust('vE 1, 2-4, 5-7'), {rule: '∨E', cites: [{n: 1}, {a: 2, b: 4}, {a: 5, b: 7}]});
    t.eq(D.parseJust('-I 2–5'), {rule: '~I', cites: [{a: 2, b: 5}]});
    t.eq(D.parseJust('=E 1,2').rule, '≡E');
    t.eq(D.parseJust('<->I 2-3, 4-5').rule, '≡I');
    t.eq(D.parseJust('&i 1,2').rule, '&I');
    t.eq(D.parseJust('reit 2').rule, 'R');
    t.eq(D.parseJust('¬E 3—6').rule, '~E');
  });
  t.test('bad justifications are explained', () => {
    t.ok(D.parseJust('A').err.includes('Assume'));
    t.ok(D.parseJust('Premise').err.includes('Premises'));
    t.ok(D.parseJust('MP 1, 2').err.includes('isn’t one of the rules'));
    t.ok(D.parseJust('').err);
    t.ok(D.parseJust('&E 1-').err.includes('can’t read'));
  });
  t.test('citation shapes are checked for every rule', () => {
    const st = setup(['A', 'A ⊃ B']);
    bad(st, 'A', 'R 1, 2', 'one line');
    bad(st, 'A & A', '&I 1', 'two lines');
    bad(st, 'B', '⊃E 1', 'two lines');
    bad(st, 'A ⊃ B', '⊃I 1', 'range');
    bad(st, '~A', '~I 1', 'range');
    bad(st, 'A', '~E 1', 'range');
    bad(st, 'A ≡ A', '≡I 1, 2', 'two subproofs');
    bad(st, 'A', '∨E 1, 2', 'disjunction and two subproofs');
  });

  // ----- Each rule -----
  t.test('R: repeats an accessible line exactly', () => {
    const st = setup(['A', 'B'], ['1|C|A']);
    ok(st, 'A', 'R 1');
    bad(setup(['A'], ['1|C|A']), 'B', 'R 1', 'repeats a line exactly');
  });
  t.test('&I: either order, rejects the wrong conjunction', () => {
    ok(setup(['A', 'B']), 'A & B', '&I 1, 2');
    ok(setup(['A', 'B']), 'B & A', '&I 1, 2');
    ok(setup(['A']), 'A & A', '&I 1, 1');
    bad(setup(['A', 'B']), 'A ∨ B', '&I 1, 2', 'conjunction');
    bad(setup(['A', 'B']), 'A & C', '&I 1, 2', 'would give');
  });
  t.test('&E: either conjunct; needs a conjunction', () => {
    ok(setup(['A & B']), 'A', '&E 1');
    ok(setup(['A & B']), 'B', '&E 1');
    bad(setup(['A & B']), 'C', '&E 1', 'either');
    bad(setup(['A ∨ B']), 'A', '&E 1', 'needs a conjunction');
  });
  t.test('∨I: either side; one side must be the cited line', () => {
    ok(setup(['A']), 'A ∨ Z', '∨I 1');
    ok(setup(['A']), 'Z ∨ A', '∨I 1');
    bad(setup(['A']), 'B ∨ C', '∨I 1', 'one side');
    bad(setup(['A']), 'A & B', '∨I 1', 'disjunction');
  });
  const orCases = () => setup(['A ∨ B', 'A ⊃ C', 'B ⊃ C'], ['1|A|A', '1|C|⊃E 2, 4', '1|B|A', '1|C|⊃E 3, 6'], true);
  t.test('∨E: two cases reaching the same sentence', () => {
    ok(orCases(), 'C', '∨E 1, 4–5, 6–7');
    ok(orCases(), 'C', '∨E 1, 6–7, 4–5');
  });
  t.test('∨E: rejects wrong disjunction, wrong assumptions, wrong conclusion', () => {
    bad(orCases(), 'C', '∨E 2, 4–5, 6–7', 'disjunction');
    bad(orCases(), 'A', '∨E 1, 4–5, 6–7', 'must end with');
    const st = setup(['A ∨ B', 'C'], ['1|A|A', '1|C|R 2', '1|D|A', '1|C|R 2'], true);
    bad(st, 'C', '∨E 1, 3–4, 5–6', 'must assume');
  });
  const condSub = () => setup(['A ⊃ B'], ['1|A|A', '1|B|⊃E 1, 2'], true);
  t.test('⊃I: assumption ⊃ last line', () => {
    ok(condSub(), 'A ⊃ B', '⊃I 2–3');
    bad(condSub(), 'B ⊃ A', '⊃I 2–3', 'antecedent');
    bad(condSub(), 'A ⊃ A', '⊃I 2–3', 'consequent');
    bad(condSub(), 'A & B', '⊃I 2–3', 'conditional');
  });
  t.test('⊃E: either citation order; rejects affirming the consequent', () => {
    ok(setup(['A ⊃ B', 'A']), 'B', '⊃E 1, 2');
    ok(setup(['A ⊃ B', 'A']), 'B', '⊃E 2, 1');
    bad(setup(['A ⊃ B', 'B']), 'A', '⊃E 1, 2', 'affirming the consequent');
    bad(setup(['A ⊃ B', 'C']), 'B', '⊃E 1, 2', 'antecedent');
    bad(setup(['A ⊃ B', 'A']), 'A', '⊃E 1, 2', 'consequent');
    bad(setup(['A', 'B']), 'B', '⊃E 1, 2', 'neither cited line is a conditional');
  });
  const negSub = () => setup(['A ⊃ B', '~B'], ['1|A|A', '1|B|⊃E 1, 3', '1|~B|R 2'], true);
  t.test('~I: assumption leads to a contradiction', () => {
    ok(negSub(), '~A', '~I 3–5');
    bad(negSub(), 'A', '~I 3–5', 'negation of the subproof’s assumption');
    bad(setup(['A ⊃ B'], ['1|A|A', '1|B|⊃E 1, 2'], true), '~A', '~I 2–3', 'sentence and its negation');
  });
  t.test('~I: the contradiction must be at the subproof’s own level', () => {
    const st = setup(['~B'], ['1|A|A', '2|B|A', '2|~B|R 1', '1|B ⊃ ~B|⊃I 3–4'], true);
    bad(st, '~A', '~I 2–5', 'sentence and its negation');
  });
  t.test('~E: assumed negation leads to a contradiction', () => {
    ok(setup(['~~A'], ['1|~A|A', '1|~~A|R 1'], true), 'A', '~E 2–3');
    bad(setup(['~~A'], ['1|~A|A', '1|~~A|R 1'], true), '~A', '~E 2–3', 'whose negation was assumed');
    bad(setup(['B', '~B'], ['1|A|A', '1|B|R 1', '1|~B|R 2'], true), 'A', '~E 3–5', 'assumes a negation');
    bad(setup(['B'], ['1|~A|A', '1|B|R 1'], true), 'A', '~E 2–3', 'sentence and its negation');
  });
  const bicondSubs = () => setup(['A ⊃ B', 'B ⊃ A'], ['1|A|A', '1|B|⊃E 1, 3', '1|B|A', '1|A|⊃E 2, 5'], true);
  t.test('≡I: one subproof each way, in either citation order', () => {
    ok(bicondSubs(), 'A ≡ B', '≡I 3–4, 5–6');
    ok(bicondSubs(), 'A ≡ B', '≡I 5–6, 3–4');
    ok(bicondSubs(), 'B ≡ A', '≡I 3–4, 5–6');
    bad(bicondSubs(), 'A ⊃ B', '≡I 3–4, 5–6', 'biconditional');
    bad(setup(['A ⊃ B'], ['1|A|A', '1|B|⊃E 1, 2', '1|A|A', '1|B|⊃E 1, 4'], true), 'A ≡ B', '≡I 2–3, 4–5', 'another that assumes');
  });
  t.test('≡E: from either side to the other', () => {
    ok(setup(['A ≡ B', 'A']), 'B', '≡E 1, 2');
    ok(setup(['A ≡ B', 'B']), 'A', '≡E 1, 2');
    ok(setup(['A ≡ B', 'B']), 'A', '≡E 2, 1');
    bad(setup(['A ≡ B', 'A']), 'A', '≡E 1, 2', 'gives B');
    bad(setup(['A ≡ B', 'C']), 'B', '≡E 1, 2', 'one of its sides');
    bad(setup(['A ⊃ B', 'A']), 'B', '≡E 1, 2', 'neither cited line is a biconditional');
  });

  // ----- Scope -----
  t.test('scope: a line inside a closed subproof cannot be cited', () => {
    const st = condSub();
    bad(st, 'B', 'R 3', 'already closed');
    bad(st, 'B', 'R 3', '2–3');
    bad(st, 'A', 'R 2', 'out of scope');
  });
  t.test('scope: lines of an open subproof are available inside it, and outer lines too', () => {
    const st = setup(['A ⊃ B'], ['1|A|A', '2|C|A']);
    ok(st, 'B', '⊃E 1, 2');
  });
  t.test('scope: a subproof cannot be cited while it is still open', () => {
    const st = setup(['A'], ['1|B|A', '1|A|R 1']);
    bad(st, 'B ⊃ A', '⊃I 2–3', 'still open');
  });
  t.test('scope: a subproof nested in a closed subproof is out of scope', () => {
    const st = setup(['A'], ['1|B|A', '2|C|A', '2|A|R 1', '1|C ⊃ A|⊃I 3–4'], true);
    bad(st, 'C ⊃ A', '⊃I 3–4', 'already closed');
  });
  t.test('scope: ranges must start at an assumption and end where the subproof ends', () => {
    const st = condSub();
    bad(st, 'A ⊃ A', '⊃I 2–2', 'ends at line 3');
    bad(st, 'A ⊃ B', '⊃I 1–3', 'isn’t an assumption');
  });
  t.test('scope: citing future or nonexistent lines', () => {
    const st = setup(['A']);
    bad(st, 'A', 'R 5', 'doesn’t exist yet');
    bad(st, 'A', 'R 2', 'doesn’t exist yet');
    bad(st, 'A', 'R 0', 'no line 0');
  });
  t.test('scope: a subproof that ends inside a nested subproof has no last line of its own', () => {
    const st = setup(['A'], ['1|B|A', '2|C|A', '2|A|R 1'], true);
    bad(st, 'B ⊃ A', '⊃I 2–4', 'nested');
  });

  // ----- Bookkeeping -----
  t.test('ending a subproof at the top level is an error', () => {
    t.ok(D.endSub(setup(['A'])).err);
  });
  t.test('undo restores lines and subproof depth', () => {
    const st = setup(['A']);
    D.assume(st, 'B'); t.eq(st.stack.length, 1);
    D.endSub(st); t.eq(st.stack.length, 0);
    D.undo(st); t.eq(st.stack.length, 1);
    D.undo(st); t.eq(st.lines.length, 1); t.eq(st.stack.length, 0);
    t.ok(!D.undo(st));
  });
  t.test('assumptions must parse', () => {
    const st = setup(['A']);
    t.ok(D.assume(st, 'A &').err);
    t.eq(st.lines.length, 1);
  });
  t.test('a proof is complete only with the conclusion on the outermost level', () => {
    const P = S.parse;
    const st = setup(['A ⊃ B'], ['1|A|A', '1|B|⊃E 1, 2']);
    t.ok(!D.isComplete(st, P('B')), 'B only inside a subproof');
    D.endSub(st);
    t.ok(!D.isComplete(st, P('A ⊃ B')), 'a premise alone does not count');
    ok(st, 'A ⊃ B', '⊃I 2–3');
    t.ok(D.isComplete(st, P('A ⊃ B')));
  });

  // ----- Exercises and hints -----
  t.test('at least 40 exercises across three levels', () => {
    t.ok(D.DERS.length >= 40, `${D.DERS.length}`);
    [1, 2, 3].forEach(lv => t.ok(D.DERS.filter(d => d.lv === lv).length >= 10, `level ${lv}`));
  });
  t.test('every exercise’s model proof checks and completes', () => {
    D.DERS.forEach(d => {
      const r = D.runModel(d.p, d.proof);
      t.ok(!r.err, `#${d.id + 1}: ${r.err}`);
      t.ok(D.isComplete(r.st, S.parse(d.c)), `#${d.id + 1} complete`);
    });
  });
  t.test('every exercise’s conclusion actually follows (truth-table check)', () => {
    D.DERS.forEach(d => t.ok(S.validArg(d.p.map(S.parse), S.parse(d.c)), `#${d.id + 1}`));
  });
  t.test('hints: a strategy first, then the model’s first step', () => {
    D.DERS.forEach(d => {
      const ex = {d, st: D.newProof(d.p)};
      const h1 = D.hintFor(ex, 1), h2 = D.hintFor(ex, 2);
      t.ok(h1 && h1.length > 20, `#${d.id + 1} tier 1`);
      const first = d.proof[0].split('|')[1].trim();
      t.ok(h2.includes(S.show(S.parse(first))), `#${d.id + 1} tier 2 should mention ${first}: ${h2}`);
    });
  });
  t.test('hints follow the student’s progress through a proof', () => {
    D.DERS.forEach(d => {
      for (let k = 1; k < d.proof.length; k++) {
        const r = D.runModel(d.p, d.proof.slice(0, k));
        const h = D.hintFor({d, st: r.st}, 2);
        t.ok(typeof h === 'string' && h.length > 10, `#${d.id + 1} after ${k} lines`);
      }
    });
  });
  t.test('hint inside a subproof names what to aim for', () => {
    const d = D.DERS.find(x => x.c === 'A ⊃ C' && x.p.length === 2);
    const r = D.runModel(d.p, d.proof.slice(0, 1));
    t.ok(D.hintFor({d, st: r.st}, 1).includes('C'));
  });
};
