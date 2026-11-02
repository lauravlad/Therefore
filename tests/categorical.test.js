// Categorical logic: syllogism validity (both readings), statement diagrams,
// square of opposition, immediate inferences.
module.exports = (t, E) => {
  const C = E.categorical;
  const forms = [];
  for (const a of 'AEIO') for (const b of 'AEIO') for (const c of 'AEIO') for (const f of [1, 2, 3, 4]) forms.push([a + b + c, f]);
  const key = ([m, f]) => `${m}-${f}`;

  t.test('there are 256 mood/figure combinations', () => t.eq(forms.length, 256));
  t.test('every pair of premises can be diagrammed', () => {
    forms.forEach(fm => t.ok(C.diagramPremises(C.syllogismParts(fm[0], fm[1]).slice(0, 2), true), key(fm)));
  });
  t.test('the Venn-diagram method agrees with model checking on all 256 forms', () => {
    forms.forEach(([m, f]) => {
      const parts = C.syllogismParts(m, f), d = C.diagramPremises(parts.slice(0, 2), true);
      t.eq(C.isValid(d, parts[2]), C.validFor(m, f, 'boolean'), `${m}-${f}`);
    });
  });
  t.test('Boolean reading: exactly the 15 unconditionally valid forms', () => {
    t.eq(forms.filter(([m, f]) => C.validFor(m, f, 'boolean')).map(key).sort(), C.VALID_BOOLEAN.slice().sort());
  });
  t.test('the named forms without an existence condition are the Boolean-valid ones', () => {
    t.eq(Object.keys(C.NAMES).filter(k => !C.NAMES[k].needs).sort(), C.VALID_BOOLEAN.slice().sort());
  });
  t.test('Aristotelian reading: exactly the 24 named forms', () => {
    t.eq(forms.filter(([m, f]) => C.validFor(m, f, 'aristotelian')).map(key).sort(), Object.keys(C.NAMES).sort());
  });
  t.test('each conditionally valid form needs exactly the listed term to exist', () => {
    for (const k in C.NAMES) {
      const n = C.NAMES[k]; if (!n.needs) continue;
      const m = k.slice(0, 3), f = +k[4];
      t.ok(C.validWith(m, f, [n.needs]), `${k} should be valid if ${n.needs} exists`);
      t.ok(!C.validWith(m, f, []), `${k} should be invalid with no existence assumption`);
    }
  });
  t.test('a sample of forms: Barbara valid, AAA-2 invalid, Darapti depends on reading', () => {
    t.ok(C.validFor('AAA', 1, 'boolean'));
    t.ok(!C.validFor('AAA', 2, 'boolean') && !C.validFor('AAA', 2, 'aristotelian'));
    t.ok(!C.validFor('AAI', 3, 'boolean') && C.validFor('AAI', 3, 'aristotelian'));
  });

  // Statement diagrams. Regions: 1 = S only, 2 = P only, 3 = both.
  const R = [1, 2, 3];
  t.test('statement diagrams: A shades S-outside-P, E shades the overlap', () => {
    t.eq(C.correctState(C.correctStmt('A'), R), {1: 1, 2: 0, 3: 0});
    t.eq(C.correctState(C.correctStmt('E'), R), {1: 0, 2: 0, 3: 1});
  });
  t.test('statement diagrams: I puts an X in the overlap, O in S-outside-P', () => {
    t.eq(C.correctState(C.correctStmt('I'), R), {1: 0, 2: 0, 3: 2});
    t.eq(C.correctState(C.correctStmt('O'), R), {1: 2, 2: 0, 3: 0});
  });
  t.test('diagram checker reports exactly the mismatched regions', () => {
    t.eq(C.diffRegions({1: 1, 2: 0, 3: 0}, C.correctStmt('A'), R), []);
    t.eq(C.diffRegions({1: 0, 2: 0, 3: 1}, C.correctStmt('A'), R), [1, 3]);
    t.eq(C.diffRegions({1: 0, 2: 1, 3: 2}, C.correctStmt('I'), R), [2]);
  });

  // Square of opposition, checked against the traditional table.
  const ARI = {
    AT: {E: 'F', I: 'T', O: 'F'}, AF: {E: '?', I: '?', O: 'T'},
    ET: {A: 'F', I: 'F', O: 'T'}, EF: {A: '?', I: 'T', O: '?'},
    IT: {A: '?', E: 'F', O: '?'}, IF: {A: 'F', E: 'T', O: 'T'},
    OT: {A: 'F', E: '?', I: '?'}, OF: {A: 'T', E: 'F', I: 'T'},
  };
  const CONTRA = {A: 'O', O: 'A', E: 'I', I: 'E'};
  t.test('square, Aristotelian reading: all 24 cases match the traditional table', () => {
    for (const k in ARI) for (const tgt in ARI[k])
      t.eq(C.squareTruth(k[0], k[1] === 'T', tgt, 'aristotelian'), ARI[k][tgt], `${k} → ${tgt}`);
  });
  t.test('square, Boolean reading: only contradictories are determined', () => {
    for (const g of 'AEIO') for (const gv of [true, false]) for (const tgt of 'AEIO') {
      if (tgt === g) continue;
      const want = tgt === CONTRA[g] ? (gv ? 'F' : 'T') : '?';
      t.eq(C.squareTruth(g, gv, tgt, 'boolean'), want, `${g}${gv ? 'T' : 'F'} → ${tgt}`);
    }
  });
  t.test('square relations are named correctly', () => {
    t.eq(C.relation('A', 'O'), 'contradictories'); t.eq(C.relation('I', 'E'), 'contradictories');
    t.eq(C.relation('E', 'A'), 'contraries'); t.eq(C.relation('O', 'I'), 'subcontraries');
    t.eq(C.relation('A', 'I'), 'subalternation'); t.eq(C.relation('O', 'E'), 'subalternation');
  });

  // Immediate inferences.
  t.test('converse, obverse, contrapositive are formed correctly', () => {
    t.eq(C.transform('A', 'converse'), {type: 'A', a: 'P', b: 'S'});
    t.eq(C.transform('A', 'obverse'), {type: 'E', a: 'S', b: '!P'});
    t.eq(C.transform('O', 'obverse'), {type: 'I', a: 'S', b: '!P'});
    t.eq(C.transform('A', 'contrapositive'), {type: 'A', a: '!P', b: '!S'});
  });
  t.test('equivalence: conversion for E and I, contraposition for A and O, obversion for all', () => {
    for (const ty of 'AEIO') for (const op of ['converse', 'obverse', 'contrapositive']) {
      const want = C.OP_EQUIV[op].includes(ty);
      t.eq(C.equivalentStatements({type: ty, a: 'S', b: 'P'}, C.transform(ty, op)), want, `${op} of ${ty}`);
    }
  });
  t.test('the "inverse" distractor is never equivalent', () => {
    for (const ty of 'AEIO') t.ok(!C.equivalentStatements({type: ty, a: 'S', b: 'P'}, C.transform(ty, 'inverse')), ty);
  });
};
