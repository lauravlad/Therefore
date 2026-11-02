# Therefore

A free logic practice web app, hosted on GitHub Pages from `index.html`. It's a static site with no build step, no framework, and no package manager.

## Non-negotiables

- **Free, with no accounts.** No sign-up, login, paywall, tracking, or server-side user data. Progress and settings are saved only in the browser's `localStorage` (key `therefore-v1`; don't rename it, or people lose their progress).
- **Every module starts with a collapsible "Key definitions" section** (use `keyDefs()` from `core.js`), followed by practice exercises with step-by-step feedback. Feedback explains why an answer is right or wrong, not just whether it is.
- **All definitions, explanations, examples, and exercises are original**, written in our own words.
- **Allowed sources (CC BY 4.0 only)**, and every one used must be credited on the Credits page (title, author, license, link):
  - Matthew Knachel, *Fundamental Methods of Logic*, **original 2017 edition** (wisconsin.pressbooks.pub/logicfundamentals)
  - *forall x: Calgary* (forallx.openlogicproject.org)
  - The Open Logic Project (openlogicproject.org)
- **Never use as a source:** *The Logic Book*, Hurley, Baronett, the revised Knachel/Gould edition (NC license), or any source with an NC or SA license. (Offering a notation style named after a book is fine; using the book's content is not.)
- **Answer checkers must have tests.** Any code that grades answers (validity, truth tables, proofs, symbolizations, and so on) needs automated tests in `tests/`, and **all tests must pass before committing**: `node tests/run.js`.
- **It must keep working on GitHub Pages as plain files.** Use relative paths and classic `<script src>` tags (not ES modules, so the page also works when opened from disk). External resources are limited to Google Fonts.

## Levels

| # | Level | File | Modules |
|---|-------|------|---------|
| 1 | Intro to logic | `js/level1-intro.js` | Categorical logic (statements, square of opposition, immediate inferences, syllogisms, named forms); Fallacies (study by family) |
| 2 | Sentential logic | `js/level2-sentential.js` | Symbolization; Truth tables (main connective, full tables, spot the error, equivalence/consistency/validity); Derivations (Fitch-style checker) |
| 3 | Predicate logic | `js/level3-predicate.js` | Quantifiers (symbolization); Quantifier derivations (∀E, ∀I, ∃I, ∃E) |
| 4 | Multi-valued and fuzzy logic (shown as "Beyond two values") | `js/level4-multivalued.js` | Three-valued tables (K3, Ł3); fuzzy truth values; which tautologies survive |

## Logic conventions

- **Categorical diagrams use the Boolean reading by default.** The `reading` setting switches the square of opposition and syllogism validity to the Aristotelian reading (for syllogisms, every term is assumed to have members). Forms valid only on the Aristotelian reading are flagged with the term that must exist.
- **Notation.** The default is The Logic Book style: `~ & ∨ ⊃ ≡` with capital sentence letters. Settings also offers Hurley style (`~ • ∨ ⊃ ≡`) and modern style (`¬ ∧ ∨ → ↔`). The choice applies across the whole app:
  - Print sentences with `show()`, which reads the shared `SYMBOLS` map.
  - Write fixed text (rule names like `⊃E`, definitions, examples) in Logic Book symbols and pass it through `sym()` when displaying it.
  - Input in any style, plus keyboard forms (`- & v -> <->`, `\A` and `\E` for quantifiers), is always accepted.
- **Quantifiers are always written `(∀x)` and `(∃x)`**, whatever the notation setting. Variables are x, y, z; constants are lowercase a–u and w (v is reserved as a keyboard form of ∨).
- **Binary connectives need their own parentheses**, except around the whole sentence. Truth-table rows start with all T (three-valued tables: T, U, F, with the first letter changing slowest).
- **Derivation rules:** R, &I, &E, ∨I, ∨E, ⊃I, ⊃E, ~I, ~E, ≡I, ≡E, plus ∀E, ∀I, ∃I, ∃E in Level 3. For ∀I and ∃E, the constant must not appear in any premise or undischarged assumption, or in the sentence concluded. For ∃E, it also must not appear in the existential sentence.
- **Symbolization answers are accepted when equivalent to the model answer**: by truth table in Level 2, and on every interpretation with a domain of up to 3 objects in Level 3. The model answer is shown afterward.
- **Many-valued logic:** T = 1, U = ½, F = 0, and only T is designated. K3 conditional: max(1 − P, Q). Ł3 and fuzzy conditional: min(1, 1 − P + Q). Fuzzy logic: ~ = 1 − x, & = min, ∨ = max.

## Code layout

```
index.html              page shell; loads the CSS, then core.js, then each level file in order
css/style.css           all styles; light and dark palettes are CSS custom properties
js/core.js              helpers, saved progress and settings, notation (SYMBOLS, sym), registry,
                        hash routing, delegated events, keyDefs()/seg(), home, Settings, Credits
js/levelN-*.js          one file per level, each wrapped in an IIFE so its names stay private
tests/run.js            loads the app files into a sandbox and runs tests/*.test.js
```

- A level calls `registerLevel({num, title, topics})` for its home-page card (a topic without `go` shows "Coming soon") and `registerView(name, {render, init?, click?, change?, input?, keydown?, onSetting?, after?})` for each screen. The URL hash mirrors the current view.
- `Engines.*` exposes each level's pure logic to the tests. `Shared.*` holds building blocks that later levels reuse: Level 2's parser and proof checker (`Shared.logic`, `Shared.derivations`, including `registerRule` and `makeDerivationModule`).
- Use `score(kind)` and `tally(kind, ok)` for progress, and `getSetting`/`setSetting` for settings. Escape all interpolated text with `esc()`.

## Style

- The UI must work at phone width and in both light and dark themes. Use the CSS variables; don't hard-code colors.
