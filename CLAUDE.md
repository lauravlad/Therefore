# Therefore

A free logic practice web app, hosted on GitHub Pages from `index.html`. It's a static site with no build step, no framework, and no package manager.

## Non-negotiables

- **It stays free, with no accounts.** No sign-up, login, paywall, or server-side user data. Progress is saved only in the browser's `localStorage` (key `therefore-v1`; don't rename it, or people lose their progress).
- **All content is original.** Every exercise, example, term list, hint, and explanation must be written fresh. Don't copy or closely paraphrase textbook problems or prose, including from The Logic Book. Using standard notation and standard technical terms (mood, figure, Barbara, modus ponens, and so on) is fine.
- **It must keep working on GitHub Pages as plain files.** Use relative paths, classic `<script src>` tags (not ES modules, so the page also works when opened from disk), and no bundler or transpiler. External resources are limited to Google Fonts.

## Levels

| # | Level | File | Status |
|---|-------|------|--------|
| 1 | Intro to logic (categorical logic; fallacies planned) | `js/level1-intro.js` | Categorical logic is live |
| 2 | Sentential logic (symbolization, truth tables, derivations) | `js/level2-sentential.js` | Placeholder |
| 3 | Predicate logic (quantifiers, derivations) | `js/level3-predicate.js` | Placeholder |
| 4 | Multi-valued and fuzzy logic (shown as "Beyond two values") | `js/level4-multivalued.js` | Placeholder |

## Logic conventions

- **Categorical diagrams use the Boolean (modern) reading by default.** Universal statements (A, E) carry no existential import. Forms that are valid only on the Aristotelian reading (Barbari, Darapti, and the rest) are marked invalid, and the feedback names the term that would have to exist.
- **Sentential notation follows The Logic Book:** `~` (negation), `&` (conjunction), `∨` (disjunction), `⊃` (material conditional), `≡` (biconditional). Quantifiers are written `(∀x)` and `(∃x)`.
- **A notation setting is planned** (for example, `¬ ∧ → ↔`). Always print connectives through the `SYMBOLS` map in `js/level2-sentential.js` rather than hard-coding the characters, so the setting can switch them in one place.

## Code layout

```
index.html          page shell; loads the CSS, then core.js, then each level file in order
css/style.css       all styles; light/dark palettes are CSS custom properties
js/core.js          shared: pick/esc helpers, saved progress (score/tally), level and view registry, routing, delegated events, home page
js/levelN-*.js      one file per level, each wrapped in an IIFE so its names stay private
```

- A level file calls `registerLevel({num, title, topics})` to add its home-page card. A topic without `go` shows as "Coming soon".
- Each screen is a view: `registerView(name, {render, init?, click?, change?})`. `render()` returns HTML. `init()` returns new exercise state, which is stored in `App.ex`. `core.js` handles `data-go="<view>"` and `data-act="next"`, and passes any other click or change to the current view's handlers.
- Use `score(kind)` and `tally(kind, ok)` for per-exercise progress.
- Escape all interpolated content with `esc()`.

## Style

- The UI must work at phone width and in both light and dark themes. Use the CSS variables; don't hard-code colors.
- Feedback explains why an answer is right or wrong, not just whether it is.
