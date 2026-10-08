# How the typo audit is triaged

[`typos.md`](typos.md) lists what the scanners find; this document records how each finding was
judged, so that later triage reaches the same answers. Every row of `typos.md` was triaged on
2026-10-02 against master at `19cdde9029` by reading the declaration, comment or file it points
at — the scanner's own suggestion was treated as a hint, never as the fix. The verdict is the
row's `Status` and `Note`; [`typo_review.jsonl`](typo_review.jsonl) keeps, for every triaged
row, the declarations it covers and what happens to each (`rename` with the new name, `keep`,
`drop-name`, `deprecate`). Notes refer to other rows by an id such as `NAME-B2#0022`; the `id`
field of `typo_review.jsonl` says which row that is.

A `confirmed` row is meant to become part of a pull request that maintainers review, so the bar
is "this is an improvement a reviewer will accept", not "the scanner is technically right". When
in doubt a row is not `confirmed`. #44329 (`preserves_limit_cone` → `preservesLimit_cone`) was
closed by a maintainer as "not an improvement"; most of the rules below exist to avoid repeating
it.

## Statuses

- `confirmed` — a real error or a clear convention violation, with a known exact fix. For a
  rename the note starts ``→ `newName` ``; for prose ``fix: `replacement` ``; for a duplicate
  ``deprecate `X` in favour of `Y` ``; for an instance whose name goes ``→ `(anonymous instance)` ``.
- `fp` — not a problem: a scanner false positive, an English word or phrase, an accepted exception,
  a deliberate choice, or a name that follows its family.
- `wontfix` — a real inconsistency that should still not be changed: no consensus, churn far
  above the benefit, meta code mirroring Lean core, a keyword workaround.
- `open` — needs a maintainer's decision; the note says what the question is.

## Naming conventions

1. Theorems and lemmas: `snake_case`. `Prop`-valued definitions, structures, classes, inductive
   types and `Type`-valued definitions: `UpperCamelCase`. Other definitions (functions, data):
   `lowerCamelCase`. Fields and constructors follow the rule for a declaration of the same kind.
2. An `UpperCamelCase` name inside another name is written by lowercasing the **whole initial run
   of capitals**: `IsCompact → isCompact`, `SFinite → sfinite`, `NNReal → nnreal`,
   `AEMeasurable → aemeasurable`, `SMulPosReflectLE → smulPosReflectLE`. Never `sFinite`,
   `nnReal`, `aeMeasurable` (stated by a maintainer on #44292).
3. A name describes the statement. A `snake_case` token sequence is a Lean 3 leftover only if it
   spells a declaration (or notation) that occurs in the statement. Not leftovers: English
   phrases (`preserves_limit_cone` for `IsLimit (F.mapCone t)`), the `of_` connector introducing
   a hypothesis (`compl_isBase_of_dual`), adjacent components naming separate things
   (`iterate_frobenius` is `(frobenius R p)^[n]`), and tokens that are themselves declarations.
4. A deprecated declaration is never renamed; `Mathlib/Deprecated/` is out of scope.
5. Instances: the fix for a *badly named* instance (an `UpperCamelCase` name, a `snake_case` name
   on a data instance, a name that shadows its class) is to drop the name, with no deprecated
   alias, replacing its uses by `inferInstance`/`inferInstanceAs`. A `Prop`-valued instance with
   a conventional `snake_case` name is fine: making every instance anonymous is not the goal.
6. A renamed theorem keeps `@[deprecated (since := "…")] alias old := new`, a renamed `def` keeps
   `@[deprecated new (since := "…")] abbrev old := new`, and an `@[to_additive]` declaration
   renames its additive twin too. `Archive/` and `Counterexamples/` need no aliases.
7. A new name must be free. If it is taken by the same statement, the fix is a deprecation.
8. Dictionary spellings: `{x | p x}` is `setOfPred` (`setOf` became `Set.ofPred` in #41507),
   `∉` is `notMem`. A primed or unbundled twin takes its twin's spelling; an established family
   (e.g. the `.restrictScalars` dot-notation lemmas) counts as evidence even when the statement
   does not contain the camelCase name literally.
9. The new name is derived from the statement and the sibling names, not taken from the scanner
   (`nnorm → norm` should have been `nnorm → nnnorm`; `nequiv → equiv` would have dropped a
   negation).
10. A name that follows no convention but does not misdescribe its statement (`not_eq` for `≠`, a
    loose `mem`) is `wontfix`.

## Category guidance

### Prose typos — `NAME-F1`, `STR-*`, `TREE-*`, `TEXT-*`, `DATA-Y1`–`Y4`, `DEP-X1`, `DEP-X2`, `DOC-C3`

- Decide from the sentence whether the word is a mistake. Real-word slips count
  (`subjective` for `surjective`, `form` for `from`). Technical terms, proper names, foreign
  words, identifiers, code, and deliberate wording are `fp`.
- British versus American spelling is `wontfix` (Mathlib does not enforce one) unless the same
  docstring mixes both spellings of that word.
- Derive the correction from context; the scanner's guess is often wrong (`entirery` →
  `entirety`, not `entirely`). You may add other clear-cut slips in the same sentence or
  docstring, labelled "same sentence:" or "nearby:", but do not go hunting beyond that. If the same slip occurs at other sites (grep), list
  them in the note ("also at path:line") so one PR fixes all.
- Titles of papers and books (bibliography, YAML `title:` fields) are quoted: never change
  their wording; only a real misspelling of the published title is `confirmed`.
- `DOC-C3` doubled words: `confirmed` for accidental doubling ("the the"), `fp` when intended
  ("that that", "had had") or when the two words are in different clauses, list items, or code.
- `STR-*`: string literals are user-facing messages or test names; a misspelling is still a
  misspelling. Hyphenated real words (`round-trips`) are `fp`.

### References — `DOC-A5`, `DOC-B1`–`B4`, `DOC-D2`, `DEP-X3`–`X5`, `DATA-Y5`, `DATA-Y6`, `PATH-*`

- Find the correct target (grep the tree, `docs/references.bib`, `library_note`s) and confirm
  with the exact replacement, e.g. ``fix: `[Stone1938]` `` or
  ``fix: `Mathlib/Order/TFAE.lean` ``. If the referent is gone, the fix is to reword or delete
  the reference: say exactly how.
- `DOC-D2` unbalanced backticks: confirm with the exact corrected text after checking the whole
  docstring (multi-line code spans and ``` fences are legitimate).
- `DATA-Y5` uncited bibliography entries: `wontfix` (removing entries is a separate cleanup)
  unless a citation spells the key differently — then confirm fixing the citation or the key.
- `DATA-Y6` duplicates: confirm merging when two entries are the same work and edition.
- `PATH-*` file renames move every importer: confirm only when the file name is clearly
  misspelled or cased against Mathlib's own spelling of the identifier; state the new path.

### Module docstring headings — `DOC-A1`–`DOC-A4`

Mathlib's documentation style: a module docstring starts with a `# Title`; standard sections
are `## Main definitions`, `## Main statements` (`## Main results` is also common),
`## Notation`, `## Implementation notes`, `## References`, `## Tags`, `## TODO`; headings
are in sentence case (proper nouns keep their capitals).

- `DOC-A1` case variants (`Main Definitions`, `Implementation Notes`): `confirmed` with the
  sentence-case heading, unless the capital is a proper noun or acronym.
- `DOC-A2` trailing punctuation: `confirmed` when the line really is a heading; `fp` when the
  scanner mistook a non-heading line (a line of code or maths starting with `#`) for one.
- `DOC-A3` rare variants: `Main definition`/`Main result`/`Reference` in the singular when the
  section lists exactly one item are acceptable (`fp`); a singular heading over two or more items
  → plural (`confirmed`). Established synonyms (`Implementation details`, `Implementation`,
  `Main theorems`, `TODOs`) are `wontfix` (renaming is churn). Confirm misspellings.
- `DOC-A4` structure anomalies: missing `#` title in the module docstring → `confirmed` only if
  the file has a normal module docstring that lacks a title line (meta/tactic files with a
  one-paragraph docstring are common and acceptable: `wontfix`); `###` outside a `##` section →
  usually `wontfix` (harmless) unless clearly a level typo.

### Spelling and markup consistency — `DOC-C1`, `DOC-C2`, `DOC-D1`, `DOC-D3`, `DOC-D4`

- `DOC-C1` hyphenation (`type-classes` vs `typeclasses`, `semi-ring` vs `semiring`): confirm the
  majority form unless the minority form is inside a quotation/title or code. British vs
  American variants: `wontfix`, unless mixed within one docstring.
- `DOC-C2` lowercase proper nouns (`krull`, `hopf`): confirm when it is prose; `fp` when it is an
  identifier, a lemma-name fragment, inside code, or an adjective conventionally lowercase
  (`abelian`).
- `DOC-D1` ASCII stand-ins (`->`, `<=`, `<=>`): confirm in prose and maths; `fp` inside quoted
  Lean syntax that needs ASCII, or inside quotations of external text.
- `DOC-D3` marker casing (`Todo`, `todo`): confirm `TODO` when it is a marker; `fp` in prose.
- `DOC-D4` `--comment`: confirm `-- comment` for a comment; for commented-out code also confirm
  `-- ` (the fix is the space; do not delete code).

### Declaration names

- `NAME-A1` uppercase tokens in theorem names: confirm when the token is an `UpperCamelCase`
  declaration and the name refers to it (usually it occurs in the statement):
  lowercase per rule 2, e.g. `polarizationIn_Injective → polarizationIn_injective`.
  `fp`: geometry labels and point names (IMO archive), single letters, Greek, data-valued
  definitions that are `UpperCamelCase` by exception (`Gamma`, `LSeries`, `Lp`), names of
  syntax/tactics in meta code. `True`/`False` → `true`/`false` follows siblings.
- `NAME-A2`/`A3`/`A5`/`A9`/`A10`/`A11` casing of definitions, types, constructors,
  namespaces: renames are costly; confirm only clear violations outside meta code (meta code
  under `Mathlib/Tactic`, `Mathlib/Lean`, `Mathlib/Util` follows Lean core and is usually
  `wontfix`). A namespace named after a theorem for dot notation (`namespace isSheaf_iff`) is
  `fp`. A trailing underscore working around a keyword is `wontfix`.
- `NAME-A4` data definitions in `snake_case`: confirm `lowerCamelCase` when it is a plain data
  definition (`copy_of_normedField` → `copyOfNormedField`); `fp` for `Simps` projections, names
  prescribed by a framework, and definitions whose name is a lemma-style description of a proof
  term used as data (judge by the family in the same file).
- `NAME-I1` instance names to drop: the fix is always to drop the name (an anonymous instance,
  no alias) and replace every use. Confirmed when the name is genuinely wrong — `UpperCamelCase`,
  `snake_case` on a data instance, a Lean 3 `has_…` relic (`hasInv` for an `Inv` instance), or a
  misspelled or miscased component — and its uses can be replaced simply; `wontfix` when the name
  is needed (`attribute [local instance]`, `@name`, many uses, `@[simps]` lemma names). A
  `Prop`-valued instance with a conventional `snake_case` name is not flagged at all.
- `NAME-A8` structure fields: rows marked `mixed convention` and `carrier : Type u` are `fp`
  (established); confirm only clear violations (a `Prop` field in `lowerCamelCase` that is a
  conjunction-style statement, a data field in `snake_case`), and note that renaming a field
  needs a deprecated alias for the projection.
- `NAME-B1` misspelled name components: confirm misspellings with the corrected name of every
  affected declaration; `fp` for abbreviations, prefixes and real words. Casing slips are B3 and
  instance names are I1, so neither appears here.
- `NAME-B3` miscased name components (`relindex` for `relIndex`, `Lseries` for `LSeries`,
  `localizationtoStalkₗ` for `localizationToStalk…`): confirm with the corrected casing. Rule 2
  applies (`ltSeries` → `ltseries`), except where it would make a different word (`gOne` would
  become `gone`) or fight a large consistent family: `wontfix`.
- `NAME-B2` camelCase tokens that name no declaration: confirm when the token is an outdated or
  misspelled spelling of a declaration that occurs in the statement (e.g. `uniformInducing` for
  `IsUniformInducing`); `fp` for deliberate abbreviations of a longer name used consistently in a family, names of local definitions/variables/notation,
  English compounds, and IMO labels.
- `NAME-C1` `snake_case` spellings of camelCase names: rule 3 is decisive. Confirm only the
  declarations whose statement contains the camelCase declaration; for a row covering several declarations, confirm the row if any declaration
  is a real leftover and list exactly which ones (others `keep`).
- `NAME-C2` outdated components (`nonzero → ne_zero`, `coe_nat → natCast`, `supr → iSup`):
  confirm when the statement uses the modern concept (`≠ 0`, `Nat.cast`, `⨆`); `fp` when the
  word means something else.
- `NAME-D1` name/statement mismatches: most rows are `fp` (the relation is hidden behind a
  definition, notation or coercion, or the name follows its family). Confirm only a clearly
  wrong relation (`_le_` naming a `<` statement) with a better name that fits the siblings.
- `NAME-D2` `succ`/`pred` in names of `+ 1`/`- 1` statements: Mathlib keeps `succ` in names of
  ℕ lemmas stated with `n + 1` (`pow_succ`, `Finset.sum_range_succ`, `Nat.factorial_succ`) —
  `fp`. Confirm only where `succ` misleads: the type has its own `succ` that is a different
  function (e.g. `Fin.succ` vs wrapping `i + 1 : Fin n`), the file or family already names the
  same pattern `add_one` (recent precedent: `Ordinal.cof_succ → cof_add_one`), or an `add_one`
  twin already exists (then deprecate the duplicate).
- `NAME-E1` textually identical statements: confirm ``deprecate `X` in favour of `Y` `` only
  for exact, non-deprecated duplicates with no purpose (keep the conventional name / the one
  with more uses / the `simp` one). `fp` for `to_additive`/dual pairs, intended restatements
  (`coe_inj` vs `coe_eq_coe`, `iff` vs `.mp` forms), statements that differ in implicit
  arguments, binder types or instances that the textual comparison hides, and Archive
  solutions that restate their main theorem.

## Decisions that apply across categories

- **`## TODOs` → `## TODO`.** #14474 ("homogenize TODO format") already made this change.
- **Heading synonyms.** Established variants of a standard heading (`Implementation details`,
  `Implementation`, `Main theorems`, `Keywords`) are `wontfix`; renaming them is churn. A
  singular heading over one item (`Main definition`, `Reference`) is `fp`; over several items it
  becomes plural.
- **British and American spellings** are `wontfix` unless one docstring mixes both.
- **No house spelling for `auto-generated`.** Its majority comes from one `#adaptation_note`
  repeated 219 times, so these rows are `wontfix`.
- **`## Tags` lines** list lowercase search keywords, not prose: `fp`.
- **Deprecation messages** of declarations that the monthly `remove_deprecated_decls.yml` run is
  about to delete are `wontfix`; the same misspellings in live comments are confirmed.
- **`succ` in names of `+ 1` statements.** For ℕ this is Mathlib's convention (`pow_succ`,
  `Finset.sum_range_succ`): `fp`. Confirmed only where `succ` misleads: wrapping `+ 1` on `Fin`,
  and types where `Order.succ` differs from `+ 1` (`ℕ∞`, `WithBot ℕ∞`, ordinals) when the family
  already says `add_one` (Krull dimension, Cantor–Bendixson). Families that say `succ` throughout
  (homological dimension, `ContDiff` with `n : ℕ∞ω`) are left alone.
- **Rule 2 against a family's current spelling.** Rule 2 is applied even where a whole family
  spells a name the other way (`ltSeries`, `nfBelow`, `leComap`, `sSet…`, `fgModuleCat`). These
  are the renames most likely to draw review comments.
- **Data definitions with underscores.** `scripts/nolints.json` lists most of them as known
  violations of the `defsWithUnderscore` linter (#34519), and recent pull requests (#41878,
  #39948, #40227, #42115) rename them the same way, lemma names included.
- **One declaration, two findings.** When two rows rename the same declaration for different
  reasons, both carry the combined name (`ιMulti_family_linearIndependent_ofBasis` →
  `ιMultiFamily_linearIndependent_of_basis`).
- **Case-only file renames** (`PATH-*`, e.g. `Ulift.lean` → `ULift.lean`) cannot leave a
  deprecated-module stub at the old path on case-insensitive file systems, so they need a pull
  request of their own and a careful review.

## Findings outside the scanner

Reviewers also reported real problems next to the rows they triaged that no scanner row covers.
They are not tracked in `typos.md`, so they are listed here.

- `Archive/Imo/Imo1988Q6.lean:20` "lead" → "led"
- `Mathlib/Control/Traversable/Basic.lean:23` "functions which external effects" → "functions with external effects"; `:26` "using calling `invite`" → "calling `invite`"
- `Mathlib/GroupTheory/GroupAction/Quotient.lean:260`, `:265` "the sum the orders" → "the sum of the orders"
- `Mathlib/Topology/Order/HullKernel.lean:70` "set of element of `T`" → "set of elements of `T`"
- `Mathlib/Geometry/Euclidean/Triangle.lean:324` "theorem. an exterior angle" → "theorem. An exterior angle"
- `Mathlib/Algebra/Group/Finsupp.lean:83`, `:94` docstrings say "If `M` is the trivial monoid" but the hypothesis is on `ι` (content error)
- `Mathlib/Analysis/Convex/Deriv.lean:277` and `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:374` "as it already implied" → "as it is already implied"
- `scripts/README.md:132` "the state after of a freshly cloned fork" → "the state of a freshly cloned fork"
- `Mathlib/CategoryTheory/Galois/FullSubcategory.lean:37` garbled: "If `C` has a terminal object,`P` is sat."
- `Mathlib/MeasureTheory/Measure/Haar/Unique.lean:248` comment cites the old name `integral_mulLeftInvariant_mulRightInvariant_combo`
- `Mathlib/NumberTheory/SelbergSieve.lean:28` (module docstring) names `lambdaSquared_mainSum_eq_diag_quad_form`, which does not exist
- `Mathlib/Algebra/Lie/LieTheorem.lean:16`, `:207` cite `LieModule.exists_forall_lie_eq_smul_of_isSolvable`, which does not exist; the theorem is `exists_nontrivial_weightSpace_of_isSolvable`
- `Mathlib/Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:261` comment names `gauss_product`, which no longer exists; the code uses `logGammaSeq`
- `Mathlib/AlgebraicGeometry/Modules/Tilde.lean:630` citation `[Theoreme 1.4.1, grothendieck-1971]` should be `[Theoreme 1.4.1][grothendieck-1971]`, as at :658
- `Mathlib/RingTheory/Noetherian/Basic.lean:375` "an noetherian submodule" → "a Noetherian submodule"; `:379`, `:384` `noetherian` → `Noetherian`
- `Mathlib/Condensed/Light/Sequence.lean:316` prose arrow "T' -> S' ⊗ N∪{∞}" → `T' → S' ⊗ ℕ∪{∞}`
- `Mathlib/Algebra/Lie/SerreConstruction.lean:52` cites `(serre1965)` as a parenthesised link instead of `[serre1965]`
- UpperCamelCase `Prop` fields the scanner missed: `NonemptyChain.Nonempty'` (`Mathlib/Order/BourbakiWitt.lean:40`), `RingHom.PropertyIsLocal.StableUnderCompositionWithLocalizationAwayTarget` (`Mathlib/RingTheory/LocalProperties/Basic.lean:185`), `FirstOrder.Language.IsFraisse.FG` (`Mathlib/ModelTheory/Fraisse.lean:119`)
- `Mathlib/Algebra/Homology/Embedding/Connect.lean:221` `CochainComplex.ConnectData.homologyMap_map_of_eq_succ` takes `hmn : m = n` with no `+ 1`: a possible name/statement mismatch
- `Mathlib/FieldTheory/IsAlgClosed/Classification.lean:24` docstring cites `IsAlgClosed.ringEquivOfCardinalEqOfCharEq`, which does not exist; the theorem is `ringEquiv_of_equiv_of_char_eq`
- `Mathlib/Data/Finset/Grade.lean:20` cites `Multiset.instGradeMinOrder_nat` (it is `Multiset.instGradeMinOrder`); `Mathlib/Order/Sum/Order.lean:24` cites `Sum.LE`/`Sum.LT` (they are `Sum.instLESum`/`Sum.instLTSum`); the RankOne module-doc bullet stops mid-sentence at "as defined in"
- `Ideal.IsTwoSided.pow_succ : I ^ (n + 1) = I * I ^ n` has the shape Mathlib calls `pow_succ'` (compare `Submodule.pow_succ : M ^ (n + 1) = M ^ n * M`)
- `Counterexamples/DiscreteTopologyNonDiscreteUniformity.lean:68`–`70` module docstring cites `TopIsDiscrete`/`idIsCauchy` where the primed versions are meant
- More exact duplicates not flagged as rows: `Finset.nonempty_Iio`/`Iio_nonempty`, `Set.union_distrib_iInter_right` vs `Set.iInter_union`; `compl_antitone` is subsumed by `compl_anti` and unused
- `Mathlib/CategoryTheory/Monoidal/Rigid/Basic.lean:462` docstring says `tensor_right Y` where it means the functor `tensorRight`
