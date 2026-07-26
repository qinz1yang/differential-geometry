# `main16.tex` — style review and changelog

`main16.tex` is a cleaned successor to `main15.tex` for the standalone
"Hamilton's Three-Manifold Theorem and its Lean Formalization" paper. It
incorporates the in-progress rewrites from the working draft (chiefly a
math-first "Evolution equations" section), resolves the stray editorial notes,
and applies the safe fixes below. It compiles under pdfLaTeX (MiKTeX) with all
cross-references resolving; only the external `references.bib` citations are
undefined (pre-existing — the `.bib` is not in the repo).

## What changed relative to `main15.tex`

1. **Abstract** — now names what is *concretely proved* (Levi-Civita/tensor
   calculus; inverse-metric, connection, Ricci, scalar, Ricci-norm evolution;
   scalar and tensor weak maximum principles; 3-D curvature algebra; improved
   pinching) vs *assumed* (short-time existence, maximal-time extension,
   no-local-collapsing, CGH compactness, topological handoff). Frames the
   contribution as a machine-checked reduction to named inputs.
2. **§3 "Differential-geometric infrastructure" opener** — replaced the abrupt
   opening (the working draft dropped the section's purpose statement, leaving
   "Our construction builds on mathlib…") with a one-sentence purpose statement,
   keeping the mathlib discussion. (Resolves the draft's "should we discuss
   mathlib here" note: yes.)
3. **§3.2 "Construction of the Levi-Civita connection"** — added the motivation
   paragraph the draft flagged with "need work out the connector…", flowing
   directly into the first subsubsection.
4. **§5 "Evolution equations"** — adopted the draft's math-first rewrite: each
   evolution lemma now shows the textbook proof, then a short "the Lean
   development follows / is checked by …" coda. Uses plain `\begin{proof}`
   uniformly in this section, normalized the long file paths to the paper's
   short `\rffile{RicciFlow/…}` convention, and fixed the dangling
   "section …?" cross-reference (now points to §(analytic) and the
   short-time-existence appendix).
5. **§5.3 three-dimensional curvature identity — SIGN FIX (please double-check).**
   The main-text Riemann-from-Ricci display was the exact *negative* of the
   appendix version, while the text claimed they were "the same classical
   identity." Verified four ways that the appendix form is the correct one for
   the geometric `Rm04` and negated the main-text display to match; also
   `K_{ij}=R_{ijij}` → `K_{ij}=R_{ijji}` (the declared sectional numerator is
   `Rm04(X,Y,Y,X)=R_{ijji}`). Verification:
   - Round `S^3` (`Ric=2g`, `R=6`): appendix form gives `R_{ijji}=+1`
     (matching `K>0`); the old main-text form gave `-1`.
   - In Lean, `displayedRiemannFromRicciRhs3 = -stdRhs`, and
     `displayedRiemannFromRicci3D_…` proves `R_{ijlk}=displayedRhs`; with
     last-pair antisymmetry this is `Rm04_{ijkl}=` the appendix form. The
     geometric bridge `rm04Comp_displayedRiemannFromRicci3D_at` ties `Rm04` to
     that displayed (appendix) form.
   - The appendix already used the correct form; the fix makes its "same
     identity" claim true.
   Authors should sanity-check this once against
   `Geometry/Curvature/DimensionThree/RiemannFromRicci.lean`, since it is a
   sign in a displayed identity.
6. **§2** — added a `\paragraph{Frontier.}` (the term is used ~15× as a status
   word but was undefined).
7. **Preamble** — removed dead macros `\owedge`, `\leanchanged`; added a comment
   noting `\norm` and `\abs` are intentionally identical single bars.
8. **LaTeX hygiene** — `\S~\ref` spacing standardized (3 sites); fixed
   "definitions not yet exists" → "do not yet exist"; reference-table caveat
   "seven direct frontiers listed in the status remark" (dangling, wrong count)
   → points to the dependency ledger; removed the trailing `\\` on the last
   longtable row. Kept `\leanref{thm_2_1}` in the table — it *is* a real Lean
   alias (`HamiltonPositiveRicci.lean`).
9. Normalized line endings to LF (the base had 26 stray CRLF lines).

## Recommended (NOT yet applied — editorial voice decisions)

These are worth doing but change the authors' voice pervasively, so they are
left for you.

### Structure (template: Armstrong–Kempe, *Formalization of De Giorgi–Nash–Moser
Theory in Lean*, arXiv:2604.05984, 2026 — the closest published analogue)

- **Add an early "Formalized statements" section** (right after the
  introduction) stating Hamilton's theorem *and each assumed global input* in
  clean math notation, and state the endpoint in its honest conditional form
  ("Assume [short-time existence], [CGH compactness], [no-local-collapsing].
  Then …") so the logical shape is visible up front rather than discovered late.
- **Add a "trusted inputs" dependency table**: one row per assumed input, with
  columns *(mathematical statement) | (cited source, e.g. Hamilton, JDG 1982) |
  (Lean status: hypothesis / not yet formalized) | (Lean identifier)*.
- **Report axiom hygiene**: if the reduction is `sorry`-free with the inputs as
  *hypotheses* (not `axiom`s), state that and give `#print axioms` on the
  endpoint (ideally only `propext`, `Classical.choice`, `Quot.sound`). NB:
  `ham3_main`'s signature currently exposes only the two geometric hypotheses,
  so a reader cannot see the black-box dependence — either surface the inputs as
  explicit hypotheses of the endpoint, or show `#print axioms ham3_main`. This
  is the single most important honesty lever for a conditional formalization.
- **Pin the paper to a commit** of the `short-time-existence` branch and say how
  to reproduce the check.
- **Split "imported/trusted (mathlib + settled `DifferentialGeometry`)" from
  "newly built for this project"**, with a one-line contribution accounting.

### Prose (from a dedicated pass over the draft)

- **State the status disclaimer once** (its natural home is §2), then use a
  one-clause pointer ("conditional on the global inputs of §2"). It is currently
  restated in full ~9× with the identical four-adjective list
  ("analytic, compactness, transfer, and topological").
- **Thin the worn qualifiers**: `endpoint` ×93, `checked` ×64, `Lean-facing`
  ×38 (18 as an identical proof title), `current`/`currently` ~40, `black-box`
  ~24. When everything is "checked", the word stops marking anything — let the
  first sentence of each proof carry the native/consumer/black-box
  classification (most already do).
- **Drop the decorative `[Lean-facing calculation]` proof titles** on most
  proofs (plain `proof`); reserve a discriminating tag only where it adds
  information. (§5 already does this after the rewrite.)
- **De-anthropomorphize "Lean"**: "Lean differentiates / introduces / applies"
  → "we" or "the proof" for mathematical choices; reserve "Lean" / "the Lean
  development" for what the machine does (checks, verifies, records). §5 already
  follows this.
- ~~**§3.4 "concrete checked example"** walks through five internal bridge lemmas~~
  — **done**: rewritten math-first (classical formula → three-step
  chart/model/coordinate narrative, the one analytic step
  `modelDeriv_eq_coordDerivRSAt` highlighted, the five-lemma chain moved to a
  footnote, identifiers switched to `\leanref`).
- **Introduction** reaches the actual contribution only in paragraph 7–8; tighten
  the two general formalization-history paragraphs into one so the reader hits
  "what this paper does" a screen earlier.

### Terminology consistency (a canonical label per concept)

- Use the §2 term **"consumer theorem"** verbatim rather than the drifting
  "checked consumer"; reserve "theorem-shaped" for the *endpoint*, not for
  inputs/interfaces ("theorem-shaped input/consumer/interface" all appear).
- **Myers's theorem** is stated as a Black Box but appears in neither the §2
  list, the dependency ledger, nor the reference table — either add it (tied to
  the compact-limit step it feeds) or demote it.
- Scalar curvature `R` is overloaded (scalar curvature, the operator `R(X,Y)Z`,
  and components `R_{ijkl}`); the `\Scal` macro exists but is unused. Consider
  using `\Scal` for scalar curvature to disambiguate, or leave as-is
  deliberately.
- Curvature-symbol markup: use `\Rm_{04}` everywhere (a couple of bare `Rm04` /
  un-macroed `Rm_{13}` remain).

## Lean-name presentation (pick one convention and hold it)

The paper mixes `\leanref{…}` (dominant) with `\texttt{…}` + manual `\_`
(~67 uses, concentrated in the §3 Levi-Civita subsection). `\leanref` line-breaks
at underscores (the preamble adds `_` to `\UrlBreaks`); `\texttt` does not.
Standardize in-text Lean identifiers to `\leanref`, reserving `\texttt` for
prose words like `mathlib`. For the mathematician audience, the recommended
hybrid is: math statements in the body, Lean names in monospace, and full Lean
signatures shown only for the *endpoint* and each *assumed input*.
