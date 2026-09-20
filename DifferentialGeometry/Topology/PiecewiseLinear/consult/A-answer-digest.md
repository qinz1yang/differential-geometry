# A — answer digest (external consultant, 2026-09-20; reviewed branch head `9efccff49`)

Digest of the answer to `A-section34-recut.md`. Checkable claims verified by the lead are
marked ✓. The consultant had printed pp. 230–231, 239–240, 247–248 and excerpts, but **not**
a clean text of §34 Lemmas 4–13 and Operations 1–2 (pp. 241–246) nor pp. 249–250, and
therefore did **not** certify a complete replacement DAG.

## Verdicts

* The diagnosis is confirmed: `Moise352SkeletonExtension`'s conclusion is the original
  approximation problem and the reduction supplies its two extra hypotheses directly; there is
  no smaller extension theorem hiding in it.
* **Correction to our prompt:** `Moise341` is **not** a misstatement ✓ — it matches printed
  p. 239 (Euclidean polyhedral 3-cell, constant ε). What is missing is a controlled
  **chart-transport lemma**, not an arbitrary-target replacement. Do not delete or weaken it.
* **The tame 30.5 suffices for §34 Lemma 3 (p. 240)** ✓ (`Moise305Tame`,
  `TameNestedCells.lean:27`, extra hypothesis `IsBicollared (frontier C₂)`, outer cell not
  required PL): choose nested source PL balls `B₁ ⊂ B₂` around the simplex with a bicollar of
  `∂B₂` inside the open domain of `h`; an embedding defined on an open set is an open embedding,
  so the collar transports to a topological bicollar of `∂h(B₂) = h(∂B₂)`. Not checked for
  every other use of 30.5 in §§32–35; the criterion is "outer image cell = image of a bicollared
  source cell under an embedding defined near the collar".
* Continuous vs strongly positive tolerance in 35.1 is not a geometric issue: a strongly
  positive `ρ` has a continuous minorant `0 < ψ < ρ` (partition of unity), so the continuous
  form of `Moise351` recovers the book's.

## A false strengthening to avoid ✓

> **False:** "`Moise352 3` can be realised by a cellwise construction whose compact target cells
> form a locally finite family in the whole target manifold."

`M₁ = M₂ = K = ℝ³`, `h x = x / (1 + ‖x‖)`, `φ = 1`. Any admissible `F` has `‖F x‖ < 2`. If compact
source cells `Pᵢ` cover `ℝ³` and the `F(Pᵢ)` are locally finite in `ℝ³`, then `F(ℝ³)` is closed;
it is open by invariance of domain; so it is all of `ℝ³`, contradicting boundedness.
**Target local finiteness must be relative to the image `Y`, or otherwise explicitly
controlled.** (Not a counterexample to `Moise352`; a counterexample to a tempting shape for its
reconstruction data.)

## The re-cut: separate *constructing* a compatible target decomposition from *extending* across one

Replacing `SkeletonExtension` by "there exists an appropriate prepared configuration" would not
help: a configuration that already supplies small target balls with the source incidence
pattern is nearly a certificate for the whole theorem. The reusable, genuinely smaller pieces:

**(Control) tolerance selection.** `X` metrizable, `(Aᵢ)` a locally finite family of closed
sets, `aᵢ > 0`, `φ` continuous positive ⇒ `∃ ψ` continuous, `0 < ψ < φ/4`, and
`∀ i, ∀ x ∈ Aᵢ, ψ x < aᵢ`. (Lower semicontinuous
`b x = min(1, φ x / 4, {aᵢ | x ∈ Aᵢ})` + partition of unity.) Quantifier order
`∀ (Aᵢ) ∀ (aᵢ) ∃ ψ` — never a tolerance sequence chosen before the geometric family. A margin
computed from an `N` that `Moise351` has not yet produced cannot be fed into an earlier
application of `Moise351`.

**(Carrier control).** `Pᵢ` cover `K`, `h(Pᵢ) ⊂ Wᵢ`, `diam Wᵢ < φ x` for `x ∈ Pᵢ`; then any `F`
with `F(Pᵢ) ⊂ Wᵢ` has `d(F x, h x) < φ x`. This is where the **final** tolerance lives; once
target cells are built inside the `Wᵢ`, ball filling needs no metric estimate — which is why a
huge tolerance is harmless: the geometric control is chosen below *both* the tolerance and the
chart/incidence margins.

**(Ball extension).** PL `d`-balls `P, Q`, `1 ≤ d ≤ 3`, `b : ∂P → ∂Q` a PL homeomorphism ⇒ a PL
homeomorphism `B : P → Q` extending `b` (coning). Two hypotheses must not disappear: `Q` is
already a PL ball; `b` is already a PL homeomorphism.

**(PL gluing with incidence).** `(Pᵢ)`, `(Qᵢ)` locally finite closed polyhedral covers of `K`
and of `Y` (local finiteness **in `K` and in `Y`**), `gᵢ : Pᵢ → Qᵢ` PL homeomorphisms with
`gᵢ = gⱼ` on `Pᵢ ∩ Pⱼ` **and** `gᵢ(Pᵢ ∩ Pⱼ) = Qᵢ ∩ Qⱼ` ⇒ the `gᵢ` glue to a PL homeomorphism
`K → Y`. The incidence clause is essential (agreement on overlaps alone does not give global
injectivity). `LocallyFinitePieceTower.exists_glue_of_eqOn` is set-theoretic only ✓.

**The first geometric obligations of §34 (p. 240)**, with `Â = f₁(A)`, `N_σ` the solid torus
assembled from the dual cells at the vertices of a 2-simplex `σ`:
`h(K¹) ⊂ Int N̂`; `D̂_e ∩ h(σ) ≠ ∅ ⇒ e < σ`; `Ĉ_v ∩ h(σ) ≠ ∅ ⇒ v < σ`;
`h(∂σ) ⊂ Int N̂_σ`; the approximation bound on `f₁`; Lemma 2: `π₁(h(∂σ)) → π₁(N̂_σ)` surjective
(uses 30.8); Lemma 3: arbitrarily small PL-ball neighbourhoods of `h(σ)` with boundaries in
general position (uses 30.5, tame form suffices). These need a **joint producer of `N`, its
compatible splitting data and `f₁`** — an arbitrary output of `Moise351` does not carry them.

**The seven stages** (left: new correspondence; right: input that cannot be omitted — the right
column is the consultant's identification, *not* a transcription of Lemmas 4–13):

| # | correspondence | input |
| - | --- | --- |
| 1 | `∂D^σ ∩ ∂D_e ↦ ∂D̂^σ ∩ ∂D̂_e` | consistent matching of marked points |
| 2 | `∂D_e ↦ ∂D̂_e` | cyclic-order compatibility of that matching |
| 3 | `∂C_v ∩ ∂D^σ ↦ ∂Ĉ_v ∩ ∂D̂^σ` | matching arc components, end-points, incidences |
| 4 | `X(σ³,v) ↦ X̂(σ³,v)` | PL types of the patches; earlier boundary maps match |
| 5 | `C_v ↦ Ĉ_v` | complete compatible boundary data incl. shared splitting disks |
| 6 | `D^σ ↦ D̂^σ` | target a PL disk, whole boundary map defined |
| 7 | `C(σ³) ↦ Ĉ(σ³)` | target a PL 3-ball, boundary correspondence complete, correct intersections |

Stage `j` asserts `F_j = F_{j-1}` on the cumulative domain — ordinary extension of a partial map,
**not** the refuted agreement between independently chosen approximations. The contracts should
not require `F|_N = f₁`; §34's closing paragraph raises that as a separate question.
**Missing:** exact producers for the right column with the separation invariants preserved by
Operations 1–2, and a locally finite implementation of the cleanup.

## Q2 — the two reductions, charts, termination

The reductions of p. 251: (1) the inward move makes `h` and the tolerance available on an open
neighbourhood of the moved copy; (2) choose that neighbourhood so `K` is **relatively closed**
in it and regard it as the ambient manifold. Neither makes `M₂` Euclidean nor `K` finite.
Independent fact: `K` locally compact in a Hausdorff `M₁` ⇒ `K` closed in some open `U` (the
tower gives local compactness) — a separate small infrastructure theorem.
*Chart-local replacement.* For each finite **interaction region** `Aᵢ` (the simplex together
with the relevant incident dual cells, surrounding neighbourhoods and adjustment supports)
choose a target PL chart `Vᵢ` with `h(Aᵢ) ⋐ Vᵢ` and a margin `aᵢ` with
`{y | d(y, h(Aᵢ)) < aᵢ} ⊂ Vᵢ`; (Control) combines the margins. The subdivision condition is an
open-cover refinement on interaction **stars**, not on single simplexes; independently
subdividing the finite pieces of the tower does not give compatible global stars.
*"Unbounded component".* In a chart, replace it by a **marked outer collar** of a coordinate
ball — valid only after proving that the relevant vertices and excluded sets lie on the
prescribed side; these clauses must be extracted from Lemma 5(7).
*Termination.* Finitely many intersections per star does not justify an infinite sequence of
surgeries; a locally finite cleanup needs fixed locally finite supports and a proof that an
operation in one support does not recreate removed defects elsewhere.

## Q3 — chart-local 34.1, from the existing `Moise341`

`C ⊂ ℝ³` a PL 3-ball, `M` a metrised PL 3-manifold, `h : C ↪ M` an embedding, `χ : V → W ⊂ ℝ³`
a PL chart with `h(C) ⊂ V`, `τ : C → (0,∞)` continuous ⇒ a PL embedding `f : C ↪ V` with
`d_M(f x, h x) < τ x`. Proof: `A = χ(h C)` compact in the open `W`; `r > 0` with the closed
`r`-neighbourhood of `A` inside `W`; `m = min τ`; uniform continuity of `χ⁻¹` there gives
`δ < r`; apply `Moise341` to `χ ∘ h` with `δ`; `f = χ⁻¹ ∘ g`. Order of choices:
`χ, h(C), τ → δ → g`. When source cells are modified or enlarged, carry
`h(C_v^modified) ⊂ Int E_v` explicitly and prove it is preserved.

## Q4 — prerequisites actually verified

32.1–32.3: consumed at p. 231 (pseudo-cells `E_e`; 32.3(8) gives smallness). 30.5: p. 240
Lemma 3 (tame form suffices there). 30.8: p. 240 Lemma 2. **Not verified:** where 26.4,
30.6–30.7, 27.3/28.8, 32.4 are consumed.

## Q5 — other routes

*Hamilton 1976*: handle straightening needs punctured-torus immersions, Wall's end-capping,
Waldhausen/Scott rigidity, and explicitly invokes the generalised Dehn lemma (p. 67) — not
closer to this tree, not a shortcut. *Bing 1959*: moves a closed topological image of a 2-complex
onto a polyhedron within a continuous `ρ`; the alternative most worth a separate full audit, but
not certified shorter. (Bing's *Approximating surfaces from the side* is 1963, distinct from
the 1957/1959 papers.) *Shalen 1984*: only the bibliographic identification was verified.
**Recommendation: keep the Moise route, factor the reusable §34 geometry.**

## Q6

"Six chapter-scale items" double counts (the proof of 34.1 *is* the §34 construction, to be
made reusable for §35) and hides work (finite → locally finite, compatible subdivisions,
relative target local finiteness, PL embedding gluing). Track deliverables instead: the disk /
shell / neighbourhood inputs in their consumed forms; a *producer* for §33; reusable §34
preparation (incidence, generator, separation, cleanup preservation); the seven-stage PL
assembly; §35 globalisation. **The decisive question:** can the §34 geometric preparation be
produced without its hypotheses or conclusion already containing a disguised approximation of
the whole 3-manifold?
