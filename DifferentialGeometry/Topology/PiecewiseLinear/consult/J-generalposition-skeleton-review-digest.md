# Digest — external review of `Skeleton/GeneralPositionInDouble.lean` (snapshot `9dc7c8023c09`)

Verdicts: 2 OK, **1 FALSE**, 2 FIX. Corrections to our docstring: (a) the finite cover does not
follow from adapted charts only near the double point set; (b) the last leaf never relates `D'` to
`Rs`, `Bv`, `φ`, so its difficulty was **not** reduced to the vertex-perturbation leaf; (c) sign:
interior charts of the chosen copy have `ℓ > 0`, of the other copy `ℓ < 0` (the leaf's statement
already allows both).

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_adaptedHalfSpaceChart_in_double` | **OK — freeze** | arbitrarily small PL charts of the actual pair; tetrahedral 3-ball and its double as model |
| `exists_finiteAdaptedCover_of_doublePointSet` | **FALSE** | the finite-family conditions force `U = ⋃ W j` to be clopen |
| `SingularTwoCell.exists_cutOutPiece_of_closure_subset` | **OK — freeze** | finite PL surface neighbourhood + outer frozen collar; physical/artificial boundary distinction correct |
| `exists_small_vertexMap_relative_in_adaptedChart` | **FIX** | guard right, vertex retention redundant; output needs a certificate localising the frozen exceptions |
| `exists_normalizationStep_on_prescribedRegion` | **FIX** | conclusion independent of `φ`: modulo leaf 4 it *is* the prescribed-region normalization theorem |

## Leaf 2 is false
`closure U = ⋃_{j<n} closure (W j) ⊆ ⋃ V j ⊆ U`, so `U` is clopen; in a connected `M` with
`Σ(D) ≠ ∅`, `U = M`. Counterexample: `M = ℝ³`, `D(s,t) = (c₁ s, c₂ s, t)` with `c` a polygonal
immersed interval with one crossing, `C = M`, `BdM = {p}`, `p ∉ Σ(D)`: adapted charts exist near
`Σ(D)` (translated affine charts avoiding `p`, `ℓ > 0`), but some `V j ∋ p` would need
`ℓ (e p) = 0` with `ℓ ∘ e ≥ 0` on an open target. (This also refutes the local-cover repair
suggested at the end of `C-answer-digest.md`.)
**Repair:** add `[CompactSpace M]`; charts at **every** point (`hchart : ∀ y : M, ∀ U ∈ 𝓝 y, ∃ ec ℓ, …`,
supplied by leaf 1); conclusion `(⋃ j, W j) = Set.univ`. Then `D`, `hloc` and compactness of the
double point set are unnecessary. A modest covering lemma.

## Leaf 4: keep the guard, localise its exceptions
* `dim ker ℓ = 2`, so the guard is `|s| ≤ 4`, `|s ∩ Bv| ≤ 3`; four boundary vertices are coplanar —
  removing the guard makes the leaf false. The frozen-part implication
  `AI (φ|_{s ∩ A}) → AI (φ|_s)` is the right relative form; do **not** require frozen subsets to be
  independent (excludes ordinary frozen planar patches).
* `Rc.vertices ⊆ Rs.vertices` is **already implied**: apply `IsSubdivision.exists_face_subset_of_mem`
  to the singleton face `{v}`. Worth a derived lemma `IsSubdivision.original_vertices_subset`; no
  new hypothesis.
* **Missing implication: "frozen-dependent" ≠ "already normal".** Model: `c : [0,7] → ℝ²` linear
  through `(−2,0), (−1,0), (1,0), (1,2), (−1,2), (−1,0), (1,0), (2,−1)`, `D(s,t) = (c s, t)` on
  `[0,7] × [−1,1]`: locally injective, ≤ 2-to-1, the segment `(−1,0)–(1,0)` traversed twice ⇒ a
  2-dimensional coincident double sheet. `Rc` = two source rectangles over it, each triangulated as
  an outer ring + a central square in two triangles, `Ac` = the ring; `W` a small ball at the
  origin. With `Rs = Rc` and the old vertex map every guard instance is tautological, yet the
  coincidence is not a normal crossing. (Also a non-degenerate cut-out fixture: `BdM = D(∂S)`,
  `C = B = M`.)
* **Repair:** give the leaf the prescribed `W` and `Disjoint Ac.space (⇑D ⁻¹' closure W)`, and add
  to the output `∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) → Disjoint (simplicialMap Rs φ ''
  convexHull ℝ σ) (ec '' closure W)`. Produced by fine subdivision near `Ac` then a small
  perturbation; compactness gives the buffer. Half-space fixture: tent disk
  `D(s,t) = (s, t, 1 − max(|s|,|t|))`, `C = {z ≥ 0}`, `BdM = {z = 0}`, `Lc = ∂S`, a frozen
  subtriangle in one face.

## Leaf 5: the `ε` quantifier expresses nothing
Form `∃ ε, ∀ Rs Bv φ, P_ε → Q` with `Q` free of `Rs, Bv, φ, ε`; given leaf 4 this is equivalent
to `Q`. The coincident-rectangle model refutes the *intended* reading (literal gluing of an admitted
perturbation normalises the region) — the unchanged map is admitted.
**Mandatory repairs for a genuine gluing theorem:**
1. `EqOn ⇑D' (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space ∧ EqOn ⇑D' ⇑D Rc.spaceᶜ` (whole
   complement — the conclusion talks about unrestricted preimages);
   `MapsTo (simplicialMap Rs φ) Rc.space (ec '' V)`; add `(hVopen : IsOpen V)` (the assembly has it).
2. **Fixed-scale control** chosen *before* the perturbation and retained by the producer:
   `def UniformInjectivityScale (S) (f) (η) := ∀ x ∈ S, ∀ y ∈ S, dist x y < η → f x = f y → x = y`.
   Piecewise multiplicity inside `Rc` does not bound multiplicity on the whole disk (a new small
   double curve can meet a third unchanged sheet in the transition region); the existing
   multiplicity-stability theorem needs injectivity on closed stars of a *fixed* complex.
3. **Protect a closed target, not the open `Ok`:** call with
   `Z := ⋃ j, ⋃ (_ : j < k), closure (W j)`, `hZclosed`, existing `hOkZ`; choose open `O₀` with
   `Z ⊆ O₀ ⊆ O` and preserve full fibres `∀ y ∈ O₀, ⇑D' ⁻¹' {y} = ⇑D ⁻¹' {y}` (pointwise agreement
   on vertices is not enough). Frozen pieces meeting `closure W`: old-model transport.
4. **Honest decomposition** (five different theorems): controlled preparation (fixed injective
   patches/scale; chart, side and boundary-track buffers; protection of the closed old target) ·
   relative perturbation (strengthened leaf 4) · literal PL gluing (the two `EqOn`, same disk) ·
   global invariants + boundary homotopy (whole-domain multiplicity, properness, side, fibres off
   the support, buffered boundary track) · crossing recognition and transport (new crossings on the
   active target, old crossings on the protected target).
   *Alternative:* drop the perturbation arguments and state `Q` directly as "prescribed-region
   relative normalization producer" — honest, but then it is recorded as one large open obligation.

**Most likely surprise:** the passage from guarded affine independence to normal crossings in the
presence of frozen vertices. The exemption is not the mistake; treating exempt configurations as
harmless without proving they lie outside the active target or inside a protected normal model is.

## Second review, of the repaired skeleton (snapshot `08eca8995a81`, 2026-09-21)
Our docstring's transport guarantee does **not** hold: a closed buffer plus "ε fixed beforehand" is
not a crossing-stability certificate, and `θ` is returned *with* `φ`, so it is not a scale fixed
before the perturbation and preserved by it.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_normalizationPreparation_on_prescribedRegion` | **FALSE** | shrinking a neighbourhood of an arbitrary closed `Z` needs normality; and `ε` carries no stability field |
| `exists_small_vertexMap_relative_in_adaptedChart` | **FIX** | existence form fine, `hsep` producible; the a-posteriori `θ` gives no predetermined control downstream |
| `exists_gluedCell_of_vertexMap_in_adaptedChart` | **OK — freeze** | literal gluing, equality on the whole complement, frozen seam |
| `exists_globalInvariants_of_gluedCell` | **FALSE** | seam-neighbourhood hypotheses not passed; injectivity on both sides does not give local injectivity across the seam |
| `exists_normalCrossings_of_gluedCell` | **FALSE** | frozen exemptions do not protect the alternating pairing of the two source sheets; `hfrozen` also not passed |

* **Preparation.** `M = N ⊔ ℝ³`, `N` a non-normal Hausdorff 3-manifold (doubled Prüfer half-surface
  × ℝ), closed `Z, F ⊂ N` not separable by open sets, `O = M \ F`: no `O₀` exists. Repair:
  `[CompactSpace M]` (the assembly has it) or `IsCompact Z`. That fixes shrinking only.
* **`hsep` is fine**, single frozen vertices included: `F = (ec ∘ D)(Ac.space)` is compact and
  disjoint from `closure (ec '' closure W)`; subdivide so every simplex with a frozen vertex maps
  into `N_δ(F)`, perturb by `< min ε δ`. A frozen vertex near `frontier (closure W)` only needs a
  finer mesh.
* **Global invariants — the fold.** `S = [−1,1]²`, `h = 1 − max(|s|,|t|)`, `D = (s,t,h)`,
  `D' = (|s|,t,h)` on `Rc = S ∩ {s ≤ 0}`, `Ac = {0} × [−1,1]`, `Lc = Rc ∩ ∂S`, `Ω = ∅`,
  `C = {z ≥ 0}`, `BdM = B = {z = 0}`, `ec = id`, `ℓ = z`, `V = B(0,10)`, `ε = 3`, `η = θ = 1`:
  every hypothesis holds, `D'` is not locally injective on the seam. The leaf lacked `hNbfr`, `hNbA`.
  **Scale interface:** fix a control complex of the *whole* source before perturbing.
  `StarInj T g := ∀ v ∈ T.vertices, InjOn g (starComplex T v).space`. Preparation (given also
  `hfiber`) yields `∃ T κ ε, 0 < κ ∧ 0 < ε ∧ T.space = D.domain ∧ ∀ g, Close_ε g D ∧ StarInj T g →
  UniformInjectivityScale D.domain g κ ∧ ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2` (ambient metric of
  the double, chart error converted beforehand); the relative perturbation then *produces*
  `StarInj T g_φ` for the literal glued function `g_φ`. Suppliers in this order exist:
  `exists_pos_eq_of_dist_lt_of_injOn_starComplex`,
  `exists_fiber_encard_le_two_of_close_of_injOn_starComplex` (three-point separation budget).
* **Crossings — ABAB → AABB.** `D(s,t) = (c s, t)` on `[0,3] × [−1,1]`, `c` through
  `(−2,−2), (2,2), (2,−2), (−2,2)`, `BdM = D(∂S)`; sheets `v = u`, `v = −u`. `Rc` = two small
  source rectangles, `Ac` ⊇ outer rings and both copies of the edge over the common axis. Moving free
  vertices in an inner strip of width `r` sends the four rays along `A: (1,2), (−1,3)`,
  `B: (1,−4), (−1,−5)`: cyclic pairing `AABB`, not two transverse planes; change `O(r)`, each sheet
  still embedded, fibres ≤ 2, `hguard` holds (the forced dependence on the common axis is frozen,
  hence exempt). With `Z = {0}`, `O₀ ⋐ O`, `W = ∅`, `V ⊇` support: `hsep`, `hactive`, `hfibV` and
  even `hfrozen` hold. So the transport statement itself is false. **Repair:** off `V` transport by
  compact support; inside `Z ∩ V` the relative perturbation producer must output a
  *source-sheet pairing certificate*: open `U ⊆ O`, `U' ⊇ Z`, PL `χ : U → U'`,
  PL `ψ : S ∩ D⁻¹ U → S ∩ D'⁻¹ U'` with `D' ∘ ψ = χ ∘ D`, `χ (U ∩ BdM) = U' ∩ BdM`, on the **full**
  source preimage (no new sheet may enter). Produced by the protected-model construction, not
  assumed.

**Missing obligations:** predetermined whole-source injectivity control; a relative perturbation
producer that protects the pairing of the two source sheets. **Fixture:** a proper PL immersed disk
in the 3-ball with a transverse double arc, non-empty frozen outer ring, a small non-identity
perturbation on a fixed control subdivision, protected and active regions allowed to meet.
**Most likely surprise:** the ABAB/AABB pairing change near frozen exemptions — not `hsep`.

## Third review (snapshot `94791ab1c755`, 2026-09-21)
Docstring errors: "one `ε` also converts chart error to ambient distance" is wrong; and "`χ` need
not be the identity" does not show that the pairing certificate and genericity are jointly producible.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_normalizationPreparation_on_prescribedRegion` | **FALSE** | whole-source certificate has the right quantifiers; the conversion buffer wrongly reuses the same `ε` |
| `exists_small_vertexMap_relative_in_adaptedChart` | **FIX** | fixed control and pairing protection are *stability* obligations, not by-products of a generic choice |
| `exists_globalInvariants_of_gluedCell` | **OK — freeze** | `hcert hclose hstar` give whole-source control; seam and chart buffers build the boundary homotopy |
| `exists_normalCrossings_of_gluedCell` | **FALSE** | transport through the pairing is sufficient; active recognition lost `MapsTo (simplicialMap Rs φ) Rc.space (ec '' V)` |

* **Preparation.** Flat torus `(ℝ/20ℤ)³`, `S = [−1,1]²`, `D = (s,t,0)`, `ec q = q/2`, `V = B(0,1)`,
  `Rc = [−¼,¼]²`, `Ac` = the ring `3/16 ≤ ‖·‖∞ ≤ ¼`, `W = B(0,⅛)`, `Z = {0}`, `O = V`, `B = M`: the
  chart buffer forces `ε ≤ ½` at `x = 0`; `z = ¾ ε e₁` has chart error `< ε` and ambient error
  `3ε/2`. **Repair:** choose `T, κ, δ_amb` first, then `ε_chart`, then perturb:
  `(∀ g, (∀ x ∈ D.domain, dist (g x) (D x) < δ) → StarInj T g → UniformInjectivityScale D.domain g κ
  ∧ ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧ (∀ x ∈ Rc.space, ∀ z, dist z (ec (D x)) < ε →
  z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ)`; `hcert/hclose` use `δ`, `hsmall` and the chart
  buffer use `ε` (the order of `ManifoldApproximation.lean`). Suppliers: the first cited theorem
  allows any target; `exists_fiber_encard_le_two_of_close_of_injOn_starComplex` still has
  `[NormedAddCommGroup F]` — its proof uses only distance, compactness and three-point separation,
  so generalise to `[MetricSpace F]`, or compose with the ambient inclusion of the double.
* **Relative perturbation — split stability from generic choice.**
  Stability preparation: `∃ R τ, 0 < τ ∧ ∀ φ, A_R φ τ → StarInj T g_φ ∧ Pair D g_φ`, with `R` a
  **fixed** subdivision on which `ec ∘ D` is facewise affine and `A_R` = vertex error `< τ`, frozen
  vertices equal, physical boundary vertices at height zero, the others at positive height; `R`
  and `τ` also secure `hsep`, the valid chart range and the cut-out's seam conditions beforehand.
  Generic choice: `∀ τ > 0, ∃ φ, A_R φ τ ∧ hguard`. The expensive part is the pairing stability;
  one cannot take a generic perturbation first and add the certificate afterwards.
  **Localise the pairing:** choose `K ⋐ V` compact with `D(|Rc|) ∪ g_φ(|Rc|) ⊆ K`; produce the
  full-preimage pairing only near `Z ∩ K`; on the open set `O \ K` transport by the identity. The
  two crossing models are used side by side — no need to glue one `χ, ψ`. Not `Z ∩ V` (not compact;
  `Vᶜ` is not an open neighbourhood of boundary points).
* **Crossings.** Without `hmaps` one cannot get `ec (D' x) = simplicialMap Rs φ x` from `hglue`:
  `ec.symm` is unconstrained off `ec.target`. Counterexample: the fold `D' = (|s|,t,h)` with
  `p_φ = (10+s, t, h)`, `ec = id` on `(−3,3)³` and `ec.symm (p_φ (s,t)) := D' (s,t)` off the target,
  `Ac = ∅`, `Ω = univ`, `ε = 11`: all half-space and guard clauses hold, pairing with
  `χ = ψ = id` far away, yet two sheets coincide in `W`. **Repair:** pass
  `(hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))` (the frozen gluing leaf already
  receives it). On point (iii): the pairing gives `ψ '' (S ∩ D⁻¹{q}) = S ∩ D'⁻¹{χ q}`, so new double
  points are old ones, no extra sheet enters, `hχbd` transports the boundary models; no hypothesis
  that `ψ` preserves the source boundary is needed; with a certificate for all of `Z`, `O₀` and
  `hfibV` become redundant for this half.

**Missing obligations:** the pairing-stability producer on a fixed subdivision; the metric version
of the multiplicity lemma; the chart-range parameter of the crossing leaf. **Fixture:** a proper PL
disk in the 3-ball already in general position with one transverse double arc, `Rc` the whole disk,
`Ac = Lc = ∂S`, a small non-identity shear fixing the boundary plane, `ψ = id`, `Z` and `W`
overlapping. **Most likely surprise:** writing "both scales are chosen before the perturbation" as
"one scale does not grow under the inverse chart".

## Fourth review (snapshot `3be6d2b15412`, 2026-09-21)
**The reviewer withdraws the third review's suggestion "pairing preserved for *all* admissible
vertex perturbations": too strong.** Fixing the subdivision and shrinking `τ` does not make an
arbitrary PL normal crossing stable in the *current* chart coordinates. Our docstring's guarantee
to that effect is false.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_normalizationPreparation_on_prescribedRegion` | **OK — freeze** | `T, κ, δ, ε` all precede the perturbation; conversion `ε → δ`. (The multiplicity supplier still needs its `[MetricSpace]` generalisation.) |
| `exists_pairingStableSubdivision_in_adaptedChart` | **FALSE** | a normal *folded* double crossing becomes a tangency under arbitrarily small admissible perturbations; the pairing conclusion fails |
| `exists_guardedVertexMap_in_adaptedChart` | **OK** (as stated) | frozen vertices, boundary heights and the relative guard are compatible; it only chooses vertices |
| `exists_normalCrossings_of_gluedCell` | **OK — freeze** | `hmaps` present; full pairing handles `Z ∩ K`, full fibre equality handles the open set `O ∩ Kᶜ`, boundary case included; normal region `G_W ∪ U' ∪ (O ∩ Kᶜ)`, no `O₀` needed |

* **`K` is quantified correctly** (`D(|Rc|) ⊆ int K`, `K ⋐ V`, then shrink `τ`); protecting `Z ∩ K`
  suffices. **No full-subcomplex hypothesis is needed**: facewise affine + non-negative height +
  old zero set `= Lc.space` give `|σ| ∩ Lc.space = conv {v ∈ σ : v ∈ Lc.space}`, i.e.
  `restrict R Lc.space` is full; with the same zero vertex set and non-negative barycentric
  coefficients this yields the new `hpzero`.
* **Counterexample to the universal pairing.** In a coordinate block of a large flat 3-torus:
  `S = [0,6] × [−1,1]`, `D(s,t) = (c s, 2 + t)`, `c` through
  `(0,1), (0,0), (3,0), (3,3), (−3,3), (0,0), (1,1)` at the integers; `C = M`, `BdM = D(∂S)`,
  `ec = id` on `Q = (−½,½)² × (3/2,5/2)`, `ℓ = z`, `O = V = Q`, `y₀ = (0,0,2)`,
  `W = B(y₀, 1/100)`, `Z = closure W`; `Rc` = the two source rectangles
  `P_i = [i − 1/16, i + 1/16] × [−¼,¼]`, `i = 1, 5`, `Ac` = their outer rings, `Lc = ∅`. Old rays
  `A: (1,0), (0,1)`, `B: (1,1), (−1,1)` — cyclic order ABAB, a genuine normal crossing (straightened
  by a sectorwise PL map). `hsep` forces all faces adjacent to the two preimages of `y₀` to be free;
  translate the **free vertices of sheet B** by `a·(1,0,0)`, `a > 0` small: still admissible, but
  near `q = (a,0,2) ∈ Z ∩ int K` sheet A is `y = 0` and sheet B is `y = |x − a|`: **tangent, not
  crossing**. Smaller `τ`, another `K`, a finer `R` do not help; the guard is not even involved.
* **Revised interface.** Let `𝒫_R` be the finite vertex-parameter space with the linear constraints
  (frozen vertices fixed, physical boundary vertices at height zero). Stability leaf:
  `∃ R τ K (𝒢 ⊆ 𝒫_R), 𝒢.Nonempty ∧ IsOpen 𝒢 (in 𝒫_R) ∧ ∀ φ ∈ 𝒢, Admissible_τ φ ∧ Controlled φ ∧
  Pair_{Z ∩ K} D g_φ` — `Controlled` = the present conclusions other than pairing. The old vertex
  map need **not** be interior to `𝒢`. The generic choice must be made **inside `𝒢`** (a density
  statement for the guard), not by taking any output of the present guarded leaf. Constructing
  `𝒢` and proving it non-empty is the substantive geometric obligation.
* **Also missing from the stability leaf:** the cut-out's seam conditions, to be passed by the
  caller: `hΩ : IsOpen Ω`, `hΩR : D.domain ∩ Ω ⊆ Rc.space`, `hNb : IsOpen Nb`,
  `hNbfr : Rc.space \ Ω ⊆ Nb`, `hNbA : Rc.space ∩ Nb ⊆ Ac.space` — otherwise translating an
  unfrozen flat `Rc` can overlap a neighbouring unmoved sheet and break `StarInj T`.

**Missing obligation:** a controlled, non-empty, open family of pairing-protecting perturbations
admitting a generic choice — not one more scale. **Fixture:** a proper PL immersed disk with two
*flat* sheets crossing transversally, non-empty frozen outer ring, `Z ∩ W ≠ ∅`, a non-identity small
perturbation inside the open set of parameters keeping transversality. **Most likely surprise:**
"some PL coordinates straighten the double crossing" is not "every small vertex perturbation in
the present coordinates keeps it a double crossing".

## Fifth review (snapshot `c18a78c78212`, 2026-09-21)
Correction to our question: as interior points of two complete local sheets, `y = 0` and `y = |x|`
is a **tangency**, not a normal double crossing (Moise p. 184 excludes touching singularities); in
the fourth review it was the *bad perturbed* model, not the old one. The docstring's local example
(translate B downwards) is right but does not replace a general non-emptiness proof.

| Leaf | Verdict | Reason |
|---|---|---|
| `exists_pairingStableSubdivision_in_adaptedChart` | **FIX** | not refuted; but the general existence of a non-empty open pairing family is **unverified** — cannot be frozen on the strength of a local example |
| `exists_guardedVertexMap_in_adaptedChart` | **OK — freeze** | the frozen-part antecedent is constant on the parameter space: if false the failure set is empty; if true, `|s| ≤ 4`, `|s ∩ Bv| ≤ 3` make the failure set a proper algebraic set; a finite union is nowhere dense. Two frozen vertices with equal images fall in the first case — the proof must not skip that branch |

* **`IsVertexSupOpen` is adequate.** After evaluation at the finitely many vertices the parameter
  space is the affine product `∏_v E_v`, `E_v = {ec (D v)}` (frozen), `ker ℓ` (on `Lc` not frozen),
  `ℝ³` (otherwise); the definition is relative sup-openness there, and the proved saturation lemma
  closes the "non-vertex values" loophole.
* **Expose the seed.** Equivalent restatement, to be used as the leaf: with `P_R` the present
  `VertexParameterSpace` and `Q_{R,τ,K,Bv} φ` the *verbatim* conjunction now following `∀ φ ∈ 𝒢`,
  `∃ R τ K Bv φ_* ρ, (present conditions on R τ K Bv) ∧ φ_* ∈ P_R ∧ 0 < ρ ∧ ∀ φ ∈ P_R,
  (∀ v ∈ R.vertices, dist (φ v) (φ_* v) < ρ) → Q φ`; then `𝒢 := VertexSupBall R P_R φ_* ρ` and the
  proved lemmas apply. The old vertex map need not be `φ_*`. The normalization happens *inside*
  the leaf; no new hypothesis for the caller.
* **Trap:** after a normalization one takes a common subdivision; openness of the old family does
  **not** upgrade to openness in the new parameter space (new vertices constrained to affine
  combinations of old ones give a lower-dimensional family). New free vertices must move
  independently and `(Seed)` must be re-proved on the final `R`.

**Open mathematical question (not a statement defect):** for arbitrary input, can one perform the
controlled relative normalization keeping `Ac`, the boundary conditions, `StarInj T` and the error
budget, and obtain the full-preimage pairing over a neighbourhood of all of `Z ∩ K`? Pointwise
straightening charts do not give this, and Moise §25 Lemma 2's general position paragraph does not
state this strengthened form. → consult `L-pairing-seed.md`.
