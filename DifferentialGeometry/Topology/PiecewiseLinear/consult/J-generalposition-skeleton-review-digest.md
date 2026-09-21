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
