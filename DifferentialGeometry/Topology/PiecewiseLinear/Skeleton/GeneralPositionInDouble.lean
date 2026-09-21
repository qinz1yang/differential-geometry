/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered

/-!
# Sorry-first skeleton of general position in the double

The assembly `generalPositionInDoubleBuffered` below is proved for real from the ten leaves of
this file, from the proved cover theorem `exists_finiteAdaptedCover_of_compactSpace`, from the
proved bridge `eq_regionGluedMap_of_eqOn`, from
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the whole double by regions `closure (W j) ⊆ V j` with `closure (V j)` inside one adapted
chart, a transition subdivision on every closed overlap, then a chart-by-chart induction.

The induction invariant has two halves.  After the step for the cell `D k`, with
`Z k = ⋃ j < k, closure (W j)`, (a) the crossings are PL normal double crossings over an open set
containing `Z k`, and (b) for every later index `m`, over the compact transition zone
`Z k ∩ closure (V m \ closure (W m))` the crossings are *margin stable in the chart* `ec m`:
`HasStableCrossingBlocks`.  Half (b) is what consult L §2 shows a seed needs, and what consult O
§2 localises: on the final subdivision a simplex with a frozen vertex misses `closure (W k)` by
`hsep`, so the old crossings it can disturb lie over `Z k ∩ closure (V k \ closure (W k))`, and
there the two complete local source sheets are buffered graphs `u = a (v, t)`, `v = b (u, t)`
with `Lip a · Lip b ≤ 1 - η`; the unperturbed map is then the centre of the ball of admissible
vertex maps, so no seed `φ₀`, no radius `ρ` and no pairing certificate `χ, ψ` are needed, and
`VertexParameterSpace`, `IsVertexSupOpen` and `VertexSupBall` are gone with them.  Consult O §3
shows (b) is *not* an open condition in the current chart's vertex parameters, which is why the
generic choice leaf now carries wall conditions for the later charts.

The counterexample of consult O §3.  In the later chart `H (x, y, t) = (h (x, y), t)` with `h`
the sector map that is `(y / 3, -2 x + 5 y / 3)` on `3 x ≤ y ≤ 4 x`, `(4 x / 3, y + 2 x / 3)` on
`y ≥ 4 x` and the identity elsewhere, the two flat sheets `y = 0` and `y = x` have a strict graph
margin in both charts, yet translating both by `(a, 3 a, 0)` puts their crossing line on the wall
`y = 3 x`, where the four rays become `A : (1, 0), (0, 1)` and `B : (1, 1), (-1, 1)` — the bent
model without margin, and one further small move of `B` makes it a tangency.  So an old margin in
a later chart gives no safe ball in the current chart's parameters, and the double curve must be
kept transverse to the walls: that translate is excluded by the transversality clause
`hwalltrans` of `exists_genericVertexMap_in_adaptedChart`, because the translated double line
`x = a, y = 3 a` lies *inside* the wall `y = 3 x`, so its direction lies in the wall's direction
and no transverse `w` exists.

`IsStableCrossingBlock` is not satisfiable by degenerate data over a set carrying double points.
Over a double point of the block the two graph projections force two *different* sheets:
`sheets_nonempty_of_isStableCrossingBlock` proves that both `SA` and `SB` meet the fibre, so a
one-sheet or sheet-free block is impossible, and `HasStableCrossingBlocks` demands that the
half-size blocks cover `doublePointSet ∩ Q`; combining the two,
`exists_sheets_of_hasStableCrossingBlocks` proves that over *every* double point of `Q` the
family produces two disjoint sheets through that point, so a block-free family is impossible as
soon as `doublePointSet ∩ Q ≠ ∅`; `0 < η` is a field, so an `η`-free reading is impossible too.
`hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty` gives the base case `Z 0 = ∅` and
nothing more, and `isStableCrossingBlock_of_flatSheets` inhabits the block predicate with
`η = 1`: two transverse coordinate planes, `a = b = 0`, `La = Lb = 0`.  The uniform separation of
the remaining source from the block is not a separate field: the full-preimage equality
`S ∩ f ⁻¹' chartBlock = SA ∪ SB` already places every other source point outside the block, and
a uniform distance from the half-size block follows from compactness of the source; a separate
uniform field would not survive `isStableCrossingBlock_of_eqOn_compl`.

The folded counterexample of the fourth external review violates (b).  Its two complete local
sheets are the bent `L = {y = 0, x ≥ 0} ∪ {x = 0, y ≥ 0}` and the bent `V = {y = |x|}`, both
times the crossing line.  In any affine coordinates the two ray directions of `L` must have
`|U| ≤ La |V|` and those of `V` must have `|V| ≤ Lb |U|`; since the two `V`-values of the `L`
rays have opposite signs, adding gives `|p| + |q| ≤ La (|r| + |s|) = La |V (e₂ - e₁)| ≤ La Lb
(|p| + |q|)`, hence `1 ≤ La Lb`, contradicting `La Lb ≤ 1 - η`.  So that configuration is not a
hypothesis of the seed leaf, and the seed leaf is not refuted by it; the flat fixture (two flat
sheets crossing transversally inside the chart, frozen outer ring, `Z ∩ W ≠ ∅`) does satisfy
(b) with `η = 1`, so the seed leaf is not vacuous either.

Two scales, not one.  The third external review refuted the claim that a single `ε` can both
keep the perturbed chart image inside `⇑ec '' V` and measure the ambient error: on the flat torus
`(ℝ/20ℤ)³` with `D = (s, t, 0)`, `ec q = q / 2` and `V = B (0, 1)` the chart buffer forces
`ε ≤ 1 / 2` at the origin while the inverse chart doubles the error.  Preparation returns an
ambient `δ` and a chart `ε` with the conversion
`dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ`; `hcert` and `hclose` measure
in `M` with `δ`, while `hsmall`, the chart buffer, the active buffer and the boundary track
buffer measure in the chart with `ε`.

Admissibility is the `Prop`-valued `AdmissibleVertexMap`: vertex error `< τ`, equality with
`ec ∘ ⇑D` at vertices of the frozen collar, height zero exactly at the physical boundary vertices
`Bv`, positive height at all other vertices.  It is inhabited for every `τ > 0` by the
unperturbed vertex map (`exists_admissibleVertexMap_of_adaptedChart`), so the seed leaf cannot be
made vacuous by a tiny `τ`, and `Bv` is determined by `R` and `Lc`, so the seed leaf quantifies
over `Bv` and `φ` together and the generic leaf returns both.

The pairing is gone; localisation stays.  `K` is compact, contained in `V`, and chosen in the
seed leaf before `φ`, with `⇑D '' Rc.space ⊆ interior K`.  Over `Z ∩ K` the old crossings that a
frozen or mixed simplex can meet are protected by the seed leaf's `hprot`; off `K` the crossing
leaf transports by the identity, because
`preimage_singleton_eq_of_eqOn_compl_of_image_subset` turns `EqOn ⇑D' ⇑D Rc.spaceᶜ` together with
the two image bounds into `⇑D' ⁻¹' {y} = ⇑D ⁻¹' {y}` for every `y ∉ K`; on the free part the
crossings are recognised afresh from the guard, which in dimension three already yields the
recognition conditions of consult O §1 (an edge and a triangle meet in one point interior to
both, no edge–edge and no vertex–triangle incidence, two triangles span `⊤`), and inside
`LinearMap.ker ℓ` the boundary traces of different sheets cross transversally away from boundary
vertices because no three of four boundary vertices are collinear, the third vertices being at
strictly positive height by admissibility.

The leaves, with owner and review state.

`exists_adaptedHalfSpaceChart_in_double` (lane H, reviewed 2026-09-21, frozen): every point of
the double of a combinatorial three manifold with boundary has arbitrarily small charts of the
maximal `plGroupoid 3` atlas adapted to the actual pair.

`SingularTwoCell.exists_cutOutPiece_of_closure_subset` (lane H, reviewed 2026-09-21, frozen): the
cut-out source piece with boundary, its frozen collar `Ac` and the seam data `Ω`, `Nb`.

`exists_gluedCell_of_vertexMap_in_adaptedChart` (lane H, reviewed 2026-09-21, frozen): the
literal gluing, with equality on the whole complement.

`exists_globalInvariants_of_gluedCell` (lane H, reviewed 2026-09-21, frozen): the invariants of
the glued cell on the whole disk, with the buffered boundary homotopy.

`exists_normalizationPreparation_on_prescribedRegion` (lane H, reviewed 2026-09-21, frozen):
the control complex `T`, the scales `κ`, `δ`, `ε` and the three buffers, all before the
perturbation.

`exists_transitionSubdivisionOnOverlap` (redesigned after consult O, unreviewed): on a compact
overlap of two adapted charts, a finite complex in the first chart's target covering the overlap
on whose faces the transition is affine.  Consult O §4 forbids assuming the transitions affine.

`hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock` (redesigned after consult O, unreviewed):
a margin-stable block is a PL normal double crossing at each of its double points.  The
implication is not short — it has to produce the two embedded sheets, the PL crossing model and
the fibre germ — so it is a named leaf and not a sanity lemma.

`exists_protectedSubdivision_in_adaptedChart` (redesigned after consult O, unreviewed): the seed,
consuming (b) at `m = k`.  It fixes `R`, `τ` and `K` before any vertex map and asserts, for every
admissible `φ`, the control clauses, the protection of the old crossings over `Z ∩ K` that a
simplex with a frozen vertex takes part in, and the survival of the stable blocks with margin
`η / 2`.  The limit argument of consult O §2 needs the *predetermined* injectivity scale, so the
leaf also receives `κ`, `hcert` and the conversion `hconv` of the preparation certificate, which
the pairing leaf it replaces did not have; `Z ∩ closure (V \ closure W)` is compact because `Z` is
closed and `M` is a compact space, and its closed buffer lies in `ec.source` because the cover
theorem now returns `closure (V j) ⊆ ec.source`.

`exists_genericVertexMap_in_adaptedChart` (redesigned after consult O, unreviewed): relative
multi-chart generic production.  Beside admissibility and the relative guard it produces, for
every later chart of the fixed finite family, the wall conditions of consult L §3 and O §4 on the
fixed compact overlaps: the double curve misses the one-skeleton of the transition complex,
crosses its two-faces transversally, and no image of a source edge meets a wall on the double
curve.  Degeneracies forced by frozen data are exempt exactly as in the guard; their retention is
the proved `isStableCrossingBlock_of_eqOn_compl`.

`exists_normalCrossings_of_gluedCell` (redesigned after consult O, unreviewed): recognition on
the free part, protection on the frozen and mixed part, identity transport off `K`, and the
production of (b) for every later chart over `(Z ∪ closure W) ∩ closure (V m \ closure (W m))`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

open Classical in
theorem exists_adaptedHalfSpaceChart_in_double {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 3 K) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (y : (double 3 K).space) (U : Set (double 3 K).space), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space ∧ ℓ ≠ 0 ∧
          y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ Bd ↔ ℓ (ec x) = 0) := by
  sorry

def UniformInjectivityScale {α : Type*} [PseudoMetricSpace α] {β : Type*} (S : Set α)
    (f : α → β) (η : ℝ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y < η → f x = f y → x = y

theorem uniformInjectivityScale_of_injOn {α : Type*} [PseudoMetricSpace α] {β : Type*}
    {S : Set α} {f : α → β} (h : InjOn f S) (η : ℝ) : UniformInjectivityScale S f η :=
  fun _ hx _ hy _ hxy => h hx hy hxy

open Classical in
def StarInj {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    (T : Geometry.SimplicialComplex ℝ E) (g : E → β) : Prop :=
  ∀ v ∈ T.vertices, InjOn g (starComplex T v).space

open Classical in
theorem starInj_of_injOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {β : Type*}
    {T : Geometry.SimplicialComplex ℝ E} {g : E → β} (h : InjOn g T.space) : StarInj T g := by
  intro v _
  exact Set.InjOn.mono (space_mono_of_faces_subset (starComplex_faces_subset T v)) h

theorem preimage_singleton_eq_of_eqOn_compl_of_image_subset {α β : Type*} {f f' : α → β}
    {R : Set α} {P : Set β} (hoff : EqOn f' f Rᶜ) (hf : f '' R ⊆ P) (hf' : f' '' R ⊆ P)
    {y : β} (hy : y ∉ P) : f' ⁻¹' {y} = f ⁻¹' {y} := by
  ext x
  by_cases hx : x ∈ R
  · simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h
      exact absurd (h ▸ hf' (mem_image_of_mem f' hx)) hy
    · intro h
      exact absurd (h ▸ hf (mem_image_of_mem f hx)) hy
  · simp only [mem_preimage, mem_singleton_iff, hoff hx]

def blockBox (r tlo : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1| ≤ r ∧ |p.2.1| ≤ r ∧ p.2.2 ∈ Icc tlo r}

def complexSkeleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ E) : Set E :=
  ⋃ (s : Finset E) (_ : s ∈ K.faces) (_ : s.card ≤ n + 1), convexHull ℝ (s : Set E)

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem exists_finiteAdaptedCover_of_compactSpace [T2Space M] [CompactSpace M] (BdM C : Set M)
    (hchart : ∀ (y : M) (U : Set M), U ∈ 𝓝 y →
      ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
        (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ y ∈ ec.source ∧ ec.source ⊆ U ∧
          (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
          (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)) :
    ∃ (n : ℕ) (W V : ℕ → Set M),
      (∀ j, IsOpen (W j)) ∧ (∀ j, IsOpen (V j)) ∧ (∀ j, closure (W j) ⊆ V j) ∧
        (∀ j, n ≤ j → W j = ∅) ∧ (⋃ j, W j) = univ ∧
        ∀ j < n, ∃ (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
          (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
          ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ closure (V j) ⊆ ec.source ∧
            (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
            (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  have key : ∀ y : M, ∃ (Wy Vy : Set M)
      (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      IsOpen Wy ∧ y ∈ Wy ∧ IsOpen Vy ∧ closure Wy ⊆ Vy ∧ closure Vy ⊆ ec.source ∧
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧
        (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
        (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
    intro y
    obtain ⟨ec, ℓ, hec, hℓ, hy, -, hC, hBd⟩ := hchart y univ Filter.univ_mem
    obtain ⟨s, hs, hsub, hcomp⟩ := local_compact_nhds (ec.open_source.mem_nhds hy)
    have hVopen : IsOpen (interior s) := isOpen_interior
    have hyV : y ∈ interior s := mem_interior_iff_mem_nhds.2 hs
    have hclV : closure (interior s) ⊆ ec.source :=
      (closure_mono interior_subset).trans (hcomp.isClosed.closure_eq.subset.trans hsub)
    obtain ⟨s', hs', hsub', hcomp'⟩ := local_compact_nhds (hVopen.mem_nhds hyV)
    exact ⟨interior s', interior s, ec, ℓ, isOpen_interior,
      mem_interior_iff_mem_nhds.2 hs', hVopen,
      (closure_mono interior_subset).trans (hcomp'.isClosed.closure_eq.subset.trans hsub'),
      hclV, hec, hℓ, hC, hBd⟩
  choose Wy Vy ecy ℓy hWopen hymem hVyopen hWVy hVycl hecm hℓne hCm hBdm using key
  obtain ⟨t, -, hcover⟩ :=
    isCompact_univ.elim_nhds_subcover Wy fun y _ => (hWopen y).mem_nhds (hymem y)
  let p : ∀ j : ℕ, j < t.card → M := fun j h => ((t.equivFin.symm ⟨j, h⟩ : {x // x ∈ t}) : M)
  refine ⟨t.card, fun j => if h : j < t.card then Wy (p j h) else ∅,
    fun j => if h : j < t.card then Vy (p j h) else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hVyopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWVy _
    · simp only [dif_neg h, closure_empty]
      exact Subset.rfl
  · intro j hj
    exact dif_neg (not_lt.2 hj)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    refine mem_iUnion.2 ⟨((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ), ?_⟩
    rw [dif_pos (t.equivFin ⟨y, hy⟩).isLt]
    have hval : p ((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ) (t.equivFin ⟨y, hy⟩).isLt = y :=
      congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨y, hy⟩)
    rw [hval]
    exact hxy
  · intro j hj
    refine ⟨ecy (p j hj), ℓy (p j hj), hecm _, hℓne _, ?_, hCm _, hBdm _⟩
    simp only [dif_pos hj]
    exact hVycl _

theorem SingularTwoCell.exists_cutOutPiece_of_closure_subset [T2Space M] (D : SingularTwoCell M)
    {V₀ V : Set M} (hV : IsOpen V) (hV₀ : closure V₀ ⊆ V) :
    ∃ (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Ω Nb : Set (EuclideanSpace ℝ (Fin 2))),
      Rc.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 2 Rc ∧
        Lc.faces ⊆ Rc.faces ∧ Ac.faces ⊆ Rc.faces ∧
        Rc.space ⊆ D.domain ∧ Rc.space ⊆ ⇑D ⁻¹' V ∧
        Lc.space = Rc.space ∩ frontier D.domain ∧
        IsOpen Ω ∧ D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω ∧ D.domain ∩ Ω ⊆ Rc.space ∧
        IsOpen Nb ∧ Rc.space \ Ω ⊆ Nb ∧ Rc.space ∩ Nb ⊆ Ac.space ∧
        Disjoint Ac.space (⇑D ⁻¹' closure V₀) := by
  sorry

theorem exists_gluedCell_of_vertexMap_in_adaptedChart [T2Space M] (D : SingularTwoCell M)
    {V : Set M} (hVopen : IsOpen V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hAR : Ac.faces ⊆ Rc.faces) (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpl : IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space)
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V)) :
    ∃ D' : SingularTwoCell M, D'.domain = D.domain ∧
      EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space ∧
      EqOn (⇑D') (⇑D) Rc.spaceᶜ := by
  sorry

def chartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' blockBox r tlo)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem chartBlock_mono_of_half (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {r tlo : ℝ} (hr : 0 ≤ r) (ht : tlo ≤ 0) :
    chartBlock ec A (r / 2) (tlo / 2) ⊆ chartBlock ec A r tlo := by
  intro x hx
  obtain ⟨hxs, hxb⟩ := hx
  refine ⟨hxs, ?_⟩
  simp only [mem_preimage, blockBox, mem_ofPred_eq, mem_Icc] at hxb ⊢
  exact ⟨hxb.1.trans (by linarith), hxb.2.1.trans (by linarith),
    by linarith [hxb.2.2.1], by linarith [hxb.2.2.2]⟩

def IsStableCrossingBlock (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM : Set M)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ 0 ≤ La ∧ 0 ≤ Lb ∧ La * Lb ≤ 1 - η ∧
    ((tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
        (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
          ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))) ∧
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB ∧ Disjoint SA SB ∧
    (∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) ∧
    (∀ x ∈ SB, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2)) ∧
    InjOn (fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) SA ∧
    InjOn (fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)) SB ∧
    (∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|) ∧
    (∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) ∧
    IsPiecewiseAffineOn a univ ∧ IsPiecewiseAffineOn b univ

def HasStableCrossingBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM Q : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ))
      (r tlo : Fin m → ℝ) (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2)))
      (a b : Fin m → ℝ × ℝ → ℝ) (La Lb : Fin m → ℝ),
      doublePointSet f S ∩ Q ⊆ ⋃ i, chartBlock ec (A i) (r i / 2) (tlo i / 2) ∧
        ∀ i, IsStableCrossingBlock f S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i)
          (La i) (Lb i) η

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) (hQ : Q' ⊆ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb,
    (inter_subset_inter Subset.rfl hQ).trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (hQ : doublePointSet f S ∩ Q = ∅) (hη : 0 < η) :
    HasStableCrossingBlocks f S ec ℓ BdM Q η := by
  refine ⟨hη, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, Fin.elim0, ?_, fun i => i.elim0⟩
  rw [hQ]
  exact empty_subset _

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem sheets_nonempty_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) :
    (SA ∩ f ⁻¹' {y}).Nonempty ∧ (SB ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, -, -, -, -, -, hpre, -, -, -, hinjA, hinjB, -, -, -, -⟩ := h
  obtain ⟨x, hxS, z, hzS, hxz, hxy, hzy⟩ := hy
  have hfeq : f x = f z := by rw [hxy, hzy]
  have hxmem : x ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hxS, by simp only [mem_preimage, hxy]; exact hyB⟩
  have hzmem : z ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hzS, by simp only [mem_preimage, hzy]; exact hyB⟩
  have hnotA : ¬(x ∈ SA ∧ z ∈ SA) := by
    rintro ⟨hxA, hzA⟩
    exact hxz (hinjA hxA hzA (by simp only [hfeq]))
  have hnotB : ¬(x ∈ SB ∧ z ∈ SB) := by
    rintro ⟨hxB, hzB⟩
    exact hxz (hinjB hxB hzB (by simp only [hfeq]))
  rcases hxmem with hxA | hxB
  · rcases hzmem with hzA | hzB
    · exact absurd ⟨hxA, hzA⟩ hnotA
    · exact ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  · rcases hzmem with hzA | hzB
    · exact ⟨⟨z, hzA, hzy⟩, ⟨x, hxB, hxy⟩⟩
    · exact absurd ⟨hxB, hzB⟩ hnotB

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_sheets_of_hasStableCrossingBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Q) :
    ∃ SA' SB' : Set (EuclideanSpace ℝ (Fin 2)),
      Disjoint SA' SB' ∧ (SA' ∩ f ⁻¹' {y}).Nonempty ∧ (SB' ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
  obtain ⟨hr0, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -⟩ := hblk i
  have ht : tlo i ≤ 0 := by
    rcases hside with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · rw [h1]; linarith
    · exact le_of_eq h1
  obtain ⟨hA, hB⟩ := sheets_nonempty_of_isStableCrossingBlock (hblk i) hy.1
    (chartBlock_mono_of_half ec (A i) (le_of_lt hr0) ht hi)
  exact ⟨SA i, SB i, hdisj, hA, hB⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hinjA : InjOn (fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) SA)
    (hinjB : InjOn (fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)) SB) :
    IsStableCrossingBlock f S ec ℓ BdM A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, Or.inl ⟨rfl, hBd⟩, hpre, hdisj, hA, hB,
    hinjA, hinjB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_compl {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S Rgn : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hoff : EqOn g f Rgnᶜ) (hfree : Disjoint Rgn (S ∩ f ⁻¹' chartBlock ec A r tlo))
    (hfree' : Disjoint Rgn (S ∩ g ⁻¹' chartBlock ec A r tlo)) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hmar, hside, hpre, hdisj, hgA, hgB, hiA, hiB, hLipa, hLipb,
    hpa, hpb⟩ := h
  have hgeq : ∀ x ∈ SA ∪ SB, g x = f x := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    exact hoff fun hxR => (disjoint_left.mp hfree hxR) hxpre
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hxR : x ∉ Rgn := fun hxR => (disjoint_left.mp hfree' hxR) hx
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, ← hoff hxR]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq x hx]; exact hxpre.2⟩
  refine ⟨hr, hη, hLa, hLb, hmar, ?_, hpre', hdisj, ?_, ?_, ?_, ?_, hLipa, hLipb, hpa, hpb⟩
  · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, h2, fun x hx => ?_⟩
      rw [hgeq x hx]
      exact h3 x hx
  · intro x hx
    rw [hgeq x (Or.inl hx)]
    exact hgA x hx
  · intro x hx
    rw [hgeq x (Or.inr hx)]
    exact hgB x hx
  · intro x hx z hz hxz
    simp only [hgeq x (Or.inl hx), hgeq z (Or.inl hz)] at hxz
    exact hiA hx hz hxz
  · intro x hx z hz hxz
    simp only [hgeq x (Or.inr hx), hgeq z (Or.inr hz)] at hxz
    exact hiB hx hz hxz

theorem exists_transitionSubdivisionOnOverlap
    (ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hec : ec ∈ (plGroupoid 3).maximalAtlas M) (hec' : ec' ∈ (plGroupoid 3).maximalAtlas M)
    (N : Set M) (hN : IsCompact N) (hNec : N ⊆ ec.source) (hNec' : N ⊆ ec'.source) :
    ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
      Q.faces.Finite ∧ ⇑ec '' N ⊆ Q.space ∧
        Q.space ⊆ ⇑ec '' (ec.source ∩ ec'.source) ∧
        ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun z => ec' (ec.symm z)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) := by
  sorry

theorem hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock (D : SingularTwoCell M)
    {BdM : Set M} (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock (⇑D) D.domain ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet (⇑D) D.domain)
    (hyB : y ∈ chartBlock ec A (r / 2) (tlo / 2)) :
    ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
      HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
        (⇑e '' (e.source ∩ BdM)) (e y) := by
  sorry

def AdmissibleVertexMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (τ : ℝ) : Prop :=
  (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices ∧
    (∀ v ∈ R.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
    (∀ v ∈ R.vertices, dist (φ v) (ec (D v)) < τ) ∧
    (∀ v ∈ R.vertices, v ∈ Ac.space → φ v = ec (D v)) ∧
    (∀ v ∈ R.vertices, v ∈ Bv → ℓ (φ v) = 0) ∧
    ∀ v ∈ R.vertices, v ∉ Bv → 0 < ℓ (φ v)

open Classical in
theorem exists_admissibleVertexMap_of_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRsfin : R.faces.Finite) (hsub : IsSubdivision R Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain) {τ : ℝ} (hτ : 0 < τ) :
    ∃ Bv : Finset (EuclideanSpace ℝ (Fin 2)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv (fun v => ec (D v)) τ := by
  classical
  have hvfin : R.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn hRsfin
  have hvR : ∀ v ∈ R.vertices, v ∈ Rc.space := by
    intro v hv
    rw [← hsub.space_eq]
    exact Geometry.SimplicialComplex.vertices_subset_space hv
  have hsrc : ∀ v ∈ R.vertices, D v ∈ ec.source := fun v hv => hVec (hRV (hvR v hv))
  have hmemBv : ∀ v, v ∈ hvfin.toFinset.filter (fun w => w ∈ Lc.space) ↔
      v ∈ R.vertices ∧ v ∈ Lc.space := by
    intro v
    simp [Finset.mem_filter, hvfin.mem_toFinset]
  refine ⟨hvfin.toFinset.filter fun w => w ∈ Lc.space, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact ((hmemBv v).1 (Finset.mem_coe.mp hv)).1
  · exact fun v hv => ⟨fun h => ((hmemBv v).1 h).2, fun h => (hmemBv v).2 ⟨hv, h⟩⟩
  · intro v _
    simpa using hτ
  · exact fun _ _ _ => rfl
  · intro v hv hvB
    have hvL : v ∈ Lc.space := ((hmemBv v).1 hvB).2
    rw [hLspace] at hvL
    have hmem : v ∈ D.domain ∩ ⇑D ⁻¹' BdM := by
      rw [hproper]
      exact hvL.2
    exact (hBdchart (D v) (hsrc v hv)).1 hmem.2
  · intro v hv hvB
    have hvRc : v ∈ Rc.space := hvR v hv
    have hvL : v ∉ Lc.space := fun h => hvB ((hmemBv v).2 ⟨hv, h⟩)
    have hne : ℓ (ec (D v)) ≠ 0 := by
      intro h
      have hBd : D v ∈ BdM := (hBdchart (D v) (hsrc v hv)).2 h
      have hfr : v ∈ frontier D.domain := by
        rw [← hproper]
        exact ⟨hRdom hvRc, hBd⟩
      exact hvL (by rw [hLspace]; exact ⟨hvRc, hfr⟩)
    exact lt_of_le_of_ne ((hCchart (D v) (hsrc v hv)).1 (hmapC (hRdom hvRc))) (Ne.symm hne)

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

open Classical in
noncomputable def regionGluedMap (D : SingularTwoCell M)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) :
    EuclideanSpace ℝ (Fin 2) → M :=
  fun x => if x ∈ Rc.space then ec.symm (simplicialMap Rs φ x) else D x

theorem eq_regionGluedMap_of_eqOn {D D' : SingularTwoCell M}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {Rs Rc : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    ⇑D' = regionGluedMap D ec Rs φ Rc := by
  classical
  funext x
  by_cases hx : x ∈ Rc.space
  · simp only [regionGluedMap, if_pos hx]
    exact hglue hx
  · simp only [regionGluedMap, if_neg hx]
    exact hglueoff hx

theorem exists_normalizationPreparation_on_prescribedRegion [CompactSpace M]
    (D : SingularTwoCell M) {BdM B W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hVopen : IsOpen V) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (κ δ ε : ℝ),
      0 < κ ∧ 0 < δ ∧ 0 < ε ∧ T.faces.Finite ∧ T.space = D.domain ∧ StarInj T (⇑D) ∧
        (∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
          StarInj T g → UniformInjectivityScale D.domain g κ ∧
            ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space) ∧
        ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z) := by
  sorry

open Classical in
theorem exists_protectedSubdivision_in_adaptedChart [CompactSpace M]
    (D : SingularTwoCell M) {BdM C Z O W V : Set M} {η κ δ ε : ℝ}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hZclosed : IsClosed Z) (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVopen : IsOpen V) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hWV : closure W ⊆ V) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W))
    (hstable : HasStableCrossingBlocks (⇑D) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D))
    (hκ : 0 < κ) (hδ : 0 < δ) (hε : 0 < ε)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hconv : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ) :
    ∃ (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (τ : ℝ) (K : Set M),
      0 < τ ∧ IsSubdivision R Rc ∧ R.faces.Finite ∧
        (∀ s ∈ R.faces, ∃ A : EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
          EqOn (fun x => ec (D x)) A
            (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 2))))) ∧
        IsCompact K ∧ K ⊆ V ∧ ⇑D '' Rc.space ⊆ interior K ∧
        ∀ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
          (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
          AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ →
          IsPiecewiseAffineOn (simplicialMap R φ) Rc.space ∧
            (∀ x ∈ Rc.space, dist (simplicialMap R φ x) (ec (D x)) < ε) ∧
            EqOn (simplicialMap R φ) (fun x => ec (D x)) Ac.space ∧
            (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap R φ x)) ∧
            (∀ x ∈ Rc.space, ℓ (simplicialMap R φ x) = 0 ↔ x ∈ Lc.space) ∧
            (∀ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) →
              Disjoint
                (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
                (⇑ec '' closure W)) ∧
            MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V) ∧
            regionGluedMap D ec R φ Rc '' Rc.space ⊆ K ∧
            StarInj T (regionGluedMap D ec R φ Rc) ∧
            (∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Z ∩ K,
              (∃ σ ∈ R.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
                  (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' {y} ∩
                    convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
                ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
                  HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec R φ Rc)
                    (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' e₁.source)
                    (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
            HasStableCrossingBlocks (regionGluedMap D ec R φ Rc) D.domain ec ℓ BdM
              (Z ∩ closure (V \ closure W)) (η / 2) := by
  sorry

open Classical in
theorem exists_genericVertexMap_in_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite)
    (ι : Type) [Finite ι] (ecw : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Qw : ι → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) (Nw : ι → Set M)
    (hNcpt : ∀ i, IsCompact (Nw i)) (hNec : ∀ i, Nw i ⊆ ec.source)
    (hNecw : ∀ i, Nw i ⊆ (ecw i).source) (hQfin : ∀ i, (Qw i).faces.Finite)
    (hQcover : ∀ i, ⇑ec '' Nw i ⊆ (Qw i).space)
    (hQsrc : ∀ i, (Qw i).space ⊆ ⇑ec '' (ec.source ∩ (ecw i).source))
    (hQaff : ∀ i, ∀ s ∈ (Qw i).faces,
      ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun z => ecw i (ec.symm z)) A
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))))
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ ∧
        (∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2)))) ∧
        (∀ i : ι,
          Disjoint (⇑ec '' (doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i))
            (complexSkeleton 1 (Qw i))) ∧
        (∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i,
          ∀ F ∈ (Qw i).faces, F.card = 3 →
            ec y ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) →
              ∃ w : EuclideanSpace ℝ (Fin 3),
                w ∉ vectorSpan ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) ∧ ∃ ρ > 0,
                  ⇑ec '' (doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ ec.source) ∩
                    Metric.ball (ec y) ρ ⊆ {z | ∃ c : ℝ, z = ec y + c • w}) ∧
        ∀ i : ι, ∀ σ ∈ R.faces, σ.card ≤ 2 →
          Disjoint
            (simplicialMap R φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ∩
              ⇑ec '' (doublePointSet (regionGluedMap D ec R φ Rc) D.domain ∩ Nw i))
            (complexSkeleton 2 (Qw i)) := by
  sorry

theorem exists_globalInvariants_of_gluedCell (D D' : SingularTwoCell M)
    {BdM B C V : Set M} {ε δ κ : ℝ}
    {T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) (hκ : 0 < κ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < δ) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hclose : ∀ x ∈ D.domain, dist (D' x) (D x) < δ) (hstar : StarInj T (⇑D'))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hVopen : IsOpen V) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hΩ : IsOpen Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space) (hNb : IsOpen Nb)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hsub : IsSubdivision Rs Rc)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → z ∈ ⇑ec '' V)
    (hbdbuf : ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    MapsTo (⇑D') D'.domain C ∧ (∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z}) ∧
      (∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U) ∧
      (∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2) ∧
      D'.domain ∩ ⇑D' ⁻¹' BdM = frontier D'.domain ∧
      ∃ H : ContinuousMap (unitInterval × frontier D.domain) M,
        (∀ x : frontier D.domain, H (0, x) = D x) ∧
        (∀ x : frontier D.domain, H (1, x) = D' x) ∧
        ∀ (t : unitInterval) (x : frontier D.domain),
          H (t, x) ∈ BdM ∧ B ∈ 𝓝[BdM] (H (t, x)) := by
  sorry

open Classical in
theorem exists_normalCrossings_of_gluedCell (D D' : SingularTwoCell M)
    {BdM C Z O W V K : Set M} {ε η κ : ℝ}
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hfiber' : ∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2)
    (hloc' : ∀ x ∈ D'.domain, ∃ U ∈ 𝓝[D'.domain] x, InjOn (⇑D') U)
    (hκ : 0 < κ) (hinj : UniformInjectivityScale D.domain (⇑D) κ)
    (hinj' : UniformInjectivityScale D.domain (⇑D') κ)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (hWopen : IsOpen W) (hWV : closure W ⊆ V) (hVopen : IsOpen V) (hKclosed : IsClosed K)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : closure V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω : Set (EuclideanSpace ℝ (Fin 2))}
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hDK : ⇑D '' Rc.space ⊆ K) (hD'K : ⇑D' '' Rc.space ⊆ K)
    (hΩ : IsOpen Ω) (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω)
    (hΩR : D.domain ∩ Ω ⊆ Rc.space)
    (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
    (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hε : 0 < ε) (hsub : IsSubdivision Rs Rc) (hRsfin : Rs.faces.Finite)
    (hBvL : ∀ v ∈ Rs.vertices, v ∈ Bv ↔ v ∈ Lc.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hpnonneg : ∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x))
    (hpzero : ∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space)
    (hfrozen : EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    (hguard : ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
      (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices → s.card ≤ 4 →
        (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ
          (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
        AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))))
    (hprot : ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Z ∩ K,
      (∃ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) ∧
          (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' {y} ∩
            convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) →
        ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
          HasPLNormalDoubleCrossingAt (⇑e₁ ∘ regionGluedMap D ec Rs φ Rc)
            (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' e₁.source)
            (⇑e₁ '' (e₁.source ∩ BdM)) (e₁ y))
    (hpersist : HasStableCrossingBlocks (regionGluedMap D ec Rs φ Rc) D.domain ec ℓ BdM
      (Z ∩ closure (V \ closure W)) η)
    (ι : Type) [Finite ι] (ecw : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓw : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ))
    (Qw : ι → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (Nw Pw : ι → Set M) (ηw : ι → ℝ)
    (hNcpt : ∀ i, IsCompact (Nw i)) (hNec : ∀ i, Nw i ⊆ ec.source)
    (hNecw : ∀ i, Nw i ⊆ (ecw i).source) (hPw : ∀ i, Pw i ⊆ (ecw i).source)
    (hQfin : ∀ i, (Qw i).faces.Finite) (hQcover : ∀ i, ⇑ec '' Nw i ⊆ (Qw i).space)
    (hQaff : ∀ i, ∀ s ∈ (Qw i).faces,
      ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
        EqOn (fun z => ecw i (ec.symm z)) A
          (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))))
    (hlater : ∀ i, HasStableCrossingBlocks (⇑D) D.domain (ecw i) (ℓw i) BdM
      (Z ∩ Pw i) (ηw i))
    (hwallskel : ∀ i : ι,
      Disjoint (⇑ec '' (doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i))
        (complexSkeleton 1 (Qw i)))
    (hwalltrans : ∀ i : ι, ∀ y ∈ doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i,
      ∀ F ∈ (Qw i).faces, F.card = 3 →
        ec y ∈ convexHull ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) →
          ∃ w : EuclideanSpace ℝ (Fin 3),
            w ∉ vectorSpan ℝ (F : Set (EuclideanSpace ℝ (Fin 3))) ∧ ∃ ρ > 0,
              ⇑ec '' (doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ ec.source) ∩
                Metric.ball (ec y) ρ ⊆ {z | ∃ c : ℝ, z = ec y + c • w})
    (hwallfold : ∀ i : ι, ∀ σ ∈ Rs.faces, σ.card ≤ 2 →
      Disjoint
        (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))) ∩
          ⇑ec '' (doublePointSet (regionGluedMap D ec Rs φ Rc) D.domain ∩ Nw i))
        (complexSkeleton 2 (Qw i)))
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    (∃ O' : Set M, IsOpen O' ∧ Z ∪ closure W ⊆ O' ∧
        ∀ y ∈ doublePointSet (⇑D') D'.domain ∩ O',
          ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
            HasPLNormalDoubleCrossingAt (e₁ ∘ ⇑D') (D'.domain ∩ ⇑D' ⁻¹' e₁.source)
              (e₁ '' (e₁.source ∩ BdM)) (e₁ y)) ∧
      ∀ i : ι, ∃ η' : ℝ, 0 < η' ∧
        HasStableCrossingBlocks (⇑D') D'.domain (ecw i) (ℓw i) BdM
          ((Z ∪ closure W) ∩ Pw i) η' := by
  sorry

end MetricAmbient

open Classical in
theorem generalPositionInDoubleBuffered : GeneralPositionInDoubleBufferedStatement := by
  classical
  intro E _ _ _ S K
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let _ := combinatorialChartedSpace (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold)
  let _ : CompactSpace (double 3 K).space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space (double 3 K)).isCompact
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  intro ι C Bd B G β γ hloc hfiber _ hbuffer _ hmapC hproper hsurj hparam havoid
  have hBspace : S.boundaryNeighborhood.space ⊆ K.space := fun x hx =>
    PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex hx)
  obtain ⟨n, W, V, hWopen, hVopen, hWV, hWn, huniv, hcharts⟩ :=
    exists_finiteAdaptedCover_of_compactSpace Bd C
      fun y U hU => exists_adaptedHalfSpaceChart_in_double K S.isManifold y U hU
  choose ecf ℓf hecf hℓf hVclf hCf hBdf using hcharts
  have hoverlap : ∀ (j : ℕ) (hj : j < n) (m : ℕ) (hm : m < n),
      ∃ Q : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)),
        Q.faces.Finite ∧ ⇑(ecf j hj) '' (closure (V j) ∩ closure (V m)) ⊆ Q.space ∧
          Q.space ⊆ ⇑(ecf j hj) '' ((ecf j hj).source ∩ (ecf m hm).source) ∧
          ∀ s ∈ Q.faces, ∃ A : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3),
            EqOn (fun z => ecf m hm ((ecf j hj).symm z)) A
              (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin 3)))) :=
    fun j hj m hm =>
      exists_transitionSubdivisionOnOverlap (ecf j hj) (ecf m hm) (hecf j hj) (hecf m hm)
        (closure (V j) ∩ closure (V m))
        ((isClosed_closure.inter isClosed_closure).isCompact)
        (inter_subset_left.trans (hVclf j hj)) (inter_subset_right.trans (hVclf m hm))
  choose Qf hQfin hQcover hQsrc hQaff using hoverlap
  have hVW : ∀ j, V j ⊆ ⋃ i, W i := by
    intro j
    rw [huniv]
    exact subset_univ _
  have hdpG : doublePointSet (⇑G) G.domain ⊆ ⋃ j, W j := by
    rw [huniv]
    exact subset_univ _
  have hUW : ⋃ j, W j ⊆ ⋃ j, ⋃ (_ : j < n), closure (W j) := by
    refine iUnion_subset fun j => ?_
    by_cases hj : j < n
    · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hj, subset_closure hx⟩⟩
    · rw [hWn j (not_lt.mp hj)]
      exact empty_subset _
  have key : ∀ k : ℕ, ∃ (cell : SingularTwoCell (double 3 K).space)
      (Ok : Set (double 3 K).space) (b : ContinuousMap loopCircle (frontier cell.domain))
      (g : freeLoop S.boundaryNeighborhoodSpace),
      cell.domain = G.domain ∧ MapsTo (⇑cell) cell.domain C ∧
        (∀ x ∈ cell.domain, ∃ U ∈ 𝓝[cell.domain] x, InjOn (⇑cell) U) ∧
        (∀ y, (cell.domain ∩ ⇑cell ⁻¹' {y}).encard ≤ 2) ∧
        cell.domain ∩ ⇑cell ⁻¹' Bd = frontier cell.domain ∧
        (∀ z ∈ Set.range cell.boundary, B ∈ 𝓝[Bd] z) ∧
        doublePointSet (⇑cell) cell.domain ⊆ ⋃ j, W j ∧
        IsOpen Ok ∧ (⋃ j, ⋃ (_ : j < k), closure (W j)) ⊆ Ok ∧
        (∀ y ∈ doublePointSet (⇑cell) cell.domain ∩ Ok,
          ∃ e₂ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₂.source ∧
            HasPLNormalDoubleCrossingAt (e₂ ∘ ⇑cell) (cell.domain ∩ ⇑cell ⁻¹' e₂.source)
              (e₂ '' (e₂.source ∩ Bd)) (e₂ y)) ∧
        (∀ (m : ℕ) (hm : m < n), k ≤ m → ∃ ηm : ℝ, 0 < ηm ∧
          HasStableCrossingBlocks (⇑cell) cell.domain (ecf m hm) (ℓf m hm) Bd
            ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩ closure (V m \ closure (W m))) ηm) ∧
        Function.Surjective b ∧
        (∀ θ, ((cell (b θ) : (double 3 K).space) : E × E × ℝ) = ι (g θ)) ∧
        ¬loopClassMeets g S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, ∅, β, γ, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, isOpen_empty,
          ?_, ?_, ?_, hsurj, hparam, havoid⟩
        · exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
        · exact fun y hy => absurd hy.2 (notMem_empty y)
        · intro m hm _
          have hz : (⋃ j, ⋃ (_ : j < 0), closure (W j)) = (∅ : Set (double 3 K).space) :=
            eq_empty_of_subset_empty (iUnion_subset fun j => iUnion_subset fun hj =>
              absurd hj (Nat.not_lt_zero j))
          refine ⟨1, one_pos,
            hasStableCrossingBlocks_of_doublePointSet_inter_eq_empty ?_ one_pos⟩
          rw [hz, empty_inter, inter_empty]
    | succ k ih =>
        obtain ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
          hcelldp, hOkopen, hOkZ, hOkcross, hcellstb, hbsurj, hbparam, hbavoid⟩ := ih
        have hZsucc : (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) ⊆
            (⋃ j, ⋃ (_ : j < k), closure (W j)) ∪ closure (W k) := by
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with h | h
          · exact fun x hx => mem_union_left _ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨h, hx⟩⟩)
          · subst h
            exact fun x hx => mem_union_right _ hx
        by_cases hk : k < n
        · set ec := ecf k hk with hecdef
          set ℓ := ℓf k hk with hℓdef
          have hec : ec ∈ (plGroupoid 3).maximalAtlas (double 3 K).space := hecf k hk
          have hℓ : ℓ ≠ 0 := hℓf k hk
          have hVcl : closure (V k) ⊆ ec.source := hVclf k hk
          have hVec : V k ⊆ ec.source := subset_closure.trans hVcl
          have hCchart := hCf k hk
          have hBdchart := hBdf k hk
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cell.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          have hZclosed : IsClosed (⋃ j, ⋃ (_ : j < k), closure (W j)) :=
            Set.Finite.isClosed_biUnion (Set.finite_lt_nat k) fun j _ => isClosed_closure
          obtain ⟨ηk, hηk, hstk⟩ := hcellstb k hk le_rfl
          obtain ⟨T, κ, δ, ε, hκ, hδ, hε, hTfin, hTspace, hTstar, hcert, hconv, hactive,
            hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cell hcellloc hcellfib
              hcellbuf (hVopen k) (hWV k) ec hVec Rc Ac hRfin hAR hRdom hRV hAfree
          have hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
              dist z (ec (cell x)) < ε → z ∈ ⇑ec '' V k :=
            fun x hx z hz => (hconv x hx z hz).1
          obtain ⟨R, τ, Kt, hτ, hsub, hRsfin, -, hKcpt, -, hDKint, hcontrol⟩ :=
            exists_protectedSubdivision_in_adaptedChart cell hcellloc hcellfib hcellpr
              hcellC hOkcross hZclosed hOkopen hOkZ ec ℓ hec hℓ (hVopen k) hVcl hCchart
              hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom hRV hLspace hΩ hΩR hNb hNbfr hNbA
              (hWV k) hAfree hstk T hTfin hTspace hTstar hκ hδ hε hcert hconv
          have : Finite ↥(Set.Ioo k n) := (Set.finite_Ioo k n).to_subtype
          obtain ⟨Bv, φ, hadm, hguard, hwallskel, hwalltrans, hwallfold⟩ :=
            exists_genericVertexMap_in_adaptedChart cell hcellpr hcellC ec ℓ hℓ hVec hCchart
              hBdchart Rc Lc Ac hLR hAR hRdom hRV hLspace R hsub hRsfin ↥(Set.Ioo k n)
              (fun i => ecf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => Qf k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => closure (V k) ∩ closure (V i.1))
              (fun _ => (isClosed_closure.inter isClosed_closure).isCompact)
              (fun _ => inter_subset_left.trans hVcl)
              (fun i => inter_subset_right.trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => hQfin k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQcover k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQsrc k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQaff k hk i.1 (Set.mem_Ioo.mp i.2).2) hτ
          obtain ⟨hpl, hsmall, hfrozen, hpnonneg, hpzero, hsep, hmaps, hgK, hstar, hprot,
            hpersist⟩ := hcontrol Bv φ hadm
          obtain ⟨cell', hdom', hglue, hglueoff⟩ :=
            exists_gluedCell_of_vertexMap_in_adaptedChart cell (hVopen k) ec hec hVec Rc Ac
              hRfin hRman hAR hRdom hRV hΩ hΩR hNb hNbfr hNbA R φ hsub hRsfin hfrozen hpl
              hmaps
          have hbridge : ⇑cell' = regionGluedMap cell ec R φ Rc :=
            eq_regionGluedMap_of_eqOn hglue hglueoff
          have hclose : ∀ x ∈ cell.domain, dist (cell' x) (cell x) < δ := by
            intro x _
            by_cases hxR : x ∈ Rc.space
            · rw [hglue hxR]
              exact (hconv x hxR _ (hsmall x hxR)).2
            · rw [hglueoff hxR, dist_self]
              exact hδ
          have hstar' : StarInj T (⇑cell') := by
            rw [hbridge]
            exact hstar
          have hDK : ⇑cell '' Rc.space ⊆ Kt := hDKint.trans interior_subset
          have hD'K : ⇑cell' '' Rc.space ⊆ Kt := by
            rw [hbridge]
            exact hgK
          obtain ⟨hC', hfibV, hloc', hcard', hpr', H, hH0, hH1, hHtrack⟩ :=
            exists_globalInvariants_of_gluedCell cell cell' hcellpr hcellC hcellbuf hκ hcert
              hclose hstar' ec ℓ (hVopen k) hVec hCchart hBdchart Rc Lc Ac hRfin hRman hRdom
              hRV hLspace hΩ hΩR hNb hNbfr hNbA R φ hsub hsmall hfrozen hpnonneg hpzero
              hchartbuf hbdbuf hdom' hglue hglueoff
          have hlaterfam : ∀ i : ↥(Set.Ioo k n), ∃ ηm : ℝ, 0 < ηm ∧
              HasStableCrossingBlocks (⇑cell) cell.domain
                (ecf i.1 (Set.mem_Ioo.mp i.2).2) (ℓf i.1 (Set.mem_Ioo.mp i.2).2) Bd
                ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩
                  closure (V i.1 \ closure (W i.1))) ηm :=
            fun i => hcellstb i.1 (Set.mem_Ioo.mp i.2).2 (le_of_lt (Set.mem_Ioo.mp i.2).1)
          have hinjD : UniformInjectivityScale cell.domain (⇑cell) κ :=
            (hcert (⇑cell) (fun x _ => by rw [dist_self]; exact hδ) hTstar).1
          have hinjD' : UniformInjectivityScale cell.domain (⇑cell') κ :=
            (hcert (⇑cell') hclose hstar').1
          obtain ⟨⟨O', hO'open, hO'Z, hcross'⟩, hstable'⟩ :=
            exists_normalCrossings_of_gluedCell cell cell' hcellfib hcard' hloc' hκ hinjD
              hinjD' hcellpr
              hOkcross hOkopen hOkZ (hWopen k) (hWV k) (hVopen k) hKcpt.isClosed ec ℓ hec hℓ
              hVcl hCchart hBdchart Rc Lc Ac hRfin hRman hRdom hRV hLspace hDK hD'K hΩ
              hΩcover hΩR R Bv φ hε hsub hRsfin hadm.2.1 hsmall hpnonneg hpzero hfrozen
              hactive hsep hmaps hguard hprot hpersist ↥(Set.Ioo k n)
              (fun i => ecf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => ℓf i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => Qf k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => closure (V k) ∩ closure (V i.1))
              (fun i => closure (V i.1 \ closure (W i.1)))
              (fun i => (hlaterfam i).choose)
              (fun _ => (isClosed_closure.inter isClosed_closure).isCompact)
              (fun _ => inter_subset_left.trans hVcl)
              (fun i => inter_subset_right.trans (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => (closure_mono Set.sdiff_subset).trans
                (hVclf i.1 (Set.mem_Ioo.mp i.2).2))
              (fun i => hQfin k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQcover k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => hQaff k hk i.1 (Set.mem_Ioo.mp i.2).2)
              (fun i => (hlaterfam i).choose_spec.2)
              hwallskel hwalltrans hwallfold hdom' hglue hglueoff
          have hbuf' : ∀ z ∈ Set.range cell'.boundary, B ∈ 𝓝[Bd] z := by
            rintro _ ⟨x, rfl⟩
            have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ frontier cell.domain := by
              rw [← hdom']
              exact x.2
            have h1 := hHtrack 1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩
            rw [hH1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩] at h1
            exact h1.2
          have hdpnew : doublePointSet (⇑cell') cell'.domain ⊆ ⋃ j, W j := by
            rw [hdom']
            exact doublePointSet_subset_of_preimage_singleton_eq_off cell.domain hfibV
              hcelldp (hVW k)
          have hHB : ∀ (t : unitInterval) (x : frontier cell.domain), H (t, x) ∈ B :=
            fun t x => mem_of_mem_nhdsWithin (hHtrack t x).1 (hHtrack t x).2
          obtain ⟨c, δ₀, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cell cell' b g hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          refine ⟨cell', O', ⟨c, c.continuous⟩, δ₀, hdom'.trans hdom, hC', hloc', hcard',
            hpr', hbuf', hdpnew, hO'open, ?_, hcross', ?_, c.surjective, hcδ, hδavoid⟩
          · exact hZsucc.trans hO'Z
          · intro m hm hkm
            have hik : m ∈ Set.Ioo k n := Set.mem_Ioo.mpr ⟨by omega, hm⟩
            obtain ⟨ηm, hηm, hstm⟩ := hstable' ⟨m, hik⟩
            exact ⟨ηm, hηm, hstm.mono (inter_subset_inter hZsucc Subset.rfl)⟩
        · refine ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
            hcelldp, hOkopen, ?_, hOkcross, ?_, hbsurj, hbparam, hbavoid⟩
          · refine iUnion_subset fun j => iUnion_subset fun hj => ?_
            by_cases hjk : j < k
            · exact fun x hx => hOkZ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩)
            · rw [hWn j (by omega), closure_empty]
              exact empty_subset _
          · intro m hm hkm
            exact absurd hm (by have := not_lt.mp hk; omega)
  obtain ⟨A, On, b, g, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hOnZ, hAcross, -,
    hbsurj, hbparam, hbavoid⟩ := key n
  have hAcross' : ∀ y ∈ doublePointSet (⇑A) A.domain,
      ∃ e₃ ∈ atlas (EuclideanSpace ℝ (Fin 3)) (double 3 K).space, y ∈ e₃.source ∧
        HasPLNormalDoubleCrossingAt (e₃ ∘ ⇑A) (A.domain ∩ ⇑A ⁻¹' e₃.source)
          (e₃ '' (e₃.source ∩ Bd)) (e₃ y) :=
    fun y hy => hAcross y ⟨hy, hOnZ (hUW (hAdp hy))⟩
  have hAbd : Set.range A.boundary ⊆ B := by
    rintro _ ⟨x, rfl⟩
    have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ A.domain ∩ ⇑A ⁻¹' Bd := by
      rw [hApr]
      exact x.2
    exact mem_of_mem_nhdsWithin hx.2 (hAbuf _ ⟨x, rfl⟩)
  have hAimage : A '' A.domain ∩ Bd = Set.range A.boundary := by
    rw [← image_inter_preimage, hApr]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩, fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  obtain ⟨hA⟩ := SingularTwoCell.nonempty_normalSingularCellData_of_fields (double 3 K)
    (isCombinatorialManifold_double_succ_succ K S.isManifold) A Bd B hAloc hAfib hAbd
    hAimage hAcross'
  obtain ⟨c, δ₁, hcδ, hδavoid⟩ :=
    exists_boundary_loop_of_buffered_homotopy S K A A b g rfl hAC hbparam hbavoid hbsurj
      ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ₁, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
