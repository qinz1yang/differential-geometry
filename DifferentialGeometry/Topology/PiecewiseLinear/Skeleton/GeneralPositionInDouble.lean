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

The assembly `generalPositionInDoubleBuffered` below is proved for real from the eight leaves of
this file, from the proved cover theorem `exists_finiteAdaptedCover_of_compactSpace`, from the
proved bridge `eq_regionGluedMap_of_eqOn`, from
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the whole double by regions `closure (W j) ⊆ V j` with `V j` inside one adapted chart, then a
chart-by-chart induction whose step cuts out a source piece carrying all sheets over
`closure (W k)`, chooses **before any perturbation** a control complex `T` of the whole source
disk, an injectivity scale `κ`, an ambient perturbation size `δ`, a chart perturbation size `ε`
and three uniform buffers, then a fixed control subdivision `R`, a vertex tolerance `τ` and a
compact target buffer `K`, only then chooses a generic guarded vertex map `φ`, glues the result
back literally, re-establishes the global invariants together with the buffered boundary
homotopy, and only then recognises the crossings; at the last index every double point lies in
the already normalised region, which is the `crossing` field of `NormalSingularCellData`.

Two scales, not one.  The third external review (snapshot `94791ab1c755`, digested in
`consult/J-generalposition-skeleton-review-digest.md`) refuted the claim that a single `ε` can
both keep the perturbed chart image inside `⇑ec '' V` and measure the ambient error, and that
claim is **withdrawn**: on the flat torus `(ℝ/20ℤ)³` with `D = (s, t, 0)`, `ec q = q / 2` and
`V = B (0, 1)` the chart buffer forces `ε ≤ 1 / 2` at the origin while the inverse chart doubles
the error, so `z = 3 ε e₁ / 4` has chart error `< ε` and ambient error `3 ε / 2`.  Preparation
now returns an ambient `δ` and a chart `ε` with the conversion
`dist z (ec (D x)) < ε → z ∈ ⇑ec '' V ∧ dist (ec.symm z) (D x) < δ`, satisfiable there for
`ε ≤ δ / 2`; `hcert` and `hclose` measure in `M` with `δ`, while `hsmall`, the chart buffer, the
active buffer and the boundary track buffer measure in the chart with `ε`.

Stability before genericity.  The claim that "`χ` need not be the identity" exhibits the pairing
certificate and the guarded genericity as jointly producible is also **withdrawn**: it shows only
that the certificate alone is satisfiable.  The old perturbation leaf is therefore split.
`exists_pairingStableSubdivision_in_adaptedChart` fixes `R`, `τ` and `K` first and asserts, for
*every* admissible vertex map on that `R`, the chart closeness, the frozen seam, the half-space
conditions, `hsep`, `MapsTo (simplicialMap R φ) Rc.space (⇑ec '' V)`, the image bound in `K`,
`StarInj T` for the literal glued map, and the source-sheet pairing certificate.
`exists_guardedVertexMap_in_adaptedChart` then chooses, for that fixed `R` and every `τ > 0`, an
admissible `φ` satisfying the guard.  Admissibility is the `Prop`-valued `AdmissibleVertexMap`:
vertex error `< τ`, equality with `ec ∘ ⇑D` at vertices of the frozen collar, height zero exactly
at the physical boundary vertices `Bv`, positive height at all other vertices.  It is inhabited
for every `τ > 0` by the unperturbed vertex map `fun v => ec (D v)`, strict positivity included
(`exists_admissibleVertexMap_of_adaptedChart`): `hproper` puts a vertex of `Rc.space \ Lc.space`
off `BdM`, so its height is nonzero, and `hmapC` with `hCchart` makes every height nonnegative.
Frozen vertices are no exception, whether they sit at height zero or above: those on `Lc.space`
lie in `Bv` and have height zero, the others have positive height.  So `A_R` is satisfiable for
every `τ > 0`, and the stability leaf cannot be made vacuous by a tiny `τ`.

The pairing is localised.  `K` is compact, contained in `V`, and chosen in the stability leaf
*before* `φ`, with `⇑D '' Rc.space ⊆ interior K`; that interior buffer is what makes
`regionGluedMap D ec R φ Rc '' Rc.space ⊆ K` a consequence of the tolerance `τ` instead of an
extra assumption, and it is asserted for every admissible `φ`.  The full-preimage certificate
`U, U', χ, ψ` is produced only near the compact set `Z ∩ K`; off `K` the crossing leaf transports
by the identity, because `preimage_singleton_eq_of_eqOn_compl_of_image_subset` turns
`EqOn ⇑D' ⇑D Rc.spaceᶜ` together with the two image bounds into `⇑D' ⁻¹' {y} = ⇑D ⁻¹' {y}` for
every `y ∉ K`.  `Z ∩ V` would not do: it is not compact, and `Vᶜ` is not a neighbourhood of a
boundary point of `V`.  Since `Z ⊆ O` with `O` open, the transport half needs no shrunk `O₀`, so
the open set `O₀` and the fibre agreement `hfibV` are gone from the crossing leaf, and with them
`O₀`, `Z` and `O` from the preparation leaf.

The four refuted counterexamples are recorded, each with the clause that now kills it.  The fold
`D = (s, t, 1 - max |s| |t|)`, `D' = (|s|, t, 1 - max |s| |t|)` on `Rc = S ∩ {s ≤ 0}` with
`Ac = {0} × [-1, 1]` and `Ω = ∅` satisfied every hypothesis of the old invariants leaf although
`D'` folds along the seam, and it is excluded because `hNbfr` and `hNbA` force
`Rc.space ⊆ Ac.space` when `Ω = ∅`, so `hfrozen` leaves the cell unchanged there.  The pairing
change `ABAB → AABB`, in which the four rays of two transverse source sheets are re-paired by an
arbitrarily small perturbation with every frozen exemption respected, is excluded because the
crossing leaf consumes a PL homeomorphism `ψ` of the **full** source preimage conjugating `⇑D`
into `⇑D'` near `Z ∩ K`, and that model's crossing point lies in `⇑D '' Rc.space ⊆ K`, so the
localisation does not release it.  The flat torus above is excluded by the two scales.  The fold
with `p_φ = (10 + s, t, h)`, `ec = id` on `(-3, 3)³`, `Ac = ∅`, `Ω = univ` and `ε = 11`, whose
inverse chart is unconstrained off `ec.target`, is excluded by
`hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V)`, which the stability leaf produces and
the frozen gluing leaf already received.

Non-degeneracy of the pairing certificate is part of its statement: `Z ∩ K ⊆ U'` together with
`χ '' U = U'` forbids the empty solution `U = ∅` whenever `Z ∩ K ≠ ∅`, and `IsPLHomeomorphOn`
asks for a bijection onto `D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' U'`, so no sheet may leave
or enter.

Instance binders.  The control certificate compares a competitor `g` with `⇑D` in the metric of
the ambient manifold, which the skeleton's `[TopologicalSpace M]` does not supply.  The five
leaves that mention that comparison are therefore stated for `[MetricSpace M]`, whose topology is
the one they already used; the assembly instantiates `M` by `(double 3 K).space`, a subtype of
the normed space `E × E × ℝ`, so `Subtype.metricSpace` supplies it.  Preparation and the
stability leaf also take `[CompactSpace M]`, which the assembly has from `isPolyhedron_space`,
and which is what lets `K` be chosen compact inside `V` and `Z ∩ K` be treated as compact.

The leaves, with owner and review state.

`exists_adaptedHalfSpaceChart_in_double` (lane H, H8 and (11), reviewed 2026-09-21, frozen):
every point of the double of a combinatorial three manifold with boundary has arbitrarily small
charts of the maximal `plGroupoid 3` atlas adapted to the actual pair, `x ∈ C ↔ 0 ≤ ℓ (ec x)` and
`x ∈ Bd ↔ ℓ (ec x) = 0`.

`SingularTwoCell.exists_cutOutPiece_of_closure_subset` (lane H, H4 and B4, reviewed 2026-09-21,
frozen): the cut-out source piece with boundary.  `Rc` is a finite combinatorial two manifold
with boundary inside the source disk, `Lc` its physical boundary part, `Ω` an open set with
`D.domain ∩ ⇑D ⁻¹' closure V₀ ⊆ Ω` and `D.domain ∩ Ω ⊆ Rc.space`, which is condition (10); `Ac`
is the frozen collar subcomplex, a neighbourhood in `Rc.space` of the artificial frontier
`Rc.space \ Ω`, and `Disjoint Ac.space (⇑D ⁻¹' closure V₀)` keeps it off the region to normalise.

`exists_gluedCell_of_vertexMap_in_adaptedChart` (lane H, H6b, reviewed 2026-09-21, frozen): the
literal gluing.  On the same source disk, `EqOn ⇑D' (ec.symm ∘ simplicialMap Rs φ) Rc.space` and
`EqOn ⇑D' ⇑D Rc.spaceᶜ` on the whole complement, which is what makes unrestricted preimages of
`D'` computable from the two pieces.  Its statement is unchanged and its binders are unchanged;
`eq_regionGluedMap_of_eqOn` turns those two equalities into the single equation
`⇑D' = regionGluedMap D ec Rs φ Rc`, so the leaves downstream can speak about the literal glued
function without the frozen statement being touched.

`exists_globalInvariants_of_gluedCell` (lane H, H6c, reviewed 2026-09-21, frozen): the invariants
of the glued cell on the whole disk, from the preparation certificate `hcert`, the ambient
closeness `hclose` and `hstar`, together with the seam neighbourhood hypotheses `hNb`, `hNbfr`,
`hNbA` of the cut-out leaf, without which injectivity on each side of the seam does not give
injectivity across it.  The only change forced by the two scales is a binder: the scale list
`{ε κ : ℝ}` became `{ε δ κ : ℝ}` and `hcert`, `hclose` now measure the ambient error with `δ`
while `hsmall`, `hchartbuf`, `hbdbuf` keep the chart error `ε`.  The conclusion carries the
target `C`, the fibre agreement off `V`, local injectivity, the multiplicity bound, properness
against `BdM`, and the boundary homotopy whose whole track stays in `BdM` with `B` as a relative
neighbourhood, which is condition (12).

`exists_normalizationPreparation_on_prescribedRegion` (lane H, H6a, changed after third review,
unreviewed): everything chosen *before* the perturbation.  A control complex `T` of the whole
source disk on which `⇑D` is star injective, the scale `κ`, the ambient size `δ`, the chart size
`ε`, the certificate that every competitor `g` that is `δ`-close to `⇑D` on the whole disk in `M`
and star injective on `T` has `κ` as a uniform injectivity scale and at most two preimages over
each point, and three buffers: the combined chart-range and conversion buffer, the active buffer
keeping `ε`-competitors of frozen points off `closure W`, and the boundary track buffer, which is
condition (12).

`exists_pairingStableSubdivision_in_adaptedChart` (lane H, H5a, changed after third review,
unreviewed): the stability half of the old perturbation leaf.  `R`, `τ` and `K` are fixed before
any vertex map, and the conclusion holds for every `Bv`, `φ` with `AdmissibleVertexMap`.

`exists_guardedVertexMap_in_adaptedChart` (lane H, H5b, changed after third review, unreviewed):
the generic half, for the fixed `R` and every `τ > 0`.  The affine independence conclusion keeps
the guard `(s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1`, since four boundary vertices
are coplanar and dropping it makes the leaf false, with the frozen part of `s` exempted in the
relative form.

`exists_normalCrossings_of_gluedCell` (lane H, H6d, changed after third review, unreviewed):
recognition on the active target and transport on the protected one.  Over `closure W` the
crossings are read off the guarded affine independence, `hfrozen`, `hactive` and `hsep`, and
`hmaps` is what ties `hglue` to the chart; over `Z ∩ K` they are transported by the pairing
certificate, and over `Z \ K` by the identity, since `O` is open, `Z ⊆ O` and the fibres agree
off `K`.  The output is one open `O' ⊇ Z ∪ closure W` carrying normal crossings.
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
          ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧ V j ⊆ ec.source ∧
            (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
            (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
  have : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (H := EuclideanSpace ℝ (Fin 3)) M
  have key : ∀ y : M, ∃ (Wy : Set M)
      (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
      (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ),
      IsOpen Wy ∧ y ∈ Wy ∧ closure Wy ⊆ ec.source ∧
        ec ∈ (plGroupoid 3).maximalAtlas M ∧ ℓ ≠ 0 ∧
        (∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x)) ∧
        (∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0) := by
    intro y
    obtain ⟨ec, ℓ, hec, hℓ, hy, -, hC, hBd⟩ := hchart y univ Filter.univ_mem
    obtain ⟨s, hs, hsub, hcomp⟩ := local_compact_nhds (ec.open_source.mem_nhds hy)
    refine ⟨interior s, ec, ℓ, isOpen_interior, mem_interior_iff_mem_nhds.2 hs, ?_, hec, hℓ,
      hC, hBd⟩
    exact (closure_mono interior_subset).trans
      (hcomp.isClosed.closure_eq.subset.trans hsub)
  choose Wy ecy ℓy hWopen hymem hWcl hecm hℓne hCm hBdm using key
  obtain ⟨t, -, hcover⟩ :=
    isCompact_univ.elim_nhds_subcover Wy fun y _ => (hWopen y).mem_nhds (hymem y)
  let p : ∀ j : ℕ, j < t.card → M := fun j h => ((t.equivFin.symm ⟨j, h⟩ : {x // x ∈ t}) : M)
  refine ⟨t.card, fun j => if h : j < t.card then Wy (p j h) else ∅,
    fun j => if h : j < t.card then (ecy (p j h)).source else ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWopen _
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact (ecy _).open_source
    · simp only [dif_neg h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dif_pos h]
      exact hWcl _
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
    exact Subset.rfl

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
theorem exists_pairingStableSubdivision_in_adaptedChart [CompactSpace M]
    (D : SingularTwoCell M) {BdM C Z O W V : Set M}
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
    (hℓ : ℓ ≠ 0) (hVopen : IsOpen V) (hVec : V ⊆ ec.source)
    (hCchart : ∀ x ∈ ec.source, x ∈ C ↔ 0 ≤ ℓ (ec x))
    (hBdchart : ∀ x ∈ ec.source, x ∈ BdM ↔ ℓ (ec x) = 0)
    (Rc Lc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hRman : IsCombinatorialManifoldWithBoundary 2 Rc)
    (hLR : Lc.faces ⊆ Rc.faces) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hLspace : Lc.space = Rc.space ∩ frontier D.domain)
    (hWV : closure W ⊆ V) (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W))
    (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (hTfin : T.faces.Finite)
    (hTspace : T.space = D.domain) (hTstar : StarInj T (⇑D))
    {ε : ℝ} (hε : 0 < ε) :
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
              ∃ (U U' : Set M) (χ : M → M)
                (ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
                IsOpen U ∧ IsOpen U' ∧ U ⊆ O ∧ Z ∩ K ⊆ U' ∧
                  IsPLHomeomorphInto 3 χ U ∧ χ '' U = U' ∧ χ '' (U ∩ BdM) = U' ∩ BdM ∧
                  IsPLHomeomorphOn ψ (D.domain ∩ ⇑D ⁻¹' U)
                    (D.domain ∩ regionGluedMap D ec R φ Rc ⁻¹' U') ∧
                  ∀ x ∈ D.domain ∩ ⇑D ⁻¹' U,
                    regionGluedMap D ec R φ Rc (ψ x) = χ (D x) := by
  sorry

open Classical in
theorem exists_guardedVertexMap_in_adaptedChart (D : SingularTwoCell M) {BdM C V : Set M}
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
    (hsub : IsSubdivision R Rc) (hRsfin : R.faces.Finite) {τ : ℝ} (hτ : 0 < τ) :
    ∃ (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      AdmissibleVertexMap D ec ℓ Lc Ac R Bv φ τ ∧
        ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ R.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))) := by
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
    {BdM C Z O U U' W V K : Set M} {ε : ℝ} {χ : M → M}
    {ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hfiber' : ∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (hWopen : IsOpen W) (hWV : closure W ⊆ V) (hVopen : IsOpen V) (hKclosed : IsClosed K)
    (hUopen : IsOpen U) (hU'open : IsOpen U') (hUO : U ⊆ O) (hZKU' : Z ∩ K ⊆ U')
    (hχ : IsPLHomeomorphInto 3 χ U) (hχimage : χ '' U = U')
    (hχbd : χ '' (U ∩ BdM) = U' ∩ BdM)
    (hψ : IsPLHomeomorphOn ψ (D.domain ∩ ⇑D ⁻¹' U) (D.domain ∩ ⇑D' ⁻¹' U'))
    (hpair : ∀ x ∈ D.domain ∩ ⇑D ⁻¹' U, D' (ψ x) = χ (D x))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hec : ec ∈ (plGroupoid 3).maximalAtlas M)
    (hℓ : ℓ ≠ 0) (hVec : V ⊆ ec.source)
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
    (hdom' : D'.domain = D.domain)
    (hglue : EqOn (⇑D') (fun x => ec.symm (simplicialMap Rs φ x)) Rc.space)
    (hglueoff : EqOn (⇑D') (⇑D) Rc.spaceᶜ) :
    ∃ O' : Set M, IsOpen O' ∧ Z ∪ closure W ⊆ O' ∧
      ∀ y ∈ doublePointSet (⇑D') D'.domain ∩ O',
        ∃ e₁ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₁.source ∧
          HasPLNormalDoubleCrossingAt (e₁ ∘ ⇑D') (D'.domain ∩ ⇑D' ⁻¹' e₁.source)
            (e₁ '' (e₁.source ∩ BdM)) (e₁ y) := by
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
        Function.Surjective b ∧
        (∀ θ, ((cell (b θ) : (double 3 K).space) : E × E × ℝ) = ι (g θ)) ∧
        ¬loopClassMeets g S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, ∅, β, γ, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, isOpen_empty,
          ?_, ?_, hsurj, hparam, havoid⟩
        · exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
        · exact fun y hy => absurd hy.2 (notMem_empty y)
    | succ k ih =>
        obtain ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
          hcelldp, hOkopen, hOkZ, hOkcross, hbsurj, hbparam, hbavoid⟩ := ih
        by_cases hk : k < n
        · obtain ⟨ec, ℓ, hec, hℓ, hVec, hCchart, hBdchart⟩ := hcharts k hk
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cell.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          have hZclosed : IsClosed (⋃ j, ⋃ (_ : j < k), closure (W j)) :=
            Set.Finite.isClosed_biUnion (Set.finite_lt_nat k) fun j _ => isClosed_closure
          obtain ⟨T, κ, δ, ε, hκ, hδ, hε, hTfin, hTspace, hTstar, hcert, hconv, hactive,
            hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cell hcellloc hcellfib
              hcellbuf (hVopen k) (hWV k) ec hVec Rc Ac hRfin hAR hRdom hRV hAfree
          have hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
              dist z (ec (cell x)) < ε → z ∈ ⇑ec '' V k :=
            fun x hx z hz => (hconv x hx z hz).1
          obtain ⟨R, τ, Kt, hτ, hsub, hRsfin, -, hKcpt, -, hDKint, hstable⟩ :=
            exists_pairingStableSubdivision_in_adaptedChart cell hcellloc hcellfib hcellpr
              hcellC hOkcross hZclosed hOkopen hOkZ ec ℓ hec hℓ (hVopen k) hVec hCchart
              hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom hRV hLspace (hWV k) hAfree T hTfin
              hTspace hTstar hε
          obtain ⟨Bv, φ, hadm, hguard⟩ :=
            exists_guardedVertexMap_in_adaptedChart cell hcellpr hcellC ec ℓ hℓ hVec hCchart
              hBdchart Rc Lc Ac hLR hAR hRdom hRV hLspace R hsub hRsfin hτ
          obtain ⟨hpl, hsmall, hfrozen, hpnonneg, hpzero, hsep, hmaps, hgK, hstar, U, U', χ,
            ψ, hUopen, hU'open, hUO, hZKU', hχ, hχimage, hχbd, hψ, hpair⟩ := hstable Bv φ hadm
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
          have hψ' : IsPLHomeomorphOn ψ (cell.domain ∩ ⇑cell ⁻¹' U)
              (cell.domain ∩ ⇑cell' ⁻¹' U') := by
            rw [hbridge]
            exact hψ
          have hpair' : ∀ x ∈ cell.domain ∩ ⇑cell ⁻¹' U, cell' (ψ x) = χ (cell x) := by
            intro x hx
            rw [hbridge]
            exact hpair x hx
          obtain ⟨hC', hfibV, hloc', hcard', hpr', H, hH0, hH1, hHtrack⟩ :=
            exists_globalInvariants_of_gluedCell cell cell' hcellpr hcellC hcellbuf hκ hcert
              hclose hstar' ec ℓ (hVopen k) hVec hCchart hBdchart Rc Lc Ac hRfin hRman hRdom
              hRV hLspace hΩ hΩR hNb hNbfr hNbA R φ hsub hsmall hfrozen hpnonneg hpzero
              hchartbuf hbdbuf hdom' hglue hglueoff
          obtain ⟨O', hO'open, hO'Z, hcross'⟩ :=
            exists_normalCrossings_of_gluedCell cell cell' hcellfib hcard' hcellpr hOkcross
              hOkopen hOkZ (hWopen k) (hWV k) (hVopen k) hKcpt.isClosed hUopen hU'open hUO
              hZKU' hχ hχimage hχbd hψ' hpair' ec ℓ hec hℓ hVec hCchart hBdchart Rc Lc Ac
              hRfin hRman hRdom hRV hLspace hDK hD'K hΩ hΩcover hΩR R Bv φ hε hsub hRsfin
              hadm.2.1 hsmall hpnonneg hpzero hfrozen hactive hsep hmaps hguard hdom' hglue
              hglueoff
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
            hpr', hbuf', hdpnew, hO'open, ?_, hcross', c.surjective, hcδ, hδavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx =>
              hO'Z (mem_union_left _ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩))
          · have hjeq : j = k := by omega
            subst hjeq
            exact fun x hx => hO'Z (mem_union_right _ hx)
        · refine ⟨cell, Ok, b, g, hdom, hcellC, hcellloc, hcellfib, hcellpr, hcellbuf,
            hcelldp, hOkopen, ?_, hOkcross, hbsurj, hbparam, hbavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx => hOkZ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩)
          · rw [hWn j (by omega), closure_empty]
            exact empty_subset _
  obtain ⟨A, On, b, g, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hOnZ, hAcross,
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
