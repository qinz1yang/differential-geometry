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

The assembly `generalPositionInDoubleBuffered` below is proved for real from the seven leaves of
this file, from the proved cover theorem `exists_finiteAdaptedCover_of_compactSpace`, from the
proved bridge `eq_regionGluedMap_of_eqOn`, from
`SingularTwoCell.nonempty_normalSingularCellData_of_fields`, from
`doublePointSet_subset_of_preimage_singleton_eq_off` and from
`exists_boundary_loop_of_buffered_homotopy`; every `sorry` is a leaf, none is inside the
assembly.  The chain is: adapted half-space charts at every point of the double, a finite cover
of the whole double by regions `closure (W j) ⊆ V j` with `V j` inside one adapted chart, then a
chart-by-chart induction whose step cuts out a source piece carrying all sheets over
`closure (W k)`, chooses **before any perturbation** a control complex `T` of the whole source
disk, an injectivity scale `κ`, a perturbation size `ε` and four uniform buffers, perturbs the
vertex map of that piece relative to the frozen collar, glues the result back literally,
re-establishes the global invariants together with the buffered boundary homotopy, and only then
recognises the crossings; at the last index every double point lies in the already normalised
region, which is the `crossing` field of `NormalSingularCellData`.

The second external review (snapshot `08eca8995a81`, digested in
`consult/J-generalposition-skeleton-review-digest.md`) refuted the transport guarantee that the
previous module docstring claimed, and that guarantee is **withdrawn**: a closed buffer together
with an `ε` fixed beforehand is not a crossing-stability certificate, and the scale `θ` that the
old vertex map leaf returned *with* the perturbation was not a predetermined control at all.
Transport of the old crossings across `Z ∩ V` is now an explicit source-sheet pairing certificate
produced by the perturbation leaf, and the two a-posteriori scales `η`, `θ` are replaced by one
predetermined whole-source control certificate carried by `StarInj`.

The two counterexamples of that review are recorded, each with the clause that now kills it.  The
fold `D = (s, t, 1 - max |s| |t|)`, `D' = (|s|, t, 1 - max |s| |t|)` on `Rc = S ∩ {s ≤ 0}` with
`Ac = {0} × [-1, 1]` and `Ω = ∅` satisfied every hypothesis of the old invariants leaf although
`D'` folds along the seam, and it is excluded because `hNbfr` and `hNbA` now force
`Rc.space ⊆ Ac.space` when `Ω = ∅`, so `hfrozen` leaves the cell unchanged there.  The pairing
change `ABAB → AABB`, in which the four rays of two transverse source sheets are re-paired by an
arbitrarily small perturbation with every frozen exemption respected, satisfied every hypothesis
of the old crossing leaf, and it is excluded because the transport half now consumes a PL
homeomorphism `ψ` of the **full** source preimage conjugating `⇑D` into `⇑D'`, which no
re-pairing of the four branches allows.

Non-degeneracy of the pairing certificate is part of its statement: `Z ⊆ U'` together with
`χ '' U = U'` forbids the empty solution `U = ∅` whenever `Z ≠ ∅`, and `IsPLHomeomorphOn` asks
for a bijection onto `D.domain ∩ ⇑D' ⁻¹' U'`, so no sheet may leave or enter.  Nothing in the
certificate asks `χ` to be the identity, so it stays satisfiable when `Z` meets `closure W`.

Instance binders.  The control certificate compares a competitor `g` with `⇑D` in the metric of
the ambient manifold, which the skeleton's `[TopologicalSpace M]` does not supply.  The four
leaves that mention that comparison are therefore stated for `[MetricSpace M]`, whose topology is
the one they already used; the assembly instantiates `M` by `(double 3 K).space`, a subtype of
the normed space `E × E × ℝ`, so `Subtype.metricSpace` supplies it.  Preparation and the vertex
map also take `[CompactSpace M]`, which the assembly has from `isPolyhedron_space`, and which is
what lets a closed `Z` be shrunk inside `O` and be treated as compact.

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

`exists_normalizationPreparation_on_prescribedRegion` (lane H, H6a, changed after second review,
unreviewed): everything chosen *before* the perturbation.  A control complex `T` of the whole
source disk on which `⇑D` is star injective, one scale `κ`, one perturbation size `ε`, the open
`O₀` with `Z ⊆ O₀` and `closure O₀ ⊆ O`, and the certificate that *every* competitor `g` that is
`ε`-close to `⇑D` on the whole disk and star injective on `T` has `κ` as a uniform injectivity
scale and at most two preimages over each point.  The four buffers are the chart buffer, which
supplies the `MapsTo` clause of the gluing leaf; the conversion buffer, which turns an `ε`-error
measured in the chart into an `ε`-error measured in `M`; the active buffer, which keeps
`ε`-competitors of frozen points off `closure W`; and the boundary track buffer, which is
condition (12).

`exists_small_vertexMap_relative_in_adaptedChart` (lane H, H5 and B5, changed after second
review, unreviewed): the relative guarded half-space general position on that piece, read in the
adapted chart.  The new vertex map agrees with `ec ∘ ⇑D` on `Ac.space` only; the half-space
conditions keep the physical boundary subcomplex `Lc` in place of `boundaryComplex 2 Rc`; the
affine independence conclusion keeps the guard
`(s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1`, since four boundary vertices are
coplanar and dropping it makes the leaf false, with the frozen part of `s` exempted in the
relative form.  The leaf now receives `T` and `StarInj T ⇑D` and *produces* `StarInj T` for the
literal glued function, so the control fixed before the perturbation is the control the
invariants leaf consumes, and it produces the source-sheet pairing certificate over the protected
region; `hsep`, which keeps every face meeting the frozen collar off `ec '' closure W`, stays.

`exists_globalInvariants_of_gluedCell` (lane H, H6c, changed after second review, unreviewed):
the invariants of the glued cell on the whole disk.  The two a-posteriori scales are gone: the
leaf consumes the preparation certificate together with `StarInj T ⇑D'` and the `ε`-closeness of
`⇑D'` to `⇑D`, both established before it is called, and it now also receives the seam
neighbourhood hypotheses `hNb`, `hNbfr`, `hNbA` of the cut-out leaf, without which injectivity on
each side of the seam does not give injectivity across it.  The conclusion carries the target
`C`, the fibre agreement off `V`, local injectivity, the multiplicity bound, properness against
`BdM`, and the boundary homotopy whose whole track stays in `BdM` with `B` as a relative
neighbourhood, which is condition (12).

`exists_normalCrossings_of_gluedCell` (lane H, H6d, changed after second review, unreviewed):
recognition on the active target and transport on the protected one.  Over `closure W` the
crossings are read off the guarded affine independence, `hfrozen` and the certificate `hsep`,
which is what excludes the coincident sheet configurations the guard exempts; over `Z` they are
transported, off `V` by the fibre agreement on `O₀`, and inside `V` by the pairing certificate,
which is now a hypothesis instead of a hoped-for consequence of a scale.  The output is one open
`O' ⊇ Z ∪ closure W` carrying normal crossings.
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
    (D : SingularTwoCell M) {BdM B Z O W V : Set M}
    (hloc : ∀ x ∈ D.domain, ∃ U ∈ 𝓝[D.domain] x, InjOn (⇑D) U)
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z)
    (hZclosed : IsClosed Z) (hOopen : IsOpen O) (hZO : Z ⊆ O)
    (hVopen : IsOpen V) (hWV : closure W ⊆ V)
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))) (hVec : V ⊆ ec.source)
    (Rc Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    (hRfin : Rc.faces.Finite) (hAR : Ac.faces ⊆ Rc.faces)
    (hRdom : Rc.space ⊆ D.domain) (hRV : Rc.space ⊆ ⇑D ⁻¹' V)
    (hAfree : Disjoint Ac.space (⇑D ⁻¹' closure W)) :
    ∃ (T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))) (κ ε : ℝ) (O₀ : Set M),
      0 < κ ∧ 0 < ε ∧ T.faces.Finite ∧ T.space = D.domain ∧ StarInj T (⇑D) ∧
        IsOpen O₀ ∧ Z ⊆ O₀ ∧ closure O₀ ⊆ O ∧
        (∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < ε) →
          StarInj T g → UniformInjectivityScale D.domain g κ ∧
            ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → z ∈ ⇑ec '' V) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → dist (ec.symm z) (D x) < ε) ∧
        (∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space) ∧
        ∀ x ∈ Rc.space ∩ frontier D.domain, ∀ z : EuclideanSpace ℝ (Fin 3),
          dist z (ec (D x)) < ε → ec.symm z ∈ BdM → B ∈ 𝓝[BdM] (ec.symm z) := by
  sorry

open Classical in
theorem exists_small_vertexMap_relative_in_adaptedChart [CompactSpace M]
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
    ∃ (Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
      (Bv : Finset (EuclideanSpace ℝ (Fin 2)))
      (φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)),
      IsSubdivision Rs Rc ∧ Rs.faces.Finite ∧
        (Bv : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices ∧
        (∀ v ∈ Rs.vertices, v ∈ Bv ↔ v ∈ Lc.space) ∧
        EqOn (simplicialMap Rs φ) (fun x => ec (D x)) Ac.space ∧
        IsPiecewiseAffineOn (simplicialMap Rs φ) Rc.space ∧
        (∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε) ∧
        StarInj T (regionGluedMap D ec Rs φ Rc) ∧
        (∀ x ∈ Rc.space, 0 ≤ ℓ (simplicialMap Rs φ x)) ∧
        (∀ x ∈ Rc.space, ℓ (simplicialMap Rs φ x) = 0 ↔ x ∈ Lc.space) ∧
        (∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
          Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
            (⇑ec '' closure W)) ∧
        (∃ (U U' : Set M) (χ : M → M)
          (ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
          IsOpen U ∧ IsOpen U' ∧ U ⊆ O ∧ Z ⊆ U' ∧
            IsPLHomeomorphInto 3 χ U ∧ χ '' U = U' ∧ χ '' (U ∩ BdM) = U' ∩ BdM ∧
            IsPLHomeomorphOn ψ (D.domain ∩ ⇑D ⁻¹' U)
              (D.domain ∩ regionGluedMap D ec Rs φ Rc ⁻¹' U') ∧
            ∀ x ∈ D.domain ∩ ⇑D ⁻¹' U, regionGluedMap D ec Rs φ Rc (ψ x) = χ (D x)) ∧
        ∀ s : Finset (EuclideanSpace ℝ (Fin 2)),
          (s : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Rs.vertices → s.card ≤ 4 →
            (s ∩ Bv).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
            AffineIndependent ℝ
              (fun v : (s.filter fun x => x ∈ Ac.space) => φ (v : EuclideanSpace ℝ (Fin 2))) →
            AffineIndependent ℝ (fun v : s => φ (v : EuclideanSpace ℝ (Fin 2))) := by
  sorry

theorem exists_globalInvariants_of_gluedCell (D D' : SingularTwoCell M)
    {BdM B C V : Set M} {ε κ : ℝ}
    {T : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hmapC : MapsTo (⇑D) D.domain C)
    (hbuffer : ∀ z ∈ Set.range D.boundary, B ∈ 𝓝[BdM] z) (hκ : 0 < κ)
    (hcert : ∀ g : EuclideanSpace ℝ (Fin 2) → M, (∀ x ∈ D.domain, dist (g x) (D x) < ε) →
      StarInj T g → UniformInjectivityScale D.domain g κ ∧
        ∀ y, (D.domain ∩ g ⁻¹' {y}).encard ≤ 2)
    (hclose : ∀ x ∈ D.domain, dist (D' x) (D x) < ε) (hstar : StarInj T (⇑D'))
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
    {BdM C Z O O₀ U U' W V : Set M} {ε : ℝ} {χ : M → M}
    {ψ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hfiber : ∀ y, (D.domain ∩ ⇑D ⁻¹' {y}).encard ≤ 2)
    (hfiber' : ∀ y, (D'.domain ∩ ⇑D' ⁻¹' {y}).encard ≤ 2)
    (hproper : D.domain ∩ ⇑D ⁻¹' BdM = frontier D.domain)
    (hnormal : ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
      ∃ e₀ ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e₀.source ∧
        HasPLNormalDoubleCrossingAt (e₀ ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e₀.source)
          (e₀ '' (e₀.source ∩ BdM)) (e₀ y))
    (hZclosed : IsClosed Z) (hZO₀ : Z ⊆ O₀) (hO₀open : IsOpen O₀) (hO₀O : closure O₀ ⊆ O)
    (hWopen : IsOpen W) (hWV : closure W ⊆ V) (hVopen : IsOpen V)
    (hfibV : ∀ z ∉ V, (⇑D') ⁻¹' {z} = (⇑D) ⁻¹' {z})
    (hUopen : IsOpen U) (hU'open : IsOpen U') (hUO : U ⊆ O) (hZU' : Z ⊆ U')
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
          obtain ⟨T, κ, ε, O₀, hκ, hε, hTfin, hTspace, hTstar, hO₀open, hZO₀, hO₀O, hcert,
            hchartbuf, hconv, hactive, hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cell hcellloc hcellfib
              hcellbuf hZclosed hOkopen hOkZ (hVopen k) (hWV k) ec hVec Rc Ac hRfin hAR
              hRdom hRV hAfree
          obtain ⟨Rs, Bv, φ, hsub, hRsfin, -, hBvL, hfrozen, hpl, hsmall, hstar, hpnonneg,
            hpzero, hsep, ⟨U, U', χ, ψ, hUopen, hU'open, hUO, hZU', hχ, hχimage, hχbd, hψ,
            hpair⟩, hguard⟩ :=
            exists_small_vertexMap_relative_in_adaptedChart cell hcellloc hcellfib hcellpr
              hcellC hOkcross hZclosed hOkopen hOkZ ec ℓ hec hℓ (hVopen k) hVec hCchart
              hBdchart Rc Lc Ac hRfin hRman hLR hAR hRdom hRV hLspace (hWV k) hAfree T hTfin
              hTspace hTstar hε
          obtain ⟨cell', hdom', hglue, hglueoff⟩ :=
            exists_gluedCell_of_vertexMap_in_adaptedChart cell (hVopen k) ec hec hVec Rc Ac
              hRfin hRman hAR hRdom hRV hΩ hΩR hNb hNbfr hNbA Rs φ hsub hRsfin hfrozen hpl
              fun x hx => hchartbuf x hx _ (hsmall x hx)
          have hbridge : ⇑cell' = regionGluedMap cell ec Rs φ Rc :=
            eq_regionGluedMap_of_eqOn hglue hglueoff
          have hclose : ∀ x ∈ cell.domain, dist (cell' x) (cell x) < ε := by
            intro x _
            by_cases hxR : x ∈ Rc.space
            · have hxv : cell' x = ec.symm (simplicialMap Rs φ x) := hglue hxR
              rw [hxv]
              exact hconv x hxR _ (hsmall x hxR)
            · have hxv : cell' x = cell x := hglueoff hxR
              rw [hxv, dist_self]
              exact hε
          have hstar' : StarInj T (⇑cell') := by
            rw [hbridge]
            exact hstar
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
              hRV hLspace hΩ hΩR hNb hNbfr hNbA Rs φ hsub hsmall hfrozen hpnonneg hpzero
              hchartbuf hbdbuf hdom' hglue hglueoff
          obtain ⟨O', hO'open, hO'Z, hcross'⟩ :=
            exists_normalCrossings_of_gluedCell cell cell' hcellfib hcard' hcellpr hOkcross
              hZclosed hZO₀ hO₀open hO₀O (hWopen k) (hWV k) (hVopen k) hfibV hUopen hU'open
              hUO hZU' hχ hχimage hχbd hψ' hpair' ec ℓ hec hℓ hVec hCchart hBdchart Rc Lc Ac
              hRfin hRman hRdom hRV hLspace hΩ hΩcover hΩR Rs Bv φ hε hsub hRsfin hBvL
              hsmall hpnonneg hpzero hfrozen hactive hsep hguard hdom' hglue hglueoff
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
          obtain ⟨c, δ, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cell cell' b g hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          refine ⟨cell', O', ⟨c, c.continuous⟩, δ, hdom'.trans hdom, hC', hloc', hcard',
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
  obtain ⟨c, δ, hcδ, hδavoid⟩ :=
    exists_boundary_loop_of_buffered_homotopy S K A A b g rfl hAC hbparam hbavoid hbsurj
      ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
