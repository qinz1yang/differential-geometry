/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlock
import DifferentialGeometry.Topology.PiecewiseLinear.DoublePointFibreAgreement
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.GeneralPositionInDoubleAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwoBuffered
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleHalfSpaceChart
import DifferentialGeometry.Topology.PiecewiseLinear.TransitionSubdivisionOnOverlap
import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellInAdaptedChart
import DifferentialGeometry.Topology.PiecewiseLinear.GluedCellGlobalInvariants
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingDoubleCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.CutOutPieceOfClosureSubset
import DifferentialGeometry.Topology.PiecewiseLinear.NormalizationPreparation
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemCellTopology
import DifferentialGeometry.Topology.PiecewiseLinear.FreeGermVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlocksOfWallProductBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.CommonWallComplex
import DifferentialGeometry.Topology.PiecewiseLinear.WallProductBlocksOfWallGenericity
import DifferentialGeometry.Topology.PiecewiseLinear.AdmissibleVertexMapVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.WallGenericVertexMap
import DifferentialGeometry.Topology.PiecewiseLinear.ProtectedSubdivisionInAdaptedChart
import DifferentialGeometry.Topology.PiecewiseLinear.WallProductBlocksStableOnFixedSubdivision

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem uniformInjectivityScale_of_injOn {α : Type*} [PseudoMetricSpace α] {β : Type*}
    {S : Set α} {f : α → β} (h : InjOn f S) (η : ℝ) : UniformInjectivityScale S f η :=
  fun _ hx _ hy _ hxy => h hx hy hxy

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

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

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
    · simp only [dite_eq_left h]
      exact hWopen _
    · simp only [dite_eq_right h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dite_eq_left h]
      exact hVyopen _
    · simp only [dite_eq_right h]
      exact isOpen_empty
  · intro j
    by_cases h : j < t.card
    · simp only [dite_eq_left h]
      exact hWVy _
    · simp only [dite_eq_right h, closure_empty]
      exact Subset.rfl
  · intro j hj
    exact dite_eq_right (not_lt.2 hj)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    refine mem_iUnion.2 ⟨((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ), ?_⟩
    rw [dite_eq_left (t.equivFin ⟨y, hy⟩).isLt]
    have hval : p ((t.equivFin ⟨y, hy⟩ : Fin t.card) : ℕ) (t.equivFin ⟨y, hy⟩).isLt = y :=
      congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨y, hy⟩)
    rw [hval]
    exact hxy
  · intro j hj
    refine ⟨ecy (p j hj), ℓy (p j hj), hecm _, hℓne _, ?_, hCm _, hBdm _⟩
    simp only [dite_eq_left hj]
    exact hVycl _

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem mem_space_of_freeSourceGerm
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (h : FreeSourceGerm R Ac g S y) {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ∈ S ∩ g ⁻¹' {y}) : x ∈ R.space :=
  mem_of_mem_nhdsWithin hx.1 (h x hx).1

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem freeSourceGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {y : M}
    (hAc : Ac.space = ∅) (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    FreeSourceGerm R Ac g S y := by
  refine fun x hx => ⟨hnhds x hx, fun _ _ _ v _ => ?_⟩
  rw [hAc]
  exact notMem_empty v

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeBoundaryDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∈ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x) :
    IsFreeBoundaryDoubleGerm R Ac g S BdM y :=
  ⟨hy, freeSourceGerm_of_frozenSpace_eq_empty hAc hnhds⟩

omit [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isFreeInteriorDoubleGerm_of_frozenSpace_eq_empty
    {R Ac : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2))}
    {g : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} {BdM : Set M}
    {y : M} (hAc : Ac.space = ∅) (hy : y ∉ BdM)
    (hnhds : ∀ x ∈ S ∩ g ⁻¹' {y}, R.space ∈ 𝓝[S] x)
    (hint : ∀ x ∈ S ∩ g ⁻¹' {y}, ∃ σ ∈ R.faces, σ.card = 3 ∧
      x ∈ interior (convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))) :
    IsFreeInteriorDoubleGerm R Ac g S BdM y :=
  ⟨isFreeDoubleGerm_of_frozenSpace_eq_empty hAc hy hnhds, hint⟩

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
theorem IsStableCrossingBlock.mono_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η' :=
  ⟨h.1, hη', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans (by linarith), h.2.2.2.2.2⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.mono_doublePointSet {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q Q' : Set M} {η : ℝ}
    (h : HasStableCrossingBlocks f S ec ℓ BdM Q η)
    (hQ : doublePointSet f S ∩ Q' ⊆ doublePointSet f S ∩ Q) :
    HasStableCrossingBlocks f S ec ℓ BdM Q' η := by
  obtain ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hcov, hblk⟩ := h
  exact ⟨hη, m, A, r, tlo, SA, SB, a, b, La, Lb, hQ.trans hcov, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasStableCrossingBlocks.union {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Q₁ Q₂ : Set M} {η₁ η₂ : ℝ}
    (h₁ : HasStableCrossingBlocks f S ec ℓ BdM Q₁ η₁)
    (h₂ : HasStableCrossingBlocks f S ec ℓ BdM Q₂ η₂) :
    HasStableCrossingBlocks f S ec ℓ BdM (Q₁ ∪ Q₂) (min η₁ η₂) := by
  obtain ⟨hη₁, m₁, A₁, r₁, t₁, SA₁, SB₁, a₁, b₁, La₁, Lb₁, hcov₁, hblk₁⟩ := h₁
  obtain ⟨hη₂, m₂, A₂, r₂, t₂, SA₂, SB₂, a₂, b₂, La₂, Lb₂, hcov₂, hblk₂⟩ := h₂
  refine ⟨lt_min hη₁ hη₂, m₁ + m₂, Fin.addCases A₁ A₂, Fin.addCases r₁ r₂,
    Fin.addCases t₁ t₂, Fin.addCases SA₁ SA₂, Fin.addCases SB₁ SB₂, Fin.addCases a₁ a₂,
    Fin.addCases b₁ b₂, Fin.addCases La₁ La₂, Fin.addCases Lb₁ Lb₂, ?_, ?_⟩
  · rintro y ⟨hy, hQ | hQ⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₁ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.castAdd m₂ i, ?_⟩
      simpa only [Fin.addCases_left] using hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov₂ ⟨hy, hQ⟩)
      refine mem_iUnion.2 ⟨Fin.natAdd m₁ i, ?_⟩
      simpa only [Fin.addCases_right] using hi
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using
        (hblk₁ i).mono_margin (lt_min hη₁ hη₂) (min_le_left _ _)
    · simpa only [Fin.addCases_right] using
        (hblk₂ i).mono_margin (lt_min hη₁ hη₂) (min_le_right _ _)

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
  obtain ⟨hr0, -, -, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -, -, -⟩ := hblk i
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
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc, Or.inl ⟨rfl, hBd⟩, hpre, hdisj,
    hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_flatSheets_boundary {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r 0)))
    (hsrc : closure (chartBlock ec A r 0) ⊆ ec.source)
    (hheight : ∀ z, (A z).2.2 = ℓ z)
    (hfront : ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hpre : S ∩ f ⁻¹' chartBlock ec A r 0 = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r 0 → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane 0] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r 0 → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane 0] (blockSheetProjB ec A f x)) :
    IsStableCrossingBlock f S ec ℓ BdM A r 0 SA SB (fun _ => 0) (fun _ => 0) 0 0 1 := by
  have hpa : IsPiecewiseAffineOn (fun _ : ℝ × ℝ => (0 : ℝ)) univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ) (0 : ℝ)) isOpen_univ).congr
      fun _ _ => rfl
  refine ⟨hr, one_pos, le_rfl, le_rfl, by norm_num, hcpt, hsrc,
    Or.inr ⟨rfl, hheight, hfront⟩, hpre, hdisj, hA, hB, hplA, hplB, hnA, hnB, ?_, ?_, hpa, hpa⟩
  · intro v v' t
    simp
  · intro u u' t
    simp

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_eqOn_sheets {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hgeq : EqOn g f (SA ∪ SB))
    (hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  obtain ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, hside, -, hdisj, hgA, hgB, hplA, hplB,
    hnA, hnB, hLipa, hLipb, hpa, hpb⟩ := h
  have hprojA : EqOn (blockSheetProjA ec A g) (blockSheetProjA ec A f) SA := by
    intro x hx
    simp only [blockSheetProjA, hgeq (Or.inl hx)]
  have hprojB : EqOn (blockSheetProjB ec A g) (blockSheetProjB ec A f) SB := by
    intro x hx
    simp only [blockSheetProjB, hgeq (Or.inr hx)]
  have himA : blockSheetProjA ec A g '' SA = blockSheetProjA ec A f '' SA := image_congr hprojA
  have himB : blockSheetProjB ec A g '' SB = blockSheetProjB ec A f '' SB := image_congr hprojB
  refine ⟨hr, hη, hLa, hLb, hmar, hcpt, hsrc, ?_, hpre', hdisj, ?_, ?_, ?_, ?_, ?_, ?_,
    hLipa, hLipb, hpa, hpb⟩
  · rcases hside with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact Or.inl ⟨h1, h2⟩
    · refine Or.inr ⟨h1, h2, fun x hx => ?_⟩
      rw [hgeq hx]
      exact h3 x hx
  · intro x hx
    rw [hgeq (Or.inl hx)]
    exact hgA x hx
  · intro x hx
    rw [hgeq (Or.inr hx)]
    exact hgB x hx
  · rw [himA]
    exact hplA.congr hprojA
  · rw [himB]
    exact hplB.congr hprojB
  · intro x hx hxb
    rw [hgeq (Or.inl hx)] at hxb
    rw [himA, hprojA hx]
    exact hnA x hx hxb
  · intro x hx hxb
    rw [hgeq (Or.inr hx)] at hxb
    rw [himB, hprojB hx]
    exact hnB x hx hxb

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem preimage_chartBlock_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) :
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact hpre

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem isStableCrossingBlock_of_preimage_singleton_eq {f g : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM N : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hN : chartBlock ec A r tlo ⊆ N)
    (hfib : ∀ z ∈ N, S ∩ g ⁻¹' {z} = S ∩ f ⁻¹' {z}) :
    IsStableCrossingBlock g S ec ℓ BdM A r tlo SA SB a b La Lb η := by
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    have hmem : x ∈ S ∩ g ⁻¹' {f x} := by
      rw [hfib (f x) (hN hxpre.2)]
      exact ⟨hxpre.1, rfl⟩
    exact hmem.2
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hmem : x ∈ S ∩ f ⁻¹' {g x} := by
        rw [← hfib (g x) (hN hx.2)]
        exact ⟨hx.1, rfl⟩
      have hfx : f x = g x := hmem.2
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, hfx]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

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
  have hpre := preimage_chartBlock_eq_of_isStableCrossingBlock h
  have hgeq : EqOn g f (SA ∪ SB) := by
    intro x hx
    have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
    exact hoff fun hxR => (disjoint_left.mp hfree hxR) hxpre
  have hpre' : S ∩ g ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
    · have hxR : x ∉ Rgn := fun hxR => (disjoint_left.mp hfree' hxR) hx
      rw [← hpre]
      exact ⟨hx.1, by simp only [mem_preimage, ← hoff hxR]; exact hx.2⟩
    · have hxpre : x ∈ S ∩ f ⁻¹' chartBlock ec A r tlo := by rw [hpre]; exact hx
      exact ⟨hxpre.1, by simp only [mem_preimage, hgeq hx]; exact hxpre.2⟩
  exact isStableCrossingBlock_of_eqOn_sheets h hgeq hpre'

theorem wallIncidence_simplexBoundary {T : Finset Ea}
    (hT : AffineIndependent ℝ ((↑) : T → Ea)) (hcard : T.card = 5) :
    (simplexBoundary T hT).faces.Finite ∧
      (∀ s ∈ (simplexBoundary T hT).faces, s.card ≤ 4) ∧
      (∀ s ∈ (simplexBoundary T hT).faces,
        ∃ c ∈ wallSystemCells (simplexBoundary T hT), s ⊆ c) ∧
      (wallSystemWalls (simplexBoundary T hT)).Nonempty ∧
      ∀ w ∈ wallSystemWalls (simplexBoundary T hT),
        ∃ cm ∈ wallSystemCells (simplexBoundary T hT),
          ∃ cp ∈ wallSystemCells (simplexBoundary T hT), cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
            ∀ c ∈ wallSystemCells (simplexBoundary T hT), w ⊆ c → c = cm ∨ c = cp := by
  classical
  have hface : ∀ s : Finset Ea,
      s ∈ (simplexBoundary T hT).faces ↔ s ⊆ T ∧ s.Nonempty ∧ s ≠ T :=
    fun _ => mem_simplexBoundary_faces_iff
  have hcardle : ∀ s ∈ (simplexBoundary T hT).faces, s.card ≤ 4 := by
    intro s hs
    obtain ⟨hsT, -, hne⟩ := (hface s).1 hs
    have hle := Finset.card_le_card hsT
    by_contra hlt
    exact hne (Finset.eq_of_subset_of_card_le hsT (by omega))
  have hcell : ∀ z ∈ T, ∀ w : Finset Ea, w ⊆ T → w.card = 3 → z ∉ w →
      insert z w ∈ wallSystemCells (simplexBoundary T hT) := by
    intro z hzT w hwT hw3 hzw
    have hins : (insert z w).card = 4 := by
      rw [Finset.card_insert_of_notMem hzw, hw3]
    refine ⟨(hface _).2 ⟨Finset.insert_subset hzT hwT, Finset.insert_nonempty z w, ?_⟩, hins⟩
    intro hEq
    rw [hEq, hcard] at hins
    omega
  refine ⟨simplexBoundary_faces_finite T hT, hcardle, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsT, hsne, -⟩ := (hface s).1 hs
    obtain ⟨c, hsc, hcT, hc4⟩ :=
      Finset.exists_subsuperset_card_eq hsT (hcardle s hs) (by omega)
    refine ⟨c, ⟨(hface c).2 ⟨hcT, Finset.card_pos.mp (by omega), ?_⟩, hc4⟩, hsc⟩
    intro hEq
    rw [hEq, hcard] at hc4
    omega
  · obtain ⟨w, hwT, hw3⟩ := Finset.exists_subset_card_eq (s := T) (n := 3) (by omega)
    refine ⟨w, (hface w).2 ⟨hwT, Finset.card_pos.mp (by omega), ?_⟩, hw3⟩
    intro hEq
    rw [hEq, hcard] at hw3
    omega
  · rintro w ⟨hwf, hw3⟩
    obtain ⟨hwT, -, -⟩ := (hface w).1 hwf
    have hsd : (T \ w).card = 2 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwT, hcard, hw3]
    obtain ⟨u, v, huv, huvT⟩ := Finset.card_eq_two.mp hsd
    have huTw : u ∈ T \ w := by rw [huvT]; exact Finset.mem_insert_self u {v}
    have hvTw : v ∈ T \ w := by
      rw [huvT]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    refine ⟨insert u w, hcell u (Finset.mem_sdiff.mp huTw).1 w hwT hw3
        (Finset.mem_sdiff.mp huTw).2, insert v w,
      hcell v (Finset.mem_sdiff.mp hvTw).1 w hwT hw3 (Finset.mem_sdiff.mp hvTw).2, ?_,
      Finset.subset_insert u w, Finset.subset_insert v w, ?_⟩
    · intro hEq
      have hv : v ∈ insert u w := by rw [hEq]; exact Finset.mem_insert_self v w
      rcases Finset.mem_insert.mp hv with h1 | h1
      · exact huv h1.symm
      · exact (Finset.mem_sdiff.mp hvTw).2 h1
    · rintro c ⟨hcf, hc4⟩ hwc
      obtain ⟨hcT, -, -⟩ := (hface c).1 hcf
      have hcw : (c \ w).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwc, hc4, hw3]
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcw
      have hzc : z ∈ c \ w := by rw [hz]; exact Finset.mem_singleton_self z
      have hzmem : z ∈ T \ w :=
        Finset.mem_sdiff.mpr ⟨hcT (Finset.mem_sdiff.mp hzc).1, (Finset.mem_sdiff.mp hzc).2⟩
      have hcz : c = insert z w := by
        have h1 : w ∪ c \ w = c := Finset.union_sdiff_of_subset hwc
        rw [hz] at h1
        rw [← h1]
        ext a
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        tauto
      rw [huvT] at hzmem
      rcases Finset.mem_insert.mp hzmem with rfl | hzv
      · exact Or.inl hcz
      · rw [Finset.mem_singleton.mp hzv] at hcz
        exact Or.inr hcz

theorem exists_wallIncidence_of_fourSimplexBoundary :
    ∃ Q : Geometry.SimplicialComplex ℝ (Fin (3 + 2) → ℝ), Q.faces.Finite ∧
      (∀ s ∈ Q.faces, s.card ≤ 4) ∧ (∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c) ∧
      (wallSystemWalls Q).Nonempty ∧
      ∀ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q,
        cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
          ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp :=
  ⟨simplexBoundary (stdVertices 3) (stdVertices_affineIndependent 3),
    wallIncidence_simplexBoundary (stdVertices_affineIndependent 3) (card_stdVertices 3)⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eqOn_wallPlane_of_eqOn_transition
    {ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))} {Km Kp : Set M}
    {A₁ A₂ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)}
    {ψ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] ℝ}
    (h₁ : EqOn (fun z => ec' (ec.symm z)) A₁ (⇑ec '' Km))
    (h₂ : EqOn (fun z => ec' (ec.symm z)) A₂ (⇑ec '' Kp))
    (hspan : {z | ψ z = 0} ⊆
      (affineSpan ℝ (⇑ec '' (Km ∩ Kp)) : Set (EuclideanSpace ℝ (Fin 3)))) :
    EqOn A₁ A₂ {z | ψ z = 0} := by
  refine fun z hz => AffineMap.eqOn_affineSpan (fun u hu => ?_) (hspan hz)
  obtain ⟨x, hx, rfl⟩ := hu
  rw [← h₁ ⟨x, hx.1, rfl⟩, ← h₂ ⟨x, hx.2, rfl⟩]

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem WallProductBlock.toIsStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η := h.1

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem WallProductBlock.mono_margin {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η η' : ℝ}
    (h : WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hη' : 0 < η') (hle : η' ≤ η) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r tlo SA SB a b La Lb η' :=
  ⟨h.1.mono_margin hη' hle, h.2.1, h.2.2⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_interior {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {c : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x))
    (hc : c ∈ wallSystemCells Q)
    (hcell : chartBlock ec A r (-r) ⊆ wallSystemCellInt ρ c) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets hr hcpt hsrc hBd hpre hdisj hA hB hplA hplB hnA hnB,
    Set.disjoint_of_subset_left hcell (disjoint_wallSystemCellInt_wallSystemSkeleton hc),
    Or.inl ⟨c, hc, rfl, hcell⟩⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_wall {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {w cm cp : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r (-r))))
    (hsrc : closure (chartBlock ec A r (-r)) ⊆ ec.source)
    (hBd : Disjoint (chartBlock ec A r (-r)) BdM)
    (hpre : S ∩ f ⁻¹' chartBlock ec A r (-r) = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r (-r) → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r (-r) → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane (-r)] (blockSheetProjB ec A f x))
    (hskel : Disjoint (chartBlock ec A r (-r)) (wallSystemSkeleton Q ρ))
    (hw : w ∈ wallSystemWalls Q) (hcm : cm ∈ wallSystemCells Q)
    (hcp : cp ∈ wallSystemCells Q) (hne : cm ≠ cp) (hwm : w ⊆ cm) (hwp : w ⊆ cp)
    (hcov : chartBlock ec A r (-r) ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp)
    (hmne : (chartBlock ec A r (-r) ∩ wallSystemCellInt ρ cm).Nonempty)
    (hpne : (chartBlock ec A r (-r) ∩ wallSystemCellInt ρ cp).Nonempty)
    (hone : ∀ w' ∈ wallSystemWalls Q,
      chartBlock ec A r (-r) ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w)
    (hzero : ∀ x ∈ chartBlock ec A r (-r), x ∈ wallSystemCell ρ w ↔ (A (ec x)).2.2 = 0)
    (hsm : ∀ x ∈ chartBlock ec A r (-r) ∩ wallSystemCell ρ cm, (A (ec x)).2.2 ≤ 0)
    (hsp : ∀ x ∈ chartBlock ec A r (-r) ∩ wallSystemCell ρ cp, 0 ≤ (A (ec x)).2.2) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r (-r) SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets hr hcpt hsrc hBd hpre hdisj hA hB hplA hplB hnA hnB,
    hskel, Or.inr (Or.inl ⟨w, hw, cm, hcm, cp, hcp, rfl, hne, hwm, hwp, hcov, hmne, hpne,
      hone, hzero, hsm, hsp⟩)⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem wallProductBlock_of_flatSheets_physicalBoundary {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {c w : Finset Ea} (hr : 0 < r)
    (hcpt : IsCompact (closure (chartBlock ec A r 0)))
    (hsrc : closure (chartBlock ec A r 0) ⊆ ec.source)
    (hheight : ∀ z, (A z).2.2 = ℓ z)
    (hfront : ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))
    (hpre : S ∩ f ⁻¹' chartBlock ec A r 0 = SA ∪ SB) (hdisj : Disjoint SA SB)
    (hA : ∀ x ∈ SA, (A (ec (f x))).1 = 0) (hB : ∀ x ∈ SB, (A (ec (f x))).2.1 = 0)
    (hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA))
    (hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB))
    (hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r 0 → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane 0] (blockSheetProjA ec A f x))
    (hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r 0 → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane 0] (blockSheetProjB ec A f x))
    (hskel : Disjoint (chartBlock ec A r 0) (wallSystemSkeleton Q ρ))
    (hc : c ∈ wallSystemCells Q) (hw : w ∈ wallSystemWalls Q) (hwc : w ⊆ c)
    (hcovC : chartBlock ec A r 0 ∩ C ⊆ wallSystemCell ρ c)
    (hcne : (chartBlock ec A r 0 ∩ wallSystemCellInt ρ c).Nonempty)
    (hcovB : chartBlock ec A r 0 ∩ BdM ⊆ wallSystemCell ρ w)
    (hone : ∀ w' ∈ wallSystemWalls Q,
      chartBlock ec A r 0 ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w) :
    WallProductBlock f S ec ℓ BdM C Q ρ A r 0 SA SB (fun _ => 0) (fun _ => 0) 0 0 1 :=
  ⟨isStableCrossingBlock_of_flatSheets_boundary hr hcpt hsrc hheight hfront hpre hdisj
      hA hB hplA hplB hnA hnB,
    hskel, Or.inr (Or.inr ⟨c, hc, w, hw, rfl, hwc, hheight, hcovC, hcne, hcovB, hone⟩)⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasWallProductBlocks_empty {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ} (hη : 0 < η) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ ∅ η := by
  refine ⟨hη, ∅, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0,
    Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, isOpen_empty, Subset.rfl, ?_,
    fun i => i.elim0, fun i => i.elim0⟩
  rw [inter_empty]
  exact empty_subset _

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem hasWallProductBlocks_of_wallProductBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C N Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ} {i₀ : ι}
    (h : WallProductBlock f S (ec i₀) (ℓ i₀) BdM C Q ρ A r tlo SA SB a b La Lb η)
    (hN : IsOpen N) (hZN : Z ⊆ N)
    (hcov : doublePointSet f S ∩ N ⊆ innerChartBlock (ec i₀) A r tlo)
    (hE : chartBlock (ec i₀) A r tlo ⊆ Eb i₀) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η := by
  refine ⟨h.1.margin_pos, N, 1, fun _ => i₀, fun _ => A, fun _ => r, fun _ => tlo,
    fun _ => SA, fun _ => SB, fun _ => a, fun _ => b, fun _ => La, fun _ => Lb, hN, hZN,
    ?_, fun _ => hE, fun _ => h⟩
  exact hcov.trans (subset_iUnion (fun _ : Fin 1 => innerChartBlock (ec i₀) A r tlo) 0)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasWallProductBlocks.mono {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Z Z' : Set M} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) (hZ : Z' ⊆ Z) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z' η := by
  obtain ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZN, hcov, hE, hblk⟩ := h
  exact ⟨hη, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZ.trans hZN, hcov, hE, hblk⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem HasWallProductBlocks.union {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {Z₁ Z₂ : Set M} {η₁ η₂ : ℝ}
    (h₁ : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z₁ η₁)
    (h₂ : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z₂ η₂) :
    HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ (Z₁ ∪ Z₂) (min η₁ η₂) := by
  obtain ⟨hη₁, N₁, m₁, j₁, A₁, r₁, t₁, SA₁, SB₁, a₁, b₁, La₁, Lb₁, hN₁, hQ₁, hc₁, hE₁,
    hb₁⟩ := h₁
  obtain ⟨hη₂, N₂, m₂, j₂, A₂, r₂, t₂, SA₂, SB₂, a₂, b₂, La₂, Lb₂, hN₂, hQ₂, hc₂, hE₂,
    hb₂⟩ := h₂
  refine ⟨lt_min hη₁ hη₂, N₁ ∪ N₂, m₁ + m₂, Fin.addCases j₁ j₂, Fin.addCases A₁ A₂,
    Fin.addCases r₁ r₂, Fin.addCases t₁ t₂, Fin.addCases SA₁ SA₂, Fin.addCases SB₁ SB₂,
    Fin.addCases a₁ a₂, Fin.addCases b₁ b₂, Fin.addCases La₁ La₂, Fin.addCases Lb₁ Lb₂,
    hN₁.union hN₂, union_subset_union hQ₁ hQ₂, ?_, ?_, ?_⟩
  · rintro y ⟨hy, hNy | hNy⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hc₁ ⟨hy, hNy⟩)
      refine mem_iUnion.2 ⟨Fin.castAdd m₂ i, ?_⟩
      simpa only [Fin.addCases_left] using hi
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hc₂ ⟨hy, hNy⟩)
      refine mem_iUnion.2 ⟨Fin.natAdd m₁ i, ?_⟩
      simpa only [Fin.addCases_right] using hi
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using hE₁ i
    · simpa only [Fin.addCases_right] using hE₂ i
  · refine Fin.addCases (fun i => ?_) fun i => ?_
    · simpa only [Fin.addCases_left] using
        (hb₁ i).mono_margin (lt_min hη₁ hη₂) (min_le_left _ _)
    · simpa only [Fin.addCases_right] using
        (hb₂ i).mono_margin (lt_min hη₁ hη₂) (min_le_right _ _)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_isStableCrossingBlock_of_hasWallProductBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Z) :
    ∃ (i : ι) (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
      (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb : ℝ),
      IsStableCrossingBlock f S (ec i) (ℓ i) BdM A r tlo SA SB a b La Lb η ∧
        y ∈ innerChartBlock (ec i) A r tlo := by
  obtain ⟨-, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, -, hZN, hcov, -, hblk⟩ := h
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov ⟨hy.1, hZN hy.2⟩)
  exact ⟨j i, A i, r i, tlo i, SA i, SB i, a i, b i, La i, Lb i, (hblk i).1, hi⟩

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem exists_sheets_of_hasWallProductBlocks {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M} {BdM C Z : Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (h : HasWallProductBlocks f S ec ℓ Eb BdM C Q ρ Z η) {y : M}
    (hy : y ∈ doublePointSet f S ∩ Z) :
    ∃ SA' SB' : Set (EuclideanSpace ℝ (Fin 2)),
      Disjoint SA' SB' ∧ (SA' ∩ f ⁻¹' {y}).Nonempty ∧ (SB' ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨i, A, r, tlo, SA, SB, a, b, La, Lb, hblk, hi⟩ :=
    exists_isStableCrossingBlock_of_hasWallProductBlocks h hy
  obtain ⟨hr0, -, -, -, -, -, -, hside, -, hdisj, -, -, -, -, -, -, -, -, -, -⟩ := id hblk
  have ht : tlo ≤ 0 := by
    rcases hside with ⟨h1, -⟩ | ⟨h1, -, -⟩
    · rw [h1]; linarith
    · exact le_of_eq h1
  obtain ⟨hA, hB⟩ := sheets_nonempty_of_isStableCrossingBlock hblk hy.1
    (chartBlock_mono_of_half (ec i) A (le_of_lt hr0) ht hi)
  exact ⟨SA, SB, hdisj, hA, hB⟩

theorem exists_normalCrossing_of_hasWallProductBlocks [T2Space M] (D : SingularTwoCell M)
    {BdM C Z : Set M} {ι : Type}
    {ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)} {Eb : ι → Set M}
    {Q : Geometry.SimplicialComplex ℝ Ea} {ρ : M → Ea} {η : ℝ}
    (hec : ∀ i, ec i ∈ (plGroupoid 3).maximalAtlas M) (hℓ : ∀ i, ℓ i ≠ 0)
    (hBdchart : ∀ i, ∀ x ∈ (ec i).source, x ∈ BdM ↔ ℓ i (ec i x) = 0)
    (h : HasWallProductBlocks (⇑D) D.domain ec ℓ Eb BdM C Q ρ Z η) :
    ∃ O : Set M, IsOpen O ∧ Z ⊆ O ∧
      ∀ y ∈ doublePointSet (⇑D) D.domain ∩ O,
        ∃ e ∈ atlas (EuclideanSpace ℝ (Fin 3)) M, y ∈ e.source ∧
          HasPLNormalDoubleCrossingAt (⇑e ∘ ⇑D) (D.domain ∩ ⇑D ⁻¹' e.source)
            (⇑e '' (e.source ∩ BdM)) (e y) := by
  obtain ⟨-, N, m, j, A, r, tlo, SA, SB, a, b, La, Lb, hN, hZN, hcov, -, hblk⟩ := h
  refine ⟨N, hN, hZN, fun y hy => ?_⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hy)
  exact hasPLNormalDoubleCrossingAt_of_isStableCrossingBlock D (ec (j i)) (ℓ (j i))
    (hec (j i)) (hℓ (j i)) (hBdchart (j i)) (hblk i).1 hy.1 hi

end Ambient

section MetricAmbient

variable {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

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
  · simp only [regionGluedMap, ite_eq_left hx]
    exact hglue hx
  · simp only [regionGluedMap, ite_eq_right hx]
    exact hglueoff hx

open Classical in
theorem freeSourceGerm_of_mem_closure (D : SingularTwoCell M) {W V : Set M} {ε : ℝ}
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (Rc Ac Rs : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
    {Ω Nb : Set (EuclideanSpace ℝ (Fin 2))}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hsub : IsSubdivision Rs Rc) (hVec : V ⊆ ec.source) (hΩ : IsOpen Ω)
    (hΩcover : D.domain ∩ ⇑D ⁻¹' closure W ⊆ Ω) (hΩR : D.domain ∩ Ω ⊆ Rc.space)
    (hNbfr : Rc.space \ Ω ⊆ Nb) (hNbA : Rc.space ∩ Nb ⊆ Ac.space)
    (hsmall : ∀ x ∈ Rc.space, dist (simplicialMap Rs φ x) (ec (D x)) < ε)
    (hactive : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
      dist z (ec (D x)) < ε → ec.symm z ∈ closure W → x ∈ Rc.space \ Ac.space)
    (hsep : ∀ σ ∈ Rs.faces, (∃ v ∈ σ, v ∈ Ac.space) →
      Disjoint (simplicialMap Rs φ '' convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 2))))
        (⇑ec '' closure W))
    (hmaps : MapsTo (simplicialMap Rs φ) Rc.space (⇑ec '' V))
    {y : M} (hy : y ∈ closure W) :
    FreeSourceGerm Rs Ac (regionGluedMap D ec Rs φ Rc) D.domain y := by
  classical
  intro x hx
  have hxdom : x ∈ D.domain := hx.1
  have hxy : regionGluedMap D ec Rs φ Rc x = y := hx.2
  have hxR : x ∈ Rc.space := by
    by_contra hxR
    have hDx : D x = y := by
      rw [← hxy]
      simp only [regionGluedMap, ite_eq_right hxR]
    exact hxR (hΩR ⟨hxdom, hΩcover ⟨hxdom, by simp only [mem_preimage, hDx]; exact hy⟩⟩)
  have hgx : ec.symm (simplicialMap Rs φ x) = y := by
    rw [← hxy]
    simp only [regionGluedMap, ite_eq_left hxR]
  have hxA : x ∈ Rc.space \ Ac.space :=
    hactive x hxR _ (hsmall x hxR) (by rw [hgx]; exact hy)
  have hxΩ : x ∈ Ω := by
    by_contra hxo
    exact hxA.2 (hNbA ⟨hxR, hNbfr ⟨hxR, hxo⟩⟩)
  refine ⟨?_, ?_⟩
  · rw [hsub.space_eq]
    exact mem_nhdsWithin.2 ⟨Ω, hΩ, hxΩ, fun z hz => hΩR ⟨hz.2, hz.1⟩⟩
  · intro σ hσ hxσ v hv hvA
    obtain ⟨w, hwV, hw⟩ := hmaps hxR
    have hecy : ec y = simplicialMap Rs φ x := by
      rw [← hgx, ← hw, ec.left_inv (hVec hwV)]
    exact Set.disjoint_left.mp (hsep σ hσ ⟨v, hv, hvA⟩) ⟨x, hxσ, rfl⟩ ⟨y, hy, hecy⟩

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
  obtain ⟨Qc, Cf, Bf, Eb, Eb', hQsub, hVEint, hsys⟩ :=
    exists_commonWallComplex K S.isManifold n (fun i : Fin n => V i.1)
      (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt)
      (fun i : Fin n => hecf i.1 i.isLt) (fun i : Fin n => hℓf i.1 i.isLt)
      (fun i : Fin n => hCf i.1 i.isLt) (fun i : Fin n => hBdf i.1 i.isLt)
      (fun i : Fin n => hVclf i.1 i.isLt)
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
  have key : ∀ k : ℕ, ∃ (cl : SingularTwoCell (double 3 K).space)
      (bdry : ContinuousMap loopCircle (frontier cl.domain))
      (gl : freeLoop S.boundaryNeighborhoodSpace) (ηk : ℝ),
      cl.domain = G.domain ∧ MapsTo (⇑cl) cl.domain C ∧
        (∀ x ∈ cl.domain, ∃ U ∈ 𝓝[cl.domain] x, InjOn (⇑cl) U) ∧
        (∀ y, (cl.domain ∩ ⇑cl ⁻¹' {y}).encard ≤ 2) ∧
        cl.domain ∩ ⇑cl ⁻¹' Bd = frontier cl.domain ∧
        (∀ z ∈ Set.range cl.boundary, B ∈ 𝓝[Bd] z) ∧
        doublePointSet (⇑cl) cl.domain ⊆ ⋃ j, W j ∧ 0 < ηk ∧
        HasWallProductBlocks (⇑cl) cl.domain (fun i : Fin n => ecf i.1 i.isLt)
          (fun i : Fin n => ℓf i.1 i.isLt) Eb Bd C Qc
          ((↑) : (double 3 K).space → E × E × ℝ)
          (⋃ j, ⋃ (_ : j < k), closure (W j)) ηk ∧
        Function.Surjective bdry ∧
        (∀ θ, ((cl (bdry θ) : (double 3 K).space) : E × E × ℝ) = ι (gl θ)) ∧
        ¬loopClassMeets gl S.basepoint S.normalSubgroup := by
    intro k
    induction k with
    | zero =>
        refine ⟨G, β, γ, 1, rfl, hmapC, hloc, hfiber, hproper, hbuffer, hdpG, one_pos, ?_,
          hsurj, hparam, havoid⟩
        refine HasWallProductBlocks.mono (hasWallProductBlocks_empty one_pos) ?_
        exact iUnion_subset fun j => iUnion_subset fun hj => absurd hj (Nat.not_lt_zero j)
    | succ k ih =>
        obtain ⟨cl, bdry, gl, ηk, hdom, hclC, hclloc, hclfib, hclpr, hclbuf, hcldp, hηk,
          hwp, hbsurj, hbparam, hbavoid⟩ := ih
        have hZsucc : (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) ⊆
            (⋃ j, ⋃ (_ : j < k), closure (W j)) ∪ closure (W k) := by
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
          · exact fun x hx => mem_union_left _ (mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hlt, hx⟩⟩)
          · subst heq
            exact fun x hx => mem_union_right _ hx
        by_cases hk : k < n
        · have hZclosed : IsClosed (⋃ j, ⋃ (_ : j < k), closure (W j)) :=
            Set.Finite.isClosed_biUnion (Set.finite_lt_nat k) fun j _ => isClosed_closure
          have hVcl : closure (V k) ⊆ (ecf k hk).source := hVclf k hk
          have hVec : V k ⊆ (ecf k hk).source := subset_closure.trans hVcl
          obtain ⟨Rc, Lc, Ac, Ω, Nb, hRfin, hRman, hLR, hAR, hRdom, hRV, hLspace, hΩ,
            hΩcover, hΩR, hNb, hNbfr, hNbA, hAfree⟩ :=
            cl.exists_cutOutPiece_of_closure_subset (V₀ := W k) (hVopen k) (hWV k)
          obtain ⟨Ok, hOkopen, hOkZ, hOkcross⟩ :=
            exists_normalCrossing_of_hasWallProductBlocks cl
              (fun i : Fin n => hecf i.1 i.isLt) (fun i : Fin n => hℓf i.1 i.isLt)
              (fun i : Fin n => hBdf i.1 i.isLt) hwp
          obtain ⟨T, κ, δ, ε, hκ, hδ, hε, hTfin, hTspace, hTstar, hcert, hconv, hactive,
            hbdbuf⟩ :=
            exists_normalizationPreparation_on_prescribedRegion cl hclloc hclfib hclbuf
              (hVopen k) (hWV k) (ecf k hk) hVec Rc Ac hRfin hAR hRdom hRV hAfree
          have hchartbuf : ∀ x ∈ Rc.space, ∀ z : EuclideanSpace ℝ (Fin 3),
              dist z (ecf k hk (cl x)) < ε → z ∈ ⇑(ecf k hk) '' V k :=
            fun x hx z hz => (hconv x hx z hz).1
          have hinjD : UniformInjectivityScale cl.domain (⇑cl) κ :=
            (hcert (⇑cl) (fun x _ => by rw [dist_self]; exact hδ) hTstar).1
          have hstk : HasStableCrossingBlocks (⇑cl) cl.domain (ecf k hk) (ℓf k hk) Bd
              ((⋃ j, ⋃ (_ : j < k), closure (W j)) ∩ closure (V k \ closure (W k))) ηk :=
            hasStableCrossingBlocks_of_wallProductBlocks hsys hwp
              cl.isPLBall_domain.isPolyhedron.isCompact cl.continuousOn hclC hκ hinjD
              ⟨k, hk⟩ ((hZclosed.inter isClosed_closure).isCompact) inter_subset_left
              fun x hx => hVEint ⟨k, hk⟩ (closure_mono Set.sdiff_subset hx.2)
          obtain ⟨R, τ₀, Kt, hτ₀, hsub, hRsfin, hlinear, hKcpt, hKV, hDKint, hcontrol⟩ :=
            exists_protectedSubdivision_in_adaptedChart cl hclloc hclfib hclpr hclC
              hOkcross hZclosed hOkopen hOkZ (ecf k hk) (ℓf k hk) (hecf k hk) (hℓf k hk)
              (hVopen k) hVcl (hCf k hk) (hBdf k hk) Rc Lc Ac hRfin hRman hLR hAR hRdom
              hRV hLspace hΩ hΩR hNb hNbfr hNbA (hWV k) hAfree hstk T hTfin hTspace hTstar
              hκ hδ hε hcert hconv
          obtain ⟨τ, hτ, hτle, hstab⟩ :=
            wallProductBlocks_stable_on_fixedSubdivision cl
              (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb'
              ⟨k, hk⟩ hsys hclloc hclfib hclpr hclC hZclosed (hVopen k) hVcl
              (hWV k) (hVEint ⟨k, hk⟩) Rc Lc Ac R T hRfin hRdom hRV hLspace hΩ hΩcover
              hΩR hNb hNbfr hNbA hsub hRsfin hκ hδ hε hτ₀ hlinear hcert hconv hactive
              hKcpt hKV hDKint hwp
          obtain ⟨Bv, φ, hadm, hguard, hgenskel, hgenfold, hgencross⟩ :=
            exists_wallGenericVertexMap cl (fun i : Fin n => ecf i.1 i.isLt)
              (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb' ⟨k, hk⟩ hsys hclpr hclC hVec
              (hVEint ⟨k, hk⟩) Rc Lc Ac hLR hAR hRdom hRV hLspace R hsub hRsfin hlinear hτ
          obtain ⟨hpl, hsmall, hfrozen, hpnonneg, hpzero, hsep, hmaps, hgK, hstarG, -, -⟩ :=
            hcontrol Bv φ (hadm.mono hτle)
          obtain ⟨cl', hdom', hglue, hglueoff⟩ :=
            exists_gluedCell_of_vertexMap_in_adaptedChart cl (hVopen k) (ecf k hk)
              (hecf k hk) hVec Rc Ac hRfin hRman hAR hRdom hRV hΩ hΩR hNb hNbfr hNbA R φ
              hsub hRsfin hfrozen hpl hmaps
          have hbridge : ⇑cl' = regionGluedMap cl (ecf k hk) R φ Rc :=
            eq_regionGluedMap_of_eqOn hglue hglueoff
          have hclose : ∀ x ∈ cl.domain, dist (cl' x) (cl x) < δ := by
            intro x _
            by_cases hxR : x ∈ Rc.space
            · rw [hglue hxR]
              exact (hconv x hxR _ (hsmall x hxR)).2
            · rw [hglueoff hxR, dist_self]
              exact hδ
          have hstarcl : StarInj T (⇑cl') := by
            rw [hbridge]
            exact hstarG
          have hinjD' : UniformInjectivityScale cl.domain (⇑cl') κ :=
            (hcert (⇑cl') hclose hstarcl).1
          have hinjG : UniformInjectivityScale cl.domain
              (regionGluedMap cl (ecf k hk) R φ Rc) κ := by
            rw [← hbridge]
            exact hinjD'
          obtain ⟨hC', hfibV, hloc', hcard', hpr', H, hH0, hH1, hHtrack⟩ :=
            exists_globalInvariants_of_gluedCell cl cl' hclpr hclC hclbuf hκ hcert hclose
              hstarcl (ecf k hk) (ℓf k hk) (hVopen k) hVec (hCf k hk) (hBdf k hk) Rc Lc Ac
              hRfin hRman hRdom hRV hLspace hΩ hΩR hNb hNbfr hNbA R φ hsub hsmall hfrozen
              hpnonneg hpzero hchartbuf hbdbuf hdom' hglue hglueoff
          have hgcont : ContinuousOn (regionGluedMap cl (ecf k hk) R φ Rc) cl.domain := by
            rw [← hbridge, ← hdom']
            exact cl'.continuousOn
          have hgfiber : ∀ y, (cl.domain ∩
              regionGluedMap cl (ecf k hk) R φ Rc ⁻¹' {y}).encard ≤ 2 := by
            intro y
            rw [← hbridge, ← hdom']
            exact hcard' y
          have hwpZ := hstab Bv φ hadm hpl hsmall hfrozen hsep hmaps hgK hstarG
          have hfree : ∀ y ∈ closure (W k),
              FreeSourceGerm R Ac (regionGluedMap cl (ecf k hk) R φ Rc) cl.domain y :=
            fun y hy => freeSourceGerm_of_mem_closure cl (ecf k hk) Rc Ac R hsub hVec hΩ
              hΩcover hΩR hNbfr hNbA hsmall hactive hsep hmaps hy
          obtain ⟨ηw, hηw, hwpW⟩ :=
            wallProductBlocks_of_wallGenericity cl (fun i : Fin n => ecf i.1 i.isLt)
              (fun i : Fin n => ℓf i.1 i.isLt) Eb Eb' ⟨k, hk⟩ hsys hclfib hclpr
              hclC hκ (hVopen k) hVcl (hWV k)
              ((hWV k).trans (subset_closure.trans (hVEint ⟨k, hk⟩))) Rc Lc Ac R Bv φ
              hRfin hRdom hRV hLspace hsub hRsfin hε hadm.2.1 hsmall hpnonneg hpzero
              hfrozen hmaps hgK hKV hinjG hgcont hgfiber hguard hfree hgenskel hgenfold
              hgencross
          have hwpNext : HasWallProductBlocks (⇑cl') cl'.domain
              (fun i : Fin n => ecf i.1 i.isLt) (fun i : Fin n => ℓf i.1 i.isLt)
              Eb Bd C Qc ((↑) : (double 3 K).space → E × E × ℝ)
              (⋃ j, ⋃ (_ : j < k + 1), closure (W j)) (min (ηk / 2) ηw) := by
            rw [hdom', hbridge]
            exact (hwpZ.union hwpW).mono hZsucc
          have hbuf' : ∀ z ∈ Set.range cl'.boundary, B ∈ 𝓝[Bd] z := by
            rintro _ ⟨x, rfl⟩
            have hx : (x : EuclideanSpace ℝ (Fin 2)) ∈ frontier cl.domain := by
              rw [← hdom']
              exact x.2
            have h1 := hHtrack 1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩
            rw [hH1 ⟨(x : EuclideanSpace ℝ (Fin 2)), hx⟩] at h1
            exact h1.2
          have hdpnew : doublePointSet (⇑cl') cl'.domain ⊆ ⋃ j, W j := by
            rw [hdom']
            exact doublePointSet_subset_of_preimage_singleton_eq_off cl.domain hfibV hcldp
              (hVW k)
          have hHB : ∀ (t : unitInterval) (x : frontier cl.domain), H (t, x) ∈ B :=
            fun t x => mem_of_mem_nhdsWithin (hHtrack t x).1 (hHtrack t x).2
          obtain ⟨c, δ₀, hcδ, hδavoid⟩ :=
            exists_boundary_loop_of_buffered_homotopy S K cl cl' bdry gl hdom' hC' hbparam
              hbavoid hbsurj H hH0 hH1 hHB hBspace
          exact ⟨cl', ⟨c, c.continuous⟩, δ₀, min (ηk / 2) ηw, hdom'.trans hdom, hC', hloc',
            hcard', hpr', hbuf', hdpnew, lt_min (by linarith) hηw, hwpNext, c.surjective,
            hcδ, hδavoid⟩
        · refine ⟨cl, bdry, gl, ηk, hdom, hclC, hclloc, hclfib, hclpr, hclbuf, hcldp, hηk,
            hwp.mono ?_, hbsurj, hbparam, hbavoid⟩
          refine iUnion_subset fun j => iUnion_subset fun hj => ?_
          by_cases hjk : j < k
          · exact fun x hx => mem_iUnion.2 ⟨j, mem_iUnion.2 ⟨hjk, hx⟩⟩
          · rw [hWn j (by omega), closure_empty]
            exact empty_subset _
  obtain ⟨A, bdry, gl, ηn, hdom, hAC, hAloc, hAfib, hApr, hAbuf, hAdp, -, hAwp, hbsurj,
    hbparam, hbavoid⟩ := key n
  obtain ⟨On, -, hOnZ, hAcross⟩ :=
    exists_normalCrossing_of_hasWallProductBlocks A (fun i : Fin n => hecf i.1 i.isLt)
      (fun i : Fin n => hℓf i.1 i.isLt) (fun i : Fin n => hBdf i.1 i.isLt) hAwp
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
    exists_boundary_loop_of_buffered_homotopy S K A A bdry gl rfl hAC hbparam hbavoid
      hbsurj ⟨fun z => A.boundary z.2, A.boundary.continuous.comp continuous_snd⟩
      (fun _ => rfl) (fun _ => rfl) (fun _ x => hAbd (mem_range_self x)) hBspace
  exact ⟨A, hA, hdom, hAC, hAbuf, c, δ₁, hcδ, hδavoid⟩

end DifferentialGeometry.Topology.PiecewiseLinear
