import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnPolyhedralBall
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifoldTopology
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarManifold
import DifferentialGeometry.Topology.PiecewiseLinear.SupportedPLPrismShift
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteOpenEnlargements

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem subset_interior_symm_image_of_bicollar_shift {X : Type*} [TopologicalSpace X]
    {C W : Set X} {ρ : X × ℝ → X} {β : ℝ → ℝ} (f : X ≃ₜ X)
    (hW : frontier C ⊆ W) (hbij : BijOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) W)
    (hnegative : ρ '' (frontier C ×ˢ Ico (-1 : ℝ) 0) ⊆ Cᶜ)
    (hpositive : ρ '' (frontier C ×ˢ Ioc (0 : ℝ) 1) ⊆ interior C)
    (hβ : StrictMono β) (hβzero : 0 < β 0)
    (hβmap : MapsTo β (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1))
    (hmove : ∀ x ∈ frontier C, ∀ t ∈ Icc (-1 : ℝ) 1, f (ρ (x, t)) = ρ (x, β t))
    (hfix : EqOn f id Wᶜ) : C ⊆ interior (f.symm '' C) := by
  have himage : f.symm '' interior C ⊆ interior (f.symm '' C) :=
    interior_maximal (image_mono interior_subset) (f.symm.isOpenMap _ isOpen_interior)
  intro y hy
  apply himage
  refine ⟨f y, ?_, f.symm_apply_apply y⟩
  by_cases hyW : y ∈ W
  · obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hbij.surjOn hyW
    have ht0 : 0 ≤ t := le_of_not_gt fun h =>
      hnegative ⟨(x, t), ⟨hx, ht.1, h⟩, rfl⟩ hy
    rw [hmove x hx t ht]
    exact hpositive ⟨(x, β t), ⟨hx, hβzero.trans_le (hβ.monotone ht0),
      (hβmap ht).2⟩, rfl⟩
  · rw [hfix hyW]
    by_contra hyI
    exact hyW (hW ⟨subset_closure hy, hyI⟩)

theorem IsPLCellOn.exists_enlargement {M : Type*} [TopologicalSpace M]
    [TopologicalSpace.MetrizableSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C B O : Set M} (hC : IsPLCellOn 3 C B) (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ D : Set M, IsPLCellOn 3 D (frontier D) ∧ C ⊆ interior D ∧ D ⊆ O := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  have hball := hC.isPolyhedralBall
  have hregular := hball.closure_interior
  have hclosed := hC.isCompact.isClosed
  have hS : IsPolyhedralSphere (n := 3) 2 (frontier C) :=
    hC.boundary_eq_frontier ▸ hC.isPolyhedralSphere_boundary
  have hconn : IsConnected (frontier C) := by
    obtain ⟨T, hT⟩ := hS
    rw [← T.piece.bijOn.image_eq]
    exact hT.isConnected.image T.piece.map T.piece.continuousOn
  obtain ⟨T, W, R, η, hWO, hW, hRP, hη, hηzero⟩ :=
    hS.isPolyhedralManifold.exists_bicollar
      hball.isPolyhedralManifoldWithBoundary.isTwoSided_frontier
      (hO.mem_nhdsSet.mpr (hclosed.frontier_subset.trans hCO))
  let q := Function.invFunOn T.piece.map T.piece.complex.space
  have hq : BijOn q (frontier C) T.piece.complex.space :=
    T.piece.bijOn.invOn_invFunOn.symm.bijOn T.piece.bijOn.surjOn.mapsTo_invFunOn
      T.piece.bijOn.mapsTo
  have hqeq (x : frontier C) : q x = (T.piece.homeomorph.symm x : _) := by
    apply T.piece.bijOn.injOn (hq.mapsTo x.2) (T.piece.homeomorph.symm x).2
    exact (T.piece.bijOn.invOn_invFunOn.2 x.2).trans
      (congrArg Subtype.val (T.piece.homeomorph.apply_symm_apply x)).symm
  have hqcont : ContinuousOn q (frontier C) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_subtype_val.comp T.piece.homeomorph.symm.continuous).congr
      fun x => (hqeq x).symm
  let ρ : M × ℝ → M := fun z => R.map (q z.1, z.2)
  have hρ : ContinuousOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) := by
    apply R.continuousOn.comp (hqcont.prodMap continuousOn_id)
    intro z hz
    exact hRP.symm.subset ⟨hq.mapsTo hz.1, hz.2⟩
  have hρbij : BijOn ρ (frontier C ×ˢ Icc (-1 : ℝ) 1) W := by
    have hprod := hq.prodMap (bijOn_id (Icc (-1 : ℝ) 1))
    rw [← hRP] at hprod
    exact R.bijOn.comp hprod
  have hzero : ∀ x ∈ frontier C, ρ (x, 0) = x := by
    intro x hx
    have heq := hη ⟨q x, hq.mapsTo hx⟩ ⟨0, by norm_num⟩
    have hqx := T.piece.bijOn.invOn_invFunOn.2 hx
    dsimp [ρ]
    rw [← heq, hηzero]
    exact hqx
  have hRzero : ∀ x ∈ T.piece.complex.space, R.map (x, 0) ∈ interior W := by
    intro x hx
    have heq := (hη ⟨x, hx⟩ ⟨0, by norm_num⟩).symm.trans
      (hηzero ⟨T.piece.map x, T.piece.bijOn.mapsTo hx⟩)
    rw [heq]
    exact (subset_interior_iff_mem_nhdsSet.mpr hW) (T.piece.bijOn.mapsTo hx)
  obtain ⟨φ, β, hφ, hφi, hβ, hβzero, hβbij, hmove, hfix⟩ :=
    R.exists_supported_prism_shift T.piece.isPolyhedron_space hRP hRzero
  have hmoveρ : ∀ x ∈ frontier C, ∀ t ∈ Icc (-1 : ℝ) 1,
      φ (ρ (x, t)) = ρ (x, β t) := fun x hx t ht => hmove (q x) (hq.mapsTo hx) t ht
  have hWC : frontier C ⊆ W := (subset_interior_iff_mem_nhdsSet.mpr hW).trans interior_subset
  rcases bicollar_sides_of_regular_closed hclosed hregular hconn hW hρ hρbij hzero with
    ⟨hneg, hpos⟩ | ⟨hneg, hpos⟩
  · exact ⟨φ '' C, hC.enlargement_of_bicollar_shift φ hφ hφi hCO hWO hWC hρbij
      hneg hpos hβ hβzero hβbij.surjOn hmoveρ hfix⟩
  · have hinside := subset_interior_symm_image_of_bicollar_shift φ hWC hρbij hneg hpos
      hβ hβzero hβbij.mapsTo hmoveρ hfix
    have hφu : IsPLHomeomorphInto 3 φ.symm univ := by
      refine ⟨fun x _ => hφi x, φ.symm.injective.injOn, fun y _ => ⟨φ, ?_, ?_⟩⟩
      · rw [image_univ, φ.symm.surjective.range_eq]
        exact hφ y
      · exact fun x _ => φ.apply_symm_apply x
    have hcell := hC.image (hφu.mono_of_isPLCellOn hC (subset_univ _))
    refine ⟨φ.symm '' C, hcell.boundary_eq_frontier ▸ hcell, hinside, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    by_cases hyW : φ.symm x ∈ W
    · exact hWO hyW
    · have heq : φ.symm x = x := by
        have h := hfix hyW
        simpa only [φ.apply_symm_apply, id_eq] using h.symm
      rw [heq]
      exact hCO hx

theorem exists_locallyFinite_isPLCellOn_enlargements {M ι : Type*} [TopologicalSpace M]
    [TopologicalSpace.MetrizableSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {C B O : ι → Set M} {U : Set M} (hU : IsOpen U)
    (hC : ∀ i, IsPLCellOn 3 (C i) (B i)) (hCU : ∀ i, C i ⊆ U)
    (hLF : LocallyFinite fun i => (Subtype.val : U → M) ⁻¹' C i)
    (hO : ∀ i, IsOpen (O i)) (hCO : ∀ i, C i ⊆ O i) :
    ∃ D : ι → Set M, (∀ i, IsPLCellOn 3 (D i) (frontier (D i))) ∧
      (∀ i, C i ⊆ interior (D i)) ∧ (∀ i, D i ⊆ U ∩ O i) ∧
      LocallyFinite fun i => (Subtype.val : U → M) ⁻¹' D i := by
  let : MetricSpace M := TopologicalSpace.metrizableSpaceMetric M
  obtain ⟨V, hV, hCV, hVLF⟩ := DifferentialGeometry.Topology.exists_locallyFinite_open_supersets hLF
  have hex (i : ι) : ∃ D : Set M, IsPLCellOn 3 D (frontier D) ∧
      C i ⊆ interior D ∧ D ⊆ (Subtype.val '' V i) ∩ O i := by
    apply (hC i).exists_enlargement ((hU.isOpenMap_subtype_val _ (hV i)).inter (hO i))
    intro x hx
    exact ⟨⟨⟨x, hCU i hx⟩, hCV i hx, rfl⟩, hCO i hx⟩
  choose D hD hCD hDO using hex
  refine ⟨D, hD, hCD, ?_, hVLF.subset ?_⟩
  · intro i x hx
    obtain ⟨⟨y, -, rfl⟩, hyO⟩ := hDO i hx
    exact ⟨y.2, hyO⟩
  · intro i x hx
    obtain ⟨y, hy, heq⟩ := (hDO i hx).1
    exact Subtype.val_injective heq ▸ hy

end DifferentialGeometry.Topology.PiecewiseLinear
