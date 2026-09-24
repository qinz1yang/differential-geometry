/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingComponentStability
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalCircleBicollar
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusComplement
import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # Section34Piercing Source Bicollar -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.locallyConnectedSpace {X : Type*} [TopologicalSpace X]
    {A A₀ A₁ : Set X} (hann : IsAnnulusOn A A₀ A₁) : LocallyConnectedSpace A := by
  obtain ⟨φ, -, -⟩ := hann
  let : LocallyPathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 1)) _
  let : LocallyPathConnectedSpace (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  have : LocallyPathConnectedSpace A := φ.symm.isOpenEmbedding.locallyPathConnectedSpace
  infer_instance

theorem IsPolyhedralSphere.isConnected {M : Type*} [TopologicalSpace M] {n m : ℕ}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] {S : Set M}
    (hS : IsPolyhedralSphere (n := n) (m + 1) S) : IsConnected S := by
  obtain ⟨T, hT⟩ := hS
  rw [← T.piece.bijOn.image_eq]
  exact hT.isConnected.image T.piece.map T.piece.continuousOn

theorem IsPLCellOn.exists_piercing_bicollar {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {Y Yb J B T : Set M}
    (hY : IsPLCellOn 3 Y Yb) (hJ : IsPolyhedralSphere (n := 3) 1 J) (hJY : J ⊆ Yb)
    (hB : IsCompact B) (hBY : B ⊆ Yb) (hT : IsOpen T) (hJT : J ⊆ T)
    (hTB : T ∩ Yb ⊆ B) :
    ∃ (W R : Set M) (ρ : M × ℝ → M), IsCompact W ∧ W ⊆ B ∩ T ∧ IsCompact R ∧
      R ⊆ B \ J ∧ R ∪ W = B ∧ R ∩ W = ρ '' (J ×ˢ {(-1 : ℝ), 1}) ∧
      W ∈ 𝓝ˢ[B] J ∧ ContinuousOn ρ (J ×ˢ Icc (-1 : ℝ) 1) ∧
      BijOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W ∧ ∀ x ∈ J, ρ (x, 0) = x := by
  classical
  obtain ⟨P, r, u, hr, hu, hYP, hYb⟩ := hY
  have hb : IsPLBall 3 P := ⟨r, hr⟩
  have hSP : frontier P ⊆ P := hb.isPolyhedron.isClosed.frontier_subset
  have hS : IsPLSphere 2 (frontier P) := hb.isPLSphere_frontier
  rw [IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr] at hYb
  let v := Function.invFunOn u P
  have hvu : ∀ x ∈ P, v (u x) = x := hu.injOn.leftInvOn_invFunOn
  have huv : ∀ y ∈ u '' P, u (v y) = y := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hYbP : Yb ⊆ u '' P := by rw [hYb]; exact image_mono hSP
  have hJP : J ⊆ u '' P := hJY.trans hYbP
  let L := v '' J
  have hL : IsPLSphere 1 L := hu.isPLSphere_invFunOn_image hJ hJP
  have hLS : L ⊆ frontier P := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hYb ▸ hJY hy
    rw [hvu x (hSP hx)]
    exact hx
  have huL : u '' L = J := by
    rw [show L = v '' J from rfl, image_image]
    exact (image_congr fun y hy => huv y (hJP hy)).trans (image_id' J)
  have hvS : ∀ y ∈ Yb, v y ∈ frontier P := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hYb ▸ hy
    rw [hvu x (hSP hx)]
    exact hx
  have hvcont : ContinuousOn v Yb :=
    (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn).continuousOn.mono hYbP
  have hTU : u ⁻¹' T ∈ 𝓝ˢ[frontier P] L := by
    have hpre := (hu.continuousOn.mono hSP).preimage_mem_nhdsSetWithin_of_mem_nhdsSet
      (hT.mem_nhdsSet.mpr hJT)
    apply nhdsSetWithin_mono_left (show L ⊆ frontier P ∩ u ⁻¹' J from
      fun x hx => ⟨hLS hx, huL.subset (mem_image_of_mem u hx)⟩) hpre
  obtain ⟨V, σ, hV, hVS, hVT, hVnhds, hσ, hσzero⟩ :=
    hS.exists_bicollar_of_isPLSphere_one hL hLS hTU
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  let : Finite K.faces := hKfin.to_subtype
  have hK : IsPLSphere 2 K.space := hKS.symm ▸ hS
  obtain ⟨A, C, -, hCfin, -, -, hAV, hCeq, -, -, hmeet, hcover⟩ :=
    hK.isCombinatorialManifold.exists_annulus_complement K hL (by norm_num : (-1 : ℝ) < 1)
      hσ (hVS.trans hKS.symm.subset)
  let : Finite C.faces := hCfin.to_subtype
  rw [hAV] at hmeet hcover
  rw [hKS] at hCeq hcover
  have hCS : C.space ⊆ frontier P :=
    subset_union_right.trans hcover.subset
  have hCL : Disjoint C.space L := by
    apply Set.disjoint_left.mpr
    intro x hxC hxL
    obtain ⟨O, hO, hLO, hOV⟩ := mem_nhdsSetWithin.mp hVnhds
    rw [hCeq] at hxC
    obtain ⟨y, hyO, hyS, hyV⟩ := mem_closure_iff.mp hxC O hO (hLO hxL)
    exact hyV (hOV ⟨hyO, hyS⟩)
  let W := u '' V
  let R := B ∩ u '' C.space
  let ρ : M × ℝ → M := fun z => u (σ (v z.1, z.2))
  have hWB : W ⊆ B := fun y hy => hTB ⟨by
    obtain ⟨x, hx, rfl⟩ := hy
    exact hVT hx, by rw [hYb]; exact image_mono hVS hy⟩
  have hWc : IsCompact W := hV.isCompact.image_of_continuousOn
    (hu.continuousOn.mono (hVS.trans hSP))
  have hRc : IsCompact R := hB.inter_right
    (((isPolyhedron_space C).isCompact.image_of_continuousOn
      (hu.continuousOn.mono (hCS.trans hSP))).isClosed)
  have hRN : R ⊆ B \ J := by
    rintro y ⟨hyB, x, hx, rfl⟩
    refine ⟨hyB, fun hyJ => ?_⟩
    apply Set.disjoint_left.mp hCL hx
    have hxv : v (u x) ∈ L := mem_image_of_mem v hyJ
    rwa [hvu x (hSP (hCS hx))] at hxv
  have hRW : R ∪ W = B := by
    apply Subset.antisymm (union_subset inter_subset_left hWB)
    intro y hyB
    obtain ⟨x, hxS, rfl⟩ := hYb ▸ hBY hyB
    rcases hcover.symm.subset hxS with hxV | hxC
    · exact Or.inr (mem_image_of_mem u hxV)
    · exact Or.inl ⟨hyB, mem_image_of_mem u hxC⟩
  have hvbij : BijOn v J L := ⟨fun x hx => mem_image_of_mem v hx,
    fun x hx y hy hxy => by rw [← huv x (hJP hx), ← huv y (hJP hy), hxy],
    fun x hx => hx⟩
  have hprod (I : Set ℝ) : BijOn (Prod.map v id) (J ×ˢ I) (L ×ˢ I) :=
    hvbij.prodMap (bijOn_id I)
  have hρbij : BijOn ρ (J ×ˢ Icc (-1 : ℝ) 1) W :=
    ((hu.injOn.mono (hVS.trans hSP)).bijOn_image.comp hσ.bijOn).comp (hprod _)
  have hρcont : ContinuousOn ρ (J ×ˢ Icc (-1 : ℝ) 1) :=
    (hu.continuousOn.comp hσ.isPiecewiseAffineOn.continuousOn
      (fun x hx => hSP (hVS (hσ.bijOn.mapsTo hx)))).comp
      ((hvcont.mono hJY).prodMap continuousOn_id) (hprod _).mapsTo
  have hρimage (I : Set ℝ) : ρ '' (J ×ˢ I) = u '' (σ '' (L ×ˢ I)) := by
    change (u ∘ σ ∘ Prod.map v id) '' (J ×ˢ I) = _
    rw [image_comp, image_comp, (hprod I).image_eq]
  have hRWtrace : R ∩ W = ρ '' (J ×ˢ {(-1 : ℝ), 1}) := by
    rw [hρimage, ← hmeet, hu.injOn.image_inter (hVS.trans hSP) (hCS.trans hSP)]
    change (B ∩ u '' C.space) ∩ W = W ∩ u '' C.space
    ext y
    exact ⟨fun hy => ⟨hy.2, hy.1.2⟩, fun hy => ⟨⟨hWB hy.1, hy.2⟩, hy.1⟩⟩
  have hWnhds : W ∈ 𝓝ˢ[B] J := by
    have hpre := hvcont.preimage_mem_nhdsSetWithin hVnhds
    have hdom : Yb ∩ v ⁻¹' frontier P = Yb := inter_eq_left.mpr hvS
    have hbase : Yb ∩ v ⁻¹' L = J := by
      apply Subset.antisymm
      · intro y hy
        have hy' := huL.subset (mem_image_of_mem u hy.2)
        rwa [huv y (hYbP hy.1)] at hy'
      · exact fun y hy => ⟨hJY hy, mem_image_of_mem v hy⟩
    rw [hdom, hbase] at hpre
    obtain ⟨O, hO, hJO, hOV⟩ := mem_nhdsSetWithin.mp hpre
    refine mem_nhdsSetWithin.mpr ⟨O, hO, hJO, fun y hy => ?_⟩
    exact ⟨v y, hOV ⟨hy.1, hBY hy.2⟩, huv y (hYbP (hBY hy.2))⟩
  refine ⟨W, R, ρ, hWc, subset_inter hWB ?_, hRc, hRN, hRW, hRWtrace,
    hWnhds, hρcont, hρbij, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact hVT hx
  · intro x hx
    change u (σ (v x, 0)) = x
    rw [hσzero _ (mem_image_of_mem v hx), huv x (hJP hx)]

end DifferentialGeometry.Topology.PiecewiseLinear
