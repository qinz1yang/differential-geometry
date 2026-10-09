/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarBands
import DifferentialGeometry.Topology.PiecewiseLinear.CollarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.FrontierBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem isPLHomeomorphOn_collar_shift :
    IsPLHomeomorphOn (fun t : ℝ => 1 + t / 2) (Icc 0 2) (Icc 1 2) := by
  have hpl : IsPiecewiseAffineOn (fun t : ℝ => 1 + t / 2) (Icc 0 2) := by
    convert isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ ℝ (1 : ℝ) + (1 / 2 : ℝ) • AffineMap.id ℝ ℝ)
      (isHPolytope_Icc (a := (0 : ℝ)) (b := 2)) using 1
    ext t
    simp [div_eq_mul_inv, mul_comm]
  apply isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
    isHPolytope_Icc.isPolyhedron hpl
  refine ⟨fun t ht => ?_, fun s _ t _ hst => ?_, fun t ht => ?_⟩
  · constructor <;> linarith [ht.1, ht.2]
  · linarith
  · refine ⟨2 * (t - 1), ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    ring

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_collar_core
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) {W : Set E} {c : E × ℝ → E}
    (hc : IsPLHomeomorphOn c ((boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) 2) W)
    (hWK : W ⊆ K.space)
    (hbottom : ∀ x ∈ (boundaryComplex 3 K).space, c (x, 0) = x) :
    ∃ s : E → E,
      IsPLHomeomorphOn s K.space
        (K.space \ c '' ((boundaryComplex 3 K).space ×ˢ Ico (0 : ℝ) 1)) ∧
      EqOn s id (K.space \ W) ∧
      ∀ x ∈ (boundaryComplex 3 K).space, ∀ t ∈ Icc (0 : ℝ) 2,
        s (c (x, t)) = c (x, 1 + t / 2) := by
  let L := boundaryComplex 3 K
  let _ : Finite L.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hL : IsCombinatorialManifold 2 L := isCombinatorialManifold_boundaryComplex K hK
  have hS : IsPolyhedron L.space := isPolyhedron_space L
  have hP : IsPolyhedron (L.space ×ˢ Icc (0 : ℝ) 2) :=
    hS.prod isHPolytope_Icc.isPolyhedron
  have hW : IsPolyhedron W := by
    rw [← hc.image_eq]
    exact hP.image_of_isPiecewiseAffineOn hc.isPiecewiseAffineOn hc.bijOn.injOn
  let R := closure (K.space \ W)
  have hR : IsPolyhedron R := (isPolyhedron_space K).closure_sdiff hW
  have hRK : R ⊆ K.space := closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  have hnhds := hc.mem_nhdsSetWithin_boundaryComplex K hK (by norm_num) hWK hbottom
  have hseam : W ∩ R ⊆ c '' (L.space ×ˢ {(2 : ℝ)}) := by
    rintro y ⟨hyW, hyR⟩
    obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hc.bijOn.surjOn hyW
    by_cases ht2 : t = 2
    · exact ⟨(x, t), ⟨hx, ht2⟩, rfl⟩
    have hyn : W ∈ 𝓝[K.space] c (x, t) := by
      by_cases ht0 : t = 0
      · subst t
        rw [hbottom x hx]
        obtain ⟨O, hO, hSO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
        exact mem_nhdsWithin.mpr ⟨O, hO, hSO hx, hOW⟩
      · exact hc.mem_nhdsWithin_of_mem_prod_Ioo hK hL (by norm_num) hWK
          ⟨hx, lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht2⟩
    obtain ⟨O, hO, hyO, hOW⟩ := mem_nhdsWithin.mp hyn
    obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp hyR O hO hyO
    exact (hz.2 (hOW ⟨hzO, hz.1⟩)).elim
  let V := c '' (L.space ×ˢ Icc (1 : ℝ) 2)
  have hsub : L.space ×ˢ Icc (1 : ℝ) 2 ⊆ L.space ×ˢ Icc (0 : ℝ) 2 :=
    prod_mono subset_rfl (fun _ ht => ⟨le_trans (by norm_num) ht.1, ht.2⟩)
  have hVW : V ⊆ W := (image_mono hsub).trans hc.image_eq.subset
  let f := c ∘ Prod.map id (fun t : ℝ => 1 + t / 2) ∘
    Function.invFunOn c (L.space ×ˢ Icc (0 : ℝ) 2)
  have hf : IsPLHomeomorphOn f W V := hc.symm.trans
    ((hS.isPLHomeomorphOn_id.prodMap isPLHomeomorphOn_collar_shift).trans
      (hc.restrict (hS.prod isHPolytope_Icc.isPolyhedron) hsub))
  have hfc : ∀ x ∈ L.space, ∀ t ∈ Icc (0 : ℝ) 2,
      f (c (x, t)) = c (x, 1 + t / 2) := by
    intro x hx t ht
    change c (Prod.map id (fun t : ℝ => 1 + t / 2)
      (Function.invFunOn c (L.space ×ˢ Icc (0 : ℝ) 2) (c (x, t)))) = _
    rw [hc.bijOn.invOn_invFunOn.1 (show (x, t) ∈
      (boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) 2 from ⟨hx, ht⟩)]
    rfl
  have hfix : EqOn f id (W ∩ R) := by
    intro y hy
    obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hseam hy
    have ht2 : t = 2 := ht
    subst t
    rw [hfc x hx 2 (by norm_num)]
    norm_num
  have hmeet : f '' (W ∩ R) = V ∩ R := by
    rw [hfix.image_eq, image_id]
    apply Subset.antisymm
    · intro y hy
      refine ⟨?_, hy.2⟩
      obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ := hseam hy
      exact ⟨(x, t), ⟨hx, by rw [show t = 2 from ht]; norm_num⟩, rfl⟩
    · exact fun _ hy => ⟨hVW hy.1, hy.2⟩
  have hcover : W ∪ R = K.space := by
    apply Subset.antisymm (union_subset hWK hRK)
    intro y hy
    by_cases hyW : y ∈ W
    · exact Or.inl hyW
    · exact Or.inr (subset_closure ⟨hy, hyW⟩)
  have htarget : V ∪ R = K.space \ c '' (L.space ×ˢ Ico (0 : ℝ) 1) := by
    apply Subset.antisymm
    · rintro y (hyV | hyR)
      · refine ⟨hWK (hVW hyV), ?_⟩
        obtain ⟨z, hz, rfl⟩ := hyV
        rintro ⟨w, hw, hwz⟩
        have heq := hc.bijOn.injOn ⟨hw.1, hw.2.1, hw.2.2.le.trans (by norm_num)⟩
          (hsub hz) hwz
        have := congrArg Prod.snd heq
        linarith [hw.2.2, hz.2.1]
      · refine ⟨hRK hyR, ?_⟩
        rintro ⟨z, hz, rfl⟩
        have hzP : z ∈ L.space ×ˢ Icc (0 : ℝ) 2 :=
          ⟨hz.1, hz.2.1, hz.2.2.le.trans (by norm_num)⟩
        obtain ⟨w, hw, hwz⟩ := hseam ⟨hc.bijOn.mapsTo hzP, hyR⟩
        have hwP : w ∈ L.space ×ˢ Icc (0 : ℝ) 2 :=
          ⟨hw.1, by rw [show w.2 = 2 from hw.2]; norm_num⟩
        have heq := congrArg Prod.snd (hc.bijOn.injOn hwP hzP hwz)
        have hw2 : w.2 = 2 := hw.2
        linarith [hz.2.2]
    · rintro y ⟨hyK, hycut⟩
      by_cases hyW : y ∈ W
      · left
        obtain ⟨z, hz, rfl⟩ := hc.bijOn.surjOn hyW
        refine ⟨z, ⟨hz.1, ?_, hz.2.2⟩, rfl⟩
        by_contra hz1
        exact hycut ⟨z, ⟨hz.1, hz.2.1, lt_of_not_ge hz1⟩, rfl⟩
      · exact Or.inr (subset_closure ⟨hyK, hyW⟩)
  have hs := hf.piecewise hR.isPLHomeomorphOn_id hW hR hfix hmeet
  rw [hcover, htarget] at hs
  refine ⟨W.piecewise f id, hs, ?_, ?_⟩
  · exact fun y hy => W.piecewise_eq_of_notMem f id hy.2
  · intro x hx t ht
    rw [W.piecewise_eq_of_mem f id (hc.bijOn.mapsTo ⟨hx, ht⟩)]
    exact hfc x hx t ht

theorem IsPLBall.exists_isPLHomeomorphOn_collar_core
    (hdim : Module.finrank ℝ E = 3) {C W : Set E} (hC : IsPLBall 3 C)
    {c : E × ℝ → E} (hc : IsPLHomeomorphOn c (frontier C ×ˢ Icc (0 : ℝ) 2) W)
    (hWC : W ⊆ C) (hbottom : ∀ x ∈ frontier C, c (x, 0) = x) :
    ∃ s : E → E,
      IsPLHomeomorphOn s C (C \ c '' (frontier C ×ˢ Ico (0 : ℝ) 1)) ∧
      IsPLBall 3 (C \ c '' (frontier C ×ˢ Ico (0 : ℝ) 1)) ∧
      frontier (C \ c '' (frontier C ×ˢ Ico (0 : ℝ) 1)) =
        c '' (frontier C ×ˢ {(1 : ℝ)}) ∧
      EqOn s id (C \ W) ∧
      ∀ x ∈ frontier C, ∀ t ∈ Icc (0 : ℝ) 2,
        s (c (x, t)) = c (x, 1 + t / 2) := by
  classical
  let _ : DecidableEq E := Classical.decEq _
  obtain ⟨K, hKfin, hKspace⟩ := hC.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsPLBall 3 K.space := hKspace.symm ▸ hC
  have hboundary : (boundaryComplex 3 K).space = frontier C := by
    rw [← frontier_space_eq_boundaryComplex_space_of_finrank hdim K
      hK.isCombinatorialManifoldWithBoundary, hKspace]
  have hcK : IsPLHomeomorphOn c ((boundaryComplex 3 K).space ×ˢ Icc (0 : ℝ) 2) W := by
    rw [hboundary]
    exact hc
  obtain ⟨s, hs, hsid, hsc⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_collar_core K hcK
      (by rw [hKspace]; exact hWC) (by rw [hboundary]; exact hbottom)
  simp only [hKspace, hboundary] at hs hsid hsc
  have hD := hC.of_isPLHomeomorphOn hs
  refine ⟨s, hs, hD, ?_, hsid, hsc⟩
  rw [← hs.image_frontier rfl hC.isPolyhedron.isClosed hD.isPolyhedron.isClosed]
  have hsc0 : ∀ x ∈ frontier C, s x = c (x, 1) := by
    intro x hx
    have h := hsc x hx 0 (by norm_num)
    simpa only [hbottom x hx, zero_div, add_zero] using h
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(x, 1), ⟨hx, rfl⟩, (hsc0 x hx).symm⟩
  · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have ht1 : t = 1 := ht
    subst t
    exact ⟨x, hx, hsc0 x hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
