/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Bicollar
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ClosedStarNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ComponentComplex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComplement
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldRelativeTopology
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.Prism
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem IsPLHomeomorphOn.image_mem_nhdsWithin {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {f : E → F} {P : Set E} {Q : Set F}
    (hf : IsPLHomeomorphOn f P Q) {x : E} (hx : x ∈ P) {S : Set E} (hS : S ∈ 𝓝[P] x) :
    f '' S ∈ 𝓝[Q] (f x) := by
  have hg : ContinuousOn (Function.invFunOn f P) Q :=
    hf.isPiecewiseAffineOn_invFunOn.continuousOn
  have hfx : f x ∈ Q := hf.bijOn.mapsTo hx
  have ht : Filter.Tendsto (Function.invFunOn f P) (𝓝[Q] (f x)) (𝓝[P] x) := by
    have h := (hg (f x) hfx).tendsto_nhdsWithin hf.bijOn.surjOn.mapsTo_invFunOn
    rwa [hf.bijOn.invOn_invFunOn.1 hx] at h
  filter_upwards [ht hS, self_mem_nhdsWithin] with y hy hyQ
  exact ⟨_, hy, hf.bijOn.invOn_invFunOn.2 hyQ⟩

theorem exists_rescaled_bicollar_of_mem_nhdsSetWithin {K L W₀ : Set E} {ρ₀ : E × ℝ → E}
    (hL : IsPolyhedron L) (hρ₀ : IsPLHomeomorphOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) W₀)
    (hzero : ∀ y ∈ L, ρ₀ (y, 0) = y) (hW₀K : W₀ ⊆ K) (hnhds : W₀ ∈ 𝓝ˢ[K] L) :
    ∃ (ρ : E × ℝ → E) (W₂ : Set E), IsPLHomeomorphOn ρ (L ×ˢ Icc (-2 : ℝ) 2) W₂ ∧
      W₂ ⊆ W₀ ∧ (∀ y ∈ L, ρ (y, 0) = y) ∧
      ∃ G : Set E, IsOpen G ∧ G ∩ K = ρ '' (L ×ˢ Ioo (-1 : ℝ) 1) := by
  obtain ⟨O, hO, hLO, hOW⟩ := mem_nhdsSetWithin.mp hnhds
  obtain ⟨u, hu, hue⟩ := continuousOn_iff'.mp hρ₀.isPiecewiseAffineOn.continuousOn O hO
  have hLu : L ×ˢ ({0} : Set ℝ) ⊆ u := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have ht0 : t = 0 := ht
    subst ht0
    have hmem : (y, (0 : ℝ)) ∈ ρ₀ ⁻¹' O ∩ L ×ˢ Icc (-1 : ℝ) 1 := by
      refine ⟨?_, hy, by norm_num, by norm_num⟩
      change ρ₀ (y, 0) ∈ O
      rw [hzero y hy]
      exact hLO hy
    rw [hue] at hmem
    exact hmem.1
  obtain ⟨δ, hδ, hthick⟩ :=
    (hL.isCompact.prod isCompact_singleton).exists_thickening_subset_open hu hLu
  have hOρ : ∀ y ∈ L, ∀ t : ℝ, |t| < δ → t ∈ Icc (-1 : ℝ) 1 → ρ₀ (y, t) ∈ O := by
    intro y hy t htδ ht
    have hthk : (y, t) ∈ Metric.thickening δ (L ×ˢ ({0} : Set ℝ)) := by
      rw [Metric.mem_thickening_iff]
      refine ⟨(y, 0), ⟨hy, rfl⟩, ?_⟩
      simp only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
      exact max_lt hδ htδ
    have hmem : (y, t) ∈ u ∩ L ×ˢ Icc (-1 : ℝ) 1 := ⟨hthick hthk, hy, ht⟩
    rw [← hue] at hmem
    exact hmem.1
  set ε : ℝ := min (δ / 2) (1 / 2)
  have hε : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hmpl : IsPiecewiseAffineOn (fun t : ℝ => ε * t) (Icc (-2 : ℝ) 2) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope (ε • AffineMap.id ℝ ℝ) isHPolytope_Icc
  have hminj : InjOn (fun t : ℝ => ε * t) (Icc (-2 : ℝ) 2) := fun s _ t _ hst =>
    mul_left_cancel₀ hε.ne' hst
  have hm : IsPLHomeomorphOn (fun t : ℝ => ε * t) (Icc (-2 : ℝ) 2)
      ((fun t : ℝ => ε * t) '' Icc (-2 : ℝ) 2) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron hmpl
      hminj.bijOn_image
  have hmI : (fun t : ℝ => ε * t) '' Icc (-2 : ℝ) 2 ⊆ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
    change -1 ≤ ε * t ∧ ε * t ≤ 1
    constructor <;> nlinarith
  have hmpoly : IsPolyhedron ((fun t : ℝ => ε * t) '' Icc (-2 : ℝ) 2) :=
    isHPolytope_Icc.isPolyhedron.image_of_isPiecewiseAffineOn hmpl hminj
  have hρ := (hL.isPLHomeomorphOn_id.prodMap hm).trans
    (hρ₀.restrict (hL.prod hmpoly) (prod_mono subset_rfl hmI))
  refine ⟨ρ₀ ∘ Prod.map id (fun t : ℝ => ε * t), _, hρ, ?_, ?_, ?_⟩
  · rw [← hρ₀.image_eq]
    exact image_mono (prod_mono subset_rfl hmI)
  · intro y hy
    change ρ₀ (y, ε * 0) = y
    rw [mul_zero]
    exact hzero y hy
  have hτ : ContinuousOn (fun w => (Function.invFunOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) w).2) W₀ :=
    continuous_snd.comp_continuousOn hρ₀.isPiecewiseAffineOn_invFunOn.continuousOn
  obtain ⟨G₁, hG₁, hG₁e⟩ := continuousOn_iff'.mp hτ (Ioo (-ε) ε) isOpen_Ioo
  refine ⟨G₁ ∩ O, hG₁.inter hO, ?_⟩
  apply Subset.antisymm
  · rintro w ⟨⟨hw₁, hwO⟩, hwK⟩
    have hwW₀ : w ∈ W₀ := hOW ⟨hwO, hwK⟩
    have hwτ : w ∈ (fun w => (Function.invFunOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) w).2) ⁻¹'
        Ioo (-ε) ε ∩ W₀ := by
      rw [hG₁e]
      exact ⟨hw₁, hwW₀⟩
    set z := Function.invFunOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) w
    have hzP : z ∈ L ×ˢ Icc (-1 : ℝ) 1 := hρ₀.bijOn.surjOn.mapsTo_invFunOn hwW₀
    have hρz : ρ₀ z = w := hρ₀.bijOn.invOn_invFunOn.2 hwW₀
    have hzε : z.2 ∈ Ioo (-ε) ε := hwτ.1
    refine ⟨(z.1, z.2 / ε), ⟨hzP.1, ?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ hε]
      linarith [hzε.1]
    · rw [div_lt_iff₀ hε]
      linarith [hzε.2]
    · change ρ₀ (z.1, ε * (z.2 / ε)) = w
      rw [mul_div_cancel₀ _ hε.ne']
      exact hρz
  · rintro _ ⟨⟨y, s⟩, ⟨hy, hs1, hs2⟩, rfl⟩
    have hsI : ε * s ∈ Icc (-1 : ℝ) 1 := hmI ⟨s, ⟨by linarith, by linarith⟩, rfl⟩
    have hmem : (y, ε * s) ∈ L ×ˢ Icc (-1 : ℝ) 1 := ⟨hy, hsI⟩
    have hw : ρ₀ (y, ε * s) ∈ W₀ := hρ₀.bijOn.mapsTo hmem
    have hwτ : ρ₀ (y, ε * s) ∈
        (fun w => (Function.invFunOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) w).2) ⁻¹' Ioo (-ε) ε ∩ W₀ := by
      refine ⟨?_, hw⟩
      change (Function.invFunOn ρ₀ (L ×ˢ Icc (-1 : ℝ) 1) (ρ₀ (y, ε * s))).2 ∈ Ioo (-ε) ε
      rw [hρ₀.bijOn.invOn_invFunOn.1 hmem]
      change -ε < ε * s ∧ ε * s < ε
      constructor <;> nlinarith
    rw [hG₁e] at hwτ
    have hsδ : |ε * s| < δ := by
      rw [abs_lt]
      constructor <;> nlinarith
    exact ⟨⟨hwτ.1, hOρ y hy _ hsδ hsI⟩, hW₀K hw⟩

theorem image_inter_closure_sdiff_of_rescaled_bicollar {K L W₂ G : Set E} {ρ : E × ℝ → E}
    (hρ : IsPLHomeomorphOn ρ (L ×ˢ Icc (-2 : ℝ) 2) W₂) (hW₂K : W₂ ⊆ K) (hG : IsOpen G)
    (hGK : G ∩ K = ρ '' (L ×ˢ Ioo (-1 : ℝ) 1)) :
    ρ '' (L ×ˢ Icc (-1 : ℝ) 1) ∩ closure (K \ ρ '' (L ×ˢ Icc (-1 : ℝ) 1)) =
      ρ '' (L ×ˢ ({-1, 1} : Set ℝ)) := by
  apply Subset.antisymm
  · rintro _ ⟨⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩, hcl⟩
    by_cases hbd : t = -1 ∨ t = 1
    · exact ⟨(y, t), ⟨hy, hbd⟩, rfl⟩
    · exfalso
      obtain ⟨hne1, hne2⟩ := not_or.mp hbd
      have htI : t ∈ Ioo (-1 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht.1 (Ne.symm hne1), lt_of_le_of_ne ht.2 hne2⟩
      have hG' : ρ (y, t) ∈ G := (hGK.symm.subset ⟨(y, t), ⟨hy, htI⟩, rfl⟩).1
      obtain ⟨q, hqG, hqK, hqW⟩ := mem_closure_iff.mp hcl G hG hG'
      have hq := hGK.subset ⟨hqG, hqK⟩
      exact hqW (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self) hq)
  · rintro _ ⟨⟨y, t⟩, ⟨hy, ht⟩, rfl⟩
    have htI : t ∈ Icc (-1 : ℝ) 1 := by
      rcases ht with rfl | rfl <;> norm_num
    refine ⟨⟨(y, t), ⟨hy, htI⟩, rfl⟩, ?_⟩
    have hmaps : MapsTo (fun u : ℝ => (y, t * u)) (Icc (1 : ℝ) 2) (L ×ˢ Icc (-2 : ℝ) 2) := by
      intro u hu
      refine ⟨hy, ?_, ?_⟩
      · change -2 ≤ t * u
        rcases ht with rfl | rfl <;> linarith [hu.1, hu.2]
      · change t * u ≤ 2
        rcases ht with rfl | rfl <;> linarith [hu.1, hu.2]
    have hφ : ContinuousOn (fun u : ℝ => ρ (y, t * u)) (Icc (1 : ℝ) 2) :=
      hρ.isPiecewiseAffineOn.continuousOn.comp
        (continuousOn_const.prodMk (continuousOn_const.mul continuousOn_id)) hmaps
    have hlim : Filter.Tendsto (fun u : ℝ => ρ (y, t * u)) (𝓝[Ioc (1 : ℝ) 2] 1)
        (𝓝 (ρ (y, t))) := by
      have h : Filter.Tendsto (fun u : ℝ => ρ (y, t * u)) (𝓝[Icc (1 : ℝ) 2] 1)
          (𝓝 (ρ (y, t * 1))) := (hφ 1 ⟨le_rfl, by norm_num⟩).tendsto
      rw [mul_one] at h
      exact h.mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self)
    have := left_nhdsWithin_Ioc_neBot (show (1 : ℝ) < 2 by norm_num)
    apply mem_closure_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with u hu
    refine ⟨hW₂K (hρ.bijOn.mapsTo (hmaps (Ioc_subset_Icc_self hu))), ?_⟩
    rintro ⟨⟨y', t'⟩, ⟨hy', ht'⟩, heq⟩
    have h := hρ.bijOn.injOn
      (mk_mem_prod hy' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩)
      (hmaps (Ioc_subset_Icc_self hu)) heq
    have htu : t' = t * u := congrArg Prod.snd h
    have hu1 := hu.1
    rcases ht with rfl | rfl <;> linarith [ht'.1, ht'.2]

theorem isCombinatorialManifoldWithBoundary_of_space_eq_image_prod
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    {a b : ℝ} (hab : a < b) {ρ : E × ℝ → E} {W : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc a b) W)
    (A : Geometry.SimplicialComplex ℝ E) [Finite A.faces] (hA : A.space = W) :
    IsCombinatorialManifoldWithBoundary 3 A := by
  apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods A
  intro p hp
  rw [hA] at hp ⊢
  obtain ⟨⟨y, t⟩, hz, rfl⟩ := hρ.bijOn.surjOn hp
  obtain ⟨D, hD, hDL, hDnhds⟩ :=
    hL.exists_isPLBall_subset_of_mem_nhds hz.1 (U := univ) Filter.univ_mem
  have hDL' : D ⊆ L.space := hDL.trans inter_subset_left
  have hprod : IsPLBall 3 (D ×ˢ Icc a b) := isPLBall_three_prod hD (isPLBall_Icc hab)
  have hsub : D ×ˢ Icc a b ⊆ L.space ×ˢ Icc a b := prod_mono hDL' subset_rfl
  refine ⟨ρ '' (D ×ˢ Icc a b), hprod.of_isPLHomeomorphOn (hρ.restrict hprod.isPolyhedron hsub),
    ?_, ?_⟩
  · rw [← hρ.image_eq]
    exact image_mono hsub
  · apply hρ.image_mem_nhdsWithin hz
    rw [nhdsWithin_prod_eq]
    exact Filter.prod_mem_prod hDnhds self_mem_nhdsWithin

theorem exists_half_collar_of_eq_image_connectedComponentIn
    {L : Geometry.SimplicialComplex ℝ E} [Finite L.faces] {ρ : E × ℝ → E} {W R B : Set E}
    (hρ : IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W)
    (hzero : ∀ y ∈ L.space, ρ (y, 0) = y)
    (hRW : R ∩ W = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)))
    {y₀ : E} (hy₀ : y₀ ∈ L.space) {e : ℝ} (he : e ∈ ({-1, 1} : Set ℝ))
    (hB : B = (fun y => ρ (y, e)) '' connectedComponentIn L.space y₀) :
    ∃ σ : E × ℝ → E,
      IsPLHomeomorphOn σ (B ×ˢ Icc (0 : ℝ) 1) (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ y ∈ B, σ (y, 0) = y) ∧
      σ '' (B ×ˢ Icc (0 : ℝ) 1) ⊆ W ∧
      (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∩ R = B ∧
      (∀ z ∈ B ×ˢ Icc (0 : ℝ) 1, σ z ∈ L.space ↔ z.2 = 1) ∧
      ∃ (f : C(B, L.space)) (p : C(L.space, B)),
        (∀ y : B, (f y : E) = σ (y, 1)) ∧ Function.LeftInverse p f := by
  classical
  obtain ⟨Lα, hLαdef⟩ : ∃ Lα, Lα = connectedComponentIn L.space y₀ := ⟨_, rfl⟩
  rw [← hLαdef] at hB
  have hLαL : Lα ⊆ L.space := by
    rw [hLαdef]
    exact connectedComponentIn_subset _ _
  have hLαpoly : IsPolyhedron Lα := by
    rw [hLαdef]
    have := (restrict_faces_finite L (connectedComponentIn L.space y₀)).to_subtype
    have h := isPolyhedron_space (restrict L (connectedComponentIn L.space y₀))
    rwa [restrict_connectedComponentIn_space] at h
  have heI : e ∈ Icc (-1 : ℝ) 1 := by
    rcases he with rfl | rfl <;> norm_num
  have he0 : e ≠ 0 := by
    rcases he with rfl | rfl <;> norm_num
  have hsing : IsPolyhedron ({e} : Set ℝ) := by
    rw [← Icc_self e]
    exact isHPolytope_Icc.isPolyhedron
  have hj : IsPLHomeomorphOn (fun y => ρ (y, e)) Lα B := by
    have h := (hLαpoly.isPLHomeomorphOn_prod_const e).trans
      (hρ.restrict (hLαpoly.prod hsing) (prod_mono hLαL (singleton_subset_iff.mpr heI)))
    rw [← h.image_eq] at h
    rw [hB]
    exact h
  set g := Function.invFunOn (fun y => ρ (y, e)) Lα
  have hg : IsPLHomeomorphOn g B Lα := hj.symm
  have hgB : ∀ y ∈ B, g y ∈ Lα := fun y hy => hg.bijOn.mapsTo hy
  have hjg : ∀ y ∈ B, ρ (g y, e) = y := fun y hy => hj.bijOn.invOn_invFunOn.2 hy
  have hinj := hρ.bijOn.injOn
  have hapl : IsPiecewiseAffineOn (fun s : ℝ => e - e * s) (Icc (0 : ℝ) 1) :=
    isPiecewiseAffineOn_of_affine_of_isHPolytope
      (AffineMap.const ℝ ℝ e - e • AffineMap.id ℝ ℝ) isHPolytope_Icc
  have hainj : InjOn (fun s : ℝ => e - e * s) (Icc (0 : ℝ) 1) := fun s _ t _ hst => by
    have h : e * s = e * t := by
      change e - e * s = e - e * t at hst
      linarith
    exact mul_left_cancel₀ he0 h
  have ha : IsPLHomeomorphOn (fun s : ℝ => e - e * s) (Icc (0 : ℝ) 1)
      ((fun s : ℝ => e - e * s) '' Icc (0 : ℝ) 1) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron hapl
      hainj.bijOn_image
  have haI : (fun s : ℝ => e - e * s) '' Icc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1 := by
    rintro _ ⟨s, ⟨hs0, hs1⟩, rfl⟩
    change -1 ≤ e - e * s ∧ e - e * s ≤ 1
    rcases he with rfl | rfl <;> constructor <;> linarith
  have hapoly : IsPolyhedron ((fun s : ℝ => e - e * s) '' Icc (0 : ℝ) 1) :=
    isHPolytope_Icc.isPolyhedron.image_of_isPiecewiseAffineOn hapl hainj
  have hσ := (hg.prodMap ha).trans
    (hρ.restrict (hLαpoly.prod hapoly) (prod_mono hLαL haI))
  set σ : E × ℝ → E := ρ ∘ Prod.map g (fun s : ℝ => e - e * s)
  have hσimg := hσ.image_eq
  have hσ0 : ∀ y ∈ B, σ (y, 0) = y := by
    intro y hy
    change ρ (g y, e - e * 0) = y
    rw [mul_zero, sub_zero]
    exact hjg y hy
  have hσW : σ '' (B ×ˢ Icc (0 : ℝ) 1) ⊆ W := by
    rw [hσimg, ← hρ.image_eq]
    exact image_mono (prod_mono hLαL haI)
  have hBR : B ⊆ R := by
    intro y hy
    have hy' : y ∈ ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) := by
      rw [hB] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact ⟨(y', e), ⟨hLαL hy', he⟩, rfl⟩
    exact (hRW.symm.subset hy').1
  refine ⟨σ, ?_, hσ0, hσW, ?_, ?_, ?_⟩
  · rw [hσimg]
    exact hσ
  · apply Subset.antisymm
    · rintro _ ⟨⟨⟨y, s⟩, ⟨hy, hs⟩, rfl⟩, hR⟩
      have hW : σ (y, s) ∈ W := hσW ⟨(y, s), ⟨hy, hs⟩, rfl⟩
      obtain ⟨⟨y', t'⟩, ⟨hy', ht'⟩, heq⟩ := hRW.subset ⟨hR, hW⟩
      have ht'I : t' ∈ Icc (-1 : ℝ) 1 := by
        rcases ht' with rfl | rfl <;> norm_num
      have h := hinj ⟨hy', ht'I⟩ ⟨hLαL (hgB y hy), haI ⟨s, hs, rfl⟩⟩ heq
      have ht : t' = e - e * s := congrArg Prod.snd h
      have hs0 : s = 0 := by
        have h1 := hs.1
        have h2 := hs.2
        rcases he with rfl | rfl <;> rcases ht' with rfl | rfl <;> linarith
      subst hs0
      rw [hσ0 y hy]
      exact hy
    · intro y hy
      exact ⟨⟨(y, 0), ⟨hy, by norm_num, by norm_num⟩, hσ0 y hy⟩, hBR hy⟩
  · rintro ⟨y, s⟩ ⟨hy, hs⟩
    constructor
    · intro hL
      have h := hinj ⟨hLαL (hgB y hy), haI ⟨s, hs, rfl⟩⟩ ⟨hL, by norm_num, by norm_num⟩
        (hzero _ hL).symm
      have h2 : e - e * s = 0 := congrArg Prod.snd h
      have h3 : e * (1 - s) = 0 := by linarith
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact absurd h4 he0
      · change s = 1
        linarith
    · intro hs1
      change s = 1 at hs1
      subst hs1
      change ρ (g y, e - e * 1) ∈ L.space
      rw [mul_one, sub_self, hzero _ (hLαL (hgB y hy))]
      exact hLαL (hgB y hy)
  · have hgc : ContinuousOn g B := hg.isPiecewiseAffineOn.continuousOn
    let f : C(B, L.space) :=
      ⟨fun y => ⟨g y, hLαL (hgB y y.2)⟩,
        (continuousOn_iff_continuous_domRestrict.mp hgc).subtype_mk _⟩
    have hjc : ContinuousOn (fun y => ρ (y, e)) L.space :=
      hρ.isPiecewiseAffineOn.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        fun y hy => ⟨hy, heI⟩
    let _ : LocallyConnectedSpace L.space := locallyConnectedSpace_space L
    let x₀ : L.space := ⟨y₀, hy₀⟩
    let S : Set L.space := connectedComponent x₀
    have hS : IsClopen S := ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
    have hSα : ∀ x : L.space, x ∈ S ↔ (x : E) ∈ Lα := by
      intro x
      rw [hLαdef, connectedComponentIn_eq_image hy₀]
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨x', hx', hxx'⟩
        rw [Subtype.ext hxx'] at hx'
        exact hx'
    let q : L.space → L.space := fun x => if x ∈ S then x else x₀
    have hq : Continuous q := by
      apply Continuous.if _ continuous_id continuous_const
      intro a ha
      simp only [ofPred_mem_eq, hS.frontier_eq, mem_empty_iff_false] at ha
    have hqα : ∀ x, (q x : E) ∈ Lα := by
      intro x
      by_cases hx : x ∈ S
      · simp only [q, ite_eq_left hx]
        exact (hSα x).mp hx
      · simp only [q, ite_eq_right hx]
        rw [hLαdef]
        exact mem_connectedComponentIn hy₀
    have hqid : ∀ x : L.space, (x : E) ∈ Lα → q x = x := by
      intro x hx
      simp only [q, ite_eq_left ((hSα x).mpr hx)]
    have hpB : ∀ x : L.space, ρ ((q x : E), e) ∈ B := by
      intro x
      rw [hB]
      exact ⟨q x, hqα x, rfl⟩
    let p : C(L.space, B) :=
      ⟨fun x => ⟨ρ ((q x : E), e), hpB x⟩,
        (hjc.comp_continuous (continuous_subtype_val.comp hq) fun x => (q x).2).subtype_mk _⟩
    refine ⟨f, p, ?_, ?_⟩
    · intro y
      change g y = ρ (g y, e - e * 1)
      rw [mul_one, sub_self, hzero _ (hLαL (hgB y y.2))]
    · intro y
      apply Subtype.ext
      change ρ ((q (f y) : E), e) = y
      rw [hqid (f y) (hgB y y.2)]
      exact hjg y y.2

open Classical in
theorem exists_bicollar_complement_with_boundary_collars
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space \ (boundaryComplex 3 K).space)
    (htwo : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space)) :
    ∃ (W : Set E) (ρ : E × ℝ → E) (R : Geometry.SimplicialComplex ℝ E),
      ∃ _ : Finite R.faces,
        IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W ∧
        (∀ y ∈ L.space, ρ (y, 0) = y) ∧
        W ⊆ K.space \ (boundaryComplex 3 K).space ∧
        W ∈ 𝓝ˢ[K.space] L.space ∧
        IsCombinatorialManifoldWithBoundary 3 R ∧
        R.space = closure (K.space \ W) ∧
        R.space ⊆ K.space ∧
        Disjoint R.space L.space ∧
        (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 R).space ∧
        (R.space ∩ W = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ))) ∧
        ∀ c : ConnectedComponents (boundaryComplex 3 R).space,
          let B := (connectedComponentComplex (boundaryComplex 3 R) c).space
          B ⊆ W →
          ∃ σ : E × ℝ → E,
            IsPLHomeomorphOn σ (B ×ˢ Icc (0 : ℝ) 1)
              (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∧
            (∀ y ∈ B, σ (y, 0) = y) ∧
            σ '' (B ×ˢ Icc (0 : ℝ) 1) ⊆ W ∧
            (σ '' (B ×ˢ Icc (0 : ℝ) 1)) ∩ R.space = B ∧
            (∀ z ∈ B ×ˢ Icc (0 : ℝ) 1, σ z ∈ L.space ↔ z.2 = 1) ∧
            ∃ (f : C(B, L.space)) (p : C(L.space, B)),
              (∀ y : B, (f y : E) = σ (y, 1)) ∧ Function.LeftInverse p f := by
  have hLK' : L.space ⊆ K.space := hLK.trans sdiff_subset
  have hBd : Disjoint L.space (boundaryComplex 3 K).space :=
    disjoint_left.mpr fun _ hx hxB => (hLK hx).2 hxB
  obtain ⟨W₀, ρ₀, -, hW₀int, -, hW₀nhds, hρ₀, hρ₀zero⟩ :=
    hK.exists_bicollar hL hLK' hBd htwo (U := univ) Filter.univ_mem
  have hLpoly := isPolyhedron_space L
  obtain ⟨ρ, W₂, hρ₂, hW₂W₀, hzero, G, hG, hGK⟩ :=
    exists_rescaled_bicollar_of_mem_nhdsSetWithin hLpoly hρ₀ hρ₀zero
      (hW₀int.trans sdiff_subset) hW₀nhds
  have hIcc : Icc (-1 : ℝ) 1 ⊆ Icc (-2) 2 := Icc_subset_Icc (by norm_num) (by norm_num)
  have hρ := hρ₂.restrict (hLpoly.prod isHPolytope_Icc.isPolyhedron) (prod_mono subset_rfl hIcc)
  set W := ρ '' (L.space ×ˢ Icc (-1 : ℝ) 1) with hWdef
  have hpmI : ∀ t ∈ ({-1, 1} : Set ℝ), t ∈ Icc (-1 : ℝ) 1 := by
    rintro t (rfl | rfl) <;> norm_num
  have hW₂K : W₂ ⊆ K.space := hW₂W₀.trans (hW₀int.trans sdiff_subset)
  have hWint : W ⊆ K.space \ (boundaryComplex 3 K).space := by
    have h : W ⊆ W₂ := by
      rw [hWdef, ← hρ₂.image_eq]
      exact image_mono (prod_mono subset_rfl hIcc)
    exact (h.trans hW₂W₀).trans hW₀int
  have hWK : W ⊆ K.space := hWint.trans sdiff_subset
  have hWpoly : IsPolyhedron W :=
    (hLpoly.prod isHPolytope_Icc.isPolyhedron).image_of_isPiecewiseAffineOn
      hρ.isPiecewiseAffineOn hρ.bijOn.injOn
  have hLW : L.space ⊆ W := fun y hy => ⟨(y, 0), ⟨hy, by norm_num, by norm_num⟩, hzero y hy⟩
  have hGW : G ∩ K.space ⊆ W := by
    rw [hGK]
    exact image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)
  have hLG : L.space ⊆ G := fun y hy =>
    (hGK.symm.subset ⟨(y, 0), ⟨hy, by norm_num, by norm_num⟩, hzero y hy⟩).1
  have hWnhds : W ∈ 𝓝ˢ[K.space] L.space := mem_nhdsSetWithin.mpr ⟨G, hG, hLG, hGW⟩
  have htrace : W ∩ closure (K.space \ W) = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) :=
    image_inter_closure_sdiff_of_rescaled_bicollar hρ₂ hW₂K hG hGK
  obtain ⟨K', hK', hK'fin, hK'W⟩ := exists_isSubdivision_restrict_space K hWpoly hWK
  let _ : Finite K'.faces := hK'fin.to_subtype
  let A := restrict K' W
  let _ : Finite A.faces := (restrict_faces_finite K' W).to_subtype
  have hAspace : A.space = W := hK'W
  have hA : IsCombinatorialManifoldWithBoundary 3 A :=
    isCombinatorialManifoldWithBoundary_of_space_eq_image_prod hL (by norm_num) hρ A hAspace
  have hD : IsCombinatorialManifoldWithBoundary 2
      (restrict A (boundaryComplex 3 K').space) := by
    intro v hv
    exfalso
    have hvA : v ∈ A.space := A.subset_space hv.1 (Finset.mem_singleton_self v)
    have hvB : v ∈ (boundaryComplex 3 K').space :=
      hv.2 (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self v)))
    rw [boundaryComplex_space_of_isSubdivision K K' hK hK'] at hvB
    rw [hAspace] at hvA
    exact (hWint hvA).2 hvB
  let R := subcomplexGeneratedBy K' A.facesᶜ
  let _ : Finite R.faces := (subcomplexGeneratedBy_faces_finite K' A.facesᶜ).to_subtype
  have hR : IsCombinatorialManifoldWithBoundary 3 R :=
    (hK.of_isSubdivision hK').complement K' A hA (restrict_faces_subset K' W) hD
  have hRspace : R.space = closure (K.space \ W) := by
    have h := closure_space_sdiff_space_eq_subcomplexGeneratedBy K' K' A Subset.rfl
      (restrict_faces_subset K' W)
    rw [hK'.space_eq, hAspace] at h
    exact h.symm
  have hAK : A.space ⊆ K.space := by
    rw [hAspace]
    exact hWK
  have hAdis : Disjoint A.space (boundaryComplex 3 K).space := by
    rw [hAspace]
    exact disjoint_left.mpr fun _ hx hxB => (hWint hx).2 hxB
  have hbdA := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary K A hK hA hAK hAdis
  have hbdR := boundaryComplex_space_of_closure_sdiff K A R hK hA hAK hR
    (by rw [hAspace]; exact hRspace)
  have hKR : (boundaryComplex 3 K).space ⊆ (boundaryComplex 3 R).space := by
    intro x hx
    rw [hbdR]
    refine Or.inl (subset_closure ⟨hx, fun hxA => ?_⟩)
    rw [hAspace] at hxA
    exact (hWint hxA).2 hx
  have hρR : ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) ⊆ (boundaryComplex 3 R).space := by
    intro x hx
    have hxA : x ∈ (boundaryComplex 3 A).space := by
      rw [← hbdA, hAspace, htrace]
      exact hx
    have hxW : x ∈ W := by
      rw [← hAspace]
      exact boundaryComplex_space_subset 3 A hxA
    rw [hbdR]
    exact Or.inr (subset_closure ⟨hxA, (hWint hxW).2⟩)
  have hRW : R.space ∩ W = ρ '' (L.space ×ˢ ({-1, 1} : Set ℝ)) := by
    rw [hRspace, inter_comm]
    exact htrace
  refine ⟨W, ρ, R, inferInstance, hρ, hzero, hWint, hWnhds, hR, hRspace, ?_, ?_, hKR, hRW, ?_⟩
  · rw [hRspace]
    exact closure_minimal sdiff_subset (isPolyhedron_space K).isClosed
  · rw [disjoint_left]
    intro x hxR hxL
    obtain ⟨⟨y, t⟩, ⟨hy, ht⟩, hyt⟩ := hRW.subset ⟨hxR, hLW hxL⟩
    have h := hρ.bijOn.injOn ⟨hy, hpmI t ht⟩ ⟨hxL, by norm_num, by norm_num⟩
      (hyt.trans (hzero x hxL).symm)
    have ht0 : t = 0 := congrArg Prod.snd h
    rcases ht with rfl | rfl <;> norm_num at ht0
  · intro c B hBW
    have hBsub : B ⊆ (boundaryComplex 3 R).space := by
      change (connectedComponentComplex (boundaryComplex 3 R) c).space ⊆ _
      rw [connectedComponentComplex_space]
      exact Subtype.coe_image_subset _ _
    have hBconn : IsConnected B := isConnected_connectedComponentComplex_space _ c
    obtain ⟨b₀, hb₀⟩ := hBconn.nonempty
    have hBcomp : B = connectedComponentIn (boundaryComplex 3 R).space b₀ := by
      change (connectedComponentComplex (boundaryComplex 3 R) c).space = _
      have hb₀' : b₀ ∈ (connectedComponentComplex (boundaryComplex 3 R) c).space := hb₀
      rw [connectedComponentComplex_space] at hb₀' ⊢
      obtain ⟨p, hp, rfl⟩ := hb₀'
      rw [← hp, ← connectedComponentComplex_space, connectedComponentComplex_mk,
        restrict_connectedComponentIn_space]
    have hBRW : ∀ b ∈ B, b ∈ R.space ∩ W := fun b hb =>
      ⟨boundaryComplex_space_subset 3 R (hBsub hb), hBW hb⟩
    obtain ⟨⟨y₀, e⟩, ⟨hy₀, he⟩, hρb₀⟩ := hRW.subset (hBRW b₀ hb₀)
    refine exists_half_collar_of_eq_image_connectedComponentIn hρ hzero hRW hy₀ he ?_
    have hjc : ContinuousOn (fun y => ρ (y, e)) L.space :=
      hρ.isPiecewiseAffineOn.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
        fun y hy => ⟨hy, hpmI e he⟩
    apply Subset.antisymm
    · intro b hb
      set ψ := Function.invFunOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1)
      have hψc : ContinuousOn ψ W := hρ.isPiecewiseAffineOn_invFunOn.continuousOn
      have hψinv : ∀ z ∈ L.space ×ˢ Icc (-1 : ℝ) 1, ψ (ρ z) = z := fun z hz =>
        hρ.bijOn.invOn_invFunOn.1 hz
      have hρψ : ∀ w ∈ W, ρ (ψ w) = w := fun w hw => hρ.bijOn.invOn_invFunOn.2 hw
      have hψmem : ∀ b ∈ B, ψ b ∈ L.space ×ˢ ({-1, 1} : Set ℝ) := by
        intro b hb
        obtain ⟨z, hz, hzb⟩ := hRW.subset (hBRW b hb)
        rw [← hzb, hψinv z ⟨hz.1, hpmI z.2 hz.2⟩]
        exact hz
      have hψb₀ : ψ b₀ = (y₀, e) := by
        rw [← hρb₀]
        exact hψinv _ ⟨hy₀, hpmI e he⟩
      have h1 : (fun b => (ψ b).1) '' B ⊆ connectedComponentIn L.space y₀ :=
        IsPreconnected.subset_connectedComponentIn
          (hBconn.isPreconnected.image _ ((continuous_fst.comp_continuousOn hψc).mono hBW))
          ⟨b₀, hb₀, by change (ψ b₀).1 = y₀; rw [hψb₀]⟩
          (by rintro _ ⟨b, hb, rfl⟩; exact (hψmem b hb).1)
      have hoc : ((fun b => (ψ b).2) '' B).OrdConnected :=
        isPreconnected_iff_ordConnected.mp
          (hBconn.isPreconnected.image _ ((continuous_snd.comp_continuousOn hψc).mono hBW))
      have he₀ : e ∈ (fun b => (ψ b).2) '' B :=
        ⟨b₀, hb₀, by change (ψ b₀).2 = e; rw [hψb₀]⟩
      have h2 : (ψ b).2 = e := by
        have hbimg : (ψ b).2 ∈ (fun b => (ψ b).2) '' B := ⟨b, hb, rfl⟩
        have hb' : (ψ b).2 = -1 ∨ (ψ b).2 = 1 := (hψmem b hb).2
        have he' : e = -1 ∨ e = 1 := he
        by_contra hne
        have h0 : (0 : ℝ) ∈ (fun b => (ψ b).2) '' B := by
          rcases he' with rfl | rfl <;> rcases hb' with h | h
          · exact (hne h).elim
          · exact hoc.out he₀ hbimg ⟨by norm_num, by rw [h]; norm_num⟩
          · exact hoc.out hbimg he₀ ⟨by rw [h]; norm_num, by norm_num⟩
          · exact (hne h).elim
        obtain ⟨b', hb', h0'⟩ := h0
        have h0'' : (ψ b').2 = 0 := h0'
        have h3 : (ψ b').2 = -1 ∨ (ψ b').2 = 1 := (hψmem b' hb').2
        rw [h0''] at h3
        rcases h3 with h3 | h3 <;> norm_num at h3
      refine ⟨(ψ b).1, h1 ⟨b, hb, rfl⟩, ?_⟩
      change ρ ((ψ b).1, e) = b
      rw [← h2]
      exact hρψ b (hBW hb)
    · rw [hBcomp]
      apply IsPreconnected.subset_connectedComponentIn
      · exact isPreconnected_connectedComponentIn.image _
          (hjc.mono (connectedComponentIn_subset _ _))
      · exact ⟨y₀, mem_connectedComponentIn hy₀, hρb₀⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact hρR ⟨(y, e), ⟨connectedComponentIn_subset _ _ hy, he⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
