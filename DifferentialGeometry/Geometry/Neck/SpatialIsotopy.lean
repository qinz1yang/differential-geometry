import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Neck.FiniteSelection
import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false
noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology


universe u

theorem exists_spatial_neck_center_graph_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧
            (∀ q, (q, h q) ∈ univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ∧
            ∀ q, nk₁.map (q, h q) = nk₀.map (η q, 0) := by
  obtain ⟨eta₀, C, heta₀, _, hC, hvalue⟩ := exists_spatial_neck_anchored_overlap_estimates.{u}
  obtain ⟨eta₁, heta₁, _, hoverlap⟩ := exists_spatial_neck_intersection_tolerance.{u}
  let eta := min eta₀ (min eta₁ (1 / (4 * 369424)))
  have heta : 0 < eta := by dsimp only [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet
  have heps₀ : eps ≤ eta₀ := heps.trans (min_le_left _ _)
  have heps₁ : eps ≤ eta₁ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsG : eps ≤ 1 / (4 * 369424) :=
    heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨z, hz₀, hz₁⟩ := hmeet
  obtain ⟨σ, hσ, hest⟩ := hvalue eps heps₀ M g p₀ p₁ nk₀ nk₁ z hz₀ hz₁
  obtain ⟨_, _, _, hsub₁, _⟩ := hoverlap eps heps₁ M g p₀ p₁ nk₀ nk₁ ⟨z, hz₀, hz₁⟩
  let c := nk₀.cylindricalChart.axial z - σ * nk₁.cylindricalChart.axial z
  have hunit : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₀.eps_pos).mpr (nk₀.eps_small.trans (by norm_num))
  have hsection (q : Sphere 2) : (q, (0 : ℝ)) ∈ nk₀.cylindricalChart.domain :=
    ⟨mem_univ _, by constructor <;> linarith⟩
  have htarget (q : Sphere 2) :
      (nk₀.cylindricalChart.chart ⟨(q, (0 : ℝ)), hsection q⟩ : M) ∈
        nk₁.cylindricalChart.target := by
    have hh := hsub₁ (Or.inl ⟨(q, (0 : ℝ)), ⟨mem_univ _, by norm_num⟩, rfl⟩)
    apply (image_mono (show (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) : Set Cylinder) ⊆
        univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ from ?_)) hh
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hroot : Real.sqrt (1 + eps) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    linarith [nk₀.eps_small]
  have hgradsmall : (369424 * eps) * Real.sqrt (1 + eps) < 1 := by
    have hn := nk₀.eps_pos
    have hg := mul_le_mul_of_nonneg_left hroot (show 0 ≤ 369424 * eps by positivity)
    nlinarith
  obtain ⟨η, h, hh, hmem, heq, _⟩ :=
    nk₀.cylindricalChart.exists_graph_of_full_cross_section_and_gradient_close
      nk₁.cylindricalChart g 0 hsection htarget eps (by linarith [nk₀.eps_small])
      nk₁.cylindricalChart_metricCloseOn (fun _ => mem_univ _) σ c (369424 * eps)
      (C * eps / Real.sqrt (metricScalarAt g p₀)) hσ hgradsmall
      (fun q => (hest _ (Or.inl ⟨(q, (0 : ℝ)), ⟨mem_univ _, by norm_num⟩, rfl⟩)).2)
      (fun q => (hest _ (Or.inl ⟨(q, (0 : ℝ)), ⟨mem_univ _, by norm_num⟩, rfl⟩)).1)
  refine ⟨η, h, hh, ?_, heq⟩
  intro q
  have himage := hsub₁ (Or.inl ⟨(η q, (0 : ℝ)), ⟨mem_univ _, by norm_num⟩, rfl⟩)
  obtain ⟨y, hy, hyeq⟩ := himage
  have hySource : y ∈ nk₁.map.source := nk₁.domain
    ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  have hqSource : (q, h q) ∈ nk₁.map.source := nk₁.domain (hmem q)
  have he : y = (q, h q) := nk₁.map.injOn hySource hqSource (hyeq.trans (heq q).symm)
  exact he ▸ hy


theorem exists_spatial_neck_center_isotopy_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          ∃ (η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2) (h : Sphere 2 → ℝ),
            ContMDiff I2 𝓘(ℝ) ∞ h ∧
            let H := fun x : ℝ × Sphere 2 => nk₁.map (x.2, (1 - x.1) * h x.2)
            ContMDiffOn (𝓘(ℝ).prod I2) I3 ∞ H (Icc (0 : ℝ) 1 ×ˢ univ) ∧
            (∀ q, H (0, q) = nk₀.map (η q, 0)) ∧
            (∀ q, H (1, q) = nk₁.map (q, 0)) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, _root_.Topology.IsEmbedding (fun q => H (s, q))) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, ∀ q,
              Function.Injective (mfderiv I2 I3 (fun q => H (s, q)) q)) ∧
            ∀ x ∈ Icc (0 : ℝ) 1 ×ˢ univ,
              H x ∈ nk₁.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) := by
  obtain ⟨eta, heta, hgraph⟩ := exists_spatial_neck_center_graph_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet
  obtain ⟨η, h, hh, hmem, heq⟩ := hgraph eps heps M g p₀ p₁ nk₀ nk₁ hmeet
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk₁.eps_pos).mpr (nk₁.eps_small.trans (by norm_num))
  have hzero : (0 : ℝ) ∈ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) := by
    constructor <;> linarith
  have hinside (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (q : Sphere 2) :
      (q, (1 - s) * h q) ∈ univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1) := by
    refine ⟨mem_univ _, ?_⟩
    have hc := (convex_Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1))
      (hmem q).2 hzero (sub_nonneg.mpr hs.2) hs.1 (by ring : (1 - s) + s = 1)
    simpa only [smul_eq_mul, mul_zero, add_zero] using hc
  have hsource (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (q : Sphere 2) :
      (q, (1 - s) * h q) ∈ nk₁.map.source := by
    have hx := hinside s hs q
    exact nk₁.domain ⟨hx.1, by constructor <;> linarith [hx.2.1, hx.2.2]⟩
  let H := fun x : ℝ × Sphere 2 => nk₁.map (x.2, (1 - x.1) * h x.2)
  have hcoordinates : ContMDiff (𝓘(ℝ).prod I2) IC ∞
      (fun x : ℝ × Sphere 2 => (x.2, (1 - x.1) * h x.2)) :=
    contMDiff_snd.prodMk ((contMDiff_const.sub contMDiff_fst).mul (hh.comp contMDiff_snd))
  have hH : ContMDiffOn (𝓘(ℝ).prod I2) I3 ∞ H (Icc (0 : ℝ) 1 ×ˢ univ) :=
    nk₁.map.contMDiffOn_toFun.comp hcoordinates.contMDiffOn (fun x hx => hsource x.1 hx.1 x.2)
  refine ⟨η, h, hh, hH, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    simpa only [H, sub_zero, one_mul] using heq q
  · intro q
    dsimp only [H]
    rw [sub_self, zero_mul]
  · intro s hs
    have hcoord : Continuous (fun q : Sphere 2 => (q, (1 - s) * h q)) :=
      continuous_id.prodMk (continuous_const.mul hh.continuous)
    have hc : Continuous (fun q => H (s, q)) :=
      nk₁.map.contMDiffOn_toFun.continuousOn.comp_continuous hcoord (hsource s hs)
    apply (hc.isClosedEmbedding ?_).isEmbedding
    intro q r heq
    have hc := nk₁.map.injOn (hsource s hs q) (hsource s hs r) heq
    exact congrArg Prod.fst hc
  · intro s hs q
    let f : Sphere 2 → Cylinder := fun q => (q, (1 - s) * h q)
    have hf : ContMDiff I2 IC ∞ f :=
      contMDiff_id.prodMk (contMDiff_const.mul hh)
    have hderiv := mfderiv_comp q
      (mdifferentiableAt_fst : MDifferentiableAt IC I2 Prod.fst (f q))
      (hf.mdifferentiable (by simp) q)
    have hcomp : Prod.fst ∘ f = id := rfl
    rw [hcomp, mfderiv_id] at hderiv
    have hinj : Function.Injective (mfderiv I2 IC f q) := by
      intro v w hvw
      have hv := DFunLike.congr_fun hderiv v
      have hw := DFunLike.congr_fun hderiv w
      change v = (mfderiv IC I2 Prod.fst (f q)) (mfderiv I2 IC f q v) at hv
      change w = (mfderiv IC I2 Prod.fst (f q)) (mfderiv I2 IC f q w) at hw
      exact hv.trans ((congrArg (mfderiv IC I2 Prod.fst (f q)) hvw).trans hw.symm)
    change Function.Injective (mfderiv I2 I3 (nk₁.map ∘ f) q)
    rw [mfderiv_comp q (nk₁.map.mdifferentiableAt (by simp) (hsource s hs q))
      (hf.mdifferentiable (by simp) q)]
    have hmd : nk₁.map.toOpenPartialHomeomorph.MDifferentiable IC I3 :=
      ⟨nk₁.map.contMDiffOn_toFun.mdifferentiableOn (by simp),
        nk₁.map.contMDiffOn_invFun.mdifferentiableOn (by simp)⟩
    exact (hmd.mfderiv_injective (hsource s hs q)).comp hinj
  · intro x hx
    exact ⟨(x.2, (1 - x.1) * h x.2), hinside x.1 hx.1 x.2, rfl⟩

private theorem SpatialNeck.continuous_center_sphere
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p) :
    Continuous (fun q : Sphere 2 => nk.map (q, 0)) := by
  apply nk.map.contMDiffOn_toFun.continuousOn.comp_continuous
    (continuous_id.prodMk continuous_const)
  intro q
  exact nk.domain ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos), inv_pos.mpr nk.eps_pos⟩


theorem exists_spatial_neck_center_homotopy_tolerance :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (p₀ p₁ : M)
          (nk₀ : SpatialNeck g eps p₀) (nk₁ : SpatialNeck g eps p₁),
          (nk₀.map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
            nk₁.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty →
          ∃ η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
            (⟨fun q => nk₀.map (η q, 0),
              nk₀.continuous_center_sphere.comp η.continuous⟩ : C(Sphere 2, M)).Homotopic
                ⟨fun q => nk₁.map (q, 0), nk₁.continuous_center_sphere⟩ := by
  obtain ⟨eta, heta, hisotopy⟩ := exists_spatial_neck_center_isotopy_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g p₀ p₁ nk₀ nk₁ hmeet
  obtain ⟨η, h, _, hH, hzero, hone, _, _, _⟩ :=
    hisotopy eps heps M g p₀ p₁ nk₀ nk₁ hmeet
  refine ⟨η, ⟨{
    toFun := fun x => nk₁.map (x.2, (1 - (x.1 : ℝ)) * h x.2)
    continuous_toFun := ?_
    map_zero_left := hzero
    map_one_left := hone }⟩⟩
  exact hH.continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    (fun x => ⟨x.1.property, mem_univ _⟩)


private theorem SpatialNeck.center_mem_buffer
    {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
    {g : SmoothRiemannianMetric I3 M} {eps : ℝ} {p : M} (nk : SpatialNeck g eps p)
    (q : Sphere 2) :
    nk.map (q, 0) ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) := by
  have hlen : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  exact ⟨(q, 0), ⟨mem_univ _, by constructor <;> linarith⟩, rfl⟩


set_option backward.isDefEq.respectTransparency false in
theorem exists_spatial_neck_centers_homotopic_in_region :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C U : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p),
          (∀ p (hp : p ∈ C), (neck p hp).map ''
            (univ ×ˢ Ioo (-eps⁻¹ + 1) (eps⁻¹ - 1)) ⊆ U) →
          ∀ a b : C, ∃ η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
            ∃ H : ContinuousMap.Homotopy
              (⟨fun q => (neck a a.property).map (η q, 0),
                (neck a a.property).continuous_center_sphere.comp η.continuous⟩ : C(Sphere 2, M))
              ⟨fun q => (neck b b.property).map (q, 0),
                (neck b b.property).continuous_center_sphere⟩,
              ∀ x, H x ∈ U := by
  obtain ⟨eta, heta, hiso⟩ := exists_spatial_neck_center_isotopy_tolerance.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g C U hC neck hbuffer a b
  let f (p : C) : C(Sphere 2, M) :=
    ⟨fun q => (neck p p.property).map (q, 0), (neck p p.property).continuous_center_sphere⟩
  have hstep (a b : C)
      (hinter : ((neck a a.property).map '' (univ ×ˢ Icc (-1 : ℝ) 1) ∩
        (neck b b.property).map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty) :
      ∃ η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
        ∃ H : ContinuousMap.Homotopy ((f a).comp ⟨η, η.continuous⟩) (f b), ∀ x, H x ∈ U := by
    obtain ⟨η, h, _, hH, hzero, hone, _, _, hmem⟩ :=
      hiso eps heps M g a b (neck a a.property) (neck b b.property) hinter
    let H : ContinuousMap.Homotopy ((f a).comp ⟨η, η.continuous⟩) (f b) := {
      toFun := fun x => (neck b b.property).map (x.2, (1 - (x.1 : ℝ)) * h x.2)
      continuous_toFun := hH.continuousOn.comp_continuous
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun x => ⟨x.1.property, mem_univ _⟩)
      map_zero_left := hzero
      map_one_left := hone }
    exact ⟨η, H, fun x => hbuffer b b.property (hmem ((x.1 : ℝ), x.2) ⟨x.1.property, mem_univ _⟩)⟩
  obtain ⟨n, p, hfirst, hlast, _, hmeet, _⟩ :=
    exists_spatial_neck_chain_with_disjoint_nonadjacent_slabs g hC neck a b
  have hind (k : ℕ) (hk : k ≤ n) :
      ∃ η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
        ∃ H : ContinuousMap.Homotopy ((f (p 0)).comp ⟨η, η.continuous⟩)
          (f (p ⟨k, by omega⟩)), ∀ x, H x ∈ U := by
    induction k with
    | zero =>
      exact ⟨Diffeomorph.refl I2 (Sphere 2) ∞, ContinuousMap.Homotopy.refl (f (p 0)),
        fun x => hbuffer (p 0) (p 0).property ((neck (p 0) (p 0).property).center_mem_buffer x.2)⟩
    | succ k ih =>
      obtain ⟨η, H, hH⟩ := ih (by omega)
      let j : Fin n := ⟨k, by omega⟩
      obtain ⟨ξ, G, hG⟩ := hstep (p j.castSucc) (p j.succ) (hmeet j)
      refine ⟨ξ.trans η, (H.compContinuousMap ⟨ξ, ξ.continuous⟩).trans G, ?_⟩
      intro x
      have hx := ContinuousMap.Homotopy.trans_apply
        (H.compContinuousMap (⟨ξ, ξ.continuous⟩ : C(Sphere 2, Sphere 2))) G x
      rw [hx]
      split_ifs
      · exact hH _
      · exact hG _
  obtain ⟨η, H, hH⟩ := hind n le_rfl
  have heq : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext rfl
  let HH := H.cast (by rw [hfirst]) (by rw [heq, hlast])
  refine ⟨η, HH, ?_⟩
  intro x
  simpa only [HH, ContinuousMap.Homotopy.cast_apply] using hH x

theorem exists_spatial_neck_centers_homotopic_of_preconnected :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ eps : ℝ, eps ≤ eta →
        ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
          [IsManifold I3 ∞ M] [T2Space M]
          (g : SmoothRiemannianMetric I3 M) (C : Set M), IsPreconnected C →
          ∀ (neck : ∀ p ∈ C, SpatialNeck g eps p) (a b : C),
          ∃ η : Sphere 2 ≃ₘ⟮I2, I2⟯ Sphere 2,
            (⟨fun q => (neck a a.property).map (η q, 0),
              (neck a a.property).continuous_center_sphere.comp η.continuous⟩ :
                C(Sphere 2, M)).Homotopic
                ⟨fun q => (neck b b.property).map (q, 0),
                  (neck b b.property).continuous_center_sphere⟩ := by
  obtain ⟨eta, heta, hhom⟩ := exists_spatial_neck_centers_homotopic_in_region.{u}
  refine ⟨eta, heta, ?_⟩
  intro eps heps M _ _ _ _ g C hC neck a b
  obtain ⟨η, H, _⟩ := hhom eps heps M g C univ hC neck (fun _ _ => subset_univ _) a b
  exact ⟨η, ⟨H⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
