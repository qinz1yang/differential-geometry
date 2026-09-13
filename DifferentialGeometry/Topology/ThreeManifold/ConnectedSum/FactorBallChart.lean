import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.AssemblyReduction
import DifferentialGeometry.Topology.Manifold.BallChartAffine
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u v

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_disjointBallChart_closedBall {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (c : BallChart 3 (𝓡 3) M) :
    ∃ d δ : BallChart 3 (𝓡 3) M,
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        d.chart x ∉ δ.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 2,
        δ.chart x ∉ d.chart '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  classical
  set s₁ : E3 := (3 / 2 : ℝ) • EuclideanSpace.single 0 1 with hs₁
  have hnorm : ‖s₁‖ = 3 / 2 := by
    rw [hs₁, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
    simp
  have hs : ‖s₁‖ + 2 * (1 / 8) ≤ 2 := by
    rw [hnorm]; norm_num
  have h0 : ‖(0 : E3)‖ + 2 * (1 / 8) ≤ 2 := by norm_num
  have hsc : ∀ u : E3, ‖(1 / 8 : ℝ) • u‖ = 1 / 8 * ‖u‖ := by
    intro u
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 8)]
  have hfar : ∀ u : E3, ‖u‖ ≤ 2 → ‖s₁ + (1 / 8 : ℝ) • u‖ ≤ 2 := by
    intro u hu
    calc ‖s₁ + (1 / 8 : ℝ) • u‖ ≤ ‖s₁‖ + ‖(1 / 8 : ℝ) • u‖ :=
          norm_add_le _ _
      _ = 3 / 2 + 1 / 8 * ‖u‖ := by rw [hnorm, hsc]
      _ ≤ 2 := by nlinarith
  have hnear : ∀ u : E3, ‖u‖ ≤ 2 → ‖(1 / 8 : ℝ) • u‖ ≤ 2 := by
    intro u hu
    rw [hsc]
    nlinarith
  refine ⟨c.affine s₁ (1 / 8) (by norm_num) hs, c.affine 0 (1 / 8) (by norm_num) h0,
    ?_, ?_⟩
  · intro x hx hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy1 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have h1 : s₁ + (1 / 8 : ℝ) • x ∈ c.chart.source :=
      c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar x hx2)
    have h2 : (1 / 8 : ℝ) • y ∈ c.chart.source :=
      c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear y (by linarith))
    have hinj : s₁ + (1 / 8 : ℝ) • x = (1 / 8 : ℝ) • y :=
      c.chart.toPartialEquiv.injOn h1 h2 (by
        simpa only [BallChart.affine_apply, zero_add] using hyx.symm)
    have hdiff : s₁ = (1 / 8 : ℝ) • (y - x) := by
      rw [smul_sub, ← hinj]
      abel
    have hb : ‖s₁‖ ≤ 3 / 8 := by
      rw [hdiff, hsc]
      have hsub : ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
      have h3 : ‖y - x‖ ≤ 3 := by linarith
      have h4 : (1 / 8 : ℝ) * ‖y - x‖ ≤ (1 / 8 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    rw [hnorm] at hb
    norm_num at hb
  · intro x hx hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy1 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have h1 : (1 / 8 : ℝ) • x ∈ c.chart.source :=
      c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear x hx2)
    have h2 : s₁ + (1 / 8 : ℝ) • y ∈ c.chart.source :=
      c.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar y (by linarith))
    have hinj : (1 / 8 : ℝ) • x = s₁ + (1 / 8 : ℝ) • y :=
      c.chart.toPartialEquiv.injOn h1 h2 (by
        simpa only [BallChart.affine_apply, zero_add] using hyx.symm)
    have hdiff : s₁ = (1 / 8 : ℝ) • (x - y) := by
      rw [smul_sub, hinj]
      abel
    have hb : ‖s₁‖ ≤ 3 / 8 := by
      rw [hdiff, hsc]
      have hsub : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      have h3 : ‖x - y‖ ≤ 3 := by linarith
      have h4 : (1 / 8 : ℝ) * ‖x - y‖ ≤ (1 / 8 : ℝ) * 3 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
    rw [hnorm] at hb
    norm_num at hb

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

universe u v

namespace ConnectedSumQuotient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N]

theorem exists_ballChart_inr (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) (d' : BallChart 3 (𝓡 3) N)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : csModel) 2,
      d'.chart x ∉ d.chart '' Metric.closedBall (0 : csModel) 1) :
    letI := csChartedSpace c d a.toHomeomorph
    letI := csIsManifold c d a.toHomeomorph (contDiffOn_reflectMap a) (contDiffOn_reflectMapInv a)
    ∃ f : BallChart 3 (𝓡 3) (ConnectedSumQuotient c d a.toHomeomorph),
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        ∃ hx : d'.chart x ∉ d.chart '' Metric.ball (0 : csModel) 1,
          f.chart x = inr c d a.toHomeomorph ⟨d'.chart x, hx⟩ := by
  let _ := csChartedSpace c d a.toHomeomorph
  let _ := csIsManifold c d a.toHomeomorph (contDiffOn_reflectMap a) (contDiffOn_reflectMapInv a)
  classical
  have hclosedImage : IsClosed (d.chart '' Metric.closedBall (0 : csModel) 1) :=
    d.isCompact_closedBall_image.isClosed
  have hopenImage : IsOpen ((d.chart '' Metric.closedBall (0 : csModel) 1)ᶜ) :=
    hclosedImage.isOpen_compl
  let W : Set csModel :=
    d'.chart.source ∩ d'.chart ⁻¹' ((d.chart '' Metric.closedBall (0 : csModel) 1)ᶜ)
  have hWopen : IsOpen W :=
    d'.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d'.chart.open_source hopenImage
  have hWclosed : Metric.closedBall (0 : csModel) 2 ⊆ W := by
    intro x hx
    exact ⟨d'.closedBall_subset_source hx, hdisj x hx⟩
  have hne : W.Nonempty :=
    ⟨0, hWclosed (Metric.mem_closedBall_self (by norm_num))⟩
  have hmemW : ∀ {x : csModel}, x ∈ W →
      d'.chart x ∉ d.chart '' Metric.ball (0 : csModel) 1 := fun hx hb =>
    hx.2 (Set.image_mono Metric.ball_subset_closedBall hb)
  let z₀ : csSphere := Classical.choice (nonempty_sphere_of_neZero (n := 3))
  let u : csModel → ConnectedSumQuotient c d a.toHomeomorph := fun x =>
    if h : x ∈ W then inr c d a.toHomeomorph ⟨d'.chart x, hmemW h⟩
    else inr c d a.toHomeomorph (d.boundaryMap z₀)
  have huW : ∀ x (hx : x ∈ W),
      u x = inr c d a.toHomeomorph ⟨d'.chart x, hmemW hx⟩ := by
    intro x hx
    simp only [u, dif_pos hx]
  have hinj : Set.InjOn u W := by
    intro x hx y hy hxy
    have h1 : (⟨d'.chart x, hmemW hx⟩ : d.Punctured) = ⟨d'.chart y, hmemW hy⟩ :=
      inr_injective c d a.toHomeomorph (by rw [← huW x hx, ← huW y hy]; exact hxy)
    exact d'.chart.toPartialEquiv.injOn hx.1 hy.1 (congrArg Subtype.val h1)
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ u W := by
    intro x
    obtain ⟨x, hxW⟩ := x
    have hxsrc : x ∈ d'.chart.source := hxW.1
    have hxint : d'.chart x ∈ d.interior := hxW.2
    let g : OpenPartialHomeomorph N csModel := chartAt csModel (d'.chart x)
    have hgmem : g ∈ atlas csModel N := chart_mem_atlas csModel (d'.chart x)
    let L : OpenPartialHomeomorph csModel (ConnectedSumQuotient c d a.toHomeomorph) :=
      rightChart c d a.toHomeomorph hn3 g
    have hLmem : L.symm ∈ atlas csModel (ConnectedSumQuotient c d a.toHomeomorph) :=
      OrientationAssembly.mem_atlas_rightChart c d a.toHomeomorph g hgmem
    have hLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
      contMDiffOn_rightChart c d a g hLmem
    have hLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
      contMDiffOn_rightChart_symm c d a g hLmem
    have hgon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g g.source := contMDiffOn_chart_of_mem g hgmem
    have hgsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g.symm g.target :=
      contMDiffOn_chart_symm_of_mem g hgmem
    have hqg : d'.chart x ∈ g.source := mem_chart_source csModel (d'.chart x)
    have hgq : g (d'.chart x) ∈ L.source := ⟨d'.chart x, ⟨hqg, hxint⟩, rfl⟩
    have hqT : d'.chart x ∈ (g.trans L).source := ⟨hqg, hgq⟩
    have hTLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g.trans L) (g.trans L).source :=
      hLon.comp (hgon.mono inter_subset_left) (fun y hy => hy.2)
    have hTLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g.trans L).symm (g.trans L).target := by
      have hmap : MapsTo L.symm (g.trans L).target g.target := fun z hz => hz.2
      exact hgsymm.comp (hLsymm.mono inter_subset_left) hmap
    have hm : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun y => L (g y)) (d'.chart x) :=
      OpenPartialHomeomorph.isLocalDiffeomorphAt_of_contMDiffOn hTLon hTLsymm hqT
    have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => L (g (d'.chart y))) x :=
      (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ d'.chart hxsrc).comp
        (K := 𝓡 3) (P := ConnectedSumQuotient c d a.toHomeomorph) hm
    have hLg : ∀ (p : d.Punctured), (p : N) ∈ g.source → (p : N) ∈ d.interior →
        L (g (p : N)) = inr c d a.toHomeomorph p := by
      intro p hgs hgi
      have hmem : p ∈ rightRegion d g := ⟨hgs, hgi⟩
      have htarget : inr c d a.toHomeomorph p ∈ L.target := by
        rw [rightChart_target]
        exact ⟨p, hmem, rfl⟩
      rw [← rightChart_symm_apply_inr c d a.toHomeomorph hn3 g hmem]
      exact L.right_inv htarget
    have hgcont : ContinuousAt d'.chart x :=
      d'.chart.contMDiffOn_toFun.continuousOn.continuousAt
        (d'.chart.open_source.mem_nhds hxsrc)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
    have h1 : W ∈ 𝓝 x := hWopen.mem_nhds hxW
    have h2 : d'.chart ⁻¹' (g.source ∩ (d.interior : Set N)) ∈ 𝓝 x :=
      hgcont.preimage_mem_nhds ((g.open_source.inter d.interior.isOpen).mem_nhds ⟨hqg, hxint⟩)
    filter_upwards [h1, h2] with y hyW hyg
    rw [huW y hyW]
    exact (hLg ⟨d'.chart y, hmemW hyW⟩ hyg.1 hyW.2).symm
  obtain ⟨Φ, hsrc, -, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hWopen hne hinj
  refine ⟨⟨Φ, ?_⟩, ?_⟩
  · rw [hsrc]
    exact hWclosed
  · intro x hx
    exact ⟨hmemW (hWclosed hx), by rw [hfun, huW x (hWclosed hx)]⟩


theorem exists_ballChart_inl (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) (c' : BallChart 3 (𝓡 3) M)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : csModel) 2,
      c'.chart x ∉ c.chart '' Metric.closedBall (0 : csModel) 1) :
    letI := csChartedSpace c d a.toHomeomorph
    letI := csIsManifold c d a.toHomeomorph (contDiffOn_reflectMap a) (contDiffOn_reflectMapInv a)
    ∃ f : BallChart 3 (𝓡 3) (ConnectedSumQuotient c d a.toHomeomorph),
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        ∃ hx : c'.chart x ∉ c.chart '' Metric.ball (0 : csModel) 1,
          f.chart x = inl c d a.toHomeomorph ⟨c'.chart x, hx⟩ := by
  let _ := csChartedSpace c d a.toHomeomorph
  let _ := csIsManifold c d a.toHomeomorph (contDiffOn_reflectMap a) (contDiffOn_reflectMapInv a)
  classical
  have hclosedImage : IsClosed (c.chart '' Metric.closedBall (0 : csModel) 1) :=
    c.isCompact_closedBall_image.isClosed
  have hopenImage : IsOpen ((c.chart '' Metric.closedBall (0 : csModel) 1)ᶜ) :=
    hclosedImage.isOpen_compl
  let W : Set csModel :=
    c'.chart.source ∩ c'.chart ⁻¹' ((c.chart '' Metric.closedBall (0 : csModel) 1)ᶜ)
  have hWopen : IsOpen W :=
    c'.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c'.chart.open_source hopenImage
  have hWclosed : Metric.closedBall (0 : csModel) 2 ⊆ W := by
    intro x hx
    exact ⟨c'.closedBall_subset_source hx, hdisj x hx⟩
  have hne : W.Nonempty :=
    ⟨0, hWclosed (Metric.mem_closedBall_self (by norm_num))⟩
  have hmemW : ∀ {x : csModel}, x ∈ W →
      c'.chart x ∉ c.chart '' Metric.ball (0 : csModel) 1 := fun hx hb =>
    hx.2 (Set.image_mono Metric.ball_subset_closedBall hb)
  let z₀ : csSphere := Classical.choice (nonempty_sphere_of_neZero (n := 3))
  let u : csModel → ConnectedSumQuotient c d a.toHomeomorph := fun x =>
    if h : x ∈ W then inl c d a.toHomeomorph ⟨c'.chart x, hmemW h⟩
    else inl c d a.toHomeomorph (c.boundaryMap z₀)
  have huW : ∀ x (hx : x ∈ W),
      u x = inl c d a.toHomeomorph ⟨c'.chart x, hmemW hx⟩ := by
    intro x hx
    simp only [u, dif_pos hx]
  have hinj : Set.InjOn u W := by
    intro x hx y hy hxy
    have h1 : (⟨c'.chart x, hmemW hx⟩ : c.Punctured) = ⟨c'.chart y, hmemW hy⟩ :=
      inl_injective c d a.toHomeomorph (by rw [← huW x hx, ← huW y hy]; exact hxy)
    exact c'.chart.toPartialEquiv.injOn hx.1 hy.1 (congrArg Subtype.val h1)
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ u W := by
    intro x
    obtain ⟨x, hxW⟩ := x
    have hxsrc : x ∈ c'.chart.source := hxW.1
    have hxint : c'.chart x ∈ c.interior := hxW.2
    let g : OpenPartialHomeomorph M csModel := chartAt csModel (c'.chart x)
    have hgmem : g ∈ atlas csModel M := chart_mem_atlas csModel (c'.chart x)
    let L : OpenPartialHomeomorph csModel (ConnectedSumQuotient c d a.toHomeomorph) :=
      leftChart c d a.toHomeomorph hn3 g
    have hLmem : L.symm ∈ atlas csModel (ConnectedSumQuotient c d a.toHomeomorph) :=
      OrientationAssembly.mem_atlas_leftChart c d a.toHomeomorph g hgmem
    have hLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
      contMDiffOn_leftChart c d a g hLmem
    have hLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
      contMDiffOn_leftChart_symm c d a g hLmem
    have hgon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g g.source := contMDiffOn_chart_of_mem g hgmem
    have hgsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ g.symm g.target :=
      contMDiffOn_chart_symm_of_mem g hgmem
    have hqg : c'.chart x ∈ g.source := mem_chart_source csModel (c'.chart x)
    have hgq : g (c'.chart x) ∈ L.source := ⟨c'.chart x, ⟨hqg, hxint⟩, rfl⟩
    have hqT : c'.chart x ∈ (g.trans L).source := ⟨hqg, hgq⟩
    have hTLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g.trans L) (g.trans L).source :=
      hLon.comp (hgon.mono inter_subset_left) (fun y hy => hy.2)
    have hTLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (g.trans L).symm (g.trans L).target := by
      have hmap : MapsTo L.symm (g.trans L).target g.target := fun z hz => hz.2
      exact hgsymm.comp (hLsymm.mono inter_subset_left) hmap
    have hm : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (fun y => L (g y)) (c'.chart x) :=
      OpenPartialHomeomorph.isLocalDiffeomorphAt_of_contMDiffOn hTLon hTLsymm hqT
    have hcomp : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
        (fun y => L (g (c'.chart y))) x :=
      (PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c'.chart hxsrc).comp
        (K := 𝓡 3) (P := ConnectedSumQuotient c d a.toHomeomorph) hm
    have hLg : ∀ (p : c.Punctured), (p : M) ∈ g.source → (p : M) ∈ c.interior →
        L (g (p : M)) = inl c d a.toHomeomorph p := by
      intro p hgs hgi
      have hmem : p ∈ leftRegion c g := ⟨hgs, hgi⟩
      have htarget : inl c d a.toHomeomorph p ∈ L.target := by
        rw [leftChart_target]
        exact ⟨p, hmem, rfl⟩
      rw [← leftChart_symm_apply_inl c d a.toHomeomorph hn3 g hmem]
      exact L.right_inv htarget
    have hgcont : ContinuousAt c'.chart x :=
      c'.chart.contMDiffOn_toFun.continuousOn.continuousAt
        (c'.chart.open_source.mem_nhds hxsrc)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
    have h1 : W ∈ 𝓝 x := hWopen.mem_nhds hxW
    have h2 : c'.chart ⁻¹' (g.source ∩ (c.interior : Set M)) ∈ 𝓝 x :=
      hgcont.preimage_mem_nhds ((g.open_source.inter c.interior.isOpen).mem_nhds ⟨hqg, hxint⟩)
    filter_upwards [h1, h2] with y hyW hyg
    rw [huW y hyW]
    exact (hLg ⟨c'.chart y, hmemW hyW⟩ hyg.1 hyW.2).symm
  obtain ⟨Φ, hsrc, -, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hWopen hne hinj
  refine ⟨⟨Φ, ?_⟩, ?_⟩
  · rw [hsrc]
    exact hWclosed
  · intro x hx
    exact ⟨hmemW (hWclosed hx), by rw [hfun, huW x (hWclosed hx)]⟩

end ConnectedSumQuotient
end DifferentialGeometry.Topology
