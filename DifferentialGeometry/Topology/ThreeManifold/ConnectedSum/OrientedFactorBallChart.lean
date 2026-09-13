import DifferentialGeometry.Topology.Manifold.BallChartAffine
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransportConnected
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.OrientedTransport

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology Filter Metric
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.ConnectedSumQuotient

namespace DifferentialGeometry.Topology

universe u v u' v'

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem exists_disjointOrientedBallChart_closedBall {M : ClosedOrientedManifold.{u} 3}
    (c : OrientedBallChart M) :
    ∃ d δ : OrientedBallChart M,
      (∀ x ∈ Metric.closedBall (0 : E3) 2,
        d.chart x ∉ δ.chart '' Metric.closedBall (0 : E3) 1) ∧
      (∀ x ∈ Metric.closedBall (0 : E3) 2,
        δ.chart x ∉ d.chart '' Metric.closedBall (0 : E3) 1) := by
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
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar x hx2)
    have h2 : (1 / 8 : ℝ) • y ∈ c.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear y (by linarith))
    have hinj : s₁ + (1 / 8 : ℝ) • x = (1 / 8 : ℝ) • y :=
      c.toBallChart.chart.toPartialEquiv.injOn h1 h2 (by
        simpa only [OrientedBallChart.affine_apply, zero_add] using hyx.symm)
    have hdiff : s₁ = (1 / 8 : ℝ) • (y - x) := by
      rw [smul_sub, ← hinj]
      abel
    have hb : ‖s₁‖ ≤ 3 / 8 := by
      rw [hdiff, hsc]
      have h3 : ‖y - x‖ ≤ 3 := by
        linarith [norm_sub_le y x]
      nlinarith
    rw [hnorm] at hb
    norm_num at hb
  · intro x hx hmem
    obtain ⟨y, hy, hyx⟩ := hmem
    have hx2 : ‖x‖ ≤ 2 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hy1 : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hy
    have h1 : (1 / 8 : ℝ) • x ∈ c.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hnear x hx2)
    have h2 : s₁ + (1 / 8 : ℝ) • y ∈ c.chart.source :=
      c.toBallChart.closedBall_subset_source (by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfar y (by linarith))
    have hinj : (1 / 8 : ℝ) • x = s₁ + (1 / 8 : ℝ) • y :=
      c.toBallChart.chart.toPartialEquiv.injOn h1 h2 (by
        simpa only [OrientedBallChart.affine_apply, zero_add] using hyx.symm)
    have hdiff : s₁ = (1 / 8 : ℝ) • (x - y) := by
      rw [smul_sub, hinj]
      abel
    have hb : ‖s₁‖ ≤ 3 / 8 := by
      rw [hdiff, hsc]
      have h3 : ‖x - y‖ ≤ 3 := by
        linarith [norm_sub_le x y]
      nlinarith
    rw [hnorm] at hb
    norm_num at hb

namespace ConnectedSumQuotient

variable {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}

theorem exists_orientedBallChart_inr
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
    (d' : OrientedBallChart N.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : csModel) 2,
      d'.chart x ∉ d.chart '' Metric.closedBall (0 : csModel) 1) :
    ∃ f : OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        ∃ hx : d'.chart x ∉ d.chart '' Metric.ball (0 : csModel) 1,
          f.toBallChart.chart x = inr c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨d'.chart x, hx⟩ := by
  let _ : ChartedSpace csModel
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph (contDiffOn_reflectMap a.1)
      (contDiffOn_reflectMapInv a.1)
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
  let Wop : TopologicalSpace.Opens csModel := ⟨W, hWopen⟩
  let z₀ : csSphere := Classical.choice (nonempty_sphere_of_neZero (n := 3))
  let u : csModel → ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph := fun x =>
    if h : x ∈ W then inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨d'.chart x, hmemW h⟩
    else inr c.toBallChart d.toBallChart a.1.toHomeomorph (d.boundaryMap z₀)
  have huW : ∀ x (hx : x ∈ W),
      u x = inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨d'.chart x, hmemW hx⟩ := by
    intro x hx
    simp only [u, dif_pos hx]
  have hinj : Set.InjOn u W := by
    intro x hx y hy hxy
    have h1 : (⟨d'.chart x, hmemW hx⟩ : d.Punctured) = ⟨d'.chart y, hmemW hy⟩ :=
      inr_injective c.toBallChart d.toBallChart a.1.toHomeomorph
        (by rw [← huW x hx, ← huW y hy]; exact hxy)
    exact d'.chart.toPartialEquiv.injOn hx.1 hy.1 (congrArg Subtype.val h1)
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ u W := by
    intro x
    obtain ⟨x, hxW⟩ := x
    have hxsrc : x ∈ d'.chart.source := hxW.1
    have hxint : d'.chart x ∈ d.interior := hxW.2
    let g : OpenPartialHomeomorph N.Carrier csModel := chartAt csModel (d'.chart x)
    have hgmem : g ∈ atlas csModel N.Carrier := chart_mem_atlas csModel (d'.chart x)
    let L : OpenPartialHomeomorph csModel
        (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
      rightChart c.toBallChart d.toBallChart a.1.toHomeomorph hn3 g
    have hLmem : L.symm ∈ atlas csModel
        (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
      OrientationAssembly.mem_atlas_rightChart c.toBallChart d.toBallChart a.1.toHomeomorph g hgmem
    have hLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
      contMDiffOn_rightChart c.toBallChart d.toBallChart a.1 g hLmem
    have hLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
      contMDiffOn_rightChart_symm c.toBallChart d.toBallChart a.1 g hLmem
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
        (K := 𝓡 3) (P := ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) hm
    have hLg : ∀ (p : d.Punctured), (p : N.Carrier) ∈ g.source →
        (p : N.Carrier) ∈ d.interior →
        L (g (p : N.Carrier)) = inr c.toBallChart d.toBallChart a.1.toHomeomorph p := by
      intro p hgs hgi
      have hmem : p ∈ rightRegion d.toBallChart g := ⟨hgs, hgi⟩
      have htarget : inr c.toBallChart d.toBallChart a.1.toHomeomorph p ∈ L.target := by
        rw [rightChart_target]
        exact ⟨p, hmem, rfl⟩
      rw [← rightChart_symm_apply_inr c.toBallChart d.toBallChart a.1.toHomeomorph hn3 g hmem]
      exact L.right_inv htarget
    have hgcont : ContinuousAt d'.chart x :=
      d'.chart.contMDiffOn_toFun.continuousOn.continuousAt
        (d'.chart.open_source.mem_nhds hxsrc)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
    have h1 : W ∈ 𝓝 x := hWopen.mem_nhds hxW
    have h2 : d'.chart ⁻¹' (g.source ∩ (d.interior : Set N.Carrier)) ∈ 𝓝 x :=
      hgcont.preimage_mem_nhds ((g.open_source.inter d.interior.isOpen).mem_nhds ⟨hqg, hxint⟩)
    filter_upwards [h1, h2] with y hyW hyg
    rw [huW y hyW]
    exact (hLg ⟨d'.chart y, hmemW hyW⟩ hyg.1 hyW.2).symm
  obtain ⟨Ψ, hsrc, -, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hWopen hne hinj
  have hval : ∀ x (hx : x ∈ W), Ψ x =
      interiorRight c.toBallChart d.toBallChart a.1 ⟨d'.chart x, hx.2⟩ := by
    intro x hx
    rw [hfun, huW x hx]
    exact congrArg (inr c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext rfl)
  refine ⟨{ toBallChart := ⟨Ψ, ?_⟩, preserves_orientation := ?_ }, ?_⟩
  · rw [hsrc]
    exact hWclosed
  · intro x hx
    have hxW : x ∈ W := hsrc ▸ hx
    have hx' : x ∈ d'.chart.source := hxW.1
    have h0δ : d'.chart (0 : csModel) ∈ d.interior :=
      hdisj 0 (Metric.mem_closedBall_self (by norm_num))
    let ι' : csModel → d.interior := fun y =>
      if h : y ∈ W then (⟨d'.chart y, h.2⟩ : d.interior)
      else (⟨d'.chart (0 : csModel), h0δ⟩ : d.interior)
    let u' : csModel → ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph :=
      fun y => interiorRight c.toBallChart d.toBallChart a.1 (ι' y)
    have hι₀ : MDifferentiableAt (𝓡 3) (𝓡 3)
        (fun y : Wop => (⟨d'.chart (y : csModel), y.2.2⟩ : d.interior)) ⟨x, hxW⟩ :=
      (MDifferentiableAt.subtypeVal_comp_iff
        (I := 𝓡 3) (J := 𝓡 3) (U := d.interior)
        (f := fun y : Wop => (⟨d'.chart (y : csModel), y.2.2⟩ : d.interior)) ⟨x, hxW⟩).mp
        (DifferentialGeometry.mdifferentiableAt_subtype_iff.mpr
          (PartialDiffeomorph.mdifferentiableAt d'.chart (by simp) (x := x) hx'))
    have hι' : MDifferentiableAt (𝓡 3) (𝓡 3) ι' x := by
      refine (DifferentialGeometry.mdifferentiableAt_subtype_iff (U := Wop)
        (f := ι') (x := ⟨x, hxW⟩)).mp ?_
      rw [show (fun y : Wop => ι' (y : csModel)) =
          fun y : Wop => (⟨d'.chart (y : csModel), y.2.2⟩ : d.interior) from
        funext fun y => dif_pos y.2]
      exact hι₀
    have hι : (fun y : csModel => (ι' y : N.Carrier)) =ᶠ[𝓝 x]
        (d'.chart : csModel → N.Carrier) := by
      filter_upwards [hWopen.mem_nhds hxW] with y hy
      rw [show ι' y = (⟨d'.chart y, hy.2⟩ : d.interior) from dif_pos hy]
    have huu : u =ᶠ[𝓝 x] u' := by
      filter_upwards [hWopen.mem_nhds hxW] with y hy
      rw [huW y hy]
      change inr c.toBallChart d.toBallChart a.1.toHomeomorph ⟨d'.chart y, hmemW hy⟩ =
        inr c.toBallChart d.toBallChart a.1.toHomeomorph (d.interiorToPunctured (ι' y))
      rw [show ι' y = (⟨d'.chart y, hy.2⟩ : d.interior) from dif_pos hy]
      exact congrArg (inr c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext rfl)
    have hkey :
        (((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
            Ψ hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv :
            TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3)
              (interiorRight c.toBallChart d.toBallChart a.1 ⟨d'.chart x, hxW.2⟩)) =
          ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
              d'.chart hx').mfderivToContinuousLinearEquiv
              (by simp)).toLinearEquiv.trans
            (((smoothConnectedSum M N c d a
              ).interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
              (by simp) ⟨d'.chart x, hxW.2⟩)).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change mfderiv (𝓡 3) (𝓡 3) (Ψ : csModel →
          ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) x v =
        ((smoothConnectedSum M N c d a
          ).interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
          (by simp) ⟨d'.chart x, hxW.2⟩)
          (((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
              d'.chart hx').mfderivToContinuousLinearEquiv
              (by simp)) v)
      rw [hfun, Filter.EventuallyEq.mfderiv_eq huu]
      change mfderiv (𝓡 3) (𝓡 3)
          (fun y => interiorRight c.toBallChart d.toBallChart a.1 (ι' y)) x v = _
      erw [mfderiv_comp_apply (x := x) (f := ι')
        (g := interiorRight c.toBallChart d.toBallChart a.1)
        ((smoothConnectedSum M N c d a).interiorRight_localDiffeomorph.mdifferentiable
          (by simp) _) hι']
      rw [show ι' x = (⟨d'.chart x, hxW.2⟩ : d.interior) from dif_pos hxW]
      rw [← DifferentialGeometry.mfderiv_subtypeVal_comp ι' x,
        Filter.EventuallyEq.mfderiv_eq hι]
      rfl
    erw [hkey]
    erw [← OrientationAssembly.orientation_map_map_trans
      ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
          d'.chart hx').mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (((smoothConnectedSum M N c d a).interiorRight_localDiffeomorph.mfderivToContinuousLinearEquiv
        (by simp) ⟨d'.chart x, hxW.2⟩)).toLinearEquiv (OrientationAssembly.stdOrientation x)]
    erw [← OrientationAssembly.orientation_eq_map_chartTangentEquiv d' hx']
    rw [hval x hxW]
    exact (smoothConnectedSum M N c d a).interiorRight_preserves_orientation ⟨d'.chart x, hxW.2⟩
  · intro x hx
    exact ⟨hmemW (hWclosed hx), by rw [hfun, huW x (hWclosed hx)]⟩

theorem exists_orientedBallChart_inl
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment)
    (c' : OrientedBallChart M.toClosedOrientedManifold)
    (hdisj : ∀ x ∈ Metric.closedBall (0 : csModel) 2,
      c'.chart x ∉ c.chart '' Metric.closedBall (0 : csModel) 1) :
    ∃ f : OrientedBallChart
        (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold,
      ∀ x ∈ Metric.closedBall (0 : csModel) 2,
        ∃ hx : c'.chart x ∉ c.chart '' Metric.ball (0 : csModel) 1,
          f.toBallChart.chart x = inl c.toBallChart d.toBallChart a.1.toHomeomorph
            ⟨c'.chart x, hx⟩ := by
  let _ : ChartedSpace csModel
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ : IsManifold (𝓡 3) ∞
      (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
    csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph (contDiffOn_reflectMap a.1)
      (contDiffOn_reflectMapInv a.1)
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
  let Wop : TopologicalSpace.Opens csModel := ⟨W, hWopen⟩
  let z₀ : csSphere := Classical.choice (nonempty_sphere_of_neZero (n := 3))
  let u : csModel → ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph := fun x =>
    if h : x ∈ W then inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨c'.chart x, hmemW h⟩
    else inl c.toBallChart d.toBallChart a.1.toHomeomorph (c.boundaryMap z₀)
  have huW : ∀ x (hx : x ∈ W),
      u x = inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨c'.chart x, hmemW hx⟩ := by
    intro x hx
    simp only [u, dif_pos hx]
  have hinj : Set.InjOn u W := by
    intro x hx y hy hxy
    have h1 : (⟨c'.chart x, hmemW hx⟩ : c.Punctured) = ⟨c'.chart y, hmemW hy⟩ :=
      inl_injective c.toBallChart d.toBallChart a.1.toHomeomorph
        (by rw [← huW x hx, ← huW y hy]; exact hxy)
    exact c'.chart.toPartialEquiv.injOn hx.1 hy.1 (congrArg Subtype.val h1)
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ u W := by
    intro x
    obtain ⟨x, hxW⟩ := x
    have hxsrc : x ∈ c'.chart.source := hxW.1
    have hxint : c'.chart x ∈ c.interior := hxW.2
    let g : OpenPartialHomeomorph M.Carrier csModel := chartAt csModel (c'.chart x)
    have hgmem : g ∈ atlas csModel M.Carrier := chart_mem_atlas csModel (c'.chart x)
    let L : OpenPartialHomeomorph csModel
        (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
      leftChart c.toBallChart d.toBallChart a.1.toHomeomorph hn3 g
    have hLmem : L.symm ∈ atlas csModel
        (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) :=
      OrientationAssembly.mem_atlas_leftChart c.toBallChart d.toBallChart a.1.toHomeomorph g hgmem
    have hLon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L L.source :=
      contMDiffOn_leftChart c.toBallChart d.toBallChart a.1 g hLmem
    have hLsymm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ L.symm L.target :=
      contMDiffOn_leftChart_symm c.toBallChart d.toBallChart a.1 g hLmem
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
        (K := 𝓡 3) (P := ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) hm
    have hLg : ∀ (p : c.Punctured), (p : M.Carrier) ∈ g.source →
        (p : M.Carrier) ∈ c.interior →
        L (g (p : M.Carrier)) = inl c.toBallChart d.toBallChart a.1.toHomeomorph p := by
      intro p hgs hgi
      have hmem : p ∈ leftRegion c.toBallChart g := ⟨hgs, hgi⟩
      have htarget : inl c.toBallChart d.toBallChart a.1.toHomeomorph p ∈ L.target := by
        rw [leftChart_target]
        exact ⟨p, hmem, rfl⟩
      rw [← leftChart_symm_apply_inl c.toBallChart d.toBallChart a.1.toHomeomorph hn3 g hmem]
      exact L.right_inv htarget
    have hgcont : ContinuousAt c'.chart x :=
      c'.chart.contMDiffOn_toFun.continuousOn.continuousAt
        (c'.chart.open_source.mem_nhds hxsrc)
    refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ hcomp
    have h1 : W ∈ 𝓝 x := hWopen.mem_nhds hxW
    have h2 : c'.chart ⁻¹' (g.source ∩ (c.interior : Set M.Carrier)) ∈ 𝓝 x :=
      hgcont.preimage_mem_nhds ((g.open_source.inter c.interior.isOpen).mem_nhds ⟨hqg, hxint⟩)
    filter_upwards [h1, h2] with y hyW hyg
    rw [huW y hyW]
    exact (hLg ⟨c'.chart y, hmemW hyW⟩ hyg.1 hyW.2).symm
  obtain ⟨Ψ, hsrc, -, hfun⟩ :=
    IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn hloc hWopen hne hinj
  have hval : ∀ x (hx : x ∈ W), Ψ x =
      interiorLeft c.toBallChart d.toBallChart a.1 ⟨c'.chart x, hx.2⟩ := by
    intro x hx
    rw [hfun, huW x hx]
    exact congrArg (inl c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext rfl)
  refine ⟨{ toBallChart := ⟨Ψ, ?_⟩, preserves_orientation := ?_ }, ?_⟩
  · rw [hsrc]
    exact hWclosed
  · intro x hx
    have hxW : x ∈ W := hsrc ▸ hx
    have hx' : x ∈ c'.chart.source := hxW.1
    have h0δ : c'.chart (0 : csModel) ∈ c.interior :=
      hdisj 0 (Metric.mem_closedBall_self (by norm_num))
    let ι' : csModel → c.interior := fun y =>
      if h : y ∈ W then (⟨c'.chart y, h.2⟩ : c.interior)
      else (⟨c'.chart (0 : csModel), h0δ⟩ : c.interior)
    let u' : csModel → ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph :=
      fun y => interiorLeft c.toBallChart d.toBallChart a.1 (ι' y)
    have hι₀ : MDifferentiableAt (𝓡 3) (𝓡 3)
        (fun y : Wop => (⟨c'.chart (y : csModel), y.2.2⟩ : c.interior)) ⟨x, hxW⟩ :=
      (MDifferentiableAt.subtypeVal_comp_iff
        (I := 𝓡 3) (J := 𝓡 3) (U := c.interior)
        (f := fun y : Wop => (⟨c'.chart (y : csModel), y.2.2⟩ : c.interior)) ⟨x, hxW⟩).mp
        (DifferentialGeometry.mdifferentiableAt_subtype_iff.mpr
          (PartialDiffeomorph.mdifferentiableAt c'.chart (by simp) (x := x) hx'))
    have hι' : MDifferentiableAt (𝓡 3) (𝓡 3) ι' x := by
      refine (DifferentialGeometry.mdifferentiableAt_subtype_iff (U := Wop)
        (f := ι') (x := ⟨x, hxW⟩)).mp ?_
      rw [show (fun y : Wop => ι' (y : csModel)) =
          fun y : Wop => (⟨c'.chart (y : csModel), y.2.2⟩ : c.interior) from
        funext fun y => dif_pos y.2]
      exact hι₀
    have hι : (fun y : csModel => (ι' y : M.Carrier)) =ᶠ[𝓝 x]
        (c'.chart : csModel → M.Carrier) := by
      filter_upwards [hWopen.mem_nhds hxW] with y hy
      rw [show ι' y = (⟨c'.chart y, hy.2⟩ : c.interior) from dif_pos hy]
    have huu : u =ᶠ[𝓝 x] u' := by
      filter_upwards [hWopen.mem_nhds hxW] with y hy
      rw [huW y hy]
      change inl c.toBallChart d.toBallChart a.1.toHomeomorph ⟨c'.chart y, hmemW hy⟩ =
        inl c.toBallChart d.toBallChart a.1.toHomeomorph (c.interiorToPunctured (ι' y))
      rw [show ι' y = (⟨c'.chart y, hy.2⟩ : c.interior) from dif_pos hy]
      exact congrArg (inl c.toBallChart d.toBallChart a.1.toHomeomorph) (Subtype.ext rfl)
    have hkey :
        (((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
            Ψ hx).mfderivToContinuousLinearEquiv
          (by simp)).toLinearEquiv :
            TangentSpace (𝓡 3) x ≃ₗ[ℝ] TangentSpace (𝓡 3)
              (interiorLeft c.toBallChart d.toBallChart a.1 ⟨c'.chart x, hxW.2⟩)) =
          ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
              c'.chart hx').mfderivToContinuousLinearEquiv
              (by simp)).toLinearEquiv.trans
            (((smoothConnectedSum M N c d a
              ).interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
              (by simp) ⟨c'.chart x, hxW.2⟩)).toLinearEquiv := by
      apply LinearEquiv.ext
      intro v
      change mfderiv (𝓡 3) (𝓡 3) (Ψ : csModel →
          ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) x v =
        ((smoothConnectedSum M N c d a
          ).interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
          (by simp) ⟨c'.chart x, hxW.2⟩)
          (((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
              c'.chart hx').mfderivToContinuousLinearEquiv
              (by simp)) v)
      rw [hfun, Filter.EventuallyEq.mfderiv_eq huu]
      change mfderiv (𝓡 3) (𝓡 3)
          (fun y => interiorLeft c.toBallChart d.toBallChart a.1 (ι' y)) x v = _
      erw [mfderiv_comp_apply (x := x) (f := ι')
        (g := interiorLeft c.toBallChart d.toBallChart a.1)
        ((smoothConnectedSum M N c d a).interiorLeft_localDiffeomorph.mdifferentiable
          (by simp) _) hι']
      rw [show ι' x = (⟨c'.chart x, hxW.2⟩ : c.interior) from dif_pos hxW]
      rw [← DifferentialGeometry.mfderiv_subtypeVal_comp ι' x,
        Filter.EventuallyEq.mfderiv_eq hι]
      rfl
    erw [hkey]
    erw [← OrientationAssembly.orientation_map_map_trans
      ((PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞
          c'.chart hx').mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
      (((smoothConnectedSum M N c d a).interiorLeft_localDiffeomorph.mfderivToContinuousLinearEquiv
        (by simp) ⟨c'.chart x, hxW.2⟩)).toLinearEquiv (OrientationAssembly.stdOrientation x)]
    erw [← OrientationAssembly.orientation_eq_map_chartTangentEquiv c' hx']
    rw [hval x hxW]
    exact (smoothConnectedSum M N c d a).interiorLeft_preserves_orientation ⟨c'.chart x, hxW.2⟩
  · intro x hx
    exact ⟨hmemW (hWclosed hx), by rw [hfun, huW x (hWclosed hx)]⟩

end ConnectedSumQuotient

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c c' : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c' d a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨Θ, hΘo, hΘ⟩ := selfTransport_holds c c'
  exact csTransport_diffeomorph_preservesOrientation c c' d d a Θ
    (Diffeomorph.refl (𝓡 3) N.Carrier ∞)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΘ x hx) (fun _ _ => rfl) hΘo

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_rightChart
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d d' : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N c d a).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M N c d' a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨Θ, hΘo, hΘ⟩ := selfTransport_holds d d'
  exact csTransport_diffeomorph_preservesOrientation c c d d' a
    (Diffeomorph.refl (𝓡 3) M.Carrier ∞) Θ
    (fun _ _ => rfl) (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hΘ x hx)
    (Diffeomorph.preservesOrientation_refl M.orientation)

theorem nonempty_orientedDiffeomorph_smoothConnectedSum_of_orientedDiffeomorph
    {M M' : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{u} 3}
    (Φ : M.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M'.Carrier)
    (hΦo : Φ.preservesOrientation M.orientation M'.orientation)
    (d : OrientedBallChart N.toClosedOrientedManifold) (a : BoundaryAttachment) :
    Nonempty (ClosedOrientedManifold.OrientedDiffeomorph
      (smoothConnectedSum M N (orientedBallChart M) d a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold
      (smoothConnectedSum M' N (orientedBallChart M') d a
        ).toConnectedClosedOrientedManifold.toClosedOrientedManifold) := by
  obtain ⟨c, hc⟩ := orientedBallChartPullback Φ (orientedBallChart M') hΦo
  obtain ⟨f⟩ := nonempty_orientedDiffeomorph_smoothConnectedSum_of_leftChart
    (orientedBallChart M) c d a
  obtain ⟨g⟩ := csTransport_diffeomorph_preservesOrientation c (orientedBallChart M') d d a Φ
    (Diffeomorph.refl (𝓡 3) N.Carrier ∞)
    (fun x hx => by simpa only [Diffeomorph.coe_toHomeomorph] using hc x hx)
    (fun _ _ => rfl) hΦo
  exact ⟨f.trans g⟩

end DifferentialGeometry.Topology
