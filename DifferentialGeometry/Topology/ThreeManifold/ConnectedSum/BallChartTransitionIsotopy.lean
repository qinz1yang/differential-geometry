import DifferentialGeometry.Topology.Manifold.BallChartAffine
import DifferentialGeometry.Topology.Manifold.BallChartModelIsotopy
import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallChartTransitionOrientation

set_option autoImplicit false
noncomputable section
open Set Metric Filter Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3}

theorem exists_supported_isotopy_of_transition_tube (c c' : OrientedBallChart M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ c'.chart.target)
    {V : Set E3} (hVopen : IsOpen V) (hVsub : V ⊆ c'.chart.source)
    (hVψ : ∀ x ∈ Metric.closedBall (0 : E3) 2, c'.chart.symm (c.chart x) ∈ V)
    (hVball : Metric.closedBall (0 : E3) 2 ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • c'.chart.symm (c.chart (0 : E3)) + t • (0 : E3) ∈ V) :
    ∃ (J : ℝ → Diffeomorph (𝓡 3) (𝓡 3) M.Carrier M.Carrier ∞) (K : Set E3),
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞ (fun q : ℝ × M.Carrier => J q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun q : ℝ × M.Carrier => (J q.1).symm q.2) ∧
      J 0 = Diffeomorph.refl (𝓡 3) M.Carrier ∞ ∧
      IsCompact K ∧ K ⊆ V ∧
      (∀ t x, x ∉ c'.chart '' K → J t x = x ∧ (J t).symm x = x) ∧
      ∀ x ∈ Metric.closedBall (0 : E3) 2, J 1 (c.chart x) = c'.chart x := by
  have hover0 : c.chart (0 : E3) ∈ c'.chart.target :=
    hover 0 (Metric.mem_closedBall_self (by norm_num))
  have hdetψ : 0 < (fderiv ℝ (fun x : E3 => c'.chart.symm (c.chart x)) (0 : E3)).det :=
    OrientedBallChart.det_fderiv_chartTransition_pos c c' hover0
  let Q : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ := c.chart.trans c'.chart.symm
  let R : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    (Diffeomorph.refl 𝓘(ℝ, E3) E3 ∞).toPartialDiffeomorph
  have hQfun : (Q : E3 → E3) = fun x : E3 => c'.chart.symm (c.chart x) := rfl
  have hRfun : (R : E3 → E3) = id := rfl
  have hQsrc : Metric.closedBall (0 : E3) 2 ⊆ Q.source := by
    intro x hx
    change x ∈ c.chart.source ∩ c.chart ⁻¹' c'.chart.target
    exact ⟨c.closedBall_subset_source hx, hover x hx⟩
  have hRsrc : Metric.closedBall (0 : E3) 2 ⊆ R.source := by
    intro x _
    change x ∈ (Set.univ : Set E3)
    exact Set.mem_univ x
  have hdetQ : 0 < (fderiv ℝ (Q : E3 → E3) (0 : E3)).det := by
    rwa [hQfun]
  have hdetR : (fderiv ℝ (R : E3 → E3) (0 : E3)).det = 1 := by
    rw [hRfun, fderiv_id]
    rw [show ContinuousLinearMap.det (ContinuousLinearMap.id ℝ E3)
      = LinearMap.det (1 : E3 →ₗ[ℝ] E3) from rfl]
    exact map_one _
  obtain ⟨J, hJc, hJi, hJ0, hJ1, K, hKc, hKV, hKfix⟩ :=
    Manifold.exists_isotopy_eqOn_closedBall_of_partialDiffeomorphs_of_subset
      (n := 3) Q R hQsrc hRsrc hVopen
      (by rintro y ⟨x, hx, rfl⟩; rw [hQfun]; exact hVψ x hx)
      (by rintro y ⟨x, hx, rfl⟩; rw [hRfun]; exact hVball hx)
      (by
        intro t ht
        rw [hQfun, hRfun]
        exact hseg t ht)
      (by rw [hdetR, mul_one]; exact hdetQ)
  obtain ⟨H, hHc, hHi, hHe, -, -, hHfix⟩ :=
    Manifold.exists_diffeomorph_extension_of_partial_chart_family (P := ℝ)
      c'.chart.symm.toOpenPartialHomeomorph c'.chart.contMDiffOn_invFun
      c'.chart.contMDiffOn_toFun J hJc hJi hKc (hKV.trans hVsub)
      (fun p z hz => hKfix p z hz)
  refine ⟨H, K, hHc, hHi, ?_, hKc, hKV, ?_, ?_⟩
  · apply Diffeomorph.ext
    intro y
    rw [(hHe 0 y).1]
    by_cases hy : y ∈ c'.chart.symm.toOpenPartialHomeomorph.source
    · have h1 : Manifold.extendChartById c'.chart.symm.toOpenPartialHomeomorph (J 0) y
          = c'.chart.symm.toOpenPartialHomeomorph.symm
            (c'.chart.symm.toOpenPartialHomeomorph y) := by
        rw [Manifold.extendChartById, if_pos hy, hJ0]
        rfl
      rw [h1, OpenPartialHomeomorph.left_inv _ hy]
      simp only [Diffeomorph.coe_refl, id_eq]
    · rw [Manifold.extendChartById, if_neg hy]
      simp only [Diffeomorph.coe_refl, id_eq]
  · intro t y hy
    exact hHfix t y hy
  · intro x hx
    have h := hJ1 x hx
    rw [hQfun, hRfun] at h
    rw [(hHe 1 (c.chart x)).1,
      extendChartById_chartSymm_of_target c'.toBallChart (J 1) (hover x hx), h]
    rfl

theorem ballChartIsotopic_of_transition_tube (c c' : OrientedBallChart M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ c'.chart.target)
    {V : Set E3} (hVopen : IsOpen V) (hVsub : V ⊆ c'.chart.source)
    (hVψ : ∀ x ∈ Metric.closedBall (0 : E3) 2, c'.chart.symm (c.chart x) ∈ V)
    (hVball : Metric.closedBall (0 : E3) 2 ⊆ V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • c'.chart.symm (c.chart (0 : E3)) + t • (0 : E3) ∈ V) :
    Manifold.BallChartIsotopic c.toBallChart c'.toBallChart := by
  obtain ⟨J, -, hJc, hJi, hJ0, -, -, -, hJ1⟩ :=
    exists_supported_isotopy_of_transition_tube c c' hover hVopen hVsub hVψ hVball hseg
  exact ⟨J, hJc, hJi, hJ0, hJ1⟩

theorem ballChartIsotopic_of_center_eq (c c' : OrientedBallChart M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ c'.chart.target)
    (hc : c.chart (0 : E3) = c'.chart (0 : E3)) :
    Manifold.BallChartIsotopic c.toBallChart c'.toBallChart := by
  have h0' : (0 : E3) ∈ c'.chart.source :=
    c'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hψ0 : c'.chart.symm (c.chart (0 : E3)) = (0 : E3) := by
    rw [hc]
    exact c'.chart.left_inv h0'
  refine ballChartIsotopic_of_transition_tube c c' hover c'.chart.open_source
    (subset_refl _) (fun x hx => c'.chart.map_target (hover x hx))
    c'.closedBall_subset_source ?_
  intro t _
  rw [hψ0]
  simpa using c'.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))

theorem ballChartIsotopic_of_transition_segment_in_source (c c' : OrientedBallChart M)
    (hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ c'.chart.target)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • c'.chart.symm (c.chart (0 : E3)) + t • (0 : E3) ∈ c'.chart.source) :
    Manifold.BallChartIsotopic c.toBallChart c'.toBallChart :=
  ballChartIsotopic_of_transition_tube c c' hover c'.chart.open_source (subset_refl _)
    (fun x hx => c'.chart.map_target (hover x hx)) c'.closedBall_subset_source hseg

theorem affine_chart_source (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) :
    (c.affine s r hr hs).chart.source = {x : E3 | s + r • x ∈ c.chart.source} := by
  ext x
  rw [show ((c.affine s r hr hs).chart.source)
      = (((AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph).toOpenPartialHomeomorph.trans
          c.chart.toOpenPartialHomeomorph).source from rfl]
  rw [OpenPartialHomeomorph.trans_source]
  change (x ∈ (Set.univ : Set E3) ∧ s + r • x ∈ c.chart.source) ↔ s + r • x ∈ c.chart.source
  simp

private theorem smul_neg_inv_add_self (s : E3) (r : ℝ) (hr : 0 < r) :
    s + r • (-(r⁻¹ • s)) = (0 : E3) := by
  rw [smul_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul, add_neg_cancel]

theorem affine_chart_center_mem_target (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) :
    c.chart (0 : E3) ∈ (c.affine s r hr hs).chart.target := by
  have h0src : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  refine ⟨c.chart.map_source h0src, ?_⟩
  change c.chart.symm (c.chart (0 : E3))
    ∈ (AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph.target
  rw [show c.chart.symm (c.chart (0 : E3)) = (0 : E3) from c.chart.left_inv h0src]
  trivial

theorem affine_chart_zero_ne (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) (hs0 : s ≠ 0) :
    (c.affine s r hr hs).chart (0 : E3) ≠ c.chart (0 : E3) := by
  intro h
  rw [OrientedBallChart.affine_apply] at h
  simp only [smul_zero, add_zero] at h
  have hs2 : ‖s‖ ≤ 2 := by linarith [norm_nonneg s]
  have hs_src : s ∈ c.chart.source :=
    c.closedBall_subset_source (by rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]; exact hs2)
  have h0src : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  exact hs0 (c.chart.toPartialEquiv.injOn hs_src h0src h)

theorem det_fderiv_affine_chartTransition_pos (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) :
    0 < (fderiv ℝ (fun x : E3 => (c.affine s r hr hs).chart.symm (c.chart x))
      (0 : E3)).det :=
  OrientedBallChart.det_fderiv_chartTransition_pos c (c.affine s r hr hs)
    (affine_chart_center_mem_target c s r hr hs)

theorem ballChartIsotopic_affine (c : OrientedBallChart M) (s : E3) (r : ℝ)
    (hr : 0 < r) (hs : ‖s‖ + 2 * r ≤ 2) :
    Manifold.BallChartIsotopic c.toBallChart (c.affine s r hr hs).toBallChart := by
  set c' := c.affine s r hr hs with hc'def
  have hs2 : ‖s‖ ≤ 2 := by linarith [norm_nonneg s]
  have h0src : (0 : E3) ∈ c.chart.source :=
    c.closedBall_subset_source (Metric.mem_closedBall_self (by norm_num))
  have hsrc : ∀ y : E3, y ∈ c'.chart.source ↔ s + r • y ∈ c.chart.source := by
    intro y
    rw [hc'def, affine_chart_source c s r hr hs]
    exact Iff.rfl
  have hchart : ∀ y : E3, c'.chart y = c.chart (s + r • y) :=
    fun y => OrientedBallChart.affine_apply c s r hr hs y
  have hneg : s + r • (-(r⁻¹ • s)) = (0 : E3) := smul_neg_inv_add_self s r hr
  have halg : ∀ t : ℝ, s + r • ((1 - t) • (-(r⁻¹ • s))) = t • s := by
    intro t
    have h1 : r • ((1 - t) • (-(r⁻¹ • s))) = (-(1 - t)) • s := by
      rw [smul_neg, smul_smul, smul_neg, smul_smul,
        show r * ((1 - t) * r⁻¹) = 1 - t from by field_simp, neg_smul]
    rw [h1]
    have h2 : s + (-(1 - t)) • s = (1 + -(1 - t)) • s := by
      rw [add_smul, one_smul]
    rw [h2, show (1 : ℝ) + -(1 - t) = t from by ring]
  have hy : -(r⁻¹ • s) ∈ c'.chart.source := by
    rw [hsrc, hneg]
    exact h0src
  have hmap : c'.chart (-(r⁻¹ • s)) = c.chart (0 : E3) := by rw [hchart, hneg]
  have hψ0 : c'.chart.symm (c.chart (0 : E3)) = -(r⁻¹ • s) := by
    rw [← hmap]
    exact c'.chart.left_inv hy
  have hover : ∀ x ∈ Metric.closedBall (0 : E3) 2, c.chart x ∈ c'.chart.target := by
    intro x hx
    refine ⟨c.chart.map_source (c.closedBall_subset_source hx), ?_⟩
    change c.chart.symm (c.chart x)
      ∈ (AffineModel.affineDiffeomorph s r (ne_of_gt hr)).toPartialDiffeomorph.target
    rw [show c.chart.symm (c.chart x) = x from c.chart.left_inv (c.closedBall_subset_source hx)]
    trivial
  refine ballChartIsotopic_of_transition_segment_in_source c c' hover ?_
  intro t ht
  rw [hψ0]
  simp only [smul_zero, add_zero]
  rw [hsrc, halg]
  refine c.closedBall_subset_source ?_
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg ht.1]
  nlinarith [ht.2, hs2, norm_nonneg s]

end DifferentialGeometry.Topology
