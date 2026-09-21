import DifferentialGeometry.Geometry.Metric.ChartDistance.FirstExit
import DifferentialGeometry.Geometry.Metric.ChartDistance.InverseMetric
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.HomogeneousRegularity
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Lipschitz
import DifferentialGeometry.Geometry.Metric.CurveEnergy.Chart

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_chart_ball_and_norm_symm_le_of_metric_lower_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ ψ.symm ψ.target)
    {m R : ℝ} (hm : 0 < m) (hR : 0 < R) (hR1 : R < 1)
    (hlower : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      m * ‖ξ‖ ^ 2 ≤ g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ))
    {q : M} (hq : riemannianEDistOf g (ψ 0) q < ENNReal.ofReal (R * Real.sqrt m)) :
    q ∈ ψ '' ball (0 : plateauCoordinateSpace) R ∧
      ENNReal.ofReal ‖ψ.symm q‖ ≤
        ENNReal.ofReal (Real.sqrt m)⁻¹ * riemannianEDistOf g (ψ 0) q := by
  have hball : closedBall (0 : plateauCoordinateSpace) R ⊆ plateauOpenCube := by
    intro y hy i
    have hn : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    have hi : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact hi.trans_lt (hn.trans_lt hR1)
  have hsrc : closedBall (0 : plateauCoordinateSpace) R ⊆ ψ.source :=
    fun y hy => hsource (fun i => (hball hy i).le)
  let C : ℝ≥0 := ⟨(Real.sqrt m)⁻¹, inv_nonneg.mpr (Real.sqrt_nonneg m)⟩
  have hC : 0 < C := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  have hbound : ∀ y ∈ ψ '' ball (0 : plateauCoordinateSpace) R,
      ∀ v : TangentSpace 𝓘(ℝ, E) y,
        @norm plateauCoordinateSpace _ (mfderiv 𝓘(ℝ, E)
          𝓘(ℝ, plateauCoordinateSpace) ψ.symm y v) ≤ C * Real.sqrt (g.inner y v v) := by
    rintro y ⟨x, hx, rfl⟩ v
    exact norm_mfderiv_symm_le_inv_sqrt_mul g ψ (hψ.of_le (by simp))
      (hψinv.of_le (by simp)) (hsrc (ball_subset_closedBall hx)) hm
      (hlower x (hball (ball_subset_closedBall hx))) v
  have hCeq : (C : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt m)⁻¹ := by
    rw [ENNReal.ofReal_eq_coe_nnreal (inv_nonneg.mpr (Real.sqrt_nonneg m))]
    rfl
  have hradius : ENNReal.ofReal R / C = ENNReal.ofReal (R * Real.sqrt m) := by
    rw [hCeq, ← ENNReal.ofReal_div_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hm))]
    congr 1
    simp only [div_inv_eq_mul]
  have hq' : riemannianEDistOf g (ψ 0) q < ENNReal.ofReal R / C := by
    rwa [hradius]
  refine ⟨mem_chart_ball_of_riemannianEDistOf_lt g ψ hR hsrc
    (hψinv.of_le (by simp)) hC hbound hq', ?_⟩
  have hd := edist_chart_symm_center_le_riemannianEDistOf g ψ hR hsrc
    (hψinv.of_le (by simp)) hC hbound hq'
  simpa only [edist_dist, dist_zero_right, hCeq] using hd

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mapsTo_chart_ball_of_lipschitz_curve_energy_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ ψ.symm ψ.target)
    {m R : ℝ} (hm : 0 < m) (hR : 0 < R) (hR1 : R < 1)
    (hlower : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      m * ‖ξ‖ ^ 2 ≤ g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ))
    {γ : ℝ → M} {K : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (K : ℝ≥0∞) * edist s t)
    (hstart : γ 0 = ψ 0)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc 0 1))
    (hsmall : (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2) < m * R ^ 2) :
    MapsTo γ (Icc 0 1) (ψ '' ball (0 : plateauCoordinateSpace) R) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ENNReal.ofReal ‖ψ.symm (γ t)‖ ≤
        ENNReal.ofReal ((Real.sqrt m)⁻¹ *
          Real.sqrt (∫ s in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ s) ^ 2)) := by
  have hnonneg : 0 ≤ ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hend (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      riemannianEDistOf g (ψ 0) (γ t) ≤
        ENNReal.ofReal (Real.sqrt (∫ s in Icc (0 : ℝ) 1,
          (riemannianCurveSpeed g γ s) ^ 2)) := by
    have he := riemannianEDistOf_le_ofReal_sqrt_interval_energy g hγ ht.1
      (henergy.mono_set (Icc_subset_Icc le_rfl ht.2))
    rw [hstart] at he
    apply he.trans
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    rw [sub_zero]
    calc
      _ ≤ 1 * ∫ s in Icc (0 : ℝ) t, (riemannianCurveSpeed g γ s) ^ 2 :=
        mul_le_mul_of_nonneg_right ht.2 (integral_nonneg fun _ => sq_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        exact setIntegral_mono_set henergy (Eventually.of_forall fun _ => sq_nonneg _)
          (Eventually.of_forall (Icc_subset_Icc le_rfl ht.2))
  have hshort : Real.sqrt (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2) <
      R * Real.sqrt m := by
    have hs := Real.sqrt_lt_sqrt hnonneg hsmall
    rw [Real.sqrt_mul hm.le, Real.sqrt_sq_eq_abs, abs_of_pos hR] at hs
    simpa only [mul_comm] using hs
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    mem_chart_ball_and_norm_symm_le_of_metric_lower_bound g ψ hsource hψ hψinv hm hR hR1
      hlower ((hend t ht).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
        (mul_pos hR (Real.sqrt_pos.mpr hm))).mpr hshort))
  refine ⟨fun t ht => (hmem t ht).1, ?_⟩
  intro t ht
  apply (hmem t ht).2.trans
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr (Real.sqrt_nonneg m))]
  exact mul_le_mul_right (hend t ht) _

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open Bundle Filter Set MeasureTheory Metric Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

theorem chart_curve_energy_le_of_intrinsic_energy_lt
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (ψ : OpenPartialHomeomorph plateauCoordinateSpace M)
    (hsource : plateauClosedCube ⊆ ψ.source)
    (hψ : ContMDiffOn 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ∞ ψ ψ.source)
    (hψinv : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, plateauCoordinateSpace) ∞ ψ.symm ψ.target)
    {m R : ℝ} (hm : 0 < m) (hR : 0 < R) (hR1 : R < 1)
    (hlower : ∀ y ∈ plateauOpenCube, ∀ ξ : plateauCoordinateSpace,
      m * ‖ξ‖ ^ 2 ≤ g.inner (ψ y)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ)
        (mfderiv 𝓘(ℝ, plateauCoordinateSpace) 𝓘(ℝ, E) ψ y ξ))
    {γ : ℝ → M} {K : ℝ≥0}
    (hγ : ∀ s t, riemannianEDistOf g (γ s) (γ t) ≤ (K : ℝ≥0∞) * edist s t)
    (hstart : γ 0 = ψ 0)
    (henergy : IntegrableOn (fun t => (riemannianCurveSpeed g γ t) ^ 2) (Icc 0 1))
    (hsmall : (∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2) < m * R ^ 2) :
    MapsTo γ (Icc 0 1) (ψ '' ball (0 : plateauCoordinateSpace) R) ∧
      (∃ L : ℝ≥0, LipschitzOnWith L (ψ.symm ∘ γ) (Icc 0 1)) ∧
      IntegrableOn (fun t => ‖deriv (ψ.symm ∘ γ) t‖ ^ 2) (Icc (0 : ℝ) 1) ∧
      m * (∫ t in Icc (0 : ℝ) 1, ‖deriv (ψ.symm ∘ γ) t‖ ^ 2) ≤
        ∫ t in Icc (0 : ℝ) 1, (riemannianCurveSpeed g γ t) ^ 2 := by
  have hmaps := (mapsTo_chart_ball_of_lipschitz_curve_energy_lt
    g ψ hsource hψ hψinv hm hR hR1 hlower hγ hstart henergy hsmall).1
  have hball : ball (0 : plateauCoordinateSpace) R ⊆ plateauOpenCube := by
    intro y hy i
    have hn : ‖y‖ < R := by simpa only [mem_ball, dist_zero_right] using hy
    have hi : |y i| ≤ ‖y‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i
    exact hi.trans_lt (hn.trans hR1)
  have hsrc : ball (0 : plateauCoordinateSpace) R ⊆ ψ.source :=
    fun y hy => hsource (fun i => (hball hy i).le)
  have htarget : MapsTo γ (Icc 0 1) ψ.target := by
    intro t ht
    obtain ⟨y, hy, hyt⟩ := hmaps ht
    exact hyt ▸ ψ.map_source (hsrc hy)
  obtain ⟨L, hL⟩ := exists_lipschitzOnWith_comp_of_contMDiffOn_of_isCompact
    g ψ.open_target (hψinv.of_le (by simp)) hγ isCompact_Icc htarget
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hdm : MemLp (deriv (ψ.symm ∘ γ)) 2 μ := by
    apply MemLp.of_bound (aestronglyMeasurable_deriv _ _) L
    change ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), ‖deriv (ψ.symm ∘ γ) t‖ ≤ L
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) hL
  have hi : IntegrableOn (fun t => ‖deriv (ψ.symm ∘ γ) t‖ ^ 2) (Icc (0 : ℝ) 1) :=
    hdm.norm.integrable_sq
  refine ⟨hmaps, ⟨L, hL⟩, hi, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono_ae (hi.const_mul m) henergy
    (ae_mul_norm_deriv_symm_comp_sq_le g ψ (hψ.of_le (by simp))
      (hψinv.of_le (by simp)) hsrc (fun y hy => hlower y (hball hy))
      hγ measurableSet_Icc hmaps)

end DifferentialGeometry.Geometry

end

end
