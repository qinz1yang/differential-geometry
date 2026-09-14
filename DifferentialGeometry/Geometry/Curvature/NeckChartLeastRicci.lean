import DifferentialGeometry.Geometry.Curvature.RestrictedRoundCylinderLeastRicciField
import DifferentialGeometry.Geometry.Curvature.LeastRicciTransport
import DifferentialGeometry.Geometry.Curvature.LeastRicciScaling
import DifferentialGeometry.Geometry.Gradient.ScaledChart
import DifferentialGeometry.Geometry.Metric.RestrictedCylinderHeight

noncomputable section
open Set Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Gradient
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Curvature

theorem exists_smooth_least_ricci_field_close_to_gradient_from_neck_chart
    {E F H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    [BoundarylessManifold J N]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric J N) (Φ : O ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ N)
    (Q : ℝ) (hQ : 0 < Q) {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (Diffeomorph.pullbackMetricCross (scaleMetric Q hQ g) Φ)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    let u : N → ℝ := fun y ↦ (Real.sqrt Q)⁻¹ * (Φ.symm y : Metric.sphere (0 : E) 1 × ℝ).2
    ∃ (ν : N → ℝ) (Y : ∀ y : N, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ ν (Φ '' U) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J N)) (Φ '' U) ∧
      ∀ y ∈ Φ '' U, g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * Q * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J u y (Y y) ∧ |mvfderiv J u y (Y y) - 1| ≤ 92354 * ε ∧
        Real.sqrt (g.inner y (Y y - gradFun g u y) (Y y - gradFun g u y)) ≤ 184712 * ε := by
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let IC := (𝓡 2).prod 𝓘(ℝ)
  let gC := Diffeomorph.pullbackMetricCross (scaleMetric Q hQ g) Φ
  obtain ⟨μ, w, hμ, hw, hprop⟩ :=
    exists_smooth_least_ricci_field_close_to_gradient_on_restricted_roundCylinder
      O gC hU ε hε hsmall
  let Z := VectorField.mpullback J IC (Φ.symm : N → O) w
  let ν : N → ℝ := fun y ↦ Q * μ (Φ.symm y)
  let Y : ∀ y : N, TangentSpace J y := fun y ↦ Real.sqrt Q • Z y
  have hZ : ContMDiffOn J J.tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)) (Φ.symm ⁻¹' U) := by
    apply hw.mpullback_vectorField_preimage Φ.symm.contMDiff
    · intro y _
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ.symm) (by decide)]
      exact ContinuousLinearMap.isInvertible_equiv
    · simp
  have himage : Φ '' U ⊆ Φ.symm ⁻¹' U := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [mem_preimage, Φ.symm_apply_apply] using hx
  have hν : ContMDiffOn J 𝓘(ℝ) ∞ ν (Φ '' U) :=
    contMDiffOn_const.mul (hμ.comp Φ.symm.contMDiff.contMDiffOn himage)
  have hY : ContMDiffOn J J.tangent ∞
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle J N)) (Φ '' U) :=
    contMDiffOn_const.smul_section (hZ.mono himage)
  refine ⟨ν, Y, hν, hY, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hYeq : Y (Φ x) = Real.sqrt Q • mfderiv IC J Φ x (w x) := by
    change Real.sqrt Q • VectorField.mpullback J IC (Φ.symm : N → O) w (Φ x) = _
    rw [mpullback_symm_applyCross]
  have hνeq : ν (Φ x) = Q * μ x := by simp only [ν, Φ.symm_apply_apply]
  obtain ⟨hwn, hwe, hwm, hwa, hws, _, hwd, hwgrad⟩ := hprop x hx
  obtain ⟨hzn, hze, hzm, hzs⟩ :=
    least_ricci_eigenpair_pullback (scaleMetric Q hQ g) Φ x (μ x) (w x) hwn hwe hwm hws
  obtain ⟨hyn, hye, hym, hys⟩ :=
    least_ricci_eigenpair_of_scaleMetric g Q hQ (Φ x) (μ x) (mfderiv IC J Φ x (w x))
      hzn hze hzm hzs
  rw [hYeq, hνeq]
  refine ⟨hyn, hye, hym, ?_, hys, ?_, ?_, ?_⟩
  · rw [abs_mul, abs_of_pos hQ]
    have h := mul_le_mul_of_nonneg_left hwa hQ.le
    nlinarith only [h]
  · have hf : ContMDiff IC 𝓘(ℝ) ∞
        (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) :=
      contMDiff_snd.comp contMDiff_subtype_val
    rw [mvfderiv_scaled_chart_coordinate Φ _ hf Q hQ]
    have hb := (restricted_roundCylinder_height_differential_bound O x (w x)).trans hwd
    have hl := (abs_le.mp hb).1
    linarith only [hl, hε]
  · have hf : ContMDiff IC 𝓘(ℝ) ∞
        (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) :=
      contMDiff_snd.comp contMDiff_subtype_val
    rw [mvfderiv_scaled_chart_coordinate Φ _ hf Q hQ]
    exact (restricted_roundCylinder_height_differential_bound O x (w x)).trans hwd
  · have hf : ContMDiff IC 𝓘(ℝ) ∞
        (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) :=
      contMDiff_snd.comp contMDiff_subtype_val
    exact (sqrt_inner_sub_gradFun_scaled_chart g Φ
      (fun y : O ↦ (y : Metric.sphere (0 : E) 1 × ℝ).2) Q hQ x
      (hf.mdifferentiable (by decide) x) (w x)).trans_le hwgrad

theorem exists_smooth_least_ricci_field_from_neck_chart
    {E F H N : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2 + 1)]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
    [BoundarylessManifold J N]
    (O : TopologicalSpace.Opens (Metric.sphere (0 : E) 1 × ℝ))
    (g : SmoothRiemannianMetric J N) (Φ : O ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), J⟯ N)
    (Q : ℝ) (hQ : 0 < Q) {U : Set O} (hU : IsOpen U)
    (ε : ℝ) (hε : ε < 1 / 200000)
    (hsmall : ∀ x ∈ U, ∀ k : ℕ, k ≤ 2 →
      metricDerivNorm k (Diffeomorph.pullbackMetricCross (scaleMetric Q hQ g) Φ)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O)
        ((roundCylinderMetric (E := E) (n := 2)).restrictOpen O) x ≤ ε) :
    let u : N → ℝ := fun y ↦ (Real.sqrt Q)⁻¹ * (Φ.symm y : Metric.sphere (0 : E) 1 × ℝ).2
    ∃ (ν : N → ℝ) (Y : ∀ y : N, TangentSpace J y),
      ContMDiffOn J 𝓘(ℝ) ∞ ν (Φ '' U) ∧
      ContMDiffOn J J.tangent ∞ (fun y ↦ (⟨y, Y y⟩ : TangentBundle J N)) (Φ '' U) ∧
      ∀ y ∈ Φ '' U, g.inner y (Y y) (Y y) = 1 ∧
        ricciSharp g y (Y y) = ν y • Y y ∧
        (∀ z : TangentSpace J y, g.inner y z z = 1 → ν y ≤ ricciTensor g y z z) ∧
        |ν y| ≤ 5772 * Q * ε ∧
        Module.End.eigenspace (ricciSharp g y).toLinearMap (ν y) = Submodule.span ℝ {Y y} ∧
        0 < mvfderiv J u y (Y y) ∧ |mvfderiv J u y (Y y) - 1| ≤ 92354 * ε := by
  obtain ⟨ν, Y, hν, hY, hprop⟩ :=
    exists_smooth_least_ricci_field_close_to_gradient_from_neck_chart
      O g Φ Q hQ hU ε hε hsmall
  refine ⟨ν, Y, hν, hY, ?_⟩
  intro y hy
  obtain ⟨hu, he, hm, hb, hs, hp, hd, _⟩ := hprop y hy
  exact ⟨hu, he, hm, hb, hs, hp, hd⟩

end DifferentialGeometry.Geometry.Curvature
