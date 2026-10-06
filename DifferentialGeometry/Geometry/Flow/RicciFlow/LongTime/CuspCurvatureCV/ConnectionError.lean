import DifferentialGeometry.Geometry.Connection.Convergence.DifferenceDerivativeBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.FiniteJetCongruence
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.MetricComparison

/-!
# IMS04 / O3（O-W-CURV, suffix `_CV`）：`metric_error` k = 0, 1 ⇒ connection difference `≲ acc`

一般 `M` 上两度量 `h`（参考）、`ĝ`（被估计），`err := ĝ − h` 写成 `metric_error` 里**逐字**的 0S 2-tensor
`((continuousMultilinearCurryFin1 …).symm.toContinuousLinearMap.comp (ĝ.inner p − h.inner p))
.uncurryLeft`。若在点 `x` 处
`tensor0SFiberNorm h x (2+k) (iteratedMetricCovariantDerivative h 2 err k x) < acc`（k = 0, 1）
且 `acc ≤ 1/2`，则

`|difference (metricCov ĝ) (metricCov h) x u w|_h ≤ 3/2 (1+2acc)³ acc · |u|_h |w|_h`

——正是 `sqrt_curvature_perturbation_BD` / `sqrt_curvature_pulled_le_BD` 的 `hconnection` 形状。

证明：
* k = 0 ⇒ `MetricUniformEquivalentOn {x} h ĝ (1+2acc)`（`abs_apply_le_of_tensor0SFiberNorm_lt_BD`）；
* 桥 `metricCovariantDerivative_eq_covStep_CV`：光滑 0S 场上 `metricCovariantDerivative`（chart 公式，
  `metric_error` 用的那个）= `covStep`（`totalNabla0S`，Cheeger–Gromov 收敛 API 用的那个）——两边在光滑 slot 场上
  都是同一个 Leibniz 展开（`metricCovariantDerivative_apply_of_contMDiffAt` / `covStep_eval_smooth_slots`）；
* `err = metricTensorField ĝ − metricTensorField h`，`∇^h (metricTensorField h) = 0`
  （`iterCov_metric_zero`）⇒
  k = 1 的范数 = `metricCovDerivNorm 1 ĝ h x`；
* `connectionDifference_gJet_le`（Koszul 差公式的范数版）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.CheegerGromovCompactness
open Bundle
open scoped Manifold ContDiff
namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **桥**：光滑 0S 张量场上，chart 公式的 `metricCovariantDerivative` 等于 `covStep`
（`totalNabla0S`）。 -/
theorem metricCovariantDerivative_eq_covStep_CV [T2Space M] (h : SmoothRiemannianMetric I M)
    (s : ℕ)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) s)
    (x : M) :
    metricCovariantDerivative h s (fun y => A y) x = covStep h s A x := by
  classical
  apply tensor0SSpace_ext (I := I) (s + 1) x
  intro slots
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (slots 0)
  choose V hV using fun a : Fin s => ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (slots a.succ)
  have hslots : slots = Fin.cons (X x) (fun a : Fin s => V a x) := by
    funext a
    refine Fin.cases ?_ (fun b => ?_) a
    · exact hX.symm
    · exact (hV b).symm
  rw [hslots]
  have hA : ContMDiffAt I (I.prod 𝓘(ℝ, Tensor0SModel s ℝ E)) 1
      (fun y => (⟨y, A y⟩ : TotalSpace (Tensor0SModel s ℝ E)
        (fun z => Tensor0SSpace s I z))) x :=
    (A.contMDiff x).of_le (by simp)
  have hVs : ∀ a, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y => (⟨y, V a y⟩ : TotalSpace E (TangentSpace I : M → Type _))) x :=
    fun a => ((V a).contMDiff x).of_le (by simp)
  rw [metricCovariantDerivative_apply_of_contMDiffAt h s (fun y => A y) X (fun a => V a) x hA hVs,
    covStep_eval_smooth_slots h s A X V x]

omit [CompleteSpace E] in
/-- `metric_error` 形状的误差 tensor = `metricTensorField ĝ − metricTensorField h`。 -/
theorem metricErrorTensor_eq_CV (h ĝ : SmoothRiemannianMetric I M) :
    (fun p : M => ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm
      |>.toContinuousLinearMap.comp (ĝ.inner p - h.inner p)).uncurryLeft) =
      fun p : M => (metricTensorField ĝ - metricTensorField h) p := by
  funext p
  apply tensor0SSpace_ext (I := I) 2 p
  intro v
  change (ĝ.inner p - h.inner p) (v 0) (v 1) = _
  rw [ContMDiffSection.coe_sub, Pi.sub_apply, Tensor0SSpace.sub_apply, metricTensorField_apply,
    metricTensorField_apply]
  rfl

/-- **k = 1 的桥**：误差 tensor 的 `metricCovariantDerivative` = `metricCovDeriv ĝ h 1`
（`∇^h h = 0`，`iterCov_metric_zero`）。 -/
theorem metricCovariantDerivative_metricError_eq_CV [T2Space M]
    (h ĝ : SmoothRiemannianMetric I M) (x : M) :
    metricCovariantDerivative h 2 (fun p : M =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap
        |>.comp (ĝ.inner p - h.inner p)).uncurryLeft) x = metricCovDeriv ĝ h 1 x := by
  rw [metricErrorTensor_eq_CV, metricCovariantDerivative_eq_covStep_CV, covStep_sub]
  have hz : covStep h 2 (metricTensorField h) = 0 := iterCov_metric_zero h 0
  rw [hz, sub_zero]
  rfl

/-- **O3 主定理**：`metric_error` 的 k = 0, 1 两条（点 `x` 处，`acc ≤ 1/2`）⇒
`|difference (metricCov ĝ) (metricCov h) x u w|_h ≤ 3/2 (1+2acc)³ acc · |u|_h |w|_h`。 -/
theorem connection_difference_le_of_metric_error_CV [T2Space M]
    (h ĝ : SmoothRiemannianMetric I M) (x : M) {acc : ℝ} (hacc : acc ≤ 1 / 2)
    (h0 : tensor0SFiberNorm h x (2 + 0) (iteratedMetricCovariantDerivative h 2 (fun p : M =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap
        |>.comp (ĝ.inner p - h.inner p)).uncurryLeft) 0 x) < acc)
    (h1 : tensor0SFiberNorm h x (2 + 1) (iteratedMetricCovariantDerivative h 2 (fun p : M =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap
        |>.comp (ĝ.inner p - h.inner p)).uncurryLeft) 1 x) < acc)
    (u w : TangentSpace I x) :
    Real.sqrt (h.inner x (CovariantDerivative.difference (metricCov ĝ) (metricCov h) x u w)
        (CovariantDerivative.difference (metricCov ĝ) (metricCov h) x u w)) ≤
      3 / 2 * (1 + 2 * acc) ^ 3 * acc * Real.sqrt (h.inner x u u) *
        Real.sqrt (h.inner x w w) := by
  have hacc0 : 0 < acc := lt_of_le_of_lt (Real.sqrt_nonneg _) h0
  have hk0 : ∀ v : TangentSpace I x, |ĝ.inner x v v - h.inner x v v| ≤ acc * h.inner x v v := by
    intro v
    have hb := abs_apply_le_of_tensor0SFiberNorm_lt_BD h x (ĝ.inner x - h.inner x) acc h0 v v
    rw [mul_assoc, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)] at hb
    exact hb
  have hEq : MetricUniformEquivalentOn (I := I) {x} h ĝ (1 + 2 * acc) := by
    refine ⟨by linarith, fun y hy v => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have ha := metric_inner_self_nonneg h y v
    obtain ⟨hl, hr⟩ := abs_le.mp (hk0 v)
    have hpos : 0 < 1 + 2 * acc := by linarith
    refine ⟨?_, by nlinarith⟩
    rw [inv_mul_le_iff₀ hpos]
    nlinarith
  have hJ : MetricCovDerivOrderBoundOn (I := I) {x} 1 ĝ h acc := by
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h1' := h1
    change tensor0SFiberNorm h y 3 (metricCovariantDerivative h 2 (fun p : M =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace I p) ℝ).symm.toContinuousLinearMap
        |>.comp (ĝ.inner p - h.inner p)).uncurryLeft) y) < acc at h1'
    rw [metricCovariantDerivative_metricError_eq_CV] at h1'
    exact h1'.le
  refine (connectionDifference_gJet_le hEq hJ (Set.mem_singleton x) w u).trans_eq ?_
  ring

end GC.LongTime
