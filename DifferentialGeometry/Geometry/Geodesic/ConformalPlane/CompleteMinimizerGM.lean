import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.CompleteMetricExists
import DifferentialGeometry.Geometry.Connection.ConformalEuclidean
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.PathLength

/-!
# complete 度量下的极小测地线（泛型 wrapper）与 `ℂ` 上的共形度量（O-W-GEO-MIN G1，后缀 `_GM`）

* `exists_minimizing_geodesic_of_complete_GM`：泛型流形 `M` 上，`RiemannianMetricComplete g`
  （树里的 complete 定义，经 `letI` 打开实例）⇒ Hopf–Rinow 极小测地线
  （`exists_smooth_unit_speed_minimizing_geodesic_between_points_of_ne`）：光滑、单位速度、在
  `ContMDiffOn 1` 曲线里 `arcLength` 极小、`d(p, q) = L`、`d(p, γ t) ≤ t`；
* `continuous_riemannianEDistOf_GM`：`d(p, ·)` 连续。
  结论只含 `g.inner` / `mfderiv` / `riemannianEDistOf g`，所以可以特化到自带 Euclidean 实例的 `ℂ`。
* `t2Space_tangentBundle_complex_GM`、`neZero_finrank_complex_GM`：`ℂ` 上缺的两个实例前提。
* `mfderiv_curve_complex_GM`：`ℝ → ℂ` 曲线的 `mfderiv … 1 = deriv`。
* `sqrt_conformalEuclideanMetric_inner_GM`：`√(ĝ(v,v)) = ρ̃ ‖v‖`，`ĝ = e^{2 log ρ̃}|dz|²`。
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Interval Manifold Topology

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Hopf–Rinow wrapper：`RiemannianMetricComplete g` ⇒ `p ≠ q` 之间的光滑单位速度极小测地线，
`d(p, γ t) ≤ t`（实例全部在证明内部 `letI`）。 -/
theorem exists_minimizing_geodesic_of_complete_GM {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
    [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete (I := I) g)
    (p q : M) (hpq : p ≠ q) :
    ∃ (gamma : ℝ → M) (L : ℝ),
      0 < L ∧ gamma 0 = p ∧ gamma L = q ∧
        ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma ∧
        (∀ t : ℝ, g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) = 1) ∧
        (∀ eta : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 eta (Set.Icc 0 L) →
          eta 0 = gamma 0 → eta L = gamma L →
          Variation.arcLength (I := I) g gamma 0 L ≤ Variation.arcLength (I := I) g eta 0 L) ∧
        riemannianEDistOf (I := I) g p q = ENNReal.ofReal L ∧
        (∀ t ∈ Icc (0 : ℝ) L, riemannianEDistOf (I := I) g p (gamma t) ≤ ENNReal.ofReal t) := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨gamma, L, hL, h0, hL', hsm, -, hunit, hmin, hdist⟩ :=
    exists_smooth_unit_speed_minimizing_geodesic_between_points_of_ne
      (I := I) g hEnorm p q hpq
  have hlen (a b : ℝ) : Variation.arcLength (I := I) g gamma a b = b - a := by
    unfold Variation.arcLength
    calc (∫ t in a..b, Real.sqrt (g.inner (gamma t)
          (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))))
        = ∫ _t in a..b, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t _
          change Real.sqrt (g.inner (gamma t) (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))
            (mfderiv 𝓘(ℝ, ℝ) I gamma t (1 : ℝ))) = 1
          rw [hunit t, Real.sqrt_one]
      _ = b - a := by simp
  refine ⟨gamma, L, hL, h0, hL', hsm, hunit, hmin, hdist, ?_⟩
  intro t ht
  have hed := Riemannian.Geodesic.riemannianEDist_le_arcLength (I := I) g ht.1
    (hsm.contMDiffOn.of_le (by simp)) (fun s _ => hEnorm (gamma s) _)
  rw [h0, hlen, sub_zero] at hed
  exact hed

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- Riemannian 距离 `d_g(p, ·)` 在流形拓扑下连续（不需要 complete）。 -/
theorem continuous_riemannianEDistOf_GM {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M) :
    Continuous (fun z : M => riemannianEDistOf (I := I) g p z) := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  exact continuous_const.edist continuous_id

/-- `ℂ` 的切丛是 Hausdorff 的（model space：切丛同胚于 `ℂ × ℂ`）。 -/
theorem t2Space_tangentBundle_complex_GM : T2Space (TangentBundle 𝓘(ℝ, ℂ) ℂ) :=
  haveI : T2Space (ModelProd ℂ ℂ) := inferInstanceAs (T2Space (ℂ × ℂ))
  (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).isEmbedding.t2Space

theorem neZero_finrank_complex_GM : NeZero (Module.finrank ℝ ℂ) :=
  ⟨(Module.finrank_pos (R := ℝ) (M := ℂ)).ne'⟩

/-- `ℝ → ℂ` 曲线：`mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t 1 = deriv γ t`。 -/
theorem mfderiv_curve_complex_GM (γ : ℝ → ℂ) (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) γ t (1 : ℝ) = deriv γ t := by
  rw [mfderiv_eq_fderiv]
  rfl

/-- 共形度量 `e^{2 log ρ̃}|dz|²` 的速度：`√(ĝ(v,v)) = ρ̃ ‖v‖`（`ρ̃ > 0`）。 -/
theorem sqrt_conformalEuclideanMetric_inner_GM {ρt : ℂ → ℝ} (hρt : ∀ z, 0 < ρt z)
    (hf : ContDiff ℝ ∞ (fun z => Real.log (ρt z))) (z v : ℂ) :
    Real.sqrt ((conformalEuclideanMetric (fun z => Real.log (ρt z)) hf).inner z v v) =
      ρt z * ‖v‖ := by
  rw [conformalEuclideanMetric_inner, real_inner_self_eq_norm_sq]
  have h2 : Real.exp (2 * Real.log (ρt z)) = ρt z ^ 2 := by
    rw [show 2 * Real.log (ρt z) = Real.log (ρt z) + Real.log (ρt z) by ring, Real.exp_add,
      Real.exp_log (hρt z)]
    ring
  rw [h2, ← mul_pow, Real.sqrt_sq (mul_nonneg (hρt z).le (norm_nonneg v))]

end DifferentialGeometry.Geometry
