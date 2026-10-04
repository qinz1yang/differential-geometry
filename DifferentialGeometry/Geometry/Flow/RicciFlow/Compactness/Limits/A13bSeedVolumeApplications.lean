import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bSeedVolume

/-!
# Consumer of A13b L3: the unscaled `hvol` input

L3 (`hvol_of_traced_seed`) at the constant scale `lam n = 1`: traced regions
`isTracedRegion (t n) (y n) (k + 3) (τ k) (K k)` for every `k`, eventually in `n`, and the seed
`Vol B(y n, r₀) ≥ w r₀³`, eventually, give the `hvol` input of `LocalPointedFlowLimit.lean:221` for
the stage metrics themselves.  `scaleMetric 1 g = g` by `SmoothRiemannianMetric.ext_inner` and
`scaleMetric_one`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ContDiff ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- The `hvol` input of the local flow-limit theorem for an unscaled sequence of stages, from
traced regions of radius `k + 3` and a seed volume at radius `r₀`. -/
theorem hvol_of_traced_seed_unscaled (H : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) (y : ∀ n, ((H n).stageAt (t n)).Carrier) (τ K : ℕ → ℝ)
    (htraced : ∀ k : ℕ, ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) ((k + 3 : ℕ) : ℝ) (τ k) (K k))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * r₀ ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) r₀)) :
    ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
          ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n) r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) x a) := by
  have hone : ∀ n, scaleMetric 1 one_pos ((H n).stageMetric ((H n).activeStage (t n)) (t n)) =
      (H n).stageMetric ((H n).activeStage (t n)) (t n) := fun n =>
    SmoothRiemannianMetric.ext_inner fun x v w => by rw [scaleMetric_one]
  have h := hvol_of_traced_seed H t y (fun _ => 1) (fun _ => one_pos) τ K
    (fun k => by simpa only [Real.sqrt_one, div_one, mul_one] using htraced k) hr₀ hw
    (by simpa only [Real.sqrt_one, div_one] using hseed)
  simpa only [hone] using h

end FILL910
