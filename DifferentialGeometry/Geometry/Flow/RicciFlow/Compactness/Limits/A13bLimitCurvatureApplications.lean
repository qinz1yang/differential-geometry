import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bLimitCurvature

/-!
# A13b with the limit curvature bound (consumer of G4)

`FILL910.A13b_limit_curvature_bound` calls A13b and the G4 transfer
`curvDerivNormSq_zero_le_of_local_flow_limit` with the bound `K k ^ 2` of output (i): the local limit
flows `Gloc k` on the balls `V k = B_P(basepoint, (k + 1)/2)` satisfy `|Rm|² ≤ (K k)²` on
`[-(τ k / 2), 0]` (erratum E7; `K k` has no sign, so the bound reads `|Rm| ≤ |K k|`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- A13b + G4: under the inputs of A13b, a subsequence of the scaled stages converges to a complete
connected pointed limit `P`; the balls `V k = B_P(basepoint, (k + 1)/2)` carry compatible Ricci flows
`Gloc k` on `[-(τ k / 2), 0]` with time-0 metric the limit metric and `|Rm|² ≤ (K k)²`. -/
theorem A13b_limit_curvature_bound
    (H : ℕ → ObservedHistory.{u}) (t : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (y : ∀ n, ((H n).stageAt (t n)).Carrier) (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n)
    (τ K : ℕ → ℝ) (hτ : ∀ k, 0 < τ k)
    (htraced : ∀ k : ℕ, ∀ᶠ n in atTop,
      (H n).isTracedRegion (t n) (y n) (((k + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) (τ k / lam n)
        (K k * lam n))
    {r₀ w : ℝ} (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ∀ᶠ n in atTop,
      ENNReal.ofReal (w * (r₀ / Real.sqrt (lam n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (lam n)))) :
    let X : PointedRiemannianSeq.{u, 0, 0} ThreeModel :=
      { obj := fun n =>
          { M := ((H n).stageAt (t n)).Carrier
            basepoint := y n
            metric := scaleMetric (lam n) (hlam n)
              ((H n).stageMetric ((H n).activeStage (t n)) (t n)) } }
    ∃ (f : ℕ → ℕ), StrictMono f ∧
      ∃ (P : PointedRiemannianManifold.{u, 0, 0} ThreeModel)
        (_ : PointedRiemannianConvergenceMaps X P f),
        MetricComplete P ∧ ConnectedSpace P.M ∧
        ∃ (V : ℕ → Opens P.M) (Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k)),
          (∀ k, (V k : Set P.M) =
            riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) ∧
          (∀ k, Gloc k 0 = P.metric.restrictOpen (V k)) ∧
          (∀ k, IsSolutionOn ({ base.metric := Gloc k } :
            SolutionOn (I := ThreeModel) (M := V k)
              (RealTimeInterval.closed (-(τ k / 2)) 0 (neg_nonpos.mpr (half_pos (hτ k)).le)))) ∧
          (∀ k l, ∀ s ∈ Icc (-(τ k / 2)) 0, s ∈ Icc (-(τ l / 2)) 0 →
            (Gloc k s).restrictOpenOfSubset (inf_le_left : V k ⊓ V l ≤ V k) =
              (Gloc l s).restrictOpenOfSubset (inf_le_right : V k ⊓ V l ≤ V l)) ∧
          ∀ k, ∀ s ∈ Icc (-(τ k / 2)) 0, ∀ z : V k,
            curvDerivNormSq 0 (Gloc k s) z ≤ K k ^ 2 := by
  intro X
  obtain ⟨W, h, hdata, -, -, f, hf, P, F, -, hPc, hconn, -, V, N, hV, -, φ, hφ, -, Gloc, hG0, hG,
    hGcompat, ψ, hψ, hconv⟩ :=
    A13b_fixed_scale_local_flow_limit H t y lam hlam τ K hτ htraced hr₀ hw hseed
  refine ⟨f, hf, P, F, hPc, hconn, V, Gloc, hV, hG0, hG, hGcompat, ?_⟩
  refine curvDerivNormSq_zero_le_of_local_flow_limit (X := X) (W := W) (h := h) (N := N) (φ := φ)
    (hφ := hφ) (c := fun k => τ k / 2) hf hψ hconv fun k => ?_
  filter_upwards [hdata k] with n hn s hs x
  exact hn.2.2.2.1 s ⟨(neg_le_neg (half_lt_self (hτ k)).le).trans hs.1, hs.2⟩ x

end FILL910
