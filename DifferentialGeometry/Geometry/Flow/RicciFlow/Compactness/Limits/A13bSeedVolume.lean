import DifferentialGeometry.Geometry.Measure.BallComparison
import DifferentialGeometry.Geometry.Comparison.Volume.AllCentreSeedVolumeApplications
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegionShiWholeBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.SectionalFromCurvatureBound
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Scaling

/-!
# A13b, L2 and L3: the seed volume and the `hvol` input of the fixed-scale flow limit

Design: `docs/geometrization/chapter13/design-a13b-fixed-scale-flow-limit-20261004.md` (§4, §5, errata E3, E6).
Both statements are the frozen text of `build-logs/scratch/CH910-C5/A13bStatement.lean`, verbatim.

* L2 `seed_volume_scaleMetric`: the physical seed `Vol_g B(p, r₀/√λ) ≥ w (r₀/√λ)³` gives the normalised
  seed `Vol_{λg} B(p, r₀) ≥ w r₀³` (`riemannianVolumeMeasure_ball_ge_scaleMetric_iff`, backwards, with
  `c = λ`, `r = r₀/√λ`, `κ = ofReal w`).
* L3 `hvol_of_traced_seed`: the `hvol` input of `LocalPointedFlowLimit.lean:221` for the scaled sequence
  `scaleMetric (lam n) g_n(t_n)`.  Route (erratum E6, trace-endpoint variant): given `r R C`, apply
  `exists_hvol_shape_of_seed` with `Λ ρ = |K ⌈3ρ⌉₊|`; with `q = max r r₀` and `j = ⌈3q⌉₊` only
  `htraced j` and `hseed` are combined.  For `x ∈ B_{λg}(y, 3q) ⊆ B_{λg}(y, j + 3) = B_g(y, (j+3)/√λ)`,
  the trace of `x` evaluated at the current time (`endpoint_eq`) gives
  `‖Rm_g‖²(x) ≤ (K j · λ)²`; scaling gives `‖Rm_{λg}‖²(x) = λ⁻² ‖Rm_g‖²(x) ≤ (K j)²`, and
  `sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le` with `√((K j)²) = |K j|` gives
  `Sec_{λg} ≥ -|K j|`.  Squared norms throughout; `K` has no sign.
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

/-- L2.  The physical seed volume at radius `r₀/√lam` gives the normalised seed volume of
`scaleMetric lam g` at radius `r₀`. -/
theorem seed_volume_scaleMetric {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric ThreeModel M) {lam : ℝ} (hlam : 0 < lam) (p : M) {r₀ w : ℝ}
    (hr₀ : 0 < r₀) (hw : 0 < w)
    (hseed : ENNReal.ofReal (w * (r₀ / Real.sqrt lam) ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel M g
        (riemannianBallOf g p (r₀ / Real.sqrt lam))) :
    ENNReal.ofReal (w * r₀ ^ 3) ≤
      Integral.Measure.riemannianVolumeMeasure ThreeModel M (scaleMetric lam hlam g)
        (riemannianBallOf (scaleMetric lam hlam g) p r₀) := by
  have hfr : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hs : Real.sqrt lam ≠ 0 := (Real.sqrt_pos.mpr hlam).ne'
  have key := (Geometry.Measure.riemannianVolumeMeasure_ball_ge_scaleMetric_iff g lam hlam p
    (r₀ / Real.sqrt lam) (ENNReal.ofReal w)).mpr (by
      rw [hfr, ← ENNReal.ofReal_pow (div_nonneg hr₀.le (Real.sqrt_nonneg _)),
        ← ENNReal.ofReal_mul hw.le]
      exact hseed)
  rw [mul_div_cancel₀ r₀ hs, hfr, ← ENNReal.ofReal_pow hr₀.le, ← ENNReal.ofReal_mul hw.le] at key
  exact key

/-- L3.  Physical seed volume and the per-radius traced regions give the `hvol` input of
`LocalPointedFlowLimit.lean:221` for `scaleMetric (lam n) (g_n(t_n))`.  Route: L2, the current-time
bound `‖Rm‖² ≤ (K k)²` on `B_{scaled}(y n, k + 3)` (trace endpoint of the traced region, then
scaling), the sectional bound `sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le`, then
`exists_hvol_shape_of_seed` with `Λ ρ = |K ⌈3ρ⌉₊|`. -/
theorem hvol_of_traced_seed (H : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (H n).horizon) (y : ∀ n, ((H n).stageAt (t n)).Carrier)
    (lam : ℕ → ℝ) (hlam : ∀ n, 0 < lam n) (τ K : ℕ → ℝ)
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
    ∀ r R : ℝ, 0 < r → r < R → ∀ C : ℝ, 0 ≤ C →
      ∃ a κ : ℝ, 0 < a ∧ 0 < κ ∧ r + a ≤ R ∧ a ^ 4 * C ^ 2 ≤ 1 ∧
      ∀ᶠ n in atTop, ∀ x ∈ riemannianClosedBallOf
          (scaleMetric (lam n) (hlam n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)))
          (y n) r,
        ENNReal.ofReal (κ * a ^ Module.finrank ℝ ThreeSpace) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            (scaleMetric (lam n) (hlam n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)))
            (riemannianBallOf
              (scaleMetric (lam n) (hlam n) ((H n).stageMetric ((H n).activeStage (t n)) (t n)))
              x a) := by
  intro r R hr hrR C hC
  obtain ⟨a, κ, ha, hκ, hraR, haC, hall⟩ :=
    exists_hvol_shape_of_seed.{u} hr₀ hw (fun ρ => |K ⌈3 * ρ⌉₊|) (fun _ => abs_nonneg _)
      r R hr hrR C hC
  refine ⟨a, κ, ha, hκ, hraR, haC, ?_⟩
  filter_upwards [htraced ⌈3 * max r r₀⌉₊, hseed] with n htr hs
  set j : ℕ := ⌈3 * max r r₀⌉₊ with hj
  set g := (H n).stageMetric ((H n).activeStage (t n)) (t n) with hg
  refine hall ((H n).stageAt (t n)).Carrier (scaleMetric (lam n) (hlam n) g) (y n)
    (seed_volume_scaleMetric g (hlam n) (y n) hr₀ hw hs) ?_
  intro x hx
  have hl : 0 < lam n := hlam n
  have hsq : Real.sqrt (lam n) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
  -- `x` lies in the physical traced ball of radius `(j + 3)/√lam`
  have hxball : x ∈ riemannianBallOf g (y n) (((j + 3 : ℕ) : ℝ) / Real.sqrt (lam n)) := by
    rw [← riemannianBallOf_scaleMetric (lam n) (hlam n) g (y n), mul_div_cancel₀ _ hsq]
    refine riemannianBallOf_mono _ _ ?_ hx
    have h1 : 3 * max r r₀ ≤ (j : ℝ) := Nat.le_ceil _
    push_cast
    linarith
  -- the trace endpoint gives the ambient bound `|Rm_g| ≤ |K j · lam|` at time `t n`
  obtain ⟨-, -, a', hat, -, htrace⟩ := htr
  obtain ⟨A, hA⟩ := htrace x hxball
  have h1 := hA.1 (t n) hat le_rfl
  have hpt : A.point ((H n).activeStage (t n)) ((H n).activeStage_mono hat)
      ((H n).activeStage_mono le_rfl) = x := A.endpoint_eq
  rw [hpt] at h1
  -- scale: `|Rm_{lam g}|² = lam⁻² |Rm_g|² ≤ K j ²`
  have hnorm : normSq0S (scaleMetric (lam n) (hlam n) g) x 4
      (metricRm04At (scaleMetric (lam n) (hlam n) g) x) ≤ K j ^ 2 := by
    rw [← curvDerivNormSq_zero_eq_normSq0S_metricRm04At, curvDerivNormSq_scaleMetric,
      curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
    calc (lam n)⁻¹ ^ (0 + 2) * normSq0S g x 4 (metricRm04At g x)
        ≤ (lam n)⁻¹ ^ (0 + 2) * (K j * lam n) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (inv_nonneg.mpr hl.le) _)
      _ = K j ^ 2 * ((lam n)⁻¹ * lam n) ^ 2 := by ring
      _ = K j ^ 2 := by rw [inv_mul_cancel₀ hl.ne', one_pow, mul_one]
  have hsec := sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le _ x hnorm
  rw [Real.sqrt_sq_eq_abs] at hsec
  exact hsec

end FILL910
