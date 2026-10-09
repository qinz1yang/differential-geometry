import DifferentialGeometry.Geometry.Collapse.RescaledLimits.LowDimensionalLimit
import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottConvergence

/-!
# LC08: the uniform metric model contract

Blueprint 207A, LC08 (`thm:collapse-uniform-model`, A:20217). For every `0 < σ < 1` there are
`0 < w₀ < c₃ = 4π/3` and `L₀ ≥ 4` such that every complete Riemannian three-manifold `(M, g, p)`
and every `ρ > 0` with a volume level `0 < w < w₀` attained at a radius `r ≤ 2ρ` and with
`sec_g ≥ -(L₀ ρ)⁻²` on `B(p, L₀ ρ)` admit an actual pointed Kleiner–Lott `σ`-approximation from
`(M, ρ⁻² g, p)` to a complete proper geodesic space with nonnegative four-point comparison and
Hausdorff dimension at most two. The constants do not depend on `M, g, p, ρ, w, r`.

The proof is the blueprint's: a failure for some `σ` gives counterexamples with `L₀ = n + 4` and
`w₀ ≤ 1/(n+1)`; LC07 (`exists_rescaled_pointed_limit_dimH_le_two`) gives a subsequential pointed
limit of dimension at most two, and MC11 (`PointedGHConverges.eventually_kleinerLott_approx`)
gives actual `σ`-approximations to it at late indices, contradicting the choice.

The blueprint asks for the FIRST volume scale `r_p(w)`; any attained radius suffices.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **LC08**, the uniform metric model contract. -/
theorem exists_uniform_metric_model (hdim : Module.finrank ℝ E = 3) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ < 1) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < 4 * Real.pi / 3 ∧ ∃ L₀ : ℝ, 4 ≤ L₀ ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [CompleteSpace M]
        (g : SmoothRiemannianMetric I M),
        (∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
        ∀ (p : M) (ρ w r : ℝ) (hρ : 0 < ρ), 0 < w → w < w₀ → 0 < r → r ≤ 2 * ρ →
          ballVolume g p r = ENNReal.ofReal (w * r ^ 3) →
          (∀ y ∈ riemannianBallOf g p (L₀ * ρ),
            SectionalBoundedBelowAt g y (-((L₀ * ρ) ^ 2)⁻¹)) →
          ∃ (Y : Type) (mY : MetricSpace Y),
            letI := mY
            ∃ q : Y, CompleteSpace Y ∧ ProperSpace Y ∧ dimH (univ : Set Y) ≤ 2 ∧
              fourPointComparison 0 (univ : Set Y) ∧
              (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
                f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
                ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
              Nonempty (@KleinerLottApprox M Y (m.rescale ρ⁻¹ (inv_pos.mpr hρ)) mY p q σ) := by
  by_contra hneg
  let W : ℕ → ℝ := fun n => min (2 * Real.pi / 3) (1 / ((n : ℝ) + 1))
  have hW : ∀ n, 0 < W n ∧ W n < 4 * Real.pi / 3 := fun n =>
    ⟨lt_min (by positivity) (by positivity),
      (min_le_left _ _).trans_lt (by linarith [Real.pi_pos])⟩
  push Not at hneg
  have hcounter := fun n : ℕ => hneg (W n) (hW n).1 (hW n).2 ((n : ℝ) + 4)
    (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  choose M mM cM iM sM kM g hmetric p ρ w r hρ hw hwW hr hrρ hvol hsec hnot using hcounter
  have hL : Tendsto (fun n : ℕ => (n : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
  have hwzero : Tendsto w atTop (𝓝 0) :=
    squeeze_zero (fun n => (hw n).le) (fun n => (hwW n).le.trans (min_le_right _ _))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨Y, mY, q, φ, -, hcomplete, hproper, hconv, hdim2, hcomp, hseg⟩ :=
    exists_rescaled_pointed_limit_dimH_le_two (mX := mM) hdim g hmetric p hρ hL hsec hw hwzero hr
      hrρ hvol
  let := mY
  let : ∀ n, MetricSpace (M (φ n)) := fun n =>
    (mM (φ n)).rescale (ρ (φ n))⁻¹ (inv_pos.mpr (hρ (φ n)))
  obtain ⟨n, hn⟩ := (hconv.eventually_kleinerLott_approx hσ hσ1).exists
  exact (hnot (φ n) Y mY q hcomplete hproper hdim2 hcomp hseg).false hn.some

end DifferentialGeometry.Geometry.Collapse
