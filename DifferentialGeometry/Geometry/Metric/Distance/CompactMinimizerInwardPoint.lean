import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold MeasureTheory Set
open scoped Topology Manifold ContDiff ENNReal

open Bundle Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian

open Exponential
open HopfRinow

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

theorem exists_inward_point_and_minimizer_of_isCompact_closedBall
    (g : SmoothRiemannianMetric I M) (p x : M) {R r R' : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hx : x ∈ riemannianClosedBallOf g p R)
    (hRR' : R < R') (hcompact : IsCompact (riemannianClosedBallOf g p R')) :
    ∃ (γ : ℝ → M) (d : ℝ),
      γ 0 = p ∧ γ (riemannianEDistOf g p x).toReal = x ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 (riemannianEDistOf g p x).toReal) ∧
      (∀ a ∈ Icc 0 (riemannianEDistOf g p x).toReal,
        ∀ b ∈ Icc 0 (riemannianEDistOf g p x).toReal,
          riemannianEDistOf g (γ a) (γ b) = ENNReal.ofReal |a - b|) ∧
      d ∈ Icc 0 (riemannianEDistOf g p x).toReal ∧ d ≤ R - r ∧
      (riemannianEDistOf g p x).toReal - d ≤ r ∧
      riemannianEDistOf g (γ d) x ≤ ENNReal.ofReal r ∧
      riemannianClosedBallOf g (γ d) (r / 2) ⊆ riemannianBallOf g p R := by
  have hR : 0 < R := hr.trans_le hrR
  have hdist : riemannianEDistOf g p x ≤ ENNReal.ofReal R := hx
  have hdistR : riemannianEDistOf g p x < ENNReal.ofReal R' :=
    hdist.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hR.trans hRR')).mpr hRR')
  obtain ⟨γ, hzero, hend, hsmooth, hmetric⟩ :=
    exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall
      g p x hdistR hcompact
  let l := (riemannianEDistOf g p x).toReal
  let d := max 0 (l - r)
  have hl : 0 ≤ l := ENNReal.toReal_nonneg
  have hlR : l ≤ R := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hdist).trans_eq
      (ENNReal.toReal_ofReal hR.le)
  have hd0 : 0 ≤ d := le_max_left _ _
  have hdl : d ≤ l := max_le hl (by linarith)
  have hdR : d ≤ R - r := max_le (sub_nonneg.mpr hrR) (sub_le_sub_right hlR r)
  have hld : l - d ≤ r := by
    have h := le_max_right (0 : ℝ) (l - r)
    dsimp only [d]
    linarith
  refine ⟨γ, d, hzero, hend, hsmooth, hmetric, ⟨hd0, hdl⟩, hdR, hld, ?_, ?_⟩
  · rw [← hend, hmetric d ⟨hd0, hdl⟩ l ⟨hl, le_rfl⟩,
      abs_of_nonpos (sub_nonpos.mpr hdl)]
    apply ENNReal.ofReal_le_ofReal
    linarith
  · intro y hy
    have hpz : riemannianEDistOf g p (γ d) = ENNReal.ofReal d := by
      rw [← hzero, hmetric 0 ⟨le_rfl, hl⟩ d ⟨hd0, hdl⟩, zero_sub, abs_neg,
        abs_of_nonneg hd0]
    have hpy := (riemannianEDistOf_triangle g p (γ d) y).trans (add_le_add hpz.le hy)
    rw [← ENNReal.ofReal_add hd0 (by positivity : 0 ≤ r / 2)] at hpy
    exact hpy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith))

end DifferentialGeometry.Geometry.Riemannian
