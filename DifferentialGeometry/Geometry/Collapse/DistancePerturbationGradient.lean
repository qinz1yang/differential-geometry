import DifferentialGeometry.Geometry.Collapse.RiemannianOutwardPoint
import DifferentialGeometry.Geometry.Comparison.Soul.NoncriticalDistance
import DifferentialGeometry.Geometry.Comparison.Soul.DistanceGradient
import DifferentialGeometry.Geometry.Operator.Gradient.LipschitzBound
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

/-!
# LC29: a smooth perturbation of a distance function has nonzero gradient

Blueprint 207A, LC29 (`lem:collapse-distance-perturbation-gradient`, A:21183–21212). On a
complete Riemannian manifold, if `F - d_p` is globally `ε`-Lipschitz and `F` is differentiable at
`q ≠ p`, then `1 - ε ≤ ‖∇F(q)‖_g ≤ 1 + ε`.

Proof route (different from the blueprint's Rademacher/density argument, which it allows): the
upper bound is the gradient bound of the `(1 + ε)`-Lipschitz function `F`
(`grad_norm_le_lip`). For the lower bound take a minimizing unit geodesic `γ` from `q` to `p`
(Hopf–Rinow, `minimizingDirectionsTo_nonempty`); along it `d_p(γ t) = d_p(q) - t` and
`d(q, γ t) ≤ t`, so `F(γ t) - F(q) ≤ -(1 - ε) t` for small `t ≥ 0`. The derivative of `F ∘ γ` at
`0` is `g(∇F(q), γ'(0))` with `|γ'(0)| = 1`, so `g(∇F(q), γ'(0)) ≤ -(1 - ε)` and Cauchy–Schwarz
gives the bound. Only the derivative at `q` itself is used; no first variation through a cut
point and no measure theory.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set Filter
open scoped Topology ContDiff Manifold ENNReal NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- LC29, pointwise form: if `F - d_p` is globally `ε`-Lipschitz and `F` is differentiable at
`q ≠ p`, then `1 - ε ≤ ‖∇F(q)‖_g ≤ 1 + ε`. -/
theorem one_sub_le_norm_gradFun_and_le_one_add (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (p : M) {ε : ℝ} (hε : 0 ≤ ε) {F : M → ℝ}
    (hlip : ∀ x y, |(F x - dist x p) - (F y - dist y p)| ≤ ε * dist x y) {q : M} (hqp : q ≠ p)
    (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F q) :
    1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
      Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε := by
  constructor
  · obtain ⟨u, hu, hend⟩ := minimizingDirectionsTo_nonempty g hEnorm (singleton_nonempty p)
      isCompact_singleton (by simpa only [mem_singleton_iff] using hqp)
    set d := Metric.infDist q {p} with hd_def
    have hd : 0 < d := by rw [hd_def, Metric.infDist_singleton]; exact dist_pos.mpr hqp
    let γ := intrinsicGeodesic g hEnorm q u
    have hγ0 : γ 0 = q := intrinsicGeodesic_zero g hEnorm q u
    have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ := intrinsicGeodesic_contMDiff g hEnorm q u
    have hcomp := hasDerivAt_comp_mfderiv_along I F γ 0 (by simpa only [hγ0] using hF)
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
    have hstep (t : ℝ) (ht : t ∈ Icc 0 d) : F (γ t) - F (γ 0) ≤ -(1 - ε) * t := by
      have hdist := infDist_intrinsicGeodesic_to_set g hEnorm hu hend ht
      rw [Metric.infDist_singleton, Metric.infDist_singleton] at hdist
      have hqt : dist q (γ t) ≤ t := by
        simpa only [intrinsicGeodesic_zero, hu, Real.sqrt_one, one_mul, sub_zero] using
          dist_intrinsicGeodesic_le_mul g hEnorm q u ht.1
      have hdist' : dist (γ t) p = dist q p - t := hdist
      have hl := (abs_le.mp (hlip (γ t) q)).2
      rw [dist_comm (γ t) q] at hl
      rw [hγ0]
      nlinarith
    have hslope := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi (0 : ℝ))
      (by simp)).mp hcomp.hasDerivWithinAt
    have hD : _ ≤ -(1 - ε) := le_of_tendsto hslope (by
      filter_upwards [Ioo_mem_nhdsGT hd] with t ht
      rw [slope_def_field, sub_zero, div_le_iff₀ ht.1]
      exact hstep t ⟨ht.1.le, ht.2.le⟩)
    change mvfderiv (I := I) F (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) ≤ -(1 - ε) at hD
    have hvel : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (u : E) :=
      intrinsicGeodesic_mfderiv_zero g hEnorm q u
    rw [hvel] at hD
    erw [hγ0] at hD
    have hinner : g.inner q (gradFun g F q) u ≤ -(1 - ε) := by
      have h := inner_gradientFun g F q u
      exact h.trans_le hD
    have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g q (gradFun g F q) u
    rw [hu, mul_one] at hcs
    rcases le_or_gt (1 - ε) 0 with hneg | hpos
    · exact hneg.trans (Real.sqrt_nonneg _)
    · apply Real.le_sqrt_of_sq_le
      nlinarith
  · have hL : 0 ≤ 1 + ε := by linarith
    let L : ℝ≥0 := ⟨1 + ε, hL⟩
    have hu : ∀ y z, edist (F y) (F z) ≤ (L : ℝ≥0∞) * riemannianEDistOf g y z := by
      intro y z
      rw [riemannianEDistOf_eq_riemannianEDist g hEnorm, ← IsRiemannianManifold.out (I := I),
        edist_dist, edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (NNReal.coe_nonneg L)]
      apply ENNReal.ofReal_le_ofReal
      change |F y - F z| ≤ (1 + ε) * dist y z
      have hl := abs_le.mp (hlip y z)
      have htri := abs_dist_sub_le y z p
      rw [abs_le]
      constructor <;> nlinarith [abs_le.mp htri]
    exact grad_norm_le_lip g hu hF

/-- LC29 in the blueprint's form: if `F` is smooth on an open `W ⊆ M \ {p}` and `F - d_p` is
globally `ε`-Lipschitz, then `1 - ε ≤ ‖∇F‖_g ≤ 1 + ε` on `W`. -/
theorem one_sub_le_norm_gradFun_and_le_one_add_on (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) (p : M) {ε : ℝ} (hε : 0 ≤ ε) {F : M → ℝ}
    (hlip : ∀ x y, |(F x - dist x p) - (F y - dist y p)| ≤ ε * dist x y) {W : Set M}
    (hW : IsOpen W) (hpW : p ∉ W) (hF : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F W) :
    ∀ q ∈ W, 1 - ε ≤ Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ∧
      Real.sqrt (g.inner q (gradFun g F q) (gradFun g F q)) ≤ 1 + ε := fun q hq =>
  one_sub_le_norm_gradFun_and_le_one_add g hEnorm p hε hlip (fun h => hpW (h ▸ hq))
    ((hF.contMDiffAt (hW.mem_nhds hq)).mdifferentiableAt (by simp))

end DifferentialGeometry.Geometry.Collapse
