import DifferentialGeometry.Geometry.Curvature.SectionalPerturbation
import DifferentialGeometry.Geometry.Curvature.NegativeSectionalStability
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Geometry.Curvature.Bounds.RiemannTensorOperator

set_option autoImplicit false

/-!
# CH12-S50 / P2 + P4: distance and curvature comparison for C^2-close metrics

Generic statements on one manifold: (P2) a pointwise inequality `h ≤ c g` of metrics gives
`d_h ≤ √c d_g`; (P4) a lower sectional bound transfers across a C^2-small metric change with explicit
constants, and a strictly violated sectional bound persists.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem riemannianEDistOf_le_of_inner_le_S50 (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hcomp : ∀ (x : M) (v : TangentSpace I x), h.inner x v v ≤ c * g.inner x v v)
    (x y : M) :
    riemannianEDistOf (I := I) h x y ≤ ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y := by
  have h0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    simpa using Real.sqrt_pos.mpr hc
  have htop : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [edistOf_iInf (I := I) g x y, ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne h0 htop]
  refine le_iInf fun hγ => ?_
  rw [edistOf_iInf (I := I) h x y]
  refine (iInf₂_le γ hγ).trans ?_
  rw [← lintegral_const_mul' _ _ htop]
  refine lintegral_mono fun t => ?_
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul hc.le]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hcomp _ _))

omit [FiniteDimensional ℝ E] [T2Space M] in
theorem riemannianBallOf_subset_of_inner_le_S50 (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hcomp : ∀ (x : M) (v : TangentSpace I x), h.inner x v v ≤ c * g.inner x v v)
    (x : M) (r : ℝ) :
    riemannianBallOf (I := I) g x r ⊆ riemannianBallOf (I := I) h x (Real.sqrt c * r) := by
  intro y hy
  have h0 : ENNReal.ofReal (Real.sqrt c) ≠ 0 := by
    simpa using Real.sqrt_pos.mpr hc
  have htop : ENNReal.ofReal (Real.sqrt c) ≠ ⊤ := ENNReal.ofReal_ne_top
  change riemannianEDistOf (I := I) h x y < ENNReal.ofReal (Real.sqrt c * r)
  calc _ ≤ ENNReal.ofReal (Real.sqrt c) * riemannianEDistOf (I := I) g x y :=
        riemannianEDistOf_le_of_inner_le_S50 g h hc hcomp x y
    _ < ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal r := (ENNReal.mul_lt_mul_iff_right h0 htop).2 hy
    _ = _ := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

section Curv
variable [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
theorem gram_eq_zero_of_not_li_S50 (g : SmoothRiemannianMetric I M) (x : M) (u v : TangentSpace I x)
    (hlin : ¬ LinearIndependent ℝ ![u, v]) :
    g.inner x u u * g.inner x v v - g.inner x u v ^ 2 = 0 := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [LinearIndependent.pair_iff' hu] at hlin
    push Not at hlin
    obtain ⟨a, rfl⟩ := hlin
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring

theorem sectionalBoundedBelow_transfer_S50 (g G : SmoothRiemannianMetric I M) (x : M)
    {eps a K : ℝ} (heps : eps ≤ 1 / 2) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps)
    (hsec : SectionalBoundedBelowAt G x (-a))
    (hRm : ∀ u v w : TangentSpace I x,
      Real.sqrt (G.inner x (riemannOp (LeviCivita G) x u v w) (riemannOp (LeviCivita G) x u v w)) ≤
        K * Real.sqrt (G.inner x u u) * Real.sqrt (G.inner x v v) * Real.sqrt (G.inner x w w)) :
    SectionalBoundedBelowAt g x (-((a + eps * (360 + K)) / (1 - eps) ^ 2)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have heps0 : 0 ≤ eps := (Real.sqrt_nonneg _).trans (hsmall 0 (by norm_num))
  have h1e : 0 < 1 - eps := by linarith
  intro u v
  by_cases hlin : LinearIndependent ℝ ![u, v]
  · obtain ⟨p, q, hp, hq, hpq, heq⟩ := exists_orthonormal_pair_sectional_quotient g x u v hlin
    have hbp := (inner_bounds_of_metricDerivNorm_le G g x (hsmall 0 (by norm_num)) p).1
    have hbq := (inner_bounds_of_metricDerivNorm_le G g x (hsmall 0 (by norm_num)) q).1
    rw [hp] at hbp
    rw [hq] at hbq
    have hGp := metric_inner_self_nonneg G x p
    have hGq := metric_inner_self_nonneg G x q
    have hP : (G.inner x p p * G.inner x q q) * (1 - eps) ^ 2 ≤ 1 := by
      have h := mul_le_mul hbp hbq (mul_nonneg h1e.le hGq) zero_le_one
      calc _ = ((1 - eps) * G.inner x p p) * ((1 - eps) * G.inner x q q) := by ring
        _ ≤ 1 * 1 := h
        _ = 1 := by norm_num
    have hGP : G.inner x p p * G.inner x q q ≤ 1 / (1 - eps) ^ 2 :=
      (le_div_iff₀ (by positivity)).2 hP
    have hsecpq := hsec p q
    have hgram : G.inner x p p * G.inner x q q - G.inner x p q ^ 2 ≤ G.inner x p p * G.inner x q q := by
      nlinarith [sq_nonneg (G.inner x p q)]
    have herr := abs_metricRm04_sub_le_of_small_metric_derivatives g G x heps hsmall p q q p
    have hR := hRm p q q
    have hNp : Real.sqrt (G.inner x p p) ^ 2 = G.inner x p p := Real.sq_sqrt hGp
    have hNq : Real.sqrt (G.inner x q q) ^ 2 = G.inner x q q := Real.sq_sqrt hGq
    have herr' : |metricRm04StandardAt g x p q q p - metricRm04StandardAt G x p q q p| ≤
        eps * (360 + K) * (G.inner x p p * G.inner x q q) := by
      refine herr.trans ?_
      calc _ ≤ eps * (360 * Real.sqrt (G.inner x p p) * Real.sqrt (G.inner x q q) * Real.sqrt (G.inner x q q) +
            K * Real.sqrt (G.inner x p p) * Real.sqrt (G.inner x q q) * Real.sqrt (G.inner x q q)) *
            Real.sqrt (G.inner x p p) := by gcongr
        _ = eps * (360 + K) * (Real.sqrt (G.inner x p p) ^ 2 * Real.sqrt (G.inner x q q) ^ 2) := by ring
        _ = _ := by rw [hNp, hNq]
    have hX : 0 ≤ a + eps * (360 + K) := by positivity
    have hlow : -(a + eps * (360 + K)) * (G.inner x p p * G.inner x q q) ≤
        metricRm04StandardAt g x p q q p := by
      have h1 := (abs_le.mp herr').1
      have h2 := mul_le_mul_of_nonneg_left hgram ha
      nlinarith
    have hfin : -((a + eps * (360 + K)) / (1 - eps) ^ 2) ≤ metricRm04StandardAt g x p q q p := by
      refine le_trans ?_ hlow
      have := mul_le_mul_of_nonneg_left hGP hX
      rw [mul_one_div] at this
      linarith
    rw [heq] at hfin
    exact (le_div_iff₀ (gram_determinant_pos g x u v hlin)).mp hfin
  · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent g x u v hlin,
      gram_eq_zero_of_not_li_S50 g x u v hlin, mul_zero]

theorem exists_eps_not_sectionalBoundedBelow_S50 (G : SmoothRiemannianMetric I M) (x : M) {s : ℝ}
    (hs : 0 ≤ s) (hns : ¬ SectionalBoundedBelowAt G x (-s)) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 2 ∧ ∀ g : SmoothRiemannianMetric I M,
      (∀ k : ℕ, k ≤ 2 → metricDerivNorm k g G G x ≤ eps) → ¬ SectionalBoundedBelowAt g x (-s) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  unfold SectionalBoundedBelowAt at hns
  push Not at hns
  obtain ⟨u, v, huv⟩ := hns
  by_cases hlin : LinearIndependent ℝ ![u, v]
  · obtain ⟨p, q, hp, hq, hpq, heq⟩ := exists_orthonormal_pair_sectional_quotient G x u v hlin
    have hc : metricRm04StandardAt G x p q q p < -s := by
      rw [heq, div_lt_iff₀ (gram_determinant_pos G x u v hlin)]
      linarith
    have hK0 : 0 ≤ Real.sqrt (normSq0S G x 4 (metricRm04At G x)) := Real.sqrt_nonneg _
    have hmodel : Real.sqrt (G.inner x (riemannOp (LeviCivita G) x p q q)
        (riemannOp (LeviCivita G) x p q q)) ≤ Real.sqrt (normSq0S G x 4 (metricRm04At G x)) := by
      have := sqrt_inner_riemannOp_le G x p q q
      simpa only [hp, hq, Real.sqrt_one, mul_one] using this
    generalize Real.sqrt (normSq0S G x 4 (metricRm04At G x)) = K at hK0 hmodel
    set d := -metricRm04StandardAt G x p q q p - s with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    have hden : 0 < 2 * (360 + K + 3 * s) := by positivity
    refine ⟨min (1 / 2) (d / (2 * (360 + K + 3 * s))), lt_min (by norm_num) (div_pos hdpos hden),
      min_le_left _ _, fun g hg hsb => ?_⟩
    set eps := min (1 / 2) (d / (2 * (360 + K + 3 * s))) with heps
    have he1 : eps ≤ 1 / 2 := min_le_left _ _
    have he2 : eps ≤ d / (2 * (360 + K + 3 * s)) := min_le_right _ _
    have he0 : 0 < eps := lt_min (by norm_num) (div_pos hdpos hden)
    have hE : eps * (360 + K + 3 * s) ≤ d / 2 := by
      have := mul_le_mul_of_nonneg_right he2 (by positivity : 0 ≤ 360 + K + 3 * s)
      refine this.trans_eq ?_
      field_simp
    refine not_sectionalBoundedBelowAt_of_small_metric_derivatives g G x
      (c := -metricRm04StandardAt G x p q q p) (a := s) (K := K) he1 hs hg p q hp hq
      (by linarith) hmodel ?_ hsb
    nlinarith [sq_nonneg eps]
  · rw [metricRm04StandardAt_eq_zero_of_not_linearIndependent G x u v hlin,
      gram_eq_zero_of_not_li_S50 G x u v hlin] at huv
    simp at huv

end Curv
end GC.LongTime.Ch12
