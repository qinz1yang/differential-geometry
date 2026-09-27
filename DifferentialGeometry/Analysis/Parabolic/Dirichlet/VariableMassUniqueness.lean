import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.CoerciveMassUniqueness
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletCompactness

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal NNReal Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem eq_zero_of_variable_mass_dirichlet_equation
    (g : SmoothRiemannianMetric I_hs M) {T : ℝ} (hT : 0 ≤ T)
    (v : ℝ → M → ℝ) {c L : ℝ} (hsmall : L * T < c)
    (hv : ∀ᵐ t ∂timeMeasure T,
      ∀ᵐ x ∂riemannianVolumeMeasure (I := I_hs) (M := M) g, c ≤ v t x)
    (Z : timeL2 (H1ComplDirichlet g) T)
    (d r : timeL2 (Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) g)) T)
    (D : timeH1 (H1ComplDirichlet g →L[ℝ] ℝ) T) (hD0 : D.initial = 0)
    (hD : ∀ᵐ t ∂timeMeasure T, ∀ z,
      D.toFun t z = inner ℝ (H1ComplDirichletToLp g z) (d t))
    (hDd : ∀ᵐ t ∂timeMeasure T, ∀ z,
      D.deriv t z = inner ℝ (H1ComplDirichletToLp g (Z t)) (H1ComplDirichletToLp g z) -
        inner ℝ (Z t) z + inner ℝ (r t) (H1ComplDirichletToLp g z))
    (hp : ∀ᵐ t ∂timeMeasure T, d t =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) g]
      fun x => v t x * H1ComplDirichletToLp g (Z t) x)
    (hr : ∀ᵐ t ∂timeMeasure T, ∀ᵐ x ∂riemannianVolumeMeasure (I := I_hs) (M := M) g,
      |r t x| ≤ L * |H1ComplDirichletToLp g (Z t) x|) : Z = 0 := by
  let μ := riemannianVolumeMeasure (I := I_hs) (M := M) g
  let J := H1ComplDirichletToLp g
  let A : H1ComplDirichlet g →L[ℝ] H1ComplDirichlet g →L[ℝ] ℝ :=
    innerSL ℝ - (innerSL ℝ).bilinearComp J J
  have hA (u z : H1ComplDirichlet g) : A u z = inner ℝ u z - inner ℝ (J u) (J z) := rfl
  have hApos (u : H1ComplDirichlet g) : 0 ≤ A u u := by
    rw [hA, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hn := norm_H1ComplDirichletToLp_apply_le g u
    nlinarith only [hn, norm_nonneg (J u), norm_nonneg u]
  apply Z.eq_zero_of_coercive_mass_dual hT J (H1ComplDirichletToLp_injective g) A
      (fun u z => by simp only [hA, real_inner_comm]) hApos r D hD0 ?_ hsmall ?_ ?_
  · filter_upwards [hDd] with t ht
    intro z
    rw [ht z, hA]
    ring
  · filter_upwards [hD, hp, hv] with t ht hpt hvt
    rw [ht (Z t), L2.inner_def]
    have hsq : c * ‖J (Z t)‖ ^ 2 = ∫ x, c * (J (Z t) x) ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    rw [hsq]
    apply integral_mono_ae ((Lp.memLp (J (Z t))).norm.integrable_sq.const_mul c |>.congr ?_)
      ((Lp.memLp (J (Z t))).integrable_mul (Lp.memLp (d t)) |>.congr ?_) ?_
    · filter_upwards with x
      simp only [Real.norm_eq_abs, sq_abs]
    · filter_upwards with x
      simp only [Pi.mul_apply, RCLike.inner_apply, conj_trivial]
      ring
    · filter_upwards [hpt, hvt] with x hpx hvx
      change c * (J (Z t) x) ^ 2 ≤ inner ℝ (J (Z t) x) (d t x)
      rw [hpx]
      have hh := mul_le_mul_of_nonneg_right hvx (sq_nonneg (J (Z t) x))
      simpa only [RCLike.inner_apply, conj_trivial, pow_two, mul_assoc, mul_left_comm] using hh
  · filter_upwards [hr] with t ht
    exact Lp.norm_le_mul_norm_of_ae_le_mul (by simpa only [Real.norm_eq_abs] using ht)

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
