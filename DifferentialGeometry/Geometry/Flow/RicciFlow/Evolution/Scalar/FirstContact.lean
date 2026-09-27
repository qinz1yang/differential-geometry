import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.DerivativeRegularity
import DifferentialGeometry.Geometry.Operator.Scalar.Calculus
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Topology.Order.IntermediateValue

section
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Operator
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem norm_gradient_le_iff_differential_le
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) {A : ℝ} (hA : 0 ≤ A) :
    g.inner x (gradientFun g f x) (gradientFun g f x) ≤ A ^ 2 ↔
      ∀ v : TangentSpace I x, |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x v)| ≤
        A * Real.sqrt (g.inner x v v) := by
  have hn : 0 ≤ g.inner x (gradientFun g f x) (gradientFun g f x) :=
    metric_inner_self_nonneg g x _
  constructor
  · intro h v
    have hs : Real.sqrt (g.inner x (gradientFun g f x) (gradientFun g f x)) ≤ A :=
      (Real.sqrt_le_left hA).mpr h
    change |mvfderiv (I := I) f x v| ≤ _
    rw [← inner_gradientFun]
    exact (Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic g x _ v).trans
      (mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _))
  · intro h
    have hh := h (gradientFun g f x)
    change |mvfderiv (I := I) f x (gradientFun g f x)| ≤ _ at hh
    rw [← inner_gradientFun, abs_of_nonneg hn] at hh
    have hs := Real.sq_sqrt hn
    nlinarith [Real.sqrt_nonneg (g.inner x (gradientFun g f x) (gradientFun g f x))]

private theorem exists_gradient_direction_of_norm_gradient_eq
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M) {A : ℝ} (hA : 0 < A)
    (hcontact : g.inner x (gradientFun g f x) (gradientFun g f x) = A ^ 2) :
    ∃ v : TangentSpace I x, v ≠ 0 ∧
      A * Real.sqrt (g.inner x v v) = |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) f x v)| := by
  refine ⟨gradientFun g f x, ?_, ?_⟩
  · intro hzero
    rw [hzero] at hcontact
    simp only [map_zero] at hcontact
    nlinarith [sq_pos_of_pos hA]
  · change A * Real.sqrt (g.inner x (gradientFun g f x) (gradientFun g f x)) =
      |mvfderiv (I := I) f x (gradientFun g f x)|
    rw [← inner_gradientFun, hcontact, Real.sqrt_sq hA.le, abs_of_nonneg (sq_nonneg A)]
    ring

end DifferentialGeometry.Geometry.Operator

end
end

section
noncomputable section
open Set DifferentialGeometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.SolutionOn
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] {D : RealTimeInterval}

theorem exists_first_scalar_derivative_contact_above_scalar_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b C q Q : ℝ} (hab : a ≤ b) (hinterval : Icc a b ⊆ D.regular)
    (hC : 0 < C) (hq : 0 < q) (hqQ : q ≤ Q)
    (hinitial : ∀ x : M,
      (S.base.metric a).inner x (gradientFun (S.base.metric a) (S.scalar a) x)
        (gradientFun (S.base.metric a) (S.scalar a) x) < C ^ 2 * (max q (S.scalar a x)) ^ 3 ∧
      |derivWithin (fun t => S.scalar t x) (Iic a) a| < C * (max q (S.scalar a x)) ^ 2)
    (hlow : ∀ t ∈ Icc a b, ∀ x : M, S.scalar t x ≤ Q →
      (S.base.metric t).inner x (gradientFun (S.base.metric t) (S.scalar t) x)
        (gradientFun (S.base.metric t) (S.scalar t) x) < C ^ 2 * (max q (S.scalar t x)) ^ 3 ∧
      |derivWithin (fun v => S.scalar v x) (Iic t) t| < C * (max q (S.scalar t x)) ^ 2)
    (hfail : ∃ x : M,
      C ^ 2 * (max q (S.scalar b x)) ^ 3 ≤
        (S.base.metric b).inner x (gradientFun (S.base.metric b) (S.scalar b) x)
          (gradientFun (S.base.metric b) (S.scalar b) x) ∨
      C * (max q (S.scalar b x)) ^ 2 ≤ |derivWithin (fun t => S.scalar t x) (Iic b) b|) :
    ∃ τ ∈ Ioc a b, ∃ x : M, Q < S.scalar τ x ∧
      ((∃ v : TangentSpace I x, v ≠ 0 ∧
        C * S.scalar τ x * Real.sqrt (S.scalar τ x) *
            Real.sqrt ((S.base.metric τ).inner x v v) =
          |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (S.scalar τ) x v)|) ∨
        |derivWithin (fun t => S.scalar t x) (Iic τ) τ| = C * S.scalar τ x ^ 2) ∧
      (∀ t ∈ Ico a τ, ∀ y : M, q ≤ S.scalar t y →
        (S.base.metric t).inner y (gradientFun (S.base.metric t) (S.scalar t) y)
          (gradientFun (S.base.metric t) (S.scalar t) y) < C ^ 2 * S.scalar t y ^ 3 ∧
        (∀ v : TangentSpace I y, |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (S.scalar t) y v)| ≤
          C * S.scalar t y * Real.sqrt (S.scalar t y) *
            Real.sqrt ((S.base.metric t).inner y v v)) ∧
        |derivWithin (fun v => S.scalar v y) (Iic t) t| < C * S.scalar t y ^ 2) ∧
      (∀ y : M, q ≤ S.scalar τ y →
        (∀ v : TangentSpace I y, |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (S.scalar τ) y v)| ≤
          C * S.scalar τ y * Real.sqrt (S.scalar τ y) *
            Real.sqrt ((S.base.metric τ).inner y v v)) ∧
        |derivWithin (fun v => S.scalar v y) (Iic τ) τ| ≤ C * S.scalar τ y ^ 2) := by
  let F : ℝ × M → ℝ := fun z => max
    ((S.base.metric z.1).inner z.2
      (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2)
      (gradientFun (S.base.metric z.1) (S.scalar z.1) z.2) -
        C ^ 2 * (max q (S.scalar z.1 z.2)) ^ 3)
    (|derivWithin (fun t => S.scalar t z.2) (Iic z.1) z.1| -
      C * (max q (S.scalar z.1 z.2)) ^ 2)
  have hF : ContinuousOn F (Icc a b ×ˢ univ) :=
    (S.scalar_derivative_residual_continuousOn hS C q).mono (prod_mono hinterval Subset.rfl)
  have hFa (x : M) : F (a, x) < 0 :=
    max_lt (sub_neg.mpr (hinitial x).1) (sub_neg.mpr (hinitial x).2)
  have hFb : ∃ x : M, 0 ≤ F (b, x) := by
    obtain ⟨x, hx⟩ := hfail
    refine ⟨x, ?_⟩
    exact le_max_iff.mpr (hx.elim (fun h => Or.inl (sub_nonneg.mpr h))
      (fun h => Or.inr (sub_nonneg.mpr h)))
  obtain ⟨τ, hτ, x, hcontact, hbefore, hat⟩ := hF.exists_first_level_of_compact hab hFa hFb
  have hhigh : Q < S.scalar τ x := by
    by_contra h
    have hb := hlow τ ⟨hτ.1.le, hτ.2⟩ x (le_of_not_gt h)
    have hn : F (τ, x) < 0 := max_lt (sub_neg.mpr hb.1) (sub_neg.mpr hb.2)
    exact hn.ne hcontact
  have hsqrt (t : ℝ) (y : M) (hy : q ≤ S.scalar t y) :
      (C * S.scalar t y * Real.sqrt (S.scalar t y)) ^ 2 = C ^ 2 * S.scalar t y ^ 3 := by
    have hh := Real.sq_sqrt ((hq.trans_le hy).le)
    calc
      _ = C ^ 2 * S.scalar t y ^ 2 * (Real.sqrt (S.scalar t y)) ^ 2 := by ring
      _ = _ := by rw [hh]; ring
  have hconvert (t : ℝ) (y : M) (hy : q ≤ S.scalar t y)
      (hg : (S.base.metric t).inner y (gradientFun (S.base.metric t) (S.scalar t) y)
        (gradientFun (S.base.metric t) (S.scalar t) y) ≤ C ^ 2 * S.scalar t y ^ 3) :
      ∀ v : TangentSpace I y, |(show ℝ from mfderiv I 𝓘(ℝ, ℝ) (S.scalar t) y v)| ≤
        C * S.scalar t y * Real.sqrt (S.scalar t y) *
          Real.sqrt ((S.base.metric t).inner y v v) := by
    have hRy : 0 < S.scalar t y := hq.trans_le hy
    apply (DifferentialGeometry.Geometry.Operator.norm_gradient_le_iff_differential_le _ _ _ (by positivity)).mp
    rwa [hsqrt t y hy]
  refine ⟨τ, hτ, x, hhigh, ?_, ?_, ?_⟩
  · have hqx : q ≤ S.scalar τ x := hqQ.trans hhigh.le
    change max _ _ = 0 at hcontact
    rw [max_eq_right hqx] at hcontact
    rcases (max_eq_iff.mp hcontact) with ⟨hg, _⟩ | ⟨ht, _⟩
    · left
      have hg' : (S.base.metric τ).inner x (gradientFun (S.base.metric τ) (S.scalar τ) x)
          (gradientFun (S.base.metric τ) (S.scalar τ) x) =
          (C * S.scalar τ x * Real.sqrt (S.scalar τ x)) ^ 2 := by
        rw [hsqrt τ x hqx]
        exact sub_eq_zero.mp hg
      have hRx : 0 < S.scalar τ x := hq.trans_le hqx
      exact DifferentialGeometry.Geometry.Operator.exists_gradient_direction_of_norm_gradient_eq _ _ _ (by positivity) hg'
    · exact Or.inr (sub_eq_zero.mp ht)
  · intro t ht y hy
    have hb := max_lt_iff.mp (hbefore t ht y)
    dsimp only [F] at hb
    rw [max_eq_right hy] at hb
    exact ⟨sub_neg.mp hb.1, hconvert t y hy (sub_nonpos.mp hb.1.le), sub_neg.mp hb.2⟩
  · intro y hy
    have hb := max_le_iff.mp (hat y)
    dsimp only [F] at hb
    rw [max_eq_right hy] at hb
    exact ⟨hconvert τ y hy (sub_nonpos.mp hb.1), sub_nonpos.mp hb.2⟩

end DifferentialGeometry.PDE.RicciFlow.SolutionOn

end
end
