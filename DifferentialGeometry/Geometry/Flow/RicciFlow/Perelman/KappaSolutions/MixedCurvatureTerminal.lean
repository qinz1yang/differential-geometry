import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.CurvatureJetPolynomialContinuity
import DifferentialGeometry.Geometry.Metric.Variation.TerminalTimeDerivative


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open CanonicalNeighborhood.FiniteHorn
open Bundle Manifold Filter DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance mixedTerminalC1 : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
private local instance mixedTerminalC2 : IsManifold I 2 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)


def mixedCurvatureTensor {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (p q : ℕ) (t : ℝ) (x : M) :
    Tensor0SSpace (4 + p) I x :=
  iteratedMetricTimeDerivWithin S.base.metric D.carrier
    (fun s => nablaKRm04Field S s p x) q t


def mixedCurvatureNorm {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (p q : ℕ) (t : ℝ) (x : M) : ℝ :=
  Real.sqrt (normSq0S (I := I) (S.base.metric t) x (4 + p) (mixedCurvatureTensor S p q t x))

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
@[simp] theorem mixedCurvatureTensor_zero {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (p : ℕ) (t : ℝ) (x : M) :
    mixedCurvatureTensor S p 0 t x = nablaKRm04Field S t p x := rfl


theorem mixedCurvature_polynomial_terminal_of_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (p : ℕ) {a b : ℝ} (hab : a < b) (hcarrier : D.carrier = Set.Iic b)
    (hreg : Set.Ioo a b ⊆ D.regular)
    {n : ℕ} (P : (q : ℕ) → (Fin (4 + p) → Fin n) →
      MvPolynomial (CurvatureJetPolynomialVariable n (p + 2 * q)) ℝ)
    (x : M) (basis : Module.Basis (Fin n) ℝ (TangentSpace I x))
    (hP : ∀ q, ∀ t ∈ Set.Ioo a b,
      DifferentiableAt ℝ (fun s => mixedCurvatureTensor S p q s x) t ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q t x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) t basis) (P q slots)) :
    ∀ q, DifferentiableWithinAt ℝ (fun s => mixedCurvatureTensor S p q s x) (Set.Iic b) b ∧
      ∀ slots, component0S (I := I) basis (mixedCurvatureTensor S p q b x) slots =
        MvPolynomial.eval (curvatureJetPolynomialValues S (p + 2 * q) b basis) (P q slots) := by
  let A : ℕ → ℝ → Tensor0SSpace (4 + p) I x := fun q t => mixedCurvatureTensor S p q t x
  let B : ℕ → ℝ → Tensor0SSpace (4 + p) I x := fun q t =>
    tensorOfPolynomialComponents basis (P q) (curvatureJetPolynomialValues S (p + 2 * q) t basis)
  have hslab : Set.Icc a b ⊆ D.carrier := by
    rw [hcarrier]
    exact fun _ ht => ht.2
  have hB (q : ℕ) : ContinuousWithinAt (B q) (Set.Iio b) b :=
    solution_curvatureJetPolynomialTensor_continuousWithinAt_terminal S hS hab hslab hreg
      (p + 2 * q) basis (P q)
  have heq (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a b) : B q t = A q t :=
    tensorOfPolynomialComponents_eq_of_components basis (P q)
      (curvatureJetPolynomialValues S (p + 2 * q) t basis) (A q t) (hP q t ht).2
  have hA0 : ContinuousWithinAt (A 0) (Set.Iio b) b := by
    simpa only [A, mixedCurvatureTensor_zero] using
      (solution_nablaKRm04_continuousWithinAt_terminal S hS hab hslab hreg p x)
  have hzeroB : B 0 b = A 0 b :=
    tendsto_nhds_unique (hB 0)
      (hA0.tendsto.congr' (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
        fun t ht => heq 0 t ht).symm)
  have hzero (t : ℝ) (ht : t ∈ Set.Ioc a b) : B 0 t = nablaKRm04Field S t p x := by
    rcases lt_or_eq_of_le ht.2 with htb | rfl
    · simpa only [A, mixedCurvatureTensor_zero] using heq 0 t ⟨ht.1, htb⟩
    · simpa only [A, mixedCurvatureTensor_zero] using hzeroB
  have hcor (q : ℕ) : ContinuousWithinAt
      (fun t => covariantEndomorphismAction0S (B q t) (ricciSharp (S.base.metric t) x))
      (Set.Iio b) b :=
    solution_metricTimeCorrection_continuousWithinAt_terminal S hS hab hslab basis (hB q)
  have hderiv (q : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivAt (B q)
        (B (q + 1) t - covariantEndomorphismAction0S (B q t) (ricciSharp (S.base.metric t) x)) t := by
    have hdA : HasDerivAt (A q) (deriv (A q) t) t := (hP q t ht).1.hasDerivAt
    have hcar : D.carrier ∈ 𝓝 t := by
      rw [hcarrier]
      exact Iic_mem_nhds ht.2
    have hnext : A (q + 1) t = deriv (A q) t +
        covariantEndomorphismAction0S (A q t) (ricciSharp (S.base.metric t) x) := by
      change derivWithin (A q) D.carrier t +
        covariantEndomorphismAction0S (A q t) (ricciSharp (S.base.metric t) x) = _
      exact congrArg (fun T : Tensor0SSpace (4 + p) I x =>
        T + covariantEndomorphismAction0S (A q t) (ricciSharp (S.base.metric t) x))
        (derivWithin_of_mem_nhds hcar)
    have hval : deriv (A q) t = B (q + 1) t -
        covariantEndomorphismAction0S (B q t) (ricciSharp (S.base.metric t) x) := by
      rw [heq (q + 1) t ht, heq q t ht, hnext]
      exact (add_sub_cancel_right _ _).symm
    have hdB := hdA.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => heq q s hs)
    rwa [hval] at hdB
  have htower := iteratedMetricTimeDerivWithin_eq_of_terminal_tower S.base.metric
    (fun t => nablaKRm04Field S t p x) B hab hzero hB hcor hderiv
  intro q
  obtain ⟨hvalue, hdiff⟩ := htower q b ⟨hab, le_rfl⟩
  have hvalue' : mixedCurvatureTensor S p q b x = B q b := by
    simpa only [mixedCurvatureTensor, hcarrier] using hvalue
  refine ⟨?_, fun slots => ?_⟩
  · simpa only [mixedCurvatureTensor, hcarrier] using hdiff
  · calc
      component0S (I := I) basis (mixedCurvatureTensor S p q b x) slots =
          component0S (I := I) basis (B q b) slots :=
        congrArg (fun T => component0S (I := I) basis T slots) hvalue'
      _ = _ := component0S_tensorOfPolynomialComponents basis (P q)
        (curvatureJetPolynomialValues S (p + 2 * q) b basis) slots

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
