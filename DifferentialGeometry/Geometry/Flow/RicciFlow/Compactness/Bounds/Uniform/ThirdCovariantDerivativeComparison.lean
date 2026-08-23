import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.ConnectionSecondDerivative


set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]
variable [CompactSpace M] [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem covariant_derivative_step_zero (gRef : SmoothRiemannianMetric I M) (s : ℕ) :
    covStep (I := I) gRef s 0 = 0 := by
  have h := covStep_add (I := I) gRef s 0 0
  rw [add_zero] at h
  have hc : covStep (I := I) gRef s 0 + covStep (I := I) gRef s 0 =
      covStep (I := I) gRef s 0 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel hc

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem sqrt_covariant_tensor_norm_sq_zero (g : SmoothRiemannianMetric I M) (x : M) (s : ℕ) :
    Real.sqrt (normSq0S (I := I) g x s (0 : Tensor0SBundle.Tensor0SSpace s I x)) = 0 := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g x
  have hinv : MetricInverseInBasis_gen (I := I) g x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [normSq0S_identity_eq_sum_sq (I := I) g x s basis hinv]
  rw [show (∑ slots : Fin s → Fin (Module.finrank Real (TangentSpace I x)),
      (component0S (I := I) basis (0 : Tensor0SBundle.Tensor0SSpace s I x) slots) ^ 2) = 0 from ?_]
  · exact Real.sqrt_zero
  · refine Finset.sum_eq_zero (fun slots _ => ?_)
    rw [component0S_apply]; simp

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private theorem telescoping_covariant_derivative_difference_accumulation_one (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) :
    telescAccum (I := I) g₁ g₂ r T 1 = diffStep (I := I) g₁ g₂ r T := by
  have hunfold : telescAccum (I := I) g₁ g₂ r T 1
      = covStep (I := I) g₁ r (telescAccum (I := I) g₁ g₂ r T 0)
        + diffStep (I := I) g₁ g₂ r T := rfl
  rw [hunfold, show telescAccum (I := I) g₁ g₂ r T 0 = 0 from rfl, covariant_derivative_step_zero, zero_add]

noncomputable def covariantDerivativeStepAccumulationTwoComparisonConstant (r : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 (covStepDiff2C (E := E) r Λ Λ' Λ'' Λ''' +
    (((r + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 3)) *
      (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
        (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))) *
      ((r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 1)) *
          ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) +
        (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
          (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
            (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) + 1))
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem covariant_derivative_step_accumulation_two_le_comparison_constant
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
          (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x)) ≤
        covariantDerivativeStepAccumulationTwoComparisonConstant (E := E) r Λ Λ' Λ'' Λ''' *
          ∑ k ∈ Finset.range 3,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  classical
  let C₂ : ℝ := covStepDiff2C (E := E) r Λ Λ' Λ'' Λ'''
  have hC₂nn : 0 ≤ C₂ := by
    dsimp [C₂, covStepDiff2C]
    exact le_max_left _ _
  have hC₂ := covStepDiff2_le (I := I) g₁ g₂ r
    (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hJet3 hjet
  set CA0 : ℝ := (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hCA0def
  set CA1 : ℝ := ((r + 1 : ℕ) : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 3)) *
    (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hCA1def
  set cs0 : ℝ := (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 1)) *
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) with hcs0def
  intro T x hx
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hCA0nn : (0 : ℝ) ≤ CA0 := by rw [hCA0def]; positivity
  have hCA1nn : (0 : ℝ) ≤ CA1 := by rw [hCA1def]; positivity
  have hcs0nn : (0 : ℝ) ≤ cs0 := by rw [hcs0def]; positivity
  have hsplit : covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2)
      = covStep (I := I) g₂ (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T))
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T))
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) := by
    have h2 : telescAccum (I := I) g₁ g₂ r T 2
        = covStep (I := I) g₁ (r + 1) (diffStep (I := I) g₁ g₂ r T)
          + diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) := by
      have hu : telescAccum (I := I) g₁ g₂ r T 2
          = covStep (I := I) g₁ (r + 1) (telescAccum (I := I) g₁ g₂ r T 1)
            + diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) := rfl
      rw [hu, telescoping_covariant_derivative_difference_accumulation_one]
    have hg1 : covStep (I := I) g₁ (r + 1) (diffStep (I := I) g₁ g₂ r T)
        = covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)
          + diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) := by
      simp only [diffStep]
      abel
    rw [h2, covStep_add, hg1, covStep_add]
  have hsplitx : covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x
      = covStep (I := I) g₂ (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x
        + covStep (I := I) g₂ (r + 2)
            (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x := by
    rw [hsplit]; rfl
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_gOrthonormalBasis (I := I) g₂ x
  have hinv : MetricInverseInBasis_gen (I := I) g₂ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    intro i j; constructor <;> simp [identityInvMetric, diagonalInvMetric, hON]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  set p0 := Real.sqrt (normSq0S (I := I) g₂ x (r + 0) (iterCov (I := I) g₂ r T 0 x)) with hp0def
  set p1 := Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (iterCov (I := I) g₂ r T 1 x)) with hp1def
  set p2 := Real.sqrt (normSq0S (I := I) g₂ x (r + 2) (iterCov (I := I) g₂ r T 2 x)) with hp2def
  have hp0nn : 0 ≤ p0 := Real.sqrt_nonneg _
  have hp1nn : 0 ≤ p1 := Real.sqrt_nonneg _
  have hp2nn : 0 ≤ p2 := Real.sqrt_nonneg _
  have hb1' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      C₂ * (p0 + p1 + p2) := hC₂ T x hx
  have hb2' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      CA1 * (Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (diffStep (I := I) g₁ g₂ r T x))
        + Real.sqrt (normSq0S (I := I) g₂ x (r + 2)
            (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x))) :=
    covStepDiff_of_jets (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  have hb3' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x)) ≤
      CA1 * (p1 + p2) :=
    covStepDiff_of_jets (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1) x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  have hb2a' : Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (diffStep (I := I) g₁ g₂ r T x)) ≤
      cs0 * p0 :=
    diffStep_jet_one_le (I := I) g₁ g₂ r T hEq hjet hx
  have hb2b' : Real.sqrt (normSq0S (I := I) g₂ x (r + 2)
        (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T) x)) ≤
      CA0 * (p0 + p1) :=
    covStepDiff_of_jets (I := I) g₁ g₂ r T x
      (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx
  have hb2'' : Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2)
          (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x)) ≤
      CA1 * (cs0 * p0 + CA0 * (p0 + p1)) :=
    le_trans hb2' (mul_le_mul_of_nonneg_left (add_le_add hb2a' hb2b') hCA1nn)
  set av := covStep (I := I) g₂ (r + 2)
    (covStep (I := I) g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x with hav
  set bv := covStep (I := I) g₂ (r + 2)
    (diffStep (I := I) g₁ g₂ (r + 1) (diffStep (I := I) g₁ g₂ r T)) x with hbv
  set cv := covStep (I := I) g₂ (r + 2)
    (diffStep (I := I) g₁ g₂ (r + 1) (iterCov (I := I) g₂ r T 1)) x with hcv
  clear_value av bv cv
  have hSle : C₂ * (p0 + p1 + p2) + CA1 * (cs0 * p0 + CA0 * (p0 + p1)) + CA1 * (p1 + p2)
      ≤ (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := by
    have h1 : 0 ≤ CA1 * cs0 * p1 := by positivity
    have h2 : 0 ≤ CA1 * cs0 * p2 := by positivity
    have h3 : 0 ≤ CA1 * CA0 * p2 := by positivity
    have h4 : 0 ≤ CA1 * p0 := by positivity
    have hdiff :
        (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) -
            (C₂ * (p0 + p1 + p2) + CA1 * (cs0 * p0 + CA0 * (p0 + p1)) + CA1 * (p1 + p2))
          = CA1 * cs0 * p1 + CA1 * cs0 * p2 + CA1 * CA0 * p2 + CA1 * p0 := by
      ring
    rw [← sub_nonneg, hdiff]
    exact add_nonneg (add_nonneg (add_nonneg h1 h2) h3) h4
  have hfin : (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2)
      ≤ max 0 (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) :=
    mul_le_mul_of_nonneg_right (le_max_right _ _)
      (add_nonneg (add_nonneg hp0nn hp1nn) hp2nn)
  calc Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
        (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x))
      ≤ Real.sqrt (normSq0S (I := I) g₂ x (r + 3) av)
          + Real.sqrt (normSq0S (I := I) g₂ x (r + 3) bv)
          + Real.sqrt (normSq0S (I := I) g₂ x (r + 3) cv) := by
        rw [hsplitx]
        refine le_trans (sqrt_normSq0S_add_le (I := I) g₂ (av + bv) cv basis hinv) ?_
        exact add_le_add (sqrt_normSq0S_add_le (I := I) g₂ av bv basis hinv) (le_refl _)
    _ ≤ C₂ * (p0 + p1 + p2) + CA1 * (cs0 * p0 + CA0 * (p0 + p1)) + CA1 * (p1 + p2) :=
        add_le_add (add_le_add hb1' hb2'') hb3'
    _ ≤ (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := hSle
    _ ≤ max 0 (C₂ + CA1 * (cs0 + CA0 + 1)) * (p0 + p1 + p2) := hfin

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem exists_covariant_derivative_step_accumulation_two_bound
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (r + 3)
            (covStep (I := I) g₂ (r + 2) (telescAccum (I := I) g₁ g₂ r T 2) x)) ≤
          C * ∑ k ∈ Finset.range 3,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  refine ⟨covariantDerivativeStepAccumulationTwoComparisonConstant (E := E) r Λ Λ' Λ'' Λ''', ?_, ?_⟩
  · dsimp [covariantDerivativeStepAccumulationTwoComparisonConstant]
    exact le_max_left _ _
  · exact covariant_derivative_step_accumulation_two_le_comparison_constant (I := I) g₁ g₂ r hEq hjet hJet1 hJet2 hJet3

noncomputable def thirdIteratedCovariantDerivativeComparisonConstant (r : ℕ) (Λ Λ' Λ'' Λ''' : ℝ) : ℝ :=
  max 0 (Dtower (Module.finrank ℝ E)
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) r
    (fun m => if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) +
          (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
    else if m = 2 then covariantDerivativeStepAccumulationTwoComparisonConstant (E := E) r Λ Λ' Λ'' Λ''' else 0) 3)
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
theorem third_iterated_covariant_derivative_le_comparison_constant
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
      Real.sqrt (normSq0S (I := I) g₂ x (r + 3) (iterCov (I := I) g₁ r T 3 x)) ≤
        thirdIteratedCovariantDerivativeComparisonConstant (E := E) r Λ Λ' Λ'' Λ''' *
          ∑ k ∈ Finset.range 4,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  classical
  let C2acc : ℝ := covariantDerivativeStepAccumulationTwoComparisonConstant (E := E) r Λ Λ' Λ'' Λ'''
  have hC2accnn : 0 ≤ C2acc := by
    dsimp [C2acc, covariantDerivativeStepAccumulationTwoComparisonConstant]
    exact le_max_left _ _
  have hC2acc := covariant_derivative_step_accumulation_two_le_comparison_constant (I := I) g₁ g₂ r
    hEq hjet hJet1 hJet2 hJet3
  intro T x hx
  have hLnn : (0 : ℝ) ≤ Λ := le_trans zero_le_one hEq.1
  have hL'nn : (0 : ℝ) ≤ Λ' := le_trans (Real.sqrt_nonneg _) (hjet x hx)
  have hL''nn : (0 : ℝ) ≤ Λ'' := le_trans (Real.sqrt_nonneg _) (hJet2 x hx)
  have hCA0nn : (0 : ℝ) ≤ (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
      (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ')) := by
    positivity
  have hRnn : ∀ m : ℕ, (0 : ℝ) ≤ if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
      else if m = 2 then C2acc else 0 := by
    intro m
    split
    · exact hCA0nn
    · split
      · exact hC2accnn
      · exact le_refl 0
  refine le_trans (iterCovG1_le (I := I) g₁ g₂ r T x
    (fun m => if m = 1 then
      (r : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ (r + 2)) *
        (3 / 2 * Λ ^ 4 * (Λ'' + Λ * Λ' ^ 2) + (3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ'))
    else if m = 2 then C2acc else 0) hRnn hEq hjet hx 3 ?_) ?_
  · intro m hm
    interval_cases m
    · simp only [if_neg (by norm_num : (0 : ℕ) ≠ 1), if_neg (by norm_num : (0 : ℕ) ≠ 2), zero_mul]
      rw [show telescAccum (I := I) g₁ g₂ r T 0 = 0 from rfl, covariant_derivative_step_zero]
      simp only [ContMDiffSection.coe_zero, Pi.zero_apply, sqrt_covariant_tensor_norm_sq_zero, le_refl]
    · simp only [reduceIte]
      rw [telescoping_covariant_derivative_difference_accumulation_one (I := I) g₁ g₂ r T]
      refine le_trans (covStepDiff_of_jets (I := I) g₁ g₂ r T x
        (metricUniformEquivalentOn_symm (I := I) hEq) hJet1 hJet2 hjet hx) ?_
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
      refine mul_le_mul_of_nonneg_left ?_ hCA0nn
      have hA : Real.sqrt (normSq0S (I := I) g₂ x r (T x))
          = Real.sqrt (normSq0S (I := I) g₂ x (r + 0) (iterCov (I := I) g₂ r T 0 x)) := rfl
      have hB : Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (covStep (I := I) g₂ r T x))
          = Real.sqrt (normSq0S (I := I) g₂ x (r + 1) (iterCov (I := I) g₂ r T 1 x)) := rfl
      rw [hA, hB]
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    · simp only [reduceIte]
      rw [Finset.sum_range_succ]
      exact le_trans (hC2acc T x hx)
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hC2accnn)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _)

omit [NeZero (Module.finrank ℝ E)] in
omit [CompactSpace M] in
theorem exists_third_iterated_covariant_derivative_comparison_bound
    {K : Set M} (g₁ g₂ : SmoothRiemannianMetric I M) (r : ℕ)
    {Λ Λ' Λ'' Λ''' : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) K g₁ g₂ Λ)
    (hjet : MetricCovDerivOrderBoundOn (I := I) K 1 g₂ g₁ Λ')
    (hJet1 : MetricCovDerivOrderBoundOn (I := I) K 1 g₁ g₂ Λ')
    (hJet2 : MetricCovDerivOrderBoundOn (I := I) K 2 g₁ g₂ Λ'')
    (hJet3 : MetricCovDerivOrderBoundOn (I := I) K 3 g₁ g₂ Λ''') :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) r) (x : M), x ∈ K →
        Real.sqrt (normSq0S (I := I) g₂ x (r + 3) (iterCov (I := I) g₁ r T 3 x)) ≤
          C * ∑ k ∈ Finset.range 4,
            Real.sqrt (normSq0S (I := I) g₂ x (r + k) (iterCov (I := I) g₂ r T k x)) := by
  refine ⟨thirdIteratedCovariantDerivativeComparisonConstant (E := E) r Λ Λ' Λ'' Λ''', ?_, ?_⟩
  · dsimp [thirdIteratedCovariantDerivativeComparisonConstant]
    exact le_max_left _ _
  · exact third_iterated_covariant_derivative_le_comparison_constant (I := I) g₁ g₂ r hEq hjet hJet1 hJet2 hJet3

end RicciFlow
end PDE
end DifferentialGeometry

end
