import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.AlmostNonnegativeSectional
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompactCommonExistence
import DifferentialGeometry.Geometry.Comparison.SectionalLowerBound

/-!
# Applications of the quantitative sectional-curvature preservation (LFR50, B and C)

* Regressions at `ε = 0`. The generic shifted barrier with `f ≡ 0`, and the exponential theorem at
  `ε = 0`, both give back the conclusion of `metric_curvature_operator_nonnegative_preserved`
  (nonnegative curvature operator, same sign conventions).
* Consumer for `ε > 0`, combined with part B. A metric on a compact 3-manifold with `|Rm| ≤ B` and
  `sec ≥ -ε` starts a Ricci flow on `[0, T]`, `T = compactCurvatureControlTime 3 B`. Along it
  `|Rm| ≤ B* = √(2B² + 1)` and `sec ≥ -ε e^{6 B* t}`, hence `sec ≥ -ε e^{6 B* T}` uniformly.
  The same holds for a sequence of metrics with one bound `B` and errors `εₙ` (the LFR50 use).
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open Bundle DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff

section Regression

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- Regression (`f ≡ 0`): the shifted barrier gives back exact preservation of a nonnegative
curvature operator, with the conclusion of `metric_curvature_operator_nonnegative_preserved`. -/
theorem metric_curvature_operator_nonnegative_preserved_of_shifted_barrier
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hinit : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone) :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
  have hpres := ricci_upper_bound_add_smul_metric_preserved (I := I) hS hdim hTsub hTreg
    (f := fun _ => (0 : Real)) (differentiable_const 0)
    (by
      intro t _ x v
      simp)
    (by
      intro x v
      have hb := ricci_upper_bound_of_metric_curvature_operator_nonnegative (I := I) S (hdim x)
        (t := 0) (x := x) (hinit x) v
      rw [ricci_upper_bound_sec_apply (I := I) S 0 x v v]
      linarith)
  intro t ht x
  exact metric_curvature_operator_nonnegative_of_ricci_upper_bound_at (I := I) S (hdim x)
    (t := t) (x := x) (by
      intro v
      have h := hpres t ht x v
      rw [ricci_upper_bound_sec_apply (I := I) S t x v v] at h
      linarith)

/-- Regression (`ε = 0`): the exponential sectional estimate at `ε = 0` gives back exact
preservation of a nonnegative curvature operator, with the conclusion of
`metric_curvature_operator_nonnegative_preserved`. -/
theorem metric_curvature_operator_nonnegative_preserved_of_exp_bound
    [I.Boundaryless] [T2Space M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle (∞ : WithTop ℕ∞) E (TangentSpace I : M -> Type _) I]
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    [CompleteSpace E] [CompactSpace M]
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSmoothSolutionOn (I := I) (M := M) S)
    {T B : Real}
    (hdim : ∀ x : M, Module.finrank Real (TangentSpace I x) = 3)
    (hTsub : Set.Icc 0 T ⊆ D.carrier)
    (hTreg : Set.Ioc 0 T ⊆ D.regular)
    (hRm : ∀ t ∈ Set.Icc 0 T, ∀ x : M,
      Real.sqrt (normSq0S (S.base.metric t) x 4 (metricRm04 (S.base.metric t) x)) ≤ B)
    (hinit : ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric 0) x ∈
        algebraicCurvatureOperatorNonnegativeCone) :
    ∀ t, t ∈ Set.Icc 0 T -> ∀ x : M,
      metricAlgebraicCurvatureTensorAt (I := I) (M := M) (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
  have hsec0 : SectionalBoundedBelow (S.base.metric 0) (-0) := by
    intro x
    refine (sectionalBoundedBelowAt_iff_ricciUpperBoundSec_add_nonneg (hdim x)).mpr ?_
    intro v
    have hb := ricci_upper_bound_of_metric_curvature_operator_nonnegative (I := I) S (hdim x)
      (t := 0) (x := x) (hinit x) v
    rw [ricci_upper_bound_sec_apply (I := I) S 0 x v v]
    linarith
  have hexp := sectionalBoundedBelow_exp_preserved (I := I) hS hdim hTsub hTreg hRm le_rfl hsec0
  intro t ht x
  have hx : SectionalBoundedBelowAt (S.base.metric t) x (-0) := by
    have h := hexp t ht x
    rw [neg_zero, zero_mul] at h
    rw [neg_zero]
    exact h
  have hup := (sectionalBoundedBelowAt_iff_ricciUpperBoundSec_add_nonneg (hdim x)).mp hx
  exact metric_curvature_operator_nonnegative_of_ricci_upper_bound_at (I := I) S (hdim x)
    (t := t) (x := x) (by
      intro v
      have h := hup v
      rw [ricci_upper_bound_sec_apply (I := I) S t x v v] at h
      linarith)

end Regression

section Consumer

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [BoundarylessManifold I M]

/-- LFR50 B and C together: a metric with `|Rm| ≤ B` and `sec ≥ -ε` (`ε ≥ 0`) on a compact
boundaryless 3-manifold has a Ricci flow beyond `T = compactCurvatureControlTime 3 B`. On `[0, T]`
it keeps `|Rm| ≤ B* = √(2B² + 1)`, `sec ≥ -ε e^{6 B* t}` and `sec ≥ -ε e^{6 B* T}`. -/
theorem exists_flowTo_sectional_exp_lower_bound
    (g₀ : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) (B ε : ℝ) (hε : 0 ≤ ε)
    (hRm : ∀ x : M, Real.sqrt (normSq0S g₀ x 4 (metricRm04 g₀ x)) ≤ B)
    (hsec : SectionalBoundedBelow g₀ (-ε)) :
    ∃ τ : ℝ, compactCurvatureControlTime 3 B < τ ∧
      ∃ F : FlowTo g₀ τ, ∀ t ∈ Icc 0 (compactCurvatureControlTime 3 B),
        (∀ x : M, Real.sqrt (normSq0S (F.S.base.metric t) x 4
          (metricRm04 (F.S.base.metric t) x)) ≤ Real.sqrt (2 * B ^ 2 + 1)) ∧
        SectionalBoundedBelow (F.S.base.metric t)
          (-ε * Real.exp (6 * Real.sqrt (2 * B ^ 2 + 1) * t)) ∧
        SectionalBoundedBelow (F.S.base.metric t)
          (-ε * Real.exp (6 * Real.sqrt (2 * B ^ 2 + 1) * compactCurvatureControlTime 3 B)) := by
  obtain ⟨τ, hτ, F, hF⟩ := exists_flowTo_beyond_compactCurvatureControlTime g₀ hdim B hRm
  have hsec0 : SectionalBoundedBelow (F.S.base.metric 0) (-ε) := by
    rw [show F.S.base.metric 0 = g₀ from F.start]
    exact hsec
  have hexp := sectionalBoundedBelow_exp_preserved F.isSmoothSolutionOn (fun _ => hdim)
    (F.Icc_subset_carrier hτ) (F.Ioc_subset_regular hτ) hF hε hsec0
  refine ⟨τ, hτ, F, fun t ht => ⟨hF t ht, hexp t ht, fun x => ?_⟩⟩
  refine DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelowAt.mono (hexp t ht x) ?_
  have hBs : 0 ≤ 6 * Real.sqrt (2 * B ^ 2 + 1) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hmono : Real.exp (6 * Real.sqrt (2 * B ^ 2 + 1) * t) ≤
      Real.exp (6 * Real.sqrt (2 * B ^ 2 + 1) * compactCurvatureControlTime 3 B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hBs)
  nlinarith [mul_le_mul_of_nonneg_left hmono hε]

/-- Sequence form used by LFR50: metrics `gSeq n` with one bound `|Rm| ≤ B` and
`sec(gSeq n) ≥ -ε n` (`ε n ≥ 0`) have Ricci flows on a common interval `[0, T]`, `T > 0`, each
existing beyond `T`, with `|Rm| ≤ √(2B² + 1)` and `sec ≥ -ε n · e^{6 √(2B² + 1) t}` there. -/
theorem exists_common_flows_sectional_exp_lower_bound
    (hdim : Module.finrank ℝ E = 3) (B : ℝ)
    (gSeq : ℕ → SmoothRiemannianMetric I M) (ε : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n)
    (hRm : ∀ n x, Real.sqrt (normSq0S (gSeq n) x 4 (metricRm04 (gSeq n) x)) ≤ B)
    (hsec : ∀ n, SectionalBoundedBelow (gSeq n) (-ε n)) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ, ∃ τ : ℝ, T < τ ∧ ∃ F : FlowTo (gSeq n) τ,
      ∀ t ∈ Icc 0 T,
        (∀ x : M, Real.sqrt (normSq0S (F.S.base.metric t) x 4
          (metricRm04 (F.S.base.metric t) x)) ≤ Real.sqrt (2 * B ^ 2 + 1)) ∧
        SectionalBoundedBelow (F.S.base.metric t)
          (-ε n * Real.exp (6 * Real.sqrt (2 * B ^ 2 + 1) * t)) := by
  refine ⟨compactCurvatureControlTime 3 B, compactCurvatureControlTime_pos 3 B, fun n => ?_⟩
  obtain ⟨τ, hτ, F, hF⟩ :=
    exists_flowTo_sectional_exp_lower_bound (gSeq n) hdim B (ε n) (hε n) (hRm n) (hsec n)
  exact ⟨τ, hτ, F, fun t ht => ⟨(hF t ht).1, (hF t ht).2.1⟩⟩

end Consumer

end DifferentialGeometry.PDE.RicciFlow
