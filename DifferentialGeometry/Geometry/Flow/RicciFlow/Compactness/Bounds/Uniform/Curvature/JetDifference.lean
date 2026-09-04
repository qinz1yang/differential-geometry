import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.Supremum

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Algebra.CovariantSumCross
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback

set_option autoImplicit false

noncomputable section


open Bundle Manifold Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.HCGCompactness

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem exists_curvJet_sup (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g x (4 + a)
          (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a x)) ≤ K := by
  obtain ⟨C, hC0, hC⟩ :=
    sqrtNormSq0S_bddOn (I := I) (M := M) (K := (Set.univ : Set M)) isCompact_univ (4 + a) g
      (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a)
  exact ⟨C, hC0, fun x => hC x (Set.mem_univ x)⟩

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [SigmaCompactSpace M] in
theorem curvJet1_diff_eq (g₀ gBase : SmoothRiemannianMetric I M) :
    iterCov (I := I) g₀ 4 (metricRm04 (I := I) (M := M) g₀) 1 -
        iterCov (I := I) gBase 4 (metricRm04 (I := I) (M := M) gBase) 1 =
      diffStep (I := I) g₀ gBase 4 (metricRm04 (I := I) (M := M) g₀) +
        covStep (I := I) gBase 4
          (metricRm04 (I := I) (M := M) g₀ - metricRm04 (I := I) (M := M) gBase) := by
  change covStep (I := I) g₀ 4 (metricRm04 (I := I) (M := M) g₀) -
      covStep (I := I) gBase 4 (metricRm04 (I := I) (M := M) gBase) = _
  rw [covStep_sub (I := I) gBase 4 (metricRm04 (I := I) (M := M) g₀)
    (metricRm04 (I := I) (M := M) gBase)]
  simp only [diffStep]
  abel


omit [SigmaCompactSpace M] in
theorem uniformRm04Sup
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 4
          (metricRm04 (I := I) (M := M) g₀ x)) ≤ C := by
  classical
  obtain ⟨F, hF0, hF⟩ :=
    uniformCurvSup (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * F, by positivity, fun x => ?_⟩
  obtain ⟨basis, hON⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g₀ x
  have hinv : MetricInverseInBasisGen (I := I) g₀ x basis
      (identityInvMetric (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) g₀ basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hcompB : ∀ slots : Fin 4 → Fin (Module.finrank Real (TangentSpace I x)),
      |component0S (I := I) basis (metricRm04 (I := I) (M := M) g₀ x) slots| ≤ F := by
    intro slots
    have hvec : (fun a : Fin 4 => basis (slots a)) =
        vec4 (I := I) (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
          (basis (slots 3)) := by
      funext a
      fin_cases a <;> simp [vec4]
    have hval : component0S (I := I) basis (metricRm04 (I := I) (M := M) g₀ x) slots =
        g₀.inner x (basis (slots 3))
          (riemannOp (cov := LeviCivita (I := I) g₀) x
            (basis (slots 0)) (basis (slots 1)) (basis (slots 2))) := by
      rw [component0S, hvec]
      rw [show metricRm04 (I := I) (M := M) g₀ x = metricRm04At (I := I) (M := M) g₀ x from rfl]
      rw [← metricRm04StdAt_apply (I := I) (M := M) g₀ x]
      exact metricRm04StdAt_eq_inner_riemannOp (I := I) (M := M) g₀ x _ _ _ _
    rw [hval]
    have hunit : ∀ i, g₀.inner x (basis i) (basis i) = 1 := by
      intro i; rw [hON i i]; simp
    set R : TangentSpace I x :=
      riemannOp (cov := LeviCivita (I := I) g₀) x
        (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) with hR
    have hRR : g₀.inner x R R ≤ F ^ 2 := by
      have := hF x (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
      rw [hunit (slots 0), hunit (slots 1), hunit (slots 2)] at this
      simpa [hR] using this
    calc |g₀.inner x (basis (slots 3)) R|
        ≤ Real.sqrt (g₀.inner x (basis (slots 3)) (basis (slots 3))) *
            Real.sqrt (g₀.inner x R R) :=
          abs_metric_inner_le_sqrt_metric_quadratic (I := I) (M := M) g₀ x _ _
      _ = Real.sqrt (g₀.inner x R R) := by rw [hunit (slots 3)]; simp
      _ ≤ Real.sqrt (F ^ 2) := Real.sqrt_le_sqrt hRR
      _ = F := Real.sqrt_sq hF0
  have hcard := normSq0S_le_card_of_component_bound (I := I) g₀ x 4 basis hinv
    (metricRm04 (I := I) (M := M) g₀ x) F hF0 hcompB
  have hfr : Module.finrank Real (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcardval :
      (Fintype.card (Fin 4 → Fin (Module.finrank Real (TangentSpace I x))) : ℝ) =
        (Module.finrank ℝ E : ℝ) ^ 4 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, hfr]
    push_cast
    ring
  rw [hcardval] at hcard
  have hsq : (Module.finrank ℝ E : ℝ) ^ 4 * F ^ 2 =
      ((Module.finrank ℝ E : ℝ) ^ 2 * F) ^ 2 := by ring
  rw [hsq] at hcard
  calc Real.sqrt (normSq0S (I := I) g₀ x 4 (metricRm04 (I := I) (M := M) g₀ x))
      ≤ Real.sqrt (((Module.finrank ℝ E : ℝ) ^ 2 * F) ^ 2) := Real.sqrt_le_sqrt hcard
    _ = (Module.finrank ℝ E : ℝ) ^ 2 * F := Real.sqrt_sq (by positivity)


omit [SigmaCompactSpace M] in
theorem uniformCurvJet1Conn
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : M,
        Real.sqrt (normSq0S (I := I) g₀ x 5
          (diffStep (I := I) g₀ gBase 4
            (metricRm04 (I := I) (M := M) g₀) x)) ≤ C := by
  classical
  have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le one_pos hΛ
  obtain ⟨C0, hC00, hC0⟩ :=
    uniformRm04Sup (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2
  have hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ :=
    ⟨hΛ, fun x _ v => hcomp x v⟩
  refine ⟨(4 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
    ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) * C0, by positivity, fun x => ?_⟩
  have hneg : diffStep (I := I) g₀ gBase 4 (metricRm04 (I := I) (M := M) g₀) x =
      -(diffStep (I := I) gBase g₀ 4 (metricRm04 (I := I) (M := M) g₀) x) := by
    simp only [diffStep, ContMDiffSection.coe_sub, Pi.sub_apply]
    abel
  rw [hneg, Tensor0SBundle.normSq0S_neg]
  refine le_trans
    (diffStep_jet_one_le (I := I) (M := M) gBase g₀ 4
      (metricRm04 (I := I) (M := M) g₀) hEq hjet1 (Set.mem_univ x)) ?_
  have hpre : (0 : ℝ) ≤ (4 : ℝ) * Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5) *
      ((3 / 2 : ℝ) * (Real.sqrt (Λ ^ 3) * Λ)) := by positivity
  have hstep := mul_le_mul_of_nonneg_left (hC0 x) hpre
  refine le_trans (le_of_eq ?_) hstep
  norm_num

end RicciFlow
end PDE
end DifferentialGeometry
