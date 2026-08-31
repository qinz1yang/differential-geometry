import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.CurvatureBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private def actionRmFactor (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

omit [NeZero (Module.finrank Real E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem regSpeed_int_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegSpeedSq S T alpha) volume a b := by
  have hLag := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha halpha hreg
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [uIcc_of_le hab] using halpha.continuousOn)
  have hhalf : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegSpeedSq S T alpha s) volume a b := by
    convert hLag.sub hpot using 1
    funext s
    unfold lRegLagrangian lRegSpeedSq
    ring
  have htwice := hhalf.const_mul 2
  convert htwice using 1
  funext s
  ring

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRegCosts_bdd_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T a b : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) :
    BddBelow {r : Real | ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r} := by
  let C : Real := -2 * b ^ 2 * actionRmFactor E K
  have hb : 0 ≤ b := ha.trans hab
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  refine ⟨C * (b - a), ?_⟩
  intro r hr
  obtain ⟨alpha, halpha, _hstart, _hend, rfl⟩ := hr
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hkin := regSpeed_int_c1 (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hLag := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T a b hab alpha
    halpha.contMDiffOn hregBack
  have hbound := lRegKinetic_le (I := I) S T alpha a b
    (lRegAction S T alpha a b) C hab
    (fun s hs ↦ lRegPot_lower_rm (I := I) S K T b hb hRm s
      ⟨ha.trans hs.1, hs.2⟩ (alpha s))
    hkin hLag le_rfl
  have hnonneg : 0 ≤ ∫ s in a..b, lRegSpeedSq S T alpha s := by
    apply intervalIntegral.integral_nonneg hab
    intro s _hs
    exact lRegSpeedSq_nonneg (I := I) S T alpha s
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman
