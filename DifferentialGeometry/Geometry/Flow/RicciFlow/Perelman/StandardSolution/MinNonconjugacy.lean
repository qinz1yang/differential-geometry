import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.NegativeDirection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.PiecewiseNonnegativity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.LowerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

theorem lMinVec_nconj_lt_of_bdd
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hlt : tau < sigma)
    (hbdd : BddBelow {r : ℝ | ∃ alpha : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 alpha ∧
        alpha 0 = x ∧
        alpha (Real.sqrt sigma) = lExp S T x Z sigma ∧
        lRegularizedAction S T alpha 0 (Real.sqrt sigma) = r}) :
    ¬ IsLConjugate S T x Z tau := by
  intro hconj
  have hvec := (mem_lMinDomain S T x Z sigma).1 hmin
  have hsigma : 0 < sigma :=
    lMinDomain_pos S T x Z sigma hmin
  have hcost :
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt sigma) =
        lRegularizedCostC1 S T 0 (Real.sqrt sigma) x
          (lExp S T x Z sigma) := by
    calc
      lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt sigma) =
          lLength S T (fun r : ℝ ↦ lExp S T x Z r) 0 sigma := by
        change _ = lLength S T
          (fun r : ℝ ↦ lRegularizedCurve S T x Z (Real.sqrt r)) 0 sigma
        rw [show (fun r : ℝ ↦ lRegularizedCurve S T x Z (Real.sqrt r)) =
          squareRootReparametrization (lRegularizedCurve S T x Z) by rfl]
        exact (lLength_squareRootReparametrization_eq_lRegularizedAction (I := I) S T
          (lRegularizedCurve S T x Z) sigma hsigma.le).symm
      _ = lCost S T x (lExp S T x Z sigma) sigma := hvec.2
      _ = lRegularizedCostC1 S T 0 (Real.sqrt sigma) x
          (lExp S T x Z sigma) :=
        lCost_eq_regularity (I := I) S T x
          (lExp S T x Z sigma) sigma hsigma.le
  have hdomTau : (Z, tau) ∈ lExpPosDom S T x :=
    ((isLConjugate_iff_jacobian (I := I) S T x Z tau).1 hconj).1
  have htau : 0 < tau :=
    ((mem_lExpPosDom (I := I) S T x Z tau).1 hdomTau).1
  have hc0 : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hcb : Real.sqrt tau < Real.sqrt sigma :=
    Real.sqrt_lt_sqrt htau.le hlt
  obtain ⟨gamma, Y0, Y1, hEq, hgeo, hY0, hY1,
      hY0zero, hY1zero, hnode, hneg⟩ :=
    exists_lRegularizedIndex_split_lt_zero_of_isLConjugate (I := I) S hS T x Z hvec.1 hlt hconj
  have hminGamma : ∀ delta : ℝ → M,
      ContMDiff (modelWithCornersSelf ℝ ℝ) I 1 delta →
      delta 0 = gamma 0 →
      delta (Real.sqrt sigma) = gamma (Real.sqrt sigma) →
      lRegularizedAction S T gamma 0 (Real.sqrt sigma) ≤
        lRegularizedAction S T delta 0 (Real.sqrt sigma) := by
    intro delta hdelta hd0 hdsigma
    have hEq0 : gamma 0 = lRegularizedCurve S T x Z 0 :=
      hEq ⟨le_rfl, Real.sqrt_nonneg sigma⟩
    have hEqSigma : gamma (Real.sqrt sigma) =
        lRegularizedCurve S T x Z (Real.sqrt sigma) :=
      hEq ⟨Real.sqrt_nonneg sigma, le_rfl⟩
    have haction : lRegularizedAction S T gamma 0 (Real.sqrt sigma) =
        lRegularizedAction S T (lRegularizedCurve S T x Z) 0 (Real.sqrt sigma) := by
      apply lRegularizedAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo (0 : ℝ) (Real.sqrt sigma) := by
        simpa only [uIoo_of_le (Real.sqrt_nonneg sigma)] using hs
      exact hEq ⟨hs'.1.le, hs'.2.le⟩
    rw [haction, hcost]
    exact lRegularizedCostC1_le_bdd (I := I) S T 0 (Real.sqrt sigma) x
      (lExp S T x Z sigma) hbdd delta hdelta
      (by simpa only [lRegularizedCurve_zero] using hd0.trans hEq0)
      (hdsigma.trans hEqSigma)
  have hnonneg := lRegularizedIndex_piecewise_nonneg (I := I) S hS T gamma
    0 (Real.sqrt tau) (Real.sqrt sigma) hc0 hcb x Z hgeo hminGamma
    Y0 Y1 hY0 hY1 hY0zero hY1zero hnode
  linarith

theorem lMinVec_nconj_lt_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (x : M)
    {Z : TangentSpace I x} {sigma tau : ℝ}
    (hmin : (Z, sigma) ∈ lMinDomain S T x)
    (hlt : tau < sigma)
    (hRm : ∀ t ∈ Icc (T - sigma) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4
        (S.base.rm04 t z) ≤ K) :
    ¬ IsLConjugate S T x Z tau := by
  have hdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z sigma).1 hmin).1
  have hsigma : 0 < sigma :=
    lMinDomain_pos S T x Z sigma hmin
  have hreg : Icc (T - sigma) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T - t := sub_nonneg.mpr ht.2
    have hback : T - t ≤ sigma := by
      linarith [ht.1]
    have hsqrt : Real.sqrt (T - t) ∈
        Icc (0 : ℝ) (Real.sqrt sigma) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hback⟩
    have hclock := lExpPosDom_regularity S T x Z hdom hsqrt
    have heq : T - (Real.sqrt (T - t)) ^ 2 = t := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hclock
  apply lMinVec_nconj_lt_of_bdd (I := I) S hS T x hmin hlt
  exact lRegularizedCosts_bdd_rm (I := I) S hS K T 0 (Real.sqrt sigma)
    le_rfl (Real.sqrt_nonneg sigma)
    (by simpa only [Real.sq_sqrt hsigma.le] using hreg)
    (by simpa only [Real.sq_sqrt hsigma.le] using hRm)
    x (lExp S T x Z sigma)

end DifferentialGeometry.PDE.RicciFlow
