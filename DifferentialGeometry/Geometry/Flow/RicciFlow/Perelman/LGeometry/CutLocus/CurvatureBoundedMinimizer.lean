import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CompleteActionBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] in
omit [SigmaCompactSpace M] in
theorem lMinVec_min_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real) (x : M) {Z : TangentSpace I x} {tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (delta : Real → M)
    (hdelta : ContMDiff (modelWithCornersSelf Real Real) I 1 delta)
    (hd0 : delta 0 = lRegCurve S T x Z 0)
    (hdt : delta (Real.sqrt tau) =
      lRegCurve S T x Z (Real.sqrt tau)) :
    lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) ≤
      lRegAction S T delta 0 (Real.sqrt tau) := by
  have hvec := (mem_lMinDomain S T x Z tau).1 hmin
  have htau : 0 < tau := lMinDomain_pos S T x Z tau hmin
  have hsqrt : 0 ≤ Real.sqrt tau := Real.sqrt_nonneg tau
  have hsq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.regular := by
    simpa only [hsq] using hreg
  have hRmSq : ∀ q ∈ Icc (T - (Real.sqrt tau) ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hsq] using hRm
  have hcost : lRegAction S T (lRegCurve S T x Z) 0
      (Real.sqrt tau) = lRegCostC1 S T 0 (Real.sqrt tau) x
        (lRegCurve S T x Z (Real.sqrt tau)) := by
    calc
      lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) =
          lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau := by
        change _ = lLength S T
          (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 tau
        rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
          sqrtReparam (lRegCurve S T x Z) by rfl]
        exact (lLength_sqrt (I := I) S T (lRegCurve S T x Z) tau
          htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := hvec.2
      _ = lRegCostC1 S T 0 (Real.sqrt tau) x
          (lExp S T x Z tau) :=
        lCost_eq_reg (I := I) S T x (lExp S T x Z tau) tau htau.le
      _ = lRegCostC1 S T 0 (Real.sqrt tau) x
          (lRegCurve S T x Z (Real.sqrt tau)) := by rfl
  have hbdd := lRegCosts_bdd_rm (I := I) S hS K T 0
    (Real.sqrt tau) (by norm_num) hsqrt hregSq hRmSq x
    (lRegCurve S T x Z (Real.sqrt tau))
  rw [hcost]
  exact lRegCostC1_le_bdd (I := I) S T 0 (Real.sqrt tau) x
    (lRegCurve S T x Z (Real.sqrt tau)) hbdd delta hdelta
    (hd0.trans (by simp only [lRegCurve_zero])) hdt

end DifferentialGeometry.PDE.RicciFlow.Perelman
