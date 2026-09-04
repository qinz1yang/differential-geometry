import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedExistence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Length
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem lCost_eq_reg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (x y : M) (tau : Real) (htau : 0 ≤ tau) :
    lCost S T x y tau =
      lRegCostC1 S T 0 (Real.sqrt tau) x y := by
  unfold lCost lRegCostC1
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨alpha, halpha, h0, ht, hr⟩
    refine ⟨alpha, halpha, h0, ht, ?_⟩
    rw [lLength_squareRootReparametrization_eq_lRegAction (I := I) S T alpha tau htau] at hr
    exact hr
  · rintro ⟨alpha, halpha, h0, ht, hr⟩
    refine ⟨alpha, halpha, h0, ht, ?_⟩
    rw [lLength_squareRootReparametrization_eq_lRegAction (I := I) S T alpha tau htau]
    exact hr

theorem exists_lMinimizer
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 tau : Real) (htau : 0 < tau)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y)
    (hreg : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular) :
    ∃ (alpha : Real → M) (Z : TangentSpace I x),
      IsLRegCurveOn S T alpha (Icc (0 : Real) (Real.sqrt tau)) x Z ∧
        Set.EqOn (lRegCurve S T x Z) alpha
            (Icc (0 : Real) (Real.sqrt tau)) ∧
          (Z, tau) ∈ lExpPosDom S T x ∧
            lExp S T x Z tau = y ∧
              alpha (Real.sqrt tau) = y ∧
              lLength S T (squareRootReparametrization alpha) 0 tau = lCost S T x y tau ∧
              ∀ delta : Real → M,
                ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
                delta 0 = x → delta (Real.sqrt tau) = y →
                lLength S T (squareRootReparametrization alpha) 0 tau ≤
                  lLength S T (squareRootReparametrization delta) 0 tau := by
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  obtain ⟨alpha, Z, hcurve, hbDom, hmax, hend, hcost, hmin⟩ :=
    exists_lRegMinOn (I := I) S hS T t0 t1 (Real.sqrt tau) hsqrt
      htime hback x y alpha0 halpha0 h00 h0t hreg
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x Z tau).2 ⟨htau, htau.le, hbDom⟩
  have hExp : lExp S T x Z tau = y := by
    have heq := hmax ⟨Real.sqrt_nonneg tau, le_rfl⟩
    have heq' : lExp S T x Z tau = alpha (Real.sqrt tau) := by
      simpa only [lExp] using heq
    exact heq'.trans hend
  refine ⟨alpha, Z, hcurve, hmax, hdom, hExp, hend, ?_, ?_⟩
  · calc
      lLength S T (squareRootReparametrization alpha) 0 tau =
          lRegAction S T alpha 0 (Real.sqrt tau) :=
        lLength_squareRootReparametrization_eq_lRegAction (I := I) S T alpha tau htau.le
      _ = lRegCostC1 S T 0 (Real.sqrt tau) x y := hcost
      _ = lCost S T x y tau :=
        (lCost_eq_reg (I := I) S T x y tau htau.le).symm
  · intro delta hdelta hd0 hdt
    rw [lLength_squareRootReparametrization_eq_lRegAction (I := I) S T alpha tau htau.le,
      lLength_squareRootReparametrization_eq_lRegAction (I := I) S T delta tau htau.le]
    exact hmin delta hdelta hd0 hdt

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
