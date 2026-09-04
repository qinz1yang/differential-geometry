import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.RegularizedC1Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.C1Regularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Function Set
open scoped ContDiff Manifold

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem exists_lRegMinC1On
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real)
    (a b : Real) (hab : a < b)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ gamma : Real → M,
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b) ∧
        gamma a = x ∧ gamma b = y ∧
        lRegAction S T gamma a b = lRegCostC1 S T a b x y ∧
        ∀ delta : Real → M,
          ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
          delta a = x → delta b = y →
          lRegAction S T gamma a b ≤ lRegAction S T delta a b := by
  obtain ⟨gamma, m, t, p, uLim, _beta, _u, hgamma, hga, hgb, hcost,
      hmin, htmono, ht0, htlast, hsrc, hrep, _hbeta, _hbetaa, _hbetab,
      _hsrcBeta, _hrepBeta, _hu, _hunifBeta, _hbetaAct⟩ :=
    exists_lRegMinC1 (I := I) S hS T t0 t1 a b hab.le htime hback x y
      alpha0 halpha0 h0a h0b hreg
  have hmin' : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b := by
    intro delta hdelta hda hdb
    exact hmin delta hdelta (hda.trans hga) (hdb.trans hgb)
  have hc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a b) :=
    lMinCurve_c1 (I := I) S hS T a b hab t htmono ht0 htlast p gamma
      hgamma uLim hsrc hrep hreg hmin'
  exact ⟨gamma, hc1, hga, hgb, hcost, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
