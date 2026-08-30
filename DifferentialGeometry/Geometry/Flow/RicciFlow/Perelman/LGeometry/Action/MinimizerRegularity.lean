import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.StrictRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Strict

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lMinCurve_reg
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (hab : a < b) {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b) (p : Fin m → M)
    (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (lSegLen t i))
    (hsrc : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i, EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (lSegLen t i)))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    ∀ s ∈ Ioo a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
      DifferentiableAt Real
        (chartRepAt (I := I) gamma
          (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
          (fun r ↦ lVelocity (I := I) gamma r) s =
        lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  classical
  obtain ⟨k, s, _q, p', u', hs, _hq, hs0, hslast, _hseg, _hp,
      hsrc', hrep'⟩ := exists_lStrict (I := I) t htmono p u gamma hsrc hrep
  have hs0a : s 0 = a := hs0.trans ht0
  have hslastb : s (Fin.last k) = b := hslast.trans htlast
  have hk : 0 < k := by
    cases k with
    | zero =>
        exfalso
        apply hab.ne
        exact hs0a.symm.trans ((congrArg s (Fin.ext (by simp))).trans hslastb)
    | succ k => omega
  exact lStrict_curve_reg (I := I) S hS T a b s hs hs0a hslastb p'
    gamma hgamma u' hsrc' hrep' hreg hmin

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
