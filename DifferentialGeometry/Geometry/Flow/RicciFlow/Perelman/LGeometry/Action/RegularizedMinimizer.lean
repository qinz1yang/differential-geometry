import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MinimizerC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MinimizerRegularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Function Set
open scoped ContDiff Manifold

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

theorem exists_lRegMinOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 b : Real) (hb : 0 < b)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0b : alpha0 b = y)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular) :
    ∃ (alpha : Real → M) (Z : TangentSpace I x),
      IsLRegCurveOn S T alpha (Icc (0 : Real) b) x Z ∧
        b ∈ lRegDomain S T x Z ∧
          Set.EqOn (lRegCurve S T x Z) alpha (Icc (0 : Real) b) ∧
            alpha b = y ∧
            lRegAction S T alpha 0 b = lRegCostC1 S T 0 b x y ∧
            ∀ delta : Real → M,
              ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
              delta 0 = x → delta b = y →
              lRegAction S T alpha 0 b ≤ lRegAction S T delta 0 b := by
  obtain ⟨gamma, m, t, p, uLim, _beta, _u, hgamma, hga, hgb, hcost,
      hmin, htmono, ht0, htlast, hsrc, hrep, _hbeta, _hbetaa, _hbetab,
      _hsrcBeta, _hrepBeta, _hu, _hunifBeta, _hbetaAct⟩ :=
    exists_lRegMinC1 (I := I) S hS T t0 t1 0 b hb.le htime hback x y
      alpha0 halpha0 h00 h0b hreg
  have hmin' : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = gamma 0 → delta b = gamma b →
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hda hdb
    exact hmin delta hdelta (hda.trans hga) (hdb.trans hgb)
  have hc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) b) :=
    lMinCurve_c1 (I := I) S hS T 0 b hb t htmono ht0 htlast p gamma
      hgamma uLim hsrc hrep hreg hmin'
  have hsol : ∀ s ∈ Ioo (0 : Real) b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) :=
    lMinCurve_reg (I := I) S hS T 0 b hb t htmono ht0 htlast p gamma
      hgamma uLim hsrc hrep hreg hmin'
  obtain ⟨alpha, halpha, e, he, halphaSol⟩ :=
    exists_lRegExtOn (I := I) S hS T 0 b hb gamma hc1 hreg hsol
  have ha0 : alpha 0 = x :=
    (halpha ⟨le_rfl, hb.le⟩).trans hga
  have hab : alpha b = y :=
    (halpha ⟨hb.le, le_rfl⟩).trans hgb
  have haction : lRegAction S T alpha 0 b = lRegAction S T gamma 0 b := by
    apply lRegAction_congr (I := I) S T alpha gamma 0 b
    intro s hs
    have hs' : s ∈ Ioo (0 : Real) b := by
      simpa only [uIoo_of_le hb.le] using hs
    exact halpha ⟨hs'.1.le, hs'.2.le⟩
  let Z : TangentSpace I x :=
    (2 : Real)⁻¹ • lVelocity (I := I) alpha 0
  have hvel : lVelocity (I := I) alpha 0 = 2 • Z := by
    have hreal : lVelocity (I := I) alpha 0 = (2 : Real) • Z := by
      simp only [Z]
      exact (smul_inv_smul₀ (by norm_num : (2 : Real) ≠ 0) _).symm
    exact hreal.trans (Nat.cast_smul_eq_nsmul Real 2 Z)
  have hcurve : IsLRegCurveOn S T alpha (Icc (0 : Real) b) x Z :=
    ⟨ha0, hvel, fun s hs ↦ halphaSol s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  have hcurveOpen :
      IsLRegCurveOn S T alpha (Ioo (-e) (b + e)) x Z := by
    refine ⟨ha0, hvel, ?_⟩
    simpa only [zero_sub] using halphaSol
  have h0Open : (0 : Real) ∈ Ioo (-e) (b + e) := by
    constructor <;> linarith
  have hbOpen : b ∈ Ioo (-e) (b + e) := by
    constructor <;> linarith
  have hbDom : b ∈ lRegDomain S T x Z :=
    ⟨alpha, Ioo (-e) (b + e), isOpen_Ioo, isPreconnected_Ioo,
      h0Open, hbOpen, hcurveOpen⟩
  have hmax : Set.EqOn (lRegCurve S T x Z) alpha (Icc (0 : Real) b) :=
    lRegCurve_eqIcc S hS T b e hb.le he hcurveOpen
  refine ⟨alpha, Z, hcurve, hbDom, hmax, hab, haction.trans hcost, ?_⟩
  intro delta hdelta hda hdb
  rw [haction]
  exact hmin delta hdelta hda hdb

end DifferentialGeometry.PDE.RicciFlow.Perelman
