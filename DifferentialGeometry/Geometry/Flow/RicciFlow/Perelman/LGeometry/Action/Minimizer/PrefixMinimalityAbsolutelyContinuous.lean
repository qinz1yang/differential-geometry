import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.PrefixMinimality
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuous
set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {D : RealTimeInterval}

theorem lRegularizedAction_minimal_on_subinterval_of_absolutelyContinuousOnInterval
    (S : SolutionOn (I := I) (M := M) D) (T a c d b : ℝ)
    (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b)
    (gamma : ℝ → M) (hgamma : Manifold.absolutelyContinuousOnInterval I gamma a b)
    (hint : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume a b)
    (hmin : ∀ eta : ℝ → M, Manifold.absolutelyContinuousOnInterval I eta a b →
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume a b →
      eta a = gamma a → eta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T eta a b) :
    ∀ delta : ℝ → M, Manifold.absolutelyContinuousOnInterval I delta c d →
      IntervalIntegrable (lRegularizedLagrangian S T delta) volume c d →
      delta c = gamma c → delta d = gamma d →
      lRegularizedAction S T gamma c d ≤ lRegularizedAction S T delta c d := by
  classical
  intro delta hdelta hdeltaInt hdeltaC hdeltaD
  have hab := hac.trans (hcd.trans hdb)
  have hgammaAC (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      Manifold.absolutelyContinuousOnInterval I gamma s t :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [uIcc_of_le hst, uIcc_of_le hab] using Icc_subset_Icc has htb)
  have hgammaInt (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      IntervalIntegrable (lRegularizedLagrangian S T gamma) volume s t :=
    hint.mono_set (by
      simpa only [uIcc_of_le hst, uIcc_of_le hab] using Icc_subset_Icc has htb)
  let beta : ℝ → M := (Iic c).piecewise gamma delta
  have hbetaLeft (r : ℝ) (hr : r ≤ c) : beta r = gamma r := if_pos hr
  have hbetaRight (r : ℝ) (hr : c ≤ r) : beta r = delta r := by
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact (hbetaLeft c le_rfl).trans hdeltaC.symm
    · exact if_neg (not_le.mpr hr)
  have hbeta : Manifold.absolutelyContinuousOnInterval I beta a d :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic
      (hgammaAC a c le_rfl hac (hcd.trans hdb)) hdelta hac hcd hdeltaC.symm
  let eta : ℝ → M := (Iic d).piecewise beta gamma
  have heta : Manifold.absolutelyContinuousOnInterval I eta a b :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic hbeta
      (hgammaAC d b (hac.trans hcd) hdb le_rfl) (hac.trans hcd) hdb
      ((hbetaRight d hcd).trans hdeltaD)
  have hleft : EqOn eta gamma (Icc a c) := by
    intro r hr
    exact (if_pos (hr.2.trans hcd)).trans (hbetaLeft r hr.2)
  have hmiddle : EqOn eta delta (Icc c d) := by
    intro r hr
    exact (if_pos hr.2).trans (hbetaRight r hr.1)
  have hright : EqOn eta gamma (Icc d b) := by
    intro r hr
    rcases hr.1.eq_or_lt with heq | hlt
    · subst r
      exact (hmiddle ⟨hcd, le_rfl⟩).trans hdeltaD
    · exact if_neg (not_le.mpr hlt)
  have hlag (alpha beta : ℝ → M) (s t : ℝ) (hst : s ≤ t)
      (heq : EqOn alpha beta (Icc s t)) :
      EqOn (lRegularizedLagrangian S T alpha) (lRegularizedLagrangian S T beta) (uIoo s t) := by
    intro r hr
    rw [uIoo_of_le hst] at hr
    have hn : alpha =ᶠ[𝓝 r] beta := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
      exact heq (Ioo_subset_Icc_self hx)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
  have hlagLeft := hlag eta gamma a c hac hleft
  have hlagMiddle := hlag eta delta c d hcd hmiddle
  have hlagRight := hlag eta gamma d b hdb hright
  have hgammaIntLeft := hgammaInt a c le_rfl hac (hcd.trans hdb)
  have hgammaIntMiddle := hgammaInt c d hac hcd hdb
  have hgammaIntRight := hgammaInt d b (hac.trans hcd) hdb le_rfl
  have hetaIntLeft := hgammaIntLeft.congr_uIoo hlagLeft.symm
  have hetaIntMiddle := hdeltaInt.congr_uIoo hlagMiddle.symm
  have hetaIntRight := hgammaIntRight.congr_uIoo hlagRight.symm
  have hwhole := hmin eta heta ((hetaIntLeft.trans hetaIntMiddle).trans hetaIntRight)
    (hleft ⟨le_rfl, hac⟩) (hright ⟨hdb, le_rfl⟩)
  have hactLeft : lRegularizedAction S T eta a c = lRegularizedAction S T gamma a c :=
    intervalIntegral.integral_congr_uIoo hlagLeft
  have hactMiddle : lRegularizedAction S T eta c d = lRegularizedAction S T delta c d :=
    intervalIntegral.integral_congr_uIoo hlagMiddle
  have hactRight : lRegularizedAction S T eta d b = lRegularizedAction S T gamma d b :=
    intervalIntegral.integral_congr_uIoo hlagRight
  rw [← lRegularizedAction_add S T gamma a d b (hgammaIntLeft.trans hgammaIntMiddle) hgammaIntRight,
    ← lRegularizedAction_add S T gamma a c d hgammaIntLeft hgammaIntMiddle,
    ← lRegularizedAction_add S T eta a d b (hetaIntLeft.trans hetaIntMiddle) hetaIntRight,
    ← lRegularizedAction_add S T eta a c d hetaIntLeft hetaIntMiddle,
    hactLeft, hactMiddle, hactRight] at hwhole
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
