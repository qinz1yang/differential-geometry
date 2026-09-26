import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventAction
import DifferentialGeometry.Analysis.Calculus.Manifold.AbsolutelyContinuousPartition
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.LocalPullbackLagrangian
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.IntervalLiftAbsolutelyContinuous
set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology Interval

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe uSurvivorAC vSurvivorAC

theorem exists_survivor_curve_action_eq_of_confined_event_competitor
    {P Q : OrientedThreeStage.{uSurvivorAC}} {a s b : ℝ}
    (E : MetricCutCapEvent P Q a s) (G : Q.IncomingSlab s b)
    {X : Type vSurvivorAC} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (f : X → P.Carrier) (g : X → Q.Carrier)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
    (hfi : Function.Injective f)
    (hcross : ∀ x : X, E.RegularCrossing (f x) (g x))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (T : ℝ) {u d v : ℝ} (hud : u ≤ d) (hdv : d ≤ v)
    (hbefore : ∀ r ∈ Ioo d v, S.base.metric (T - r ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - r ^ 2)) f hf)
    (hafter : ∀ r ∈ Ioo u d, S.base.metric (T - r ^ 2) =
      localPullMetric (G.flow.base.metric (T - r ^ 2)) g hg)
    (alpha : ℝ → Q.Carrier) (beta : ℝ → P.Carrier)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha u d)
    (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta d v)
    (halphaInt : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume u d)
    (hbetaInt : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume d v)
    (halphaStay : MapsTo alpha (Icc u d) (range g))
    (hbetaStay : MapsTo beta (Icc d v) (range f))
    (hnode : ∃ z : E.old, z.val.val = beta d ∧ E.oldOutput z = alpha d) :
    ∃ gamma : ℝ → X,
      Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v ∧
      EqOn (g ∘ gamma) alpha (Icc u d) ∧
      EqOn (f ∘ gamma) beta (Icc d v) ∧
      IntervalIntegrable (lRegularizedLagrangian S T gamma) volume u v ∧
      lRegularizedAction S T gamma u v = lRegularizedAction G.flow T alpha u d +
        lRegularizedAction E.incoming.flow T beta d v := by
  classical
  have hgi : Function.Injective g := by
    intro x y hxy
    apply hfi
    exact E.regularCrossing_left_unique
      (by simpa only [hxy] using hcross x) (hcross y)
  let : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  obtain ⟨alpha', halpha', halphaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_absolutelyContinuousOnInterval_lift_of_injective_localDiffeomorph
      g hg hgi alpha halpha (by simpa only [uIcc_of_le hud] using halphaStay)
  obtain ⟨beta', hbeta', hbetaEq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_absolutelyContinuousOnInterval_lift_of_injective_localDiffeomorph
      f hf hfi beta hbeta (by simpa only [uIcc_of_le hdv] using hbetaStay)
  rw [uIcc_of_le hud] at halphaEq
  rw [uIcc_of_le hdv] at hbetaEq
  have hmatch : alpha' d = beta' d := by
    obtain ⟨z, hz, hzout⟩ := hnode
    obtain ⟨w, _, hw, hwout⟩ := hcross (alpha' d)
    have hzw : z = w := E.oldOutput_injective
      (hzout.trans ((halphaEq ⟨hud, le_rfl⟩).symm.trans hwout.symm))
    apply hfi
    exact hw.symm.trans ((congrArg (fun z : E.old => z.val.val) hzw).symm.trans
      (hz.trans (hbetaEq ⟨le_rfl, hdv⟩).symm))
  let gamma : ℝ → X := (Iic d).piecewise alpha' beta'
  have hgamma : Manifold.absolutelyContinuousOnInterval ThreeModel gamma u v :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic halpha' hbeta' hud hdv hmatch
  have hleft : EqOn (g ∘ gamma) alpha (Icc u d) := by
    intro r hr
    change g (gamma r) = alpha r
    rw [show gamma r = alpha' r from if_pos hr.2]
    exact halphaEq hr
  have hright : EqOn (f ∘ gamma) beta (Icc d v) := by
    intro r hr
    have hright : gamma r = beta' r := by
      rcases hr.1.eq_or_lt with hrd | hrd
      · subst r
        exact (show gamma d = alpha' d from
          piecewise_eq_of_mem (Iic d) alpha' beta' (show d ∈ Iic d from le_refl d)).trans hmatch
      · exact if_neg (not_le.mpr hrd)
    change f (gamma r) = beta r
    rw [hright]
    exact hbetaEq hr
  have hgammaLeft : Manifold.absolutelyContinuousOnInterval ThreeModel gamma u d :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [uIcc_of_le hud, uIcc_of_le (hud.trans hdv)] using Icc_subset_Icc le_rfl hdv)
  have hgammaRight : Manifold.absolutelyContinuousOnInterval ThreeModel gamma d v :=
    Manifold.absolutelyContinuousOnInterval_mono hgamma (by
      simpa only [uIcc_of_le hdv, uIcc_of_le (hud.trans hdv)] using Icc_subset_Icc hud le_rfl)
  have hlagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hud gamma alpha hgammaLeft (hleft.mono Ioo_subset_Icc_self) hafter
  have hlagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hdv gamma beta hgammaRight (hright.mono Ioo_subset_Icc_self) hbefore
  have hintLeft : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume u d :=
    (intervalIntegrable_congr_ae hlagLeft).mpr halphaInt
  have hintRight : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume d v :=
    (intervalIntegrable_congr_ae hlagRight).mpr hbetaInt
  refine ⟨gamma, hgamma, hleft, hright, hintLeft.trans hintRight, ?_⟩
  rw [← lRegularizedAction_add S T gamma u d v hintLeft hintRight]
  exact congrArg₂ (fun x y : ℝ => x + y)
    (intervalIntegral.integral_congr_ae_restrict hlagLeft)
    (intervalIntegral.integral_congr_ae_restrict hlagRight)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe uLocalMin vLocalMin

theorem lRegularizedAction_le_of_minimal_event_competitor
    {P Q : OrientedThreeStage.{uLocalMin}} {a s b : ℝ}
    (E : MetricCutCapEvent P Q a s) (G : Q.IncomingSlab s b)
    {X : Type vLocalMin} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (f : X → P.Carrier) (g : X → Q.Carrier)
    (hf : IsLocalDiffeomorph ThreeModel ThreeModel ∞ f)
    (hg : IsLocalDiffeomorph ThreeModel ThreeModel ∞ g)
    (hcross : ∀ x : X, E.RegularCrossing (f x) (g x))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D)
    (T : ℝ) {l c w d r : ℝ} (hlc : l ≤ c) (hcw : c ≤ w)
    (hwd : w ≤ d) (hdr : d ≤ r)
    (hbefore : ∀ t ∈ Ioo w d, S.base.metric (T - t ^ 2) =
      localPullMetric (E.incoming.flow.base.metric (T - t ^ 2)) f hf)
    (hafter : ∀ t ∈ Ioo c w, S.base.metric (T - t ^ 2) =
      localPullMetric (G.flow.base.metric (T - t ^ 2)) g hg)
    (alpha : ℝ → Q.Carrier) (beta : ℝ → P.Carrier)
    (halpha : Manifold.absolutelyContinuousOnInterval ThreeModel alpha l w)
    (hbeta : Manifold.absolutelyContinuousOnInterval ThreeModel beta w r)
    (halphaInt : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume l w)
    (hbetaInt : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume w r)
    (hmin : ∀ (alpha' : ℝ → Q.Carrier) (beta' : ℝ → P.Carrier),
      Manifold.absolutelyContinuousOnInterval ThreeModel alpha' l w →
      Manifold.absolutelyContinuousOnInterval ThreeModel beta' w r →
      IntervalIntegrable (lRegularizedLagrangian G.flow T alpha') volume l w →
      IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta') volume w r →
      alpha' l = alpha l → beta' r = beta r →
      (∃ z : E.old, z.val.val = beta' w ∧ E.oldOutput z = alpha' w) →
      lRegularizedAction G.flow T alpha l w + lRegularizedAction E.incoming.flow T beta w r ≤
        lRegularizedAction G.flow T alpha' l w + lRegularizedAction E.incoming.flow T beta' w r)
    (gamma : ℝ → X)
    (hgamma : Manifold.absolutelyContinuousOnInterval ThreeModel gamma c d)
    (hleft : EqOn (g ∘ gamma) alpha (Icc c w))
    (hright : EqOn (f ∘ gamma) beta (Icc w d)) :
    ∀ delta : ℝ → X, Manifold.absolutelyContinuousOnInterval ThreeModel delta c d →
      IntervalIntegrable (lRegularizedLagrangian S T delta) volume c d →
      delta c = gamma c → delta d = gamma d →
      lRegularizedAction S T gamma c d ≤ lRegularizedAction S T delta c d := by
  classical
  let : IsManifold ThreeModel 1 X := IsManifold.of_le (n := ∞) (by decide)
  intro delta hdelta hdeltaInt hdeltaC hdeltaD
  have hcd := hcw.trans hwd
  have hlw := hlc.trans hcw
  have hwr := hwd.trans hdr
  have hacLeft (eta : ℝ → X)
      (heta : Manifold.absolutelyContinuousOnInterval ThreeModel eta c d) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta c w :=
    Manifold.absolutelyContinuousOnInterval_mono heta (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hacRight (eta : ℝ → X)
      (heta : Manifold.absolutelyContinuousOnInterval ThreeModel eta c d) :
      Manifold.absolutelyContinuousOnInterval ThreeModel eta w d :=
    Manifold.absolutelyContinuousOnInterval_mono heta (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  have hintLeft (eta : ℝ → X)
      (heta : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume c w :=
    heta.mono_set (by
      simpa only [uIcc_of_le hcw, uIcc_of_le hcd] using Icc_subset_Icc le_rfl hwd)
  have hintRight (eta : ℝ → X)
      (heta : IntervalIntegrable (lRegularizedLagrangian S T eta) volume c d) :
      IntervalIntegrable (lRegularizedLagrangian S T eta) volume w d :=
    heta.mono_set (by
      simpa only [uIcc_of_le hwd, uIcc_of_le hcd] using Icc_subset_Icc hcw le_rfl)
  have hgammaLagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hcw gamma alpha (hacLeft gamma hgamma) (hleft.mono Ioo_subset_Icc_self) hafter
  have hgammaLagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hwd gamma beta (hacRight gamma hgamma) (hright.mono Ioo_subset_Icc_self) hbefore
  have hdeltaLagLeft := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S G.flow g hg T hcw delta (g ∘ delta) (hacLeft delta hdelta) (fun _ _ => rfl) hafter
  have hdeltaLagRight := lRegularizedLagrangian_ae_eq_of_metric_eqOn_localPullback
    S E.incoming.flow f hf T hwd delta (f ∘ delta) (hacRight delta hdelta) (fun _ _ => rfl) hbefore
  have hgdelta := Manifold.absolutelyContinuousOnInterval_comp_contMDiff
    (hacLeft delta hdelta) (hg.contMDiff.of_le (by norm_num))
  have hfdelta := Manifold.absolutelyContinuousOnInterval_comp_contMDiff
    (hacRight delta hdelta) (hf.contMDiff.of_le (by norm_num))
  have hgdeltaInt := (intervalIntegrable_congr_ae hdeltaLagLeft).mp (hintLeft delta hdeltaInt)
  have hfdeltaInt := (intervalIntegrable_congr_ae hdeltaLagRight).mp (hintRight delta hdeltaInt)
  have halphaLeft : Manifold.absolutelyContinuousOnInterval ThreeModel alpha l c :=
    Manifold.absolutelyContinuousOnInterval_mono halpha (by
      simpa only [uIcc_of_le hlc, uIcc_of_le hlw] using Icc_subset_Icc le_rfl hcw)
  have hbetaRight : Manifold.absolutelyContinuousOnInterval ThreeModel beta d r :=
    Manifold.absolutelyContinuousOnInterval_mono hbeta (by
      simpa only [uIcc_of_le hdr, uIcc_of_le hwr] using Icc_subset_Icc hwd le_rfl)
  have hmatchLeft : alpha c = (g ∘ delta) c :=
    (hleft ⟨le_rfl, hcw⟩).symm.trans (congrArg g hdeltaC.symm)
  have hmatchRight : (f ∘ delta) d = beta d :=
    (congrArg f hdeltaD).trans (hright ⟨hwd, le_rfl⟩)
  let alpha' : ℝ → Q.Carrier := (Iic c).piecewise alpha (g ∘ delta)
  let beta' : ℝ → P.Carrier := (Iic d).piecewise (f ∘ delta) beta
  have halpha' : Manifold.absolutelyContinuousOnInterval ThreeModel alpha' l w :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic halphaLeft hgdelta hlc hcw hmatchLeft
  have hbeta' : Manifold.absolutelyContinuousOnInterval ThreeModel beta' w r :=
    Manifold.absolutelyContinuousOnInterval_piecewise_Iic hfdelta hbetaRight hwd hdr hmatchRight
  have halphaEqLeft : EqOn alpha' alpha (Icc l c) := fun _ ht => if_pos ht.2
  have halphaEqRight : EqOn alpha' (g ∘ delta) (Icc c w) := by
    intro t ht
    rcases ht.1.eq_or_lt with ht | ht
    · subst t
      exact (show alpha' c = alpha c from piecewise_eq_of_mem (Iic c) alpha (g ∘ delta) (show c ∈ Iic c from le_refl c)).trans hmatchLeft
    · exact if_neg (not_le.mpr ht)
  have hbetaEqLeft : EqOn beta' (f ∘ delta) (Icc w d) := fun _ ht => if_pos ht.2
  have hbetaEqRight : EqOn beta' beta (Icc d r) := by
    intro t ht
    rcases ht.1.eq_or_lt with ht | ht
    · subst t
      exact (show beta' d = (f ∘ delta) d from piecewise_eq_of_mem (Iic d) (f ∘ delta) beta (show d ∈ Iic d from le_refl d)).trans hmatchRight
    · exact if_neg (not_le.mpr ht)
  have hlag {Y : Type uLocalMin} [TopologicalSpace Y] [ChartedSpace ThreeSpace Y]
      [IsManifold ThreeModel ∞ Y] {D' : RealTimeInterval}
      (R : SolutionOn (I := ThreeModel) (M := Y) D')
      (eta zeta : ℝ → Y) (x y : ℝ) (hxy : x ≤ y) (heq : EqOn eta zeta (Icc x y)) :
      EqOn (lRegularizedLagrangian R T eta) (lRegularizedLagrangian R T zeta) (uIoo x y) := by
    intro t ht
    rw [uIoo_of_le hxy] at ht
    have hn : eta =ᶠ[𝓝 t] zeta := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with z hz
      exact heq (Ioo_subset_Icc_self hz)
    have hv := hn.self_of_nhds
    have hder := hn.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := ThreeModel)
    unfold lRegularizedLagrangian lVelocity
    rw [hv, hder]
  have halphaIntLeft : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume l c := halphaInt.mono_set (by
    simpa only [uIcc_of_le hlc, uIcc_of_le hlw] using Icc_subset_Icc le_rfl hcw)
  have halphaIntRight : IntervalIntegrable (lRegularizedLagrangian G.flow T alpha) volume c w := halphaInt.mono_set (by
    simpa only [uIcc_of_le hcw, uIcc_of_le hlw] using Icc_subset_Icc hlc le_rfl)
  have hbetaIntLeft : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume w d := hbetaInt.mono_set (by
    simpa only [uIcc_of_le hwd, uIcc_of_le hwr] using Icc_subset_Icc le_rfl hdr)
  have hbetaIntRight : IntervalIntegrable (lRegularizedLagrangian E.incoming.flow T beta) volume d r := hbetaInt.mono_set (by
    simpa only [uIcc_of_le hdr, uIcc_of_le hwr] using Icc_subset_Icc hwd le_rfl)
  have hgammaInt : IntervalIntegrable (lRegularizedLagrangian S T gamma) volume c d :=
    ((intervalIntegrable_congr_ae hgammaLagLeft).mpr halphaIntRight).trans
      ((intervalIntegrable_congr_ae hgammaLagRight).mpr hbetaIntLeft)
  have hlagAL := hlag G.flow alpha' alpha l c hlc halphaEqLeft
  have hlagAR := hlag G.flow alpha' (g ∘ delta) c w hcw halphaEqRight
  have hlagBL := hlag E.incoming.flow beta' (f ∘ delta) w d hwd hbetaEqLeft
  have hlagBR := hlag E.incoming.flow beta' beta d r hdr hbetaEqRight
  have hintAL := halphaIntLeft.congr_uIoo hlagAL.symm
  have hintAR := hgdeltaInt.congr_uIoo hlagAR.symm
  have hintBL := hfdeltaInt.congr_uIoo hlagBL.symm
  have hintBR := hbetaIntRight.congr_uIoo hlagBR.symm
  have hnode : ∃ z : E.old, z.val.val = beta' w ∧ E.oldOutput z = alpha' w := by
    obtain ⟨z, _, hz, hzout⟩ := hcross (delta w)
    exact ⟨z, hz.trans (hbetaEqLeft ⟨le_rfl, hwd⟩).symm,
      hzout.trans (halphaEqRight ⟨hcw, le_rfl⟩).symm⟩
  have hwhole := hmin alpha' beta' halpha' hbeta'
    (hintAL.trans hintAR) (hintBL.trans hintBR)
    (halphaEqLeft ⟨le_rfl, hlc⟩) (hbetaEqRight ⟨hdr, le_rfl⟩) hnode
  rw [← lRegularizedAction_add G.flow T alpha l c w halphaIntLeft halphaIntRight,
    ← lRegularizedAction_add E.incoming.flow T beta w d r hbetaIntLeft hbetaIntRight,
    ← lRegularizedAction_add G.flow T alpha' l c w hintAL hintAR,
    ← lRegularizedAction_add E.incoming.flow T beta' w d r hintBL hintBR,
    show lRegularizedAction G.flow T alpha' l c = lRegularizedAction G.flow T alpha l c from
      intervalIntegral.integral_congr_uIoo hlagAL,
    show lRegularizedAction G.flow T alpha' c w = lRegularizedAction G.flow T (g ∘ delta) c w from
      intervalIntegral.integral_congr_uIoo hlagAR,
    show lRegularizedAction E.incoming.flow T beta' w d =
        lRegularizedAction E.incoming.flow T (f ∘ delta) w d from
      intervalIntegral.integral_congr_uIoo hlagBL,
    show lRegularizedAction E.incoming.flow T beta' d r = lRegularizedAction E.incoming.flow T beta d r from
      intervalIntegral.integral_congr_uIoo hlagBR] at hwhole
  have hgact : lRegularizedAction S T gamma c d =
      lRegularizedAction G.flow T alpha c w + lRegularizedAction E.incoming.flow T beta w d := by
    rw [← lRegularizedAction_add S T gamma c w d (hintLeft gamma hgammaInt) (hintRight gamma hgammaInt)]
    exact congrArg₂ (fun x y : ℝ => x + y)
      (intervalIntegral.integral_congr_ae_restrict hgammaLagLeft)
      (intervalIntegral.integral_congr_ae_restrict hgammaLagRight)
  have hdact : lRegularizedAction S T delta c d =
      lRegularizedAction G.flow T (g ∘ delta) c w + lRegularizedAction E.incoming.flow T (f ∘ delta) w d := by
    rw [← lRegularizedAction_add S T delta c w d (hintLeft delta hdeltaInt) (hintRight delta hdeltaInt)]
    exact congrArg₂ (fun x y : ℝ => x + y)
      (intervalIntegral.integral_congr_ae_restrict hdeltaLagLeft)
      (intervalIntegral.integral_congr_ae_restrict hdeltaLagRight)
  rw [hgact, hdact]
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

end
