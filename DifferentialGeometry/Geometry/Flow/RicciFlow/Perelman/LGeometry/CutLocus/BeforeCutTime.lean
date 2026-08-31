import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MinimizerC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.NegativeDirection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.PiecewiseNonnegativity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] [CompactSpace M] in
private theorem lVelocity_eq_of_eqOn
    {alpha beta : Real -> M} {s : Real} {A : Set Real}
    (hA : UniqueMDiffWithinAt (modelWithCornersSelf Real Real) A s)
    (halpha : MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s)
    (hbeta : MDifferentiableAt (modelWithCornersSelf Real Real) I beta s)
    (heq : EqOn alpha beta A) (hs : s ∈ A) :
    lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
  have hder := mfderivWithin_congr_of_mem
    (I := modelWithCornersSelf Real Real) (I' := I) heq hs
  rw [mfderivWithin_eq_mfderiv hA halpha,
    mfderivWithin_eq_mfderiv hA hbeta] at hder
  unfold lVelocity
  rw [hder]
  rfl

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem lRegLag_int_of_eqOn
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real)
    (alpha beta : Real -> M)
    (heq : EqOn alpha beta (uIoo a b))
    (hbeta : IntervalIntegrable (lRegLagrangian S T beta) volume a b) :
    IntervalIntegrable (lRegLagrangian S T alpha) volume a b := by
  apply hbeta.congr_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [MeasureTheory.Measure.ae_ne MeasureTheory.volume (max a b)]
    with s hsmax
  intro hs
  have hsIoo : s ∈ Ioo (min a b) (max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hev : Filter.EventuallyEq (nhds s) alpha beta := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact heq (by simpa only [uIoo] using hr)
  have hval : alpha s = beta s := hev.self_of_nhds
  have hmf :
      mfderiv (modelWithCornersSelf Real Real) I alpha s =
        mfderiv (modelWithCornersSelf Real Real) I beta s :=
    hev.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)
  have hvel : lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
    unfold lVelocity
    rw [hmf]
    rfl
  simp only [lRegLagrangian]
  rw [hval, hvel]

theorem lMinVec_unique_lt
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) {Z W : TangentSpace I x} {sigma tau : Real}
    (hZ : (Z, tau) ∈ lMinDomain S T x)
    (hsigma : 0 < sigma) (hlt : sigma < tau)
    (hW : (W, sigma) ∈ lMinDomain S T x)
    (hend : lExp S T x W sigma = lExp S T x Z sigma) :
    W = Z := by
  classical
  have hZsigma : (Z, sigma) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hZ hsigma hlt.le
  have hZvec := (mem_lMinDomain S T x Z tau).1 hZ
  have hZsigvec := (mem_lMinDomain S T x Z sigma).1 hZsigma
  have hWvec := (mem_lMinDomain S T x W sigma).1 hW
  rcases (mem_lExpPosDom S T x Z tau).1 hZvec.1 with
    ⟨htau, _htau0, hbDom⟩
  rcases (mem_lExpPosDom S T x Z sigma).1 hZsigvec.1 with
    ⟨_hsigmaZ, _hsigmaZ0, hcZDom⟩
  rcases (mem_lExpPosDom S T x W sigma).1 hWvec.1 with
    ⟨_hsigmaW, _hsigmaW0, hcWDom⟩
  let c : Real := Real.sqrt sigma
  let b : Real := Real.sqrt tau
  let gammaW : Real -> M := lRegCurve S T x W
  let gammaZ : Real -> M := lRegCurve S T x Z
  have hc0 : 0 < c := by simpa only [c] using Real.sqrt_pos.2 hsigma
  have hcb : c < b := by
    simpa only [c, b] using Real.sqrt_lt_sqrt hsigma.le hlt
  have hWc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaW
      (Icc (0 : Real) c) := by
    simpa only [gammaW, c] using lRegCurve_c1On S hS T x W hcWDom
  have hZc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaZ
      (Icc (0 : Real) b) := by
    simpa only [gammaZ, b] using lRegCurve_c1On S hS T x Z hbDom
  have hZtail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gammaZ
      (Icc c b) := hZc1.mono (by intro s hs; exact ⟨hc0.le.trans hs.1, hs.2⟩)
  have hnode : gammaW c = gammaZ c := by
    simpa only [gammaW, gammaZ, c, lExp, squareRootReparametrization] using hend
  let prW : Real -> Real := fun s =>
    ((projIcc (0 : Real) c hc0.le s : Icc (0 : Real) c) : Real)
  let prZ : Real -> Real := fun s =>
    ((projIcc c b hcb.le s : Icc c b) : Real)
  let left : Real -> M := fun s => gammaW (prW s)
  let right : Real -> M := fun s => gammaZ (prZ s)
  let gamma : Real -> M := Set.piecewise (Iic c) left right
  have hprWmem (s : Real) : prW s ∈ Icc (0 : Real) c :=
    (projIcc (0 : Real) c hc0.le s).property
  have hprZmem (s : Real) : prZ s ∈ Icc c b :=
    (projIcc c b hcb.le s).property
  have hleft : Continuous left := by
    exact hWc1.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) hprWmem
  have hright : Continuous right := by
    exact hZtail.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_projIcc) hprZmem
  have hleftc : left c = gammaW c := by
    have hmem : c ∈ Icc (0 : Real) c := ⟨hc0.le, le_rfl⟩
    simpa only [left, prW] using congrArg gammaW
      (congrArg Subtype.val (projIcc_of_mem hc0.le hmem))
  have hrightc : right c = gammaZ c := by
    have hmem : c ∈ Icc c b := ⟨le_rfl, hcb.le⟩
    simpa only [right, prZ] using congrArg gammaZ
      (congrArg Subtype.val (projIcc_of_mem hcb.le hmem))
  have hgammaCont : Continuous gamma := by
    apply hleft.piecewise (s := Iic c)
    · intro s hs
      have hs' : s = c := by
        rw [frontier_Iic] at hs
        exact Set.mem_singleton_iff.mp hs
      subst s
      exact hleftc.trans (hnode.trans hrightc.symm)
    · exact hright
  have hgammaW : EqOn gamma gammaW (Icc (0 : Real) c) := by
    intro s hs
    change Set.piecewise (Iic c) left right s = gammaW s
    rw [(Iic c).piecewise_eq_of_mem left right (mem_Iic.mpr hs.2)]
    have hpr : prW s = s := by
      simpa only [prW] using congrArg Subtype.val (projIcc_of_mem hc0.le hs)
    simp only [left, hpr]
  have hgammaZ : EqOn gamma gammaZ (Icc c b) := by
    intro s hs
    by_cases hsc : s = c
    · subst s
      exact (hgammaW ⟨hc0.le, le_rfl⟩).trans hnode
    · change Set.piecewise (Iic c) left right s = gammaZ s
      rw [(Iic c).piecewise_eq_of_notMem left right]
      · have hpr : prZ s = s := by
          simpa only [prZ] using congrArg Subtype.val
            (projIcc_of_mem hcb.le hs)
        simp only [right, hpr]
      · rw [mem_Iic]
        exact not_le.mpr (lt_of_le_of_ne hs.1 (Ne.symm hsc))
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    simpa only [b] using lExpPosDom_reg S T x Z hZvec.1 hs
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hWint := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T 0 c hc0.le gammaW hWc1
    (fun s hs => lExpPosDom_reg S T x W hWvec.1 (by simpa only [c] using hs))
  have hZint0 := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T 0 c hc0.le gammaZ
    (hZc1.mono (by intro s hs; exact ⟨hs.1, hs.2.trans hcb.le⟩))
    (fun s hs => hreg s ⟨hs.1, hs.2.trans hcb.le⟩)
  have hZint1 := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hMet hSc T c b hcb.le gammaZ hZtail
    (fun s hs => hreg s ⟨hc0.le.trans hs.1, hs.2⟩)
  have hgammaInt0 : IntervalIntegrable (lRegLagrangian S T gamma) volume 0 c :=
    lRegLag_int_of_eqOn S T 0 c gamma gammaW
      (fun s hs => hgammaW (by
        have hs' : s ∈ Ioo (0 : Real) c := by
          simpa only [uIoo_of_le hc0.le] using hs
        exact ⟨hs'.1.le, hs'.2.le⟩)) hWint
  have hgammaInt1 : IntervalIntegrable (lRegLagrangian S T gamma) volume c b :=
    lRegLag_int_of_eqOn S T c b gamma gammaZ
      (fun s hs => hgammaZ (by
        have hs' : s ∈ Ioo c b := by
          simpa only [uIoo_of_le hcb.le] using hs
        exact ⟨hs'.1.le, hs'.2.le⟩)) hZint1
  have hprefix : lRegAction S T gammaW 0 c = lRegAction S T gammaZ 0 c := by
    calc
      lRegAction S T gammaW 0 c =
          lLength S T (fun r : Real => lExp S T x W r) 0 sigma := by
        change _ = lLength S T
          (fun r : Real ↦ lRegCurve S T x W (Real.sqrt r)) 0 sigma
        rw [show (fun r : Real ↦ lRegCurve S T x W (Real.sqrt r)) =
          squareRootReparametrization gammaW by rfl]
        exact (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T gammaW sigma hsigma.le).symm
      _ = lCost S T x (lExp S T x W sigma) sigma := hWvec.2
      _ = lCost S T x (lExp S T x Z sigma) sigma := by rw [hend]
      _ = lLength S T (fun r : Real => lExp S T x Z r) 0 sigma := hZsigvec.2.symm
      _ = lRegAction S T gammaZ 0 c := by
        change lLength S T
          (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 sigma = _
        rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
          squareRootReparametrization gammaZ by rfl]
        exact lLength_squareRootReparametrization_eq_lRegAction (I := I) S T gammaZ sigma hsigma.le
  have haction : lRegAction S T gamma 0 b = lRegAction S T gammaZ 0 b := by
    rw [← lRegAction_add S T gamma 0 c b hgammaInt0 hgammaInt1,
      lRegAction_congr S T gamma gammaW 0 c (fun s hs => hgammaW (by
        have hs' : s ∈ Ioo (0 : Real) c := by
          simpa only [uIoo_of_le hc0.le] using hs
        exact ⟨hs'.1.le, hs'.2.le⟩)),
      lRegAction_congr S T gamma gammaZ c b (fun s hs => hgammaZ (by
        have hs' : s ∈ Ioo c b := by
          simpa only [uIoo_of_le hcb.le] using hs
        exact ⟨hs'.1.le, hs'.2.le⟩)),
      hprefix, lRegAction_add S T gammaZ 0 c b hZint0 hZint1]
  have hcost : lRegAction S T gammaZ 0 b =
      lRegCostC1 S T 0 b x (gammaZ b) := by
    calc
      lRegAction S T gammaZ 0 b =
          lLength S T (fun r : Real => lExp S T x Z r) 0 tau := by
        change _ = lLength S T
          (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 tau
        rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
          squareRootReparametrization gammaZ by rfl]
        exact (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T gammaZ tau htau.le).symm
      _ = lCost S T x (lExp S T x Z tau) tau := hZvec.2
      _ = lRegCostC1 S T 0 b x (gammaZ b) := by
        simpa only [gammaZ, b, lExp, squareRootReparametrization] using
          lCost_eq_reg (I := I) S T x (lExp S T x Z tau) tau htau.le
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - tau) T := by
    intro s hs
    have hsSq : s ^ 2 ≤ tau := by
      calc
        s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 (by simpa only [b] using Real.sqrt_nonneg tau)).2 hs.2
        _ = tau := by simpa only [b] using Real.sq_sqrt htau.le
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have htime : Icc (T - tau) T ⊆ D.carrier := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by linarith [hr.2]
    have hleTau : T - r ≤ tau := by linarith [hr.1]
    have hsqrtMem : Real.sqrt (T - r) ∈ Icc (0 : Real) b :=
      ⟨Real.sqrt_nonneg _, by simpa only [b] using Real.sqrt_le_sqrt hleTau⟩
    have hregR := hreg _ hsqrtMem
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    exact D.regular_subset (by simpa only [heq] using hregR)
  have hmin : ∀ delta : Real -> M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta ->
      delta 0 = gamma 0 -> delta b = gamma b ->
      lRegAction S T gamma 0 b ≤ lRegAction S T delta 0 b := by
    intro delta hdelta hd0 hdb
    rw [haction, hcost]
    apply lRegCostC1_le (I := I) S hS T (T - tau) T 0 b (hc0.trans hcb).le
      htime hback x (gammaZ b) delta hdelta
    · exact hd0.trans ((hgammaW ⟨le_rfl, hc0.le⟩).trans
        (by simp only [gammaW, lRegCurve_zero]))
    · exact hdb.trans (hgammaZ ⟨hcb.le, le_rfl⟩)
    · exact hreg
  obtain ⟨eta, m, t, p, v, hetaW, hetaZ, htmono, ht0, htlast, _hcnode,
      hsrc, hrep⟩ := exists_chartH1_join (I := I) 0 c b hc0 hcb gammaW gammaZ
        hWc1 hZtail hnode
  have hetaGamma : EqOn eta gamma (Icc (0 : Real) b) := by
    intro s hs
    rcases le_total s c with hsc | hcs
    · exact (hetaW ⟨hs.1, hsc⟩).trans (hgammaW ⟨hs.1, hsc⟩).symm
    · exact (hetaZ ⟨hcs, hs.2⟩).trans (hgammaZ ⟨hcs, hs.2⟩).symm
  have htmem (i : Fin (m + 1)) : t i ∈ Icc (0 : Real) b := by
    exact ⟨by simpa only [ht0] using htmono (Fin.zero_le i),
      by simpa only [htlast] using htmono (Fin.le_last i)⟩
  have hsegmem (i : Fin m) (s : Real)
      (hs : s ∈ Icc (t i.castSucc) (t i.succ)) : s ∈ Icc (0 : Real) b :=
    ⟨(htmem i.castSucc).1.trans hs.1, hs.2.trans (htmem i.succ).2⟩
  have hsrcGamma : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source := by
    intro i s hs
    rw [← hetaGamma (hsegmem i s hs)]
    exact hsrc i hs
  have hrepGamma : ∀ i, EqOn (v i).toFun
      (fun r => extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro i r hr
    rw [hrep i hr]
    apply congrArg (fun y => extChartAt I (p i) y)
    apply hetaGamma
    have hstart := htmem i.castSucc
    have hendseg := htmem i.succ
    simp only [partitionIntervalLength] at hr
    exact ⟨by linarith [hstart.1, hr.1], by linarith [hendseg.2, hr.2]⟩
  have hgammaC1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc (0 : Real) b) :=
    lMinCurve_c1 (I := I) S hS T 0 b (hc0.trans hcb) t htmono ht0 htlast p
      gamma hgammaCont v hsrcGamma hrepGamma hreg hmin
  have hgammaDiff : MDifferentiableAt (modelWithCornersSelf Real Real) I gamma c :=
    (hgammaC1.contMDiffAt (Icc_mem_nhds hc0 hcb)).mdifferentiableAt (by norm_num)
  have hWDiff : MDifferentiableAt (modelWithCornersSelf Real Real) I gammaW c := by
    have hpair : ContMDiffAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real)) ∞
        ((fun r : Real => (W, r)) : Real -> E × Real) c :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ((lRegCurve_smooth S hS T x hcWDom).comp c hpair).mdifferentiableAt
      (by norm_num)
  have hZDiff : MDifferentiableAt (modelWithCornersSelf Real Real) I gammaZ c := by
    have hpair : ContMDiffAt (modelWithCornersSelf Real Real)
        ((modelWithCornersSelf Real E).prod (modelWithCornersSelf Real Real)) ∞
        ((fun r : Real => (Z, r)) : Real -> E × Real) c :=
      (contMDiff_const.prodMk contMDiff_id).contMDiffAt
    exact ((lRegCurve_smooth S hS T x hcZDom).comp c hpair).mdifferentiableAt
      (by norm_num)
  have hvelW : lVelocity (I := I) gammaW c = lVelocity (I := I) gamma c := by
    apply lVelocity_eq_of_eqOn
      ((uniqueDiffOn_Icc hc0) c ⟨hc0.le, le_rfl⟩).uniqueMDiffWithinAt
      hWDiff hgammaDiff
    · exact fun s hs => (hgammaW hs).symm
    · exact ⟨hc0.le, le_rfl⟩
  have hvelZ : lVelocity (I := I) gamma c = lVelocity (I := I) gammaZ c := by
    apply lVelocity_eq_of_eqOn
      ((uniqueDiffOn_Icc hcb) c ⟨le_rfl, hcb.le⟩).uniqueMDiffWithinAt
      hgammaDiff hZDiff
    · exact hgammaZ
    · exact ⟨le_rfl, hcb.le⟩
  have hnodeVel : lVelocity (I := I) gammaW c = lVelocity (I := I) gammaZ c :=
    hvelW.trans hvelZ
  obtain ⟨JW, hJWopen, hJWconn, h0JW, hcJW, hchosenW⟩ :=
    lRegChosen_spec S T x W hcWDom
  obtain ⟨JZ, hJZopen, hJZconn, h0JZ, hcJZ, hchosenZ⟩ :=
    lRegChosen_spec S T x Z hcZDom
  let alphaW := lRegChosen S T x W hcWDom
  let alphaZ := lRegChosen S T x Z hcZDom
  have heqW := lRegCurve_eqOn S hS T hJWopen hJWconn h0JW hchosenW
  have heqZ := lRegCurve_eqOn S hS T hJZopen hJZconn h0JZ hchosenZ
  have hWgerm : Filter.EventuallyEq (nhds c) gammaW alphaW := by
    filter_upwards [hJWopen.mem_nhds hcJW] with r hr
    exact heqW hr
  have hZgerm : Filter.EventuallyEq (nhds c) gammaZ alphaZ := by
    filter_upwards [hJZopen.mem_nhds hcJZ] with r hr
    exact heqZ hr
  have hposChosen : alphaW c = alphaZ c := by
    exact hWgerm.eq_of_nhds.symm.trans (hnode.trans hZgerm.eq_of_nhds)
  have hvelChosen : lVelocity (I := I) alphaW c = lVelocity (I := I) alphaZ c := by
    unfold lVelocity
    rw [← hWgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I),
      ← hZgerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
    exact hnodeVel
  have hsolEq := lRegSol_eqOn S hS T hJWopen hJWconn hcJW hJZopen hJZconn hcJZ
    hchosenW.2.2 hchosenZ.2.2 hposChosen hvelChosen
  have heq0 : Filter.EventuallyEq (nhds (0 : Real)) alphaW alphaZ := by
    filter_upwards [(hJWopen.inter hJZopen).mem_nhds ⟨h0JW, h0JZ⟩] with r hr
    exact hsolEq hr
  have hvel0 : lVelocity (I := I) alphaW 0 = lVelocity (I := I) alphaZ 0 := by
    unfold lVelocity
    rw [heq0.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
    rfl
  have hW2 : lVelocity (I := I) alphaW 0 = (2 : Real) • W :=
    hchosenW.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 W).symm
  have hZ2 : lVelocity (I := I) alphaZ 0 = (2 : Real) • Z :=
    hchosenZ.2.1.trans (Nat.cast_smul_eq_nsmul Real 2 Z).symm
  apply smul_right_injective (TangentSpace I x) (by norm_num : (2 : Real) ≠ 0)
  exact hW2.symm.trans (hvel0.trans hZ2)

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinVec_nconj_lt
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {sigma tau : Real}
    (hmin : (Z, tau) ∈ lMinDomain S T x)
    (hlt : sigma < tau) : ¬ IsLConj S T x Z sigma := by
  intro hconj
  have htau : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hmin).1
  have hsdom : (Z, sigma) ∈ lExpPosDom S T x :=
    ((isLConj_iff_jac (I := I) S T x Z sigma).1 hconj).1
  have hspos : 0 < sigma :=
    ((mem_lExpPosDom (I := I) S T x Z sigma).1 hsdom).1
  have hc0 : 0 < Real.sqrt sigma := Real.sqrt_pos.2 hspos
  have hcb : Real.sqrt sigma < Real.sqrt tau :=
    Real.sqrt_lt_sqrt hspos.le hlt
  obtain ⟨gamma, Y0, Y1, hEq, hgeo, hY0, hY1,
      hY0zero, hY1zero, hnode, hneg⟩ :=
    exists_lRegIndex_split_lt_zero_of_isLConj (I := I) S hS T x Z htau hlt hconj
  have hminGamma : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta 0 = gamma 0 →
      delta (Real.sqrt tau) = gamma (Real.sqrt tau) →
      lRegAction S T gamma 0 (Real.sqrt tau) ≤
        lRegAction S T delta 0 (Real.sqrt tau) := by
    intro delta hdelta hd0 hdt
    have hEq0 : gamma 0 = lRegCurve S T x Z 0 :=
      hEq ⟨le_rfl, Real.sqrt_nonneg tau⟩
    have hEqT : gamma (Real.sqrt tau) =
        lRegCurve S T x Z (Real.sqrt tau) :=
      hEq ⟨Real.sqrt_nonneg tau, le_rfl⟩
    have hraw := lMinVec_reg_min (I := I) S hS T x hmin delta hdelta
      (hd0.trans hEq0) (hdt.trans hEqT)
    have haction : lRegAction S T gamma 0 (Real.sqrt tau) =
        lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Set.Ioo (0 : Real) (Real.sqrt tau) := by
        simpa only [Set.uIoo_of_le (Real.sqrt_nonneg tau)] using hs
      exact hEq ⟨hs'.1.le, hs'.2.le⟩
    rw [haction]
    exact hraw
  have hnonneg := lRegIndex_piecewise_nonneg (I := I) S hS T gamma
    0 (Real.sqrt sigma) (Real.sqrt tau) hc0 hcb x Z hgeo hminGamma
    Y0 Y1 hY0 hY1 hY0zero hY1zero hnode
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
