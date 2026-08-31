import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.ChartRamp
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.ChartPartition.TwoPieceSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.NoAdmissibleCurve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.MinimizerBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Defs

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval NNReal

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

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
theorem lCost_le_join_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : Real) (hb : 0 < b) (x y : M) {c : Real}
    (hc : 0 < c) (hcb : c < b)
    (hbdd : BddBelow {r : Real | ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = y ∧ lRegAction S T gamma 0 b = r})
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (alpha beta : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha
      (Icc (0 : Real) c))
    (hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b))
    (hnode : alpha c = beta c) (hstart : alpha 0 = x)
    (hend : beta b = y) :
    lCost S T x y (b ^ 2) ≤
      lRegAction S T alpha 0 c + lRegAction S T beta c b := by
  obtain ⟨eta, m, t, p, w, heta0, heta1, htmono, ht0, htlast,
      _hcnode, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) 0 c b hc hcb alpha beta
      halpha hbeta hnode
  obtain ⟨delta, _u, hdelta, hdelta0, hdeltab, _hsrcDelta, _hrepDelta,
      _hu, _hunif, hdeltaAct⟩ :=
    lAction_c1_dense (I := I) S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b t htmono ht0 htlast p eta w hsrc hrep hreg
  have hreg0c : ∀ s ∈ Icc (0 : Real) c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregcb : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hc.le.trans hs.1, hs.2⟩
  have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (Icc (0 : Real) c) := halpha.congr fun s hs ↦ heta0 hs
  have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (Icc c b) := hbeta.congr fun s hs ↦ heta1 hs
  have hetaHeadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T 0 c hc.le eta hetaHead hreg0c
  have hetaTailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T c b hcb.le eta hetaTail hregcb
  have hetaAdd := lRegAction_add (I := I) S T eta 0 c b
    hetaHeadInt hetaTailInt
  have hetaHeadAct : lRegAction S T eta 0 c =
      lRegAction S T alpha 0 c :=
    lRegAction_congr (I := I) S T eta alpha 0 c (by
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) c := by
        simpa only [uIoo_of_le hc.le] using hs
      exact heta0 ⟨hs'.1.le, hs'.2.le⟩)
  have hetaTailAct : lRegAction S T eta c b =
      lRegAction S T beta c b :=
    lRegAction_congr (I := I) S T eta beta c b (by
      intro s hs
      have hs' : s ∈ Ioo c b := by
        simpa only [uIoo_of_le hcb.le] using hs
      exact heta1 ⟨hs'.1.le, hs'.2.le⟩)
  have hetaAct : lRegAction S T eta 0 b =
      lRegAction S T alpha 0 c + lRegAction S T beta c b := by
    rw [← hetaAdd, hetaHeadAct, hetaTailAct]
  rw [← hetaAct]
  have hcostDelta : ∀ n, lCost S T x y (b ^ 2) ≤
      lRegAction S T (delta n) 0 b := by
    intro n
    rw [lCost_eq_reg (I := I) S T x y (b ^ 2) (sq_nonneg b),
      Real.sqrt_sq_eq_abs, abs_of_pos hb]
    apply lRegCostC1_le_bdd (I := I) S T 0 b x y hbdd
      (delta n) (hdelta n)
    · exact (hdelta0 n).trans ((heta0 ⟨le_rfl, hc.le⟩).trans hstart)
    · exact (hdeltab n).trans ((heta1 ⟨hcb.le, le_rfl⟩).trans hend)
  have hneg : Tendsto (fun n ↦ -lRegAction S T (delta n) 0 b) atTop
      (nhds (-lRegAction S T eta 0 b)) :=
    continuousAt_neg.tendsto.comp hdeltaAct
  have hlim := le_of_tendsto' hneg fun n ↦ neg_le_neg (hcostDelta n)
  linarith

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_le_ray_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hb : b ∈ lRegDomain S T x Z)
    (hbdd : BddBelow {r : Real | ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = lRegCurve S T x Z b ∧
        lRegAction S T gamma 0 b = r}) :
    lCost S T x (lRegCurve S T x Z b) (b ^ 2) ≤
      lRegAction S T (lRegCurve S T x Z) 0 b := by
  obtain ⟨rho, hrho, hrho_id, _hrho_deriv, hrho_range⟩ :=
    exists_lReg_clamp S T x Z hb0 hb
  let z : E := Z
  let gamma : Real → M := fun s ↦ lRegCurve S T x Z (rho s)
  have hrhoM : ContMDiff (modelWithCornersSelf Real Real)
      (modelWithCornersSelf Real Real) ∞ rho :=
    contMDiff_iff_contDiff.mpr hrho
  have hpair : ContMDiff (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real E).prod
        (modelWithCornersSelf Real Real)) ∞
      (fun s : Real ↦ (z, rho s)) :=
    contMDiff_const.prodMk hrhoM
  have hgammaInf : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    rw [← contMDiffOn_univ]
    change ContMDiffOn (modelWithCornersSelf Real Real) I ∞
      ((fun q : E × Real ↦ lRegCurve S T x q.1 q.2) ∘
        fun s : Real ↦ (z, rho s)) Set.univ
    exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
      (fun s _hs ↦ by
        change rho s ∈ lRegDomain S T x Z
        exact hrho_range s)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I 1 gamma :=
    hgammaInf.of_le (by norm_num)
  have heq : Set.EqOn gamma (lRegCurve S T x Z) (Icc (0 : Real) b) := by
    intro s hs
    exact congrArg (lRegCurve S T x Z) (hrho_id hs)
  have hact : lRegAction S T gamma 0 b =
      lRegAction S T (lRegCurve S T x Z) 0 b := by
    apply lRegAction_congr (I := I) S T gamma (lRegCurve S T x Z) 0 b
    intro s hs
    apply heq
    have hs' : s ∈ Ioo (0 : Real) b := by
      simpa only [uIoo_of_le hb0.le] using hs
    exact ⟨hs'.1.le, hs'.2.le⟩
  have hrho0 : rho 0 = 0 := by
    simpa only [id_eq] using hrho_id ⟨le_rfl, hb0.le⟩
  have hrhob : rho b = b := by
    simpa only [id_eq] using hrho_id ⟨hb0.le, le_rfl⟩
  rw [lCost_eq_reg (I := I) S T x (lRegCurve S T x Z b)
      (b ^ 2) (sq_nonneg b), Real.sqrt_sq_eq_abs, abs_of_pos hb0]
  calc
    lRegCostC1 S T 0 b x (lRegCurve S T x Z b) ≤
        lRegAction S T gamma 0 b :=
      lRegCostC1_le_bdd (I := I) S T 0 b x (lRegCurve S T x Z b)
        hbdd gamma hgamma
        (by simp only [gamma, hrho0, lRegCurve_zero])
        (by simp only [gamma, hrhob])
    _ = lRegAction S T (lRegCurve S T x Z) 0 b := hact

omit [NeZero (Module.finrank Real E)] in
theorem lCost_le_join
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T b : Real) (hb : 0 < b) (x y : M) {c : Real}
    (hc : 0 < c) (hcb : c < b)
    (htime : Icc (T - b ^ 2) T ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (alpha beta : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha
      (Icc (0 : Real) c))
    (hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b))
    (hnode : alpha c = beta c) (hstart : alpha 0 = x)
    (hend : beta b = y) :
    lCost S T x y (b ^ 2) ≤
      lRegAction S T alpha 0 c + lRegAction S T beta c b := by
  have hbdd : BddBelow {r : Real | ∃ gamma : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 gamma ∧
        gamma 0 = x ∧ gamma b = y ∧ lRegAction S T gamma 0 b = r} := by
    refine ⟨lRegCostC1 S T 0 b x y, ?_⟩
    intro r hr
    obtain ⟨gamma, hgamma, hgamma0, hgammab, rfl⟩ := hr
    exact lRegCostC1_le (I := I) S hS T (T - b ^ 2) T 0 b hb.le
      htime hback x y gamma hgamma hgamma0 hgammab hreg
  exact lCost_le_join_bdd (I := I) S hS T b hb x y hc hcb hbdd hreg
    alpha beta halpha hbeta hnode hstart hend

theorem lMinVec_local_bdd
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (Z : TangentSpace I x) (b : Real)
    (hb0 : 0 < b) (hZmin : (Z, b ^ 2) ∈ lMinDomain S T x)
    (p : M) {q0 : E} (hq0 : q0 ∈ (extChartAt I p).target)
    (hZend : lExp S T x Z (b ^ 2) = (extChartAt I p).symm q0) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ q ∈ Metric.ball q0 ε,
      ∀ W : TangentSpace I x, (W, b ^ 2) ∈ lMinDomain S T x →
        lExp S T x W (b ^ 2) = (extChartAt I p).symm q → ‖(W : E)‖ ≤ C := by
  obtain ⟨ρ, hρ, hρtar⟩ := Metric.isOpen_iff.1
    (isOpen_extChartAt_target (I := I) p) q0 hq0
  by_contra h
  push Not at h
  let εn : Nat → Real := fun n ↦ min (ρ / 2) (1 / (n + 1 : Real))
  have hεn (n : Nat) : 0 < εn n := by
    exact lt_min (half_pos hρ) (one_div_pos.mpr (by positivity))
  choose q hq W hWmin hWend hWnorm using
    fun n : Nat ↦ h (εn n) (hεn n) (n : Real) (Nat.cast_nonneg n)
  have hqtar (n : Nat) : q n ∈ (extChartAt I p).target := by
    apply hρtar
    apply Metric.ball_subset_ball (le_trans (min_le_left _ _)
      (half_le_self hρ.le))
    exact hq n
  have hqLim : Tendsto q atTop (nhds q0) := by
    rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
    refine ⟨N, ?_⟩
    intro n hn
    have hnpos : 0 < (n + 1 : Real) := by positivity
    have hfrac : 1 / (n + 1 : Real) < δ := by
      apply (one_div_lt hnpos hδ).2
      exact lt_of_lt_of_le hN (by
        exact_mod_cast Nat.le_trans hn (Nat.le_add_right n 1))
    exact (hq n).trans (lt_of_le_of_lt (min_le_right _ _) hfrac)
  have hsymm : Tendsto (fun n ↦ (extChartAt I p).symm (q n)) atTop
      (nhds ((extChartAt I p).symm q0)) := by
    exact ((continuousOn_extChartAt_symm (I := I) p).continuousAt
      ((isOpen_extChartAt_target (I := I) p).mem_nhds hq0)).tendsto.comp hqLim
  have hEnd : Tendsto (fun n ↦ lExp S T x (W n) (b ^ 2)) atTop
      (nhds (lRegCurve S T x Z b)) := by
    have hcenter : (extChartAt I p).symm q0 = lRegCurve S T x Z b := by
      rw [← hZend]
      simp only [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb0]
    rw [← hcenter]
    exact hsymm.congr' (Eventually.of_forall fun n ↦ (hWend n).symm)
  have hZdom : b ∈ lRegDomain S T x Z := by
    have hdom := (((mem_lExpPosDom S T x Z (b ^ 2)).1
      ((mem_lMinDomain S T x Z (b ^ 2)).1 hZmin).1).2).2
    simpa only [lExpDomain, Real.sqrt_sq_eq_abs, abs_of_pos hb0] using hdom
  have hBdd : Bornology.IsBounded (range W) :=
    lMinVec_end_bdd (I := I) S hS T x Z b hb0 hZdom W hWmin hEnd
  obtain ⟨C, hC⟩ := hBdd.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hupper : ‖(W n : E)‖ ≤ C := hC (W n) ⟨n, rfl⟩
  linarith [hWnorm n]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayChart_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x p : M) {K : Set E} {a b : Real}
    (hKcpt : IsCompact K)
    (hdom : K ×ˢ Icc a b ⊆ lRegJointDom S T x)
    (hsrc : MapsTo (fun q : E × Real ↦ lRegCurve S T x q.1 q.2)
      (K ×ˢ Icc a b) (extChartAt I p).source) :
    ∃ V : Real, 0 ≤ V ∧ ∀ Z ∈ K, ∀ c ∈ Icc a b,
      ‖(extChartAt I p) (lRegCurve S T x Z b) -
          (extChartAt I p) (lRegCurve S T x Z c)‖ ≤ V * (b - c) := by
  let Q : Set (E × Real) := K ×ˢ Icc a b
  let F : E × Real → M := fun q ↦ lRegCurve S T x q.1 q.2
  let G : E × Real → E := fun q ↦ (extChartAt I p) (F q)
  let U : Set (E × Real) := lRegJointDom S T x ∩ F ⁻¹' (chartAt H p).source
  have hFall : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ F
      (lRegJointDom S T x) := lRegCurve_smoothOn S hS T x
  have hUopen : IsOpen U := hFall.continuousOn.isOpen_inter_preimage
    (lRegJointDom_open S hS T x) (chartAt H p).open_source
  have hGm : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real))
      𝓘(Real, E) 1 G U := by
    exact (contMDiffOn_extChartAt (I := I) (n := 1) (x := p)).comp
      ((hFall.of_le (by norm_num)).mono inter_subset_left) inter_subset_right
  have hG : ContDiffOn Real 1 G U := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hGm
  have hGloc : LocallyLipschitzOn U G := by
    intro q hq
    obtain ⟨C, V, hV, hCV⟩ :=
      ((hG q hq).contDiffAt (hUopen.mem_nhds hq)).exists_lipschitzOnWith
    exact ⟨C, V, mem_nhdsWithin_of_mem_nhds hV, hCV⟩
  have hQcpt : IsCompact Q := hKcpt.prod isCompact_Icc
  have hQU : Q ⊆ U := fun q hq ↦ ⟨hdom hq, by
    change lRegCurve S T x q.1 q.2 ∈ (chartAt H p).source
    rw [← extChartAt_source (I := I) (H := H) p]
    exact hsrc hq⟩
  obtain ⟨V, hV⟩ :=
    (hGloc.mono hQU).exists_lipschitzOnWith_of_compact hQcpt
  refine ⟨(V : Real), V.coe_nonneg, ?_⟩
  intro Z hZ c hc
  have hbc : c ≤ b := hc.2
  have hcb := hV.dist_le_mul (Z, b) ⟨hZ, ⟨hc.1.trans hbc, le_rfl⟩⟩
    (Z, c) ⟨hZ, hc⟩
  have hpairNorm : ‖((Z, b) - (Z, c) : E × Real)‖ = b - c := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
      Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hbc)]
    exact max_eq_right (sub_nonneg.mpr hbc)
  simpa only [G, F, dist_eq_norm, hpairNorm] using hcb

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRayChart_tube
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x p : M) {K : Set E} {b : Real} (hb : 0 < b)
    (hKcpt : IsCompact K)
    (hbdom : ∀ Z ∈ K, b ∈ lRegDomain S T x Z)
    (hbchart : ∀ Z ∈ K, lRegCurve S T x Z b ∈ (chartAt H p).source) :
    ∃ δ > 0, δ ≤ b ∧ ∀ Z ∈ K, ∀ s ∈ Icc (b - δ) b,
      s ∈ lRegDomain S T x Z ∧
        lRegCurve S T x Z s ∈ (chartAt H p).source := by
  let F : E × Real → M := fun q ↦ lRegCurve S T x q.1 q.2
  let U : Set (E × Real) := lRegJointDom S T x ∩ F ⁻¹' (chartAt H p).source
  have hFall : ContMDiffOn (𝓘(Real, E).prod 𝓘(Real, Real)) I ∞ F
      (lRegJointDom S T x) := lRegCurve_smoothOn S hS T x
  have hUopen : IsOpen U := hFall.continuousOn.isOpen_inter_preimage
    (lRegJointDom_open S hS T x) (chartAt H p).open_source
  have hev : ∀ᶠ s in nhds b, ∀ Z ∈ K, (Z, s) ∈ U := by
    apply hKcpt.eventually_forall_of_forall_eventually
    intro Z hZ
    have hmem : (Z, b) ∈ U := ⟨by
      change b ∈ lRegDomain S T x Z
      exact hbdom Z hZ, hbchart Z hZ⟩
    exact (continuous_snd.prodMk continuous_fst).continuousAt.eventually
      (hUopen.mem_nhds hmem)
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.1 hev
  let δ : Real := min (r / 2) (b / 2)
  have hδ : 0 < δ := lt_min (half_pos hr) (half_pos hb)
  refine ⟨δ, hδ, (min_le_right _ _).trans (half_le_self hb.le), ?_⟩
  intro Z hZ s hs
  have hsball : s ∈ Metric.ball b r := by
    change dist s b < r
    have hdist : dist s b = b - s := by
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
      ring
    rw [hdist]
    exact (sub_lt_iff_lt_add.mpr (by
      linarith [hs.1, min_le_left (r / 2) (b / 2), half_lt_self hr])).trans_le le_rfl
  have hmem := hrsub hsball Z hZ
  exact ⟨by
      exact hmem.1,
    by
      exact hmem.2⟩

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
theorem lRampAct_eq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T a b : Real) (p : M) {y z : E} (hab : a < b)
    (htar : MapsTo (lChartRamp y z (sub_nonneg.mpr hab.le)).toFun
      (Icc (0 : Real) (b - a))
      (extChartAt I p).target)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    lRegAction S T
        (fun s ↦ (extChartAt I p).symm
          ((lChartRamp y z (sub_nonneg.mpr hab.le)).toFun (s - a))) a b =
      lChartAction S T a p (lChartRamp y z (sub_nonneg.mpr hab.le)) := by
  let t : Fin 2 → Real := Fin.cases a (fun _ ↦ b)
  let gamma : Real → M := fun s ↦ (extChartAt I p).symm
    ((lChartRamp y z (sub_nonneg.mpr hab.le)).toFun (s - a))
  let ps : Fin 1 → M := fun _ ↦ p
  let us : (i : Fin 1) → timeH1 E (partitionIntervalLength t i) := fun i ↦ by
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    exact lChartRamp y z (sub_nonneg.mpr hab.le)
  have htmono : Monotone t := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact le_rfl
    · exact hab.le
    · simp at hij
    · exact le_rfl
  have hsrc : ∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
      (chartAt H (ps i)).source := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    intro s hs
    change s ∈ Icc a b at hs
    have hs' : s ∈ Icc a b := hs
    have hr : s - a ∈ Icc (0 : Real) (b - a) := by
      constructor <;> linarith [hs'.1, hs'.2]
    simpa only [gamma, ps, extChartAt_source] using
      (extChartAt I p).map_target (htar hr)
  have hrep : ∀ i, EqOn (us i).toFun
      (fun r ↦ extChartAt I (ps i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    intro r hr
    change r ∈ Icc (0 : Real) (b - a) at hr
    have hrL : r ∈ Icc (0 : Real) (b - a) := hr
    change (lChartRamp y z (sub_nonneg.mpr hab.le)).toFun r =
      extChartAt I p ((extChartAt I p).symm
        ((lChartRamp y z (sub_nonneg.mpr hab.le)).toFun ((a + r) - a)))
    rw [add_sub_cancel_left]
    exact ((extChartAt I p).right_inv (htar hrL)).symm
  have hsum := lRegAction_eq_sum_lChartAction (I := I) S hS.smoothMetric
    ⟨hS.scalarCont⟩ T a b t htmono (by rfl) (by rfl)
    ps gamma us hsrc hrep hreg
  rw [Fin.sum_univ_one] at hsum
  have ht0 : t (Fin.castSucc (0 : Fin 1)) = a := by rfl
  have hp0 : ps (0 : Fin 1) = p := by rfl
  have hu0 : us (0 : Fin 1) =
      lChartRamp y z (sub_nonneg.mpr hab.le) := by rfl
  rw [ht0, hp0, hu0] at hsum
  exact hsum

omit [NeZero (Module.finrank ℝ E)] in
theorem lCost_ramp_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x p : M) {b c : Real} (hc : 0 < c) (hcb : c < b)
    (htime : Icc (T - b ^ 2) T ⊆ D.carrier)
    (hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T)
    (hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular)
    (W : TangentSpace I x) (hbdom : b ∈ lRegDomain S T x W)
    (hrayc : lRegCurve S T x W c ∈ (chartAt H p).source)
    (z : E)
    (htar : MapsTo
      (lChartRamp ((extChartAt I p) (lRegCurve S T x W c)) z
        (sub_nonneg.mpr hcb.le)).toFun (Icc (0 : Real) (b - c))
      (extChartAt I p).target) :
    lCost S T x ((extChartAt I p).symm z) (b ^ 2) ≤
      lRegAction S T (lRegCurve S T x W) 0 c +
        lChartAction S T c p
          (lChartRamp ((extChartAt I p) (lRegCurve S T x W c)) z
            (sub_nonneg.mpr hcb.le)) := by
  let y : E := (extChartAt I p) (lRegCurve S T x W c)
  let u : timeH1 E (b - c) := lChartRamp y z (sub_nonneg.mpr hcb.le)
  let beta : Real → M := fun s ↦
    (extChartAt I p).symm (u.toFun (s - c))
  have hcdom : c ∈ lRegDomain S T x W :=
    lRegDomain_seg S T x W hbdom hc.le hcb.le
  have halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (lRegCurve S T x W) (Icc (0 : Real) c) :=
    lRegCurve_c1On S hS T x W hcdom
  let v : Real → E := fun s ↦ y + ((s - c) / (b - c)) • (z - y)
  have hv : ContDiffOn Real 1 v (Icc c b) := by
    exact (contDiff_const.add
      (((contDiff_id.sub contDiff_const).div_const (b - c)).smul
        contDiff_const)).contDiffOn
  have hvmap : MapsTo v (Icc c b) (extChartAt I p).target := by
    intro s hs
    have hr : s - c ∈ Icc (0 : Real) (b - c) := by
      constructor <;> linarith [hs.1, hs.2]
    have hu := htar hr
    rw [show v s = y + ((s - c) / (b - c)) • (z - y) by rfl,
      ← lRamp_apply (y := y) (z := z) (sub_nonneg.mpr hcb.le) hr]
    exact hu
  have hbeta0 : ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (fun s ↦ (extChartAt I p).symm (v s)) (Icc c b) := by
    apply (contMDiffOn_extChartAt_symm (I := I) (n := 1) p).comp
    · exact contMDiffOn_iff_contDiffOn.mpr hv
    · exact hvmap
  have hbeta : ContMDiffOn (modelWithCornersSelf Real Real) I 1 beta
      (Icc c b) := by
    apply hbeta0.congr
    intro s hs
    have hr : s - c ∈ Icc (0 : Real) (b - c) := by
      constructor <;> linarith [hs.1, hs.2]
    exact congrArg (extChartAt I p).symm
      (lRamp_apply (y := y) (z := z) (sub_nonneg.mpr hcb.le) hr)
  have hnode : lRegCurve S T x W c = beta c := by
    change lRegCurve S T x W c =
      (extChartAt I p).symm (u.toFun (c - c))
    rw [sub_self, show u.toFun 0 = y by
      exact lRamp_start (y := y) (z := z) (sub_nonneg.mpr hcb.le)]
    exact ((extChartAt I p).left_inv (by
      simpa only [extChartAt_source] using hrayc)).symm
  have hend : beta b = (extChartAt I p).symm z := by
    simp only [beta, u, lRamp_end (sub_pos.mpr hcb)]
  have hle := lCost_le_join (I := I) S hS T b (lt_trans hc hcb) x
    ((extChartAt I p).symm z) hc hcb htime hback hreg
    (lRegCurve S T x W) beta halpha hbeta hnode
    (lRegCurve_zero S T x W) hend
  have hact := lRampAct_eq (I := I) S hS T c b p hcb htar
    (fun s hs ↦ hreg s ⟨hc.le.trans hs.1, hs.2⟩)
  rw [hact] at hle
  simpa only [y, u] using hle

theorem lCost_chart_lip
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau)
    (hslab : Icc (T - tau) T ⊆ D.regular) (p : M) :
    LocallyLipschitzOn (extChartAt I p).target
      ((fun y : M ↦ lCost S T x y tau) ∘ (extChartAt I p).symm) := by
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hb2 : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hback : ∀ s ∈ Icc (0 : Real) b,
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    intro s hs
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨by linarith, by nlinarith [sq_nonneg s]⟩
  have hreg : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hslab
    simpa only [hb2] using hback s hs
  have htime : Icc (T - b ^ 2) T ⊆ D.carrier := by
    intro t ht
    apply D.regular_subset
    apply hslab
    simpa only [hb2] using ht
  intro q0 hq0
  by_cases hreach : ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha 0 = x ∧ alpha b = (extChartAt I p).symm q0
  · obtain ⟨alpha, halpha, hstart, hend⟩ := hreach
    obtain ⟨Z0, hZ0min, hZ0end⟩ := exists_lMinVec (I := I) S hS
      T (T - b ^ 2) T (b ^ 2) (sq_pos_of_pos hb) htime (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hback)
      x ((extChartAt I p).symm q0) alpha halpha hstart (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hend) (by
          simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hreg)
    obtain ⟨ε0, hε0, C, hC, hminBdd⟩ :=
      lMinVec_local_bdd (I := I) S hS T x Z0 b hb hZ0min p hq0 (by
        simpa only [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb] using hZ0end)
    obtain ⟨R, hR, hRtar⟩ := Metric.isOpen_iff.1
      (isOpen_extChartAt_target (I := I) p) q0 hq0
    let ρ : Real := min (ε0 / 2) (R / 8)
    have hρ : 0 < ρ := lt_min (half_pos hε0) (by positivity)
    let Q : Set E := Metric.closedBall q0 ρ
    have hQtar : Q ⊆ (extChartAt I p).target := by
      intro q hq
      apply hRtar
      have hρR : ρ < R :=
        (min_le_right (ε0 / 2) (R / 8)).trans_lt (by linarith)
      exact lt_of_le_of_lt hq hρR
    have hQcpt : IsCompact Q := isCompact_closedBall q0 ρ
    let Y : Set M := (extChartAt I p).symm '' Q
    have hYcpt : IsCompact Y :=
      hQcpt.image_of_continuousOn
        ((continuousOn_extChartAt_symm (I := I) p).mono hQtar)
    let endMap : E → M := fun Z ↦ lRegCurve S T x Z b
    have hbdomAll (Z : E) : b ∈ lRegDomain S T x Z :=
      lRegDomain_of_slab S hS T x Z b hb.le (by
        simpa only [hb2] using hslab)
    have hendCont : Continuous endMap := by
      have hpair : ContMDiff 𝓘(Real, E)
          (𝓘(Real, E).prod 𝓘(Real, Real)) ∞
          (fun Z : E ↦ (Z, b)) := contMDiff_id.prodMk contMDiff_const
      have hendMD : ContMDiff 𝓘(Real, E) I ∞ endMap := by
        rw [← contMDiffOn_univ]
        exact (lRegCurve_smoothOn S hS T x).comp hpair.contMDiffOn
          (fun Z _hZ ↦ by
            change b ∈ lRegDomain S T x Z
            exact hbdomAll Z)
      exact hendMD.continuous
    let K : Set E := Metric.closedBall (0 : E) C ∩
      {Z : E | (Z, b ^ 2) ∈ lMinDomain S T x} ∩ endMap ⁻¹' Y
    have hKclosed : IsClosed K := by
      exact (Metric.isClosed_closedBall.inter
        (lMinSlice_closed S hS T x (b ^ 2) (sq_pos_of_pos hb))).inter
          (hYcpt.isClosed.preimage hendCont)
    have hKcpt : IsCompact K := by
      exact (isCompact_closedBall (0 : E) C).of_isClosed_subset hKclosed
        (fun Z hZ ↦ hZ.1.1)
    have hZ0K : (Z0 : E) ∈ K := by
      refine ⟨⟨?_, hZ0min⟩, ?_⟩
      · change dist (show E from Z0) 0 ≤ C
        rw [dist_zero_right]
        exact hminBdd q0 (Metric.mem_ball_self hε0) Z0 hZ0min hZ0end
      · refine ⟨q0, ⟨?_, ?_⟩⟩
        · exact Metric.mem_closedBall_self hρ.le
        · change (extChartAt I p).symm q0 = lRegCurve S T x Z0 b
          calc
            (extChartAt I p).symm q0 = lExp S T x Z0 (b ^ 2) := hZ0end.symm
            _ = lRegCurve S T x Z0 b := by
              rw [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    have hbchart : ∀ Z ∈ K,
        lRegCurve S T x Z b ∈ (chartAt H p).source := by
      intro Z hZ
      obtain ⟨q, hqQ, hqend⟩ := hZ.2
      change endMap Z ∈ (chartAt H p).source
      rw [← hqend]
      simpa only [extChartAt_source] using (extChartAt I p).map_target (hQtar hqQ)
    obtain ⟨δ, hδ, hδb, htube⟩ := lRayChart_tube (I := I)
      S hS T x p hb hKcpt (fun Z hZ ↦ hbdomAll Z) hbchart
    have hdomTail : K ×ˢ Icc (b - δ) b ⊆ lRegJointDom S T x := by
      intro q hq
      change q.2 ∈ lRegDomain S T x q.1
      exact (htube q.1 hq.1 q.2 hq.2).1
    have hsrcTail : MapsTo
        (fun q : E × Real ↦ lRegCurve S T x q.1 q.2)
        (K ×ˢ Icc (b - δ) b) (extChartAt I p).source := by
      intro q hq
      simpa only [extChartAt_source] using (htube q.1 hq.1 q.2 hq.2).2
    obtain ⟨V, hV, hchart⟩ := lRayChart_bound (I := I) S hS T x p
      hKcpt hdomTail hsrcTail
    obtain ⟨Cr, hCr, htail⟩ := lRayTail_bound (I := I) S hS T x
      hKcpt hdomTail
    let Qbig : Set E := Metric.closedBall q0 (R / 2)
    have hQbigCpt : IsCompact Qbig := isCompact_closedBall q0 (R / 2)
    have hQbigTar : Qbig ⊆ interior (extChartAt I p).target := by
      rw [interior_eq_iff_isOpen.mpr (isOpen_extChartAt_target (I := I) p)]
      intro q hq
      apply hRtar
      exact lt_of_le_of_lt hq (half_lt_self hR)
    obtain ⟨Cg, Cs, hCg, hCs, hramp⟩ := lRampAct_slab (I := I)
      S hS T p (A := b - δ) (B := b) (fun s hs ↦ hreg s ⟨by
        linarith [hs.1, hδb], hs.2⟩) hQbigCpt hQbigTar
    let ε : Real := min (ρ / 2)
      (min (δ / 4) (min (b / 4) (R / (16 * (V + 1)))))
    have hV1 : 0 < V + 1 := by linarith
    have hε : 0 < ε := by
      exact lt_min (half_pos hρ) (lt_min (by positivity)
        (lt_min (by positivity) (div_pos hR (by positivity))))
    let Aconst : Real := Cr + Cg / 2 * (V + 1) ^ 2 + Cs
    have hAconst : 0 ≤ Aconst := by positivity
    let Lip : NNReal := ⟨Aconst, hAconst⟩
    refine ⟨Lip, Metric.ball q0 ε,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds q0 hε), ?_⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro q hq r hr
    have hqρ : q ∈ Metric.ball q0 ρ :=
      hq.trans_le ((min_le_left (ρ / 2) _).trans (half_le_self hρ.le))
    have hrρ : r ∈ Metric.ball q0 ρ :=
      hr.trans_le ((min_le_left (ρ / 2) _).trans (half_le_self hρ.le))
    have hqtar := hQtar (Metric.ball_subset_closedBall hqρ)
    have hrtar := hQtar (Metric.ball_subset_closedBall hrρ)
    have hreachQ := exists_lC1_move (I := I) S hS T x b hb hreg p
      (convex_ball q0 ρ) (fun z hz ↦ hQtar (Metric.ball_subset_closedBall hz))
      (Metric.mem_ball_self hρ) hqρ alpha halpha hstart hend
    have hreachR := exists_lC1_move (I := I) S hS T x b hb hreg p
      (convex_ball q0 ρ) (fun z hz ↦ hQtar (Metric.ball_subset_closedBall hz))
      (Metric.mem_ball_self hρ) hrρ alpha halpha hstart hend
    obtain ⟨alphaQ, halphaQ, halphaQ0, halphaQb⟩ := hreachQ
    obtain ⟨alphaR, halphaR, halphaR0, halphaRb⟩ := hreachR
    obtain ⟨Wq, hWqmin, hWqend⟩ := exists_lMinVec (I := I) S hS
      T (T - b ^ 2) T (b ^ 2) (sq_pos_of_pos hb) htime (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hback) x
      ((extChartAt I p).symm q) alphaQ halphaQ halphaQ0 (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using halphaQb) (by
          simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hreg)
    obtain ⟨Wr, hWrmin, hWrend⟩ := exists_lMinVec (I := I) S hS
      T (T - b ^ 2) T (b ^ 2) (sq_pos_of_pos hb) htime (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hback) x
      ((extChartAt I p).symm r) alphaR halphaR halphaR0 (by
        simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using halphaRb) (by
          simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using hreg)
    have hWqK : (Wq : E) ∈ K := by
      refine ⟨⟨?_, hWqmin⟩, ?_⟩
      · change dist (show E from Wq) 0 ≤ C
        rw [dist_zero_right]
        exact hminBdd q (hqρ.trans_le (min_le_left (ε0 / 2) _ |>.trans
          (half_le_self hε0.le))) Wq hWqmin hWqend
      · refine ⟨q,
          ⟨Metric.ball_subset_closedBall hqρ, ?_⟩⟩
        change (extChartAt I p).symm q = lRegCurve S T x Wq b
        calc
          (extChartAt I p).symm q = lExp S T x Wq (b ^ 2) := hWqend.symm
          _ = lRegCurve S T x Wq b := by
            rw [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    have hWrK : (Wr : E) ∈ K := by
      refine ⟨⟨?_, hWrmin⟩, ?_⟩
      · change dist (show E from Wr) 0 ≤ C
        rw [dist_zero_right]
        exact hminBdd r (hrρ.trans_le (min_le_left (ε0 / 2) _ |>.trans
          (half_le_self hε0.le))) Wr hWrmin hWrend
      · refine ⟨r,
          ⟨Metric.ball_subset_closedBall hrρ, ?_⟩⟩
        change (extChartAt I p).symm r = lRegCurve S T x Wr b
        calc
          (extChartAt I p).symm r = lExp S T x Wr (b ^ 2) := hWrend.symm
          _ = lRegCurve S T x Wr b := by
            rw [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb]
    have oneSide : ∀ (u v : E) (Wu : TangentSpace I x),
        u ∈ Metric.ball q0 ε → v ∈ Metric.ball q0 ε →
        u ∈ (extChartAt I p).target → v ∈ (extChartAt I p).target →
        (Wu, b ^ 2) ∈ lMinDomain S T x →
        lExp S T x Wu (b ^ 2) = (extChartAt I p).symm u →
        (Wu : E) ∈ K →
        lCost S T x ((extChartAt I p).symm v) (b ^ 2) -
          lCost S T x ((extChartAt I p).symm u) (b ^ 2) ≤
            Aconst * ‖v - u‖ := by
      intro u v Wu hu hv hutar hvtar hWmin hWend hWK
      by_cases huv : u = v
      · subst v
        simp only [sub_self, norm_zero, mul_zero, le_refl]
      let d : Real := ‖v - u‖
      have hd : 0 < d := (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huv)))
      have hdist : d < 2 * ε := by
        calc
          d = dist v u := by rw [dist_eq_norm]
          _ ≤ dist v q0 + dist u q0 := by
            simpa only [dist_comm q0 u] using dist_triangle v q0 u
          _ < ε + ε := add_lt_add hv hu
          _ = 2 * ε := by ring
      have hdδ : d < δ := by
        have hεδ : ε ≤ δ / 4 :=
          (min_le_right (ρ / 2) _).trans (min_le_left _ _)
        linarith
      have hdb : d < b := by
        have hεb : ε ≤ b / 4 :=
          (min_le_right (ρ / 2) _).trans
            ((min_le_right (δ / 4) _).trans (min_le_left _ _))
        linarith
      let c : Real := b - d
      have hc : 0 < c := sub_pos.mpr hdb
      have hcb : c < b := sub_lt_self b hd
      have hcI : c ∈ Icc (b - δ) b := ⟨by dsimp only [c]; linarith, hcb.le⟩
      have hWuEnd : lRegCurve S T x Wu b = (extChartAt I p).symm u := by
        simpa only [lExp, Real.sqrt_sq_eq_abs, abs_of_pos hb] using hWend
      have hchartEnd : (extChartAt I p) (lRegCurve S T x Wu b) = u := by
        rw [hWuEnd]
        exact (extChartAt I p).right_inv hutar
      let y : E := (extChartAt I p) (lRegCurve S T x Wu c)
      have hyu : ‖y - u‖ ≤ V * d := by
        have hh := hchart (Wu : E) hWK c hcI
        rw [hchartEnd] at hh
        simpa only [y, c, sub_sub_cancel, norm_sub_rev] using hh
      have hyv : ‖v - y‖ ≤ (V + 1) * d := by
        calc
          ‖v - y‖ = ‖(v - u) + (u - y)‖ := by congr 1; abel
          _ ≤ ‖v - u‖ + ‖u - y‖ := norm_add_le _ _
          _ = d + ‖y - u‖ := by
            rw [show ‖v - u‖ = d by rfl, norm_sub_rev u y]
          _ ≤ d + V * d := add_le_add (le_refl d) hyu
          _ = (V + 1) * d := by ring
      have hεR : ε ≤ R / (16 * (V + 1)) :=
        (min_le_right (ρ / 2) _).trans
          ((min_le_right (δ / 4) _).trans (min_le_right _ _))
      have hepsR : ε ≤ R / 16 := by
        calc
          ε ≤ R / (16 * (V + 1)) := hεR
          _ ≤ R / 16 := by
            apply (div_le_div_iff_of_pos_left hR (by positivity)
              (by positivity)).2
            nlinarith [hV]
      have hdR : V * d + ε ≤ R / 2 := by
        have hd' : d ≤ R / (8 * (V + 1)) := by
          calc d ≤ 2 * ε := hdist.le
            _ ≤ 2 * (R / (16 * (V + 1))) := by gcongr
            _ = R / (8 * (V + 1)) := by field_simp; ring
        have hVR : V * d ≤ R / 8 := by
          calc
            V * d ≤ (V + 1) * (R / (8 * (V + 1))) := by
              exact mul_le_mul (by linarith) hd' hd.le hV1.le
            _ = R / 8 := by field_simp [hV1.ne']
        calc
          V * d + ε ≤ R / 8 + R / 16 := add_le_add hVR hepsR
          _ ≤ R / 2 := by linarith [hR]
      have hyQ : y ∈ Qbig := by
        change dist y q0 ≤ R / 2
        calc
          dist y q0 ≤ dist y u + dist u q0 := dist_triangle _ _ _
          _ = ‖y - u‖ + dist u q0 := by rw [dist_eq_norm]
          _ ≤ V * d + ε := add_le_add hyu hu.le
          _ ≤ R / 2 := hdR
      have hvQ : v ∈ Qbig := by
        change dist v q0 ≤ R / 2
        exact hv.le.trans (hεR.trans (by
          apply (div_le_div_iff_of_pos_left hR (by positivity)
            (by positivity)).2
          nlinarith [hV]))
      have hmap := lRamp_mapsTo (convex_closedBall q0 (R / 2))
        (sub_nonneg.mpr hcb.le) hyQ hvQ
      have htimeRamp : ∀ r ∈ Icc (0 : Real) (b - c),
          c + r ∈ Icc (b - δ) b := by
        intro r hr
        exact ⟨by linarith [hcI.1, hr.1], by linarith [hr.2]⟩
      have hrampLe := hramp (sub_pos.mpr hcb) htimeRamp hmap
      have hrampLin : lChartAction S T c p
          (lChartRamp y v (sub_nonneg.mpr hcb.le)) ≤
            (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
        calc
          lChartAction S T c p (lChartRamp y v (sub_nonneg.mpr hcb.le)) ≤
              Cg / 2 * (‖v - y‖ ^ 2 / (b - c)) + Cs * (b - c) :=
            by simpa only [y] using hrampLe
          _ ≤ (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
            have hbcEq : b - c = d := by simp only [c, sub_sub_cancel]
            rw [hbcEq]
            have hd0 := hd.le
            have hsq : ‖v - y‖ ^ 2 ≤ ((V + 1) * d) ^ 2 :=
              sq_le_sq₀ (norm_nonneg _) (mul_nonneg hV1.le hd0) |>.2 hyv
            calc
              Cg / 2 * (‖v - y‖ ^ 2 / d) + Cs * d ≤
                  Cg / 2 * (((V + 1) * d) ^ 2 / d) + Cs * d := by
                    gcongr
              _ = (Cg / 2 * (V + 1) ^ 2 + Cs) * d := by
                    field_simp
      have hrayc := (htube (Wu : E) hWK c hcI).2
      have hcostLe := lCost_ramp_le (I := I) S hS T x p hc hcb
        htime hback hreg Wu (hbdomAll (Wu : E)) hrayc v (by
          intro z hz
          exact interior_subset (hQbigTar (by
            simpa only [y, c, sub_sub_cancel] using hmap hz)))
      have hheadInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
        ⟨hS.scalarCont⟩ T 0 c hc.le (lRegCurve S T x Wu)
        (lRegCurve_c1On S hS T x Wu
          (lRegDomain_seg S T x Wu (hbdomAll (Wu : E)) hc.le hcb.le))
        (fun s hs ↦ hreg s ⟨hs.1, hs.2.trans hcb.le⟩)
      have htailInt := intervalIntegrable_lRegLagrangian_of_contMDiffOn_one (I := I) S hS.smoothMetric
        ⟨hS.scalarCont⟩ T c b hcb.le (lRegCurve S T x Wu)
        ((lRegCurve_c1On S hS T x Wu (hbdomAll (Wu : E))).mono
          (fun s hs ↦ ⟨hc.le.trans hs.1, hs.2⟩))
        (fun s hs ↦ hreg s ⟨hc.le.trans hs.1, hs.2⟩)
      have hadd := lRegAction_add (I := I) S T (lRegCurve S T x Wu)
        0 c b hheadInt htailInt
      have hminEq := ((mem_lMinDomain S T x Wu (b ^ 2)).1 hWmin).2
      have hfull : lRegAction S T (lRegCurve S T x Wu) 0 b =
          lCost S T x ((extChartAt I p).symm u) (b ^ 2) := by
        calc
          lRegAction S T (lRegCurve S T x Wu) 0 b =
              lLength S T (squareRootReparametrization (lRegCurve S T x Wu)) 0 (b ^ 2) := by
                simpa only [Real.sqrt_sq_eq_abs, abs_of_pos hb] using
                  (lLength_squareRootReparametrization_eq_lRegAction (I := I) S T (lRegCurve S T x Wu)
                    (b ^ 2) (sq_nonneg b)).symm
          _ = lCost S T x (lExp S T x Wu (b ^ 2)) (b ^ 2) := by
                change lLength S T (squareRootReparametrization (lRegCurve S T x Wu)) 0
                  (b ^ 2) = lCost S T x
                    (lRegCurve S T x Wu (Real.sqrt (b ^ 2))) (b ^ 2)
                exact hminEq
          _ = lCost S T x ((extChartAt I p).symm u) (b ^ 2) := by rw [hWend]
      have htailLe := htail (Wu : E) hWK c hcI
      rw [← hfull, ← hadd]
      have hcalc := hcostLe
      dsimp only [y] at hrampLin hcalc
      have hnegTail : -lRegAction S T (lRegCurve S T x Wu) c b ≤ Cr * d := by
        calc
          -lRegAction S T (lRegCurve S T x Wu) c b ≤
              |lRegAction S T (lRegCurve S T x Wu) c b| := by
                simpa only [abs_neg] using
                  le_abs_self (-lRegAction S T (lRegCurve S T x Wu) c b)
          _ ≤ Cr * (b - c) := htailLe
          _ = Cr * d := by simp only [c, sub_sub_cancel]
      dsimp only [Aconst]
      linarith [hcalc, hrampLin, hnegTail]
    have hqr := oneSide q r Wq hq hr hqtar hrtar hWqmin hWqend hWqK
    have hrq := oneSide r q Wr hr hq hrtar hqtar hWrmin hWrend hWrK
    change dist (lCost S T x ((extChartAt I p).symm q) tau)
      (lCost S T x ((extChartAt I p).symm r) tau) ≤
        (Lip : Real) * dist q r
    rw [Real.dist_eq, dist_eq_norm]
    rw [hb2] at hqr hrq
    change |lCost S T x ((extChartAt I p).symm q) tau -
      lCost S T x ((extChartAt I p).symm r) tau| ≤ Aconst * ‖q - r‖
    rw [abs_le]
    constructor
    · have := hqr
      rw [norm_sub_rev] at this
      linarith
    · simpa only [norm_sub_rev] using hrq
  · obtain ⟨ε, hε, hlip⟩ := lCost_zero_lip (I := I) S hS T x b hb
      hreg p hq0 hreach
    refine ⟨0, Metric.ball q0 ε,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds q0 hε), ?_⟩
    change LipschitzOnWith 0
      (fun q ↦ lCost S T x ((extChartAt I p).symm q) tau)
      (Metric.ball q0 ε)
    rw [← hb2]
    exact hlip

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
