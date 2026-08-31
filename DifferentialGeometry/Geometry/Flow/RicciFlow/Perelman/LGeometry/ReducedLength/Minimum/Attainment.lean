import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.CompleteManifoldMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Basic
import DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.FlatPaths

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private def rmFactor (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

private theorem lRmFree_subseq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b A : Real) (ha : 0 <= a) (hab : a <= b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) <= K)
    (alpha : Nat -> Real -> M)
    (halpha : ∀ n, ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn (fun s =>
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) (Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b <= A)
    (x : M) (hfixa : ∀ n, alpha n a = x) :
    ∃ (Cpt : Set M) (phi : Nat -> Nat) (g : C(Icc a b, M)),
      IsCompact Cpt ∧ StrictMono phi ∧
        (∀ n (s : Icc a b), alpha (phi n) s.1 ∈ Cpt) ∧
        TendstoUniformly
          (fun n (s : Icc a b) => alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x := by
  classical
  let C : Real := -2 * b ^ 2 * rmFactor (E := E) K
  let Q : Real := Real.exp (2 * rmFactor (E := E) K * b ^ 2)
  let B : Real := Q * (2 * (A - C * (b - a)))
  let R : Real := Real.sqrt (b - a) * Real.sqrt B
  let Cpt : Set M :=
    {z : M | riemannianEDistOf (I := I) (S.base.metric T) x z <= ENNReal.ofReal R}
  have hb : 0 <= b := ha.trans hab
  have hQ : 0 <= Q := (Real.exp_pos _).le
  have henergy (n : Nat) :
      curveEnergy (I := I) (S.base.metric T) (alpha n) a b <= B := by
    apply lRegEnergy_le (I := I) S (S.base.metric T) T (alpha n) a b A C Q
      hab hQ
    · intro s hs v
      exact lRegMetric_le_rm (I := I) S hS K T b hb hreg hRm s
        ⟨ha.trans hs.1, hs.2⟩ (alpha n s) v
    · intro s hs
      exact lRegPot_lower_rm (I := I) S K T b hb hRm s
        ⟨ha.trans hs.1, hs.2⟩ (alpha n s)
    · exact hE n
    · exact hkin n
    · exact hLag n
    · exact hact n
  have hriedist (n : Nat) {s t : Real}
      (has : a <= s) (hst : s <= t) (htb : t <= b) :
      riemannianEDistOf (I := I) (S.base.metric T) (alpha n s) (alpha n t) <=
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hsubE : curveEnergy (I := I) (S.base.metric T) (alpha n) s t <=
        curveEnergy (I := I) (S.base.metric T) (alpha n) a b :=
      curveEnergy_mono (I := I) (S.base.metric T) has hst htb (hE n)
    exact edistOf_le_budget (I := I) (S.base.metric T) hst
      ((halpha n).mono hsub) ((hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  have hCpt : IsCompact Cpt :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hg x R
  have hval (n : Nat) (s : Icc a b) : alpha n s.1 ∈ Cpt := by
    have hdist := hriedist n (s := a) (t := s.1) le_rfl s.2.1 s.2.2
    have htime : Real.sqrt (s.1 - a) <= Real.sqrt (b - a) :=
      Real.sqrt_le_sqrt (by linarith [s.2.2])
    have hradius : Real.sqrt (s.1 - a) * Real.sqrt B <= R :=
      mul_le_mul_of_nonneg_right htime (Real.sqrt_nonneg B)
    rw [hfixa n] at hdist
    exact hdist.trans (ENNReal.ofReal_le_ofReal hradius)
  let f : Nat -> C(Icc a b, M) := fun n =>
    ⟨fun s => alpha n s.1, (halpha n).continuousOn.domRestrict⟩
  have hmod : Tendsto (fun r : Real => Real.sqrt r * Real.sqrt B)
      (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun r : Real => Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hequi : Equicontinuous (fun n => (f n : Icc a b -> M)) := by
    have hunif : UniformEquicontinuous (fun n => (f n : Icc a b -> M)) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro epsilon hepsilon
      obtain ⟨rho, hrho, htoDist⟩ :=
        dist_lt_riedist_cpt (I := I) (S.base.metric T) Cpt hCpt hepsilon
      obtain ⟨delta, hdelta, hmoddelta⟩ :=
        Metric.tendsto_nhds_nhds.1 hmod rho hrho
      refine ⟨delta, hdelta, ?_⟩
      intro s t hst n
      have hsmall : Real.sqrt (dist s t) * Real.sqrt B < rho := by
        have h := hmoddelta (x := dist s t) (by simpa using hst)
        simpa only [Real.dist_eq, sub_zero,
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using h
      have hofReal : ENNReal.ofReal (Real.sqrt (dist s t) * Real.sqrt B) <
          ENNReal.ofReal rho := (ENNReal.ofReal_lt_ofReal_iff hrho).2 hsmall
      rcases le_total s.1 t.1 with hst' | hts
      · have hriem := hriedist n s.2.1 hst' t.2.2
        have hriem' := hriem.trans_lt (by
          simpa only [Subtype.dist_eq, Real.dist_eq,
            abs_of_nonpos (sub_nonpos.mpr hst'), neg_sub] using hofReal)
        exact htoDist (alpha n s.1) (hval n s) (alpha n t.1) (hval n t) hriem'
      · have hriem := hriedist n t.2.1 hts s.2.2
        have hriem' := hriem.trans_lt (by
          simpa only [Subtype.dist_eq, Real.dist_eq,
            abs_of_nonneg (sub_nonneg.mpr hts)] using hofReal)
        have hout :=
          htoDist (alpha n t.1) (hval n t) (alpha n s.1) (hval n s) hriem'
        change dist (alpha n s.1) (alpha n t.1) < epsilon
        simpa only [dist_comm] using hout
    exact hunif.equicontinuous
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_cpt Cpt hCpt f hval hequi
  refine ⟨Cpt, phi, g, hCpt, hphi, (fun n s => hval (phi n) s), ?_, ?_⟩
  · have heq : (fun n ↦ ⇑(f (phi n))) =
        fun n s ↦ alpha (phi n) s.1 := by
      funext n s
      rfl
    rw [heq] at hconv
    exact hconv
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Icc a b)
    change Tendsto (fun n => alpha (phi n) a) atTop
      (nhds (g ⟨a, le_rfl, hab⟩)) at hlim
    have hlim' : Tendsto (fun _ : Nat => x) atTop
        (nhds (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

private theorem lRmFree_lsc
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b A : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) (Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (x : M) (hfixa : ∀ n, alpha n a = x) :
    ∃ (m : Nat) (t : Fin (m + 1) → Real) (p : Fin m → M)
      (chi : Nat → Nat) (gamma : Real → M)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      StrictMono chi ∧ Continuous gamma ∧ gamma a = x ∧
      TendstoUniformly
        (fun n (s : Icc a b) ↦ alpha (chi n) s.1)
        (fun s ↦ gamma s.1) atTop ∧
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
        (chartAt H (p i)).source) ∧
      (∀ i, EqOn (uLim i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
        (Icc (0 : Real) (partitionIntervalLength t i))) ∧
      (∑ i : Fin m, (
        (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
          (chartGramOp (I := I) S.family (p i)
            (T - (t i.castSucc + r) ^ 2, (uLim i).toFun r)
            ((uLim i).deriv r)) ((uLim i).deriv r)) +
        (∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * S.scalar (T - s ^ 2) (gamma s)))) ≤
        liminf (fun n ↦ lRegAction S T (alpha (chi n)) a b) atTop := by
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hb : 0 ≤ b := ha.trans hab
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  obtain ⟨Cpt, phi0, g, hCpt, hphi0, hval0, hconv0, hga⟩ :=
    lRmFree_subseq (I := I) S hS K T hg a b A ha hab hreg hRm
      alpha halpha hE hkin hLag hact x hfixa
  let gamma : Real → M := IccExtend hab g
  have hgamma : Continuous gamma := by
    dsimp only [gamma, IccExtend, Function.comp_apply]
    exact g.continuous.comp continuous_projIcc
  have hgamma_eq (s : Icc a b) : gamma s.1 = g s :=
    IccExtend_of_mem hab g s.2
  have hga' : gamma a = x := by
    rw [hgamma_eq ⟨a, le_rfl, hab⟩]
    exact hga
  have hconvG : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha (phi0 n) s.1)
      (fun s ↦ gamma s.1) atTop := by
    convert hconv0 using 1
    funext s
    exact hgamma_eq s
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) I
  obtain ⟨q, hq0, hqmono, ⟨m, hqm⟩, hpieces⟩ :=
    DifferentialGeometry.Geometry.exists_compact_chart_subdivision (H := H) hab
      hgamma.continuousOn
  let t : Fin (m + 1) → Real := fun i ↦ (q i).1
  have htmono : Monotone t := fun i j hij ↦ hqmono hij
  have ht0 : t 0 = a := congrArg Subtype.val hq0
  have htlast : t (Fin.last m) = b := congrArg Subtype.val (hqm m le_rfl)
  choose p Kman hKman hKsrc hgammaK using fun i : Fin m ↦ hpieces i
  obtain ⟨N, Kcoord, u, hKc, hKchart, hsrc, hrep, huK⟩ :=
    exists_chartH1_coordinates_with_compact_range_of_tendstoUniformly (I := I) a b t htmono ht0 htlast p Kman hKman hKsrc
      gamma hgamma.continuousOn (fun i ↦ hgammaK i)
      (fun n ↦ alpha (phi0 n)) (fun n ↦ halpha (phi0 n)) hconvG
  let beta : Nat → Real → M := fun n ↦ alpha (phi0 (n + N))
  have hbeta : ∀ n, ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (beta n) (Icc a b) := fun n ↦ halpha _
  have hkinBeta : ∀ n, IntervalIntegrable (lRegSpeedSq S T (beta n)) volume a b :=
    fun n ↦ hkin _
  have hLagBeta : ∀ n, IntervalIntegrable (lRegLag S T (beta n)) volume a b :=
    fun n ↦ hLag _
  have hactBeta : ∀ n, lRegAction S T (beta n) a b ≤ A := fun n ↦ hact _
  obtain ⟨psi, uLim, hpsi, hdu, hu⟩ :=
    lRmChartH1_fin (I := I) S hMet K T a b ha t htmono ht0 htlast p beta
      hbeta hkinBeta hLagBeta u
      (fun i n ↦ by simpa only [beta, Nat.add_comm] using hsrc i n)
      (fun i n ↦ by simpa only [beta, Nat.add_comm] using hrep i n)
      Kcoord hKc hKchart (fun i n r ↦ by
        simpa only [beta, Nat.add_comm] using huK i n r)
      hactBeta hRm hregBack
  let chi : Nat → Nat := fun n ↦ phi0 (psi n + N)
  have hpsiN : StrictMono (fun n ↦ psi n + N) := fun i j hij ↦
    by simpa only [Nat.add_comm] using add_lt_add_right (hpsi hij) N
  have hchi : StrictMono chi := hphi0.comp hpsiN
  have hconv : TendstoUniformly
      (fun n (s : Icc a b) ↦ alpha (chi n) s.1)
      (fun s ↦ gamma s.1) atTop := by
    intro V hV
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hconvG V hV)
    filter_upwards [hpsi.tendsto_atTop.eventually (eventually_ge_atTop k)]
      with n hn
    exact hk (psi n + N) (hn.trans (Nat.le_add_right _ _))
  have hsrc' (i : Fin m) (n : Nat) : MapsTo (alpha (chi n))
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source := by
    simpa only [chi, beta, Nat.add_comm] using hsrc i (psi n)
  have hrep' (i : Fin m) (n : Nat) : EqOn (u i (psi n)).toFun
      (fun r ↦ extChartAt I (p i) (alpha (chi n) (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    simpa only [chi, beta, Nat.add_comm] using hrep i (psi n)
  have huK' (i : Fin m) (n : Nat) (r : Icc (0 : Real) (partitionIntervalLength t i)) :
      (u i (psi n)).toFun r.1 ∈ Kcoord i := by
    simpa only [beta, Nat.add_comm] using huK i (psi n) r
  have hgammaSrc (i : Fin m) : MapsTo gamma
      (Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source :=
    (hgammaK i).mono_right (interior_subset.trans (hKsrc i))
  have hdiff (i : Fin m) (n : Nat) :
      ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
        MDifferentiableAt (modelWithCornersSelf Real Real) I
          (alpha (chi n)) (t i.castSucc + r) := by
    have hseg : t i.castSucc ≤ t i.succ := htmono Fin.castSucc_lt_succ.le
    have hleft : a ≤ t i.castSucc := by
      rw [← ht0]
      exact htmono (Fin.zero_le _)
    have hright : t i.succ ≤ b := by
      rw [← htlast]
      exact htmono (Fin.le_last _)
    have hmem : ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
        r ∈ Ioo (0 : Real) (partitionIntervalLength t i) := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with r hr
    change r ∈ Ioo (0 : Real) (t i.succ - t i.castSucc) at hr
    have hsIoo : t i.castSucc + r ∈ Ioo a b := by
      constructor <;> linarith [hr.1, hr.2, hleft, hright]
    have hsWithin := halpha (chi n) (t i.castSucc + r)
      ⟨hsIoo.1.le, hsIoo.2.le⟩
    exact (hsWithin.contMDiffAt
      (Icc_mem_nhds hsIoo.1 hsIoo.2)).mdifferentiableAt (by norm_num)
  have hlimRep (i : Fin m) : EqOn (uLim i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)) := by
    intro r hr
    have hpoint : Tendsto (fun n ↦ alpha (chi n) (t i.castSucc + r)) atTop
        (nhds (gamma (t i.castSucc + r))) := by
      have hsub : t i.castSucc + r ∈ Icc a b := by
        have hleft : a ≤ t i.castSucc := by rw [← ht0]; exact htmono (Fin.zero_le _)
        have hright : t i.succ ≤ b := by rw [← htlast]; exact htmono (Fin.le_last _)
        change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
        exact ⟨by linarith [hleft, hr.1], by linarith [hr.2, hright]⟩
      exact hconv.tendsto_at ⟨t i.castSucc + r, hsub⟩
    have hrpiece : t i.castSucc + r ∈ Icc (t i.castSucc) (t i.succ) := by
      change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    let rsub : Icc (0 : Real) (partitionIntervalLength t i) := ⟨r, hr⟩
    have hExtSrc : gamma (t i.castSucc + r) ∈ (extChartAt I (p i)).source := by
      rw [extChartAt_source]
      exact hgammaSrc i hrpiece
    have hchart : Tendsto (fun n ↦
        extChartAt I (p i) (alpha (chi n) (t i.castSucc + r))) atTop
        (nhds (extChartAt I (p i) (gamma (t i.castSucc + r)))) :=
      (continuousAt_extChartAt' (I := I) hExtSrc).tendsto.comp hpoint
    have huPoint := (hu i).tendsto_at rsub
    have huChart : Tendsto (fun n ↦
        extChartAt I (p i) (alpha (chi n) (t i.castSucc + r))) atTop
        (nhds ((uLim i).toFun r)) := by
      apply huPoint.congr'
      filter_upwards with n
      exact hrep' i n rsub.2
    exact tendsto_nhds_unique huChart hchart
  have hactBound : IsBoundedUnder (· ≤ ·) atTop
      (fun n ↦ lRegAction S T (alpha (chi n)) a b) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n ↦ hact (chi n))
  have hlsc := lRegAction_fin_cpt S hMet hSc T a b t htmono ht0 htlast p
    (fun n ↦ alpha (chi n)) gamma Cpt hCpt
    (fun n s hs ↦ hval0 (psi n + N) ⟨s, hs⟩)
    (fun i n ↦ u i (psi n))
    hsrc' hrep' hdiff Kcoord hKc hKchart huK' uLim
    (fun i ↦ by intro V hV; exact hu i V hV)
    (fun i z ↦ by simpa only using hdu i z)
    hconv hactBound hregBack
  exact ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga', hconv,
    htmono, ht0, htlast, hgammaSrc, hlimRep, hlsc⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_redMin_rm [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (tau : Real) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x : M) :
    ∃ y : M, ∀ z : M,
      redLength S T x y tau ≤ redLength S T x z tau := by
  classical
  let b : Real := Real.sqrt tau
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hbSq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - b ^ 2) T ⊆ D.regular := by
    simpa only [hbSq] using hreg
  have hRmSq : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hbSq] using hRm
  let costs : Set Real := {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha 0 = x ∧ lRegAction S T alpha 0 b = r}
  have hcosts : costs.Nonempty := by
    refine ⟨lRegAction S T (fun _ : Real ↦ x) 0 b, fun _ ↦ x,
      contMDiff_const, rfl, rfl⟩
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hregBack : ∀ s ∈ Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hregSq
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  let C : Real := -2 * b ^ 2 * rmFactor (E := E) K
  have hcosts_bdd : BddBelow costs := by
    refine ⟨C * b, ?_⟩
    intro r hr
    obtain ⟨alpha, halpha, _h0, rfl⟩ := hr
    have hkin := lRegSpeed_int_c1 (I := I) S hMet hSc T 0 b hb.le alpha
      halpha.contMDiffOn hregBack
    have hLag := lRegLag_int_c1 (I := I) S hMet hSc T 0 b hb.le alpha
      halpha.contMDiffOn hregBack
    have hbound := lRegKinetic_le (I := I) S T alpha 0 b
      (lRegAction S T alpha 0 b) C hb.le
      (fun s hs ↦ lRegPot_lower_rm (I := I) S K T b hb.le hRmSq s
        ⟨hs.1, hs.2⟩ (alpha s))
      hkin hLag le_rfl
    have hnonneg : 0 ≤ ∫ s in 0..b, lRegSpeedSq S T alpha s := by
      apply intervalIntegral.integral_nonneg hb.le
      intro s _hs
      exact lRegSpeedSq_nonneg (I := I) S T alpha s
    have hbound' := hbound
    simp only [sub_zero] at hbound'
    linarith
  obtain ⟨v, hvanti, hvlim, hv⟩ :=
    exists_seq_tendsto_sInf hcosts hcosts_bdd
  choose alpha halpha hstart hval using fun n ↦ hv n
  have hE (n : Nat) : IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (Icc (0 : Real) b) :=
    lRegRef_int_c1 (I := I) (S.base.metric T) (alpha n) (halpha n) 0 b
  have hkin (n : Nat) : IntervalIntegrable
      (lRegSpeedSq S T (alpha n)) volume 0 b :=
    lRegSpeed_int_c1 (I := I) S hMet hSc T 0 b hb.le (alpha n)
      (halpha n).contMDiffOn hregBack
  have hLag (n : Nat) : IntervalIntegrable
      (lRegLag S T (alpha n)) volume 0 b :=
    lRegLag_int_c1 (I := I) S hMet hSc T 0 b hb.le (alpha n)
      (halpha n).contMDiffOn hregBack
  have hact (n : Nat) : lRegAction S T (alpha n) 0 b ≤ v 0 := by
    rw [hval n]
    exact hvanti (Nat.zero_le n)
  obtain ⟨m, t, p, chi, gamma, uLim, hchi, _hgamma, hga, _hconv,
      htmono, ht0, htlast, hsrc, hrep, hlsc⟩ :=
    lRmFree_lsc (I := I) S hS K T hg 0 b (v 0) le_rfl hb.le
      hregSq hRmSq alpha (fun n ↦ (halpha n).contMDiffOn)
      hE hkin hLag hact x hstart
  have hsubseq : Tendsto
      (fun n ↦ lRegAction S T (alpha (chi n)) 0 b) atTop
      (nhds (sInf costs)) := by
    have hlim := hvlim.comp hchi.tendsto_atTop
    have heq : v ∘ chi = fun n ↦ v (chi n) := by
      funext n
      rfl
    rw [heq] at hlim
    simpa only [hval] using hlim
  have hL : lRegAction S T gamma 0 b ≤ sInf costs := by
    have hraw : lRegAction S T gamma 0 b ≤
        liminf (fun n ↦ lRegAction S T (alpha (chi n)) 0 b) atTop := by
      rw [lRegAction_chart S hMet hSc T 0 b t htmono ht0 htlast p gamma
        uLim hsrc hrep hregBack]
      exact hlsc
    simpa only [hsubseq.liminf_eq] using hraw
  obtain ⟨beta, _u, hbeta, hbetaa, hbetab, _hsrcBeta, _hrepBeta,
      _hu, _hunifBeta, hbetaAct⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T 0 b t htmono ht0 htlast p gamma
      uLim hsrc hrep hregBack
  let y : M := gamma b
  let fixed (z : M) : Set Real := {r : Real | ∃ delta : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 delta ∧
      delta 0 = x ∧ delta b = z ∧ lRegAction S T delta 0 b = r}
  have hfixed_bdd (z : M) : BddBelow (fixed z) := by
    apply hcosts_bdd.mono
    intro r hr
    obtain ⟨delta, hdelta, hd0, _hdb, rfl⟩ := hr
    exact ⟨delta, hdelta, hd0, rfl⟩
  have hyL : lRegCostC1 S T 0 b x y ≤ lRegAction S T gamma 0 b := by
    change sInf (fixed y) ≤ lRegAction S T gamma 0 b
    apply ge_of_tendsto' hbetaAct
    intro n
    apply csInf_le (hfixed_bdd y)
    exact ⟨beta n, hbeta n, (hbetaa n).trans hga,
      by simpa only [y] using hbetab n, rfl⟩
  have hfixed (z : M) : (fixed z).Nonempty := by
    let g := S.base.metric T
    let : RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E
        (TangentSpace I : M → Type _) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    have hxz : Manifold.riemannianEDist I x z < (⊤ : ENNReal) :=
      lt_of_le_of_ne le_top
        (DifferentialGeometry.Geometry.Riemannian.Exponential.riemannianEDist_ne_top
          (I := I) x z)
    obtain ⟨path, hpath, _hlen⟩ :=
      DifferentialGeometry.Geometry.Riemannian.CGT.exists_flat_path
        (I := I) hxz
    let delta : Real → M := fun s ↦ path.extend (s / b)
    have hdelta : ContMDiff (modelWithCornersSelf Real Real) I 1 delta := by
      apply hpath.c1.comp
      rw [contMDiff_iff_contDiff]
      fun_prop
    refine ⟨lRegAction S T delta 0 b, delta, hdelta, ?_, ?_, rfl⟩
    · simp only [delta, zero_div, Path.extend_zero]
    · simp only [delta, div_self hb.ne', Path.extend_one]
  have hfree_le (z : M) : sInf costs ≤ lRegCostC1 S T 0 b x z := by
    change sInf costs ≤ sInf (fixed z)
    apply le_csInf (hfixed z)
    intro r hr
    obtain ⟨delta, hdelta, hd0, _hdb, rfl⟩ := hr
    apply csInf_le hcosts_bdd
    exact ⟨delta, hdelta, hd0, rfl⟩
  refine ⟨y, fun z ↦ ?_⟩
  rw [redLength, redLength, lCost_eq_reg (I := I) S T x y tau htau.le,
    lCost_eq_reg (I := I) S T x z tau htau.le]
  have hcost : lRegCostC1 S T 0 b x y ≤ lRegCostC1 S T 0 b x z :=
    hyL.trans (hL.trans (hfree_le z))
  exact (div_le_div_iff_of_pos_right (by positivity)).2 hcost

end DifferentialGeometry.PDE.RicciFlow.Perelman
