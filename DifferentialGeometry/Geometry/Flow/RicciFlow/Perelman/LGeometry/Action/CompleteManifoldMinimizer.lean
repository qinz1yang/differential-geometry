import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.GlobalLowerSemicontinuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.C1Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Attainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Extension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MinimizerC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.MinimizerRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.RawMinimizer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.MinimizerDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.CurvatureBounds

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
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

private def rmFactor (E : Type uE) [NormedAddCommGroup E]
    [NormedSpace Real E] (K : Real) : Real :=
  (Module.finrank Real E : Real) ^ 2 * Real.sqrt K

omit [NeZero (Module.finrank Real E)] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
theorem lRegSpeed_int_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real) (hab : a ≤ b) (alpha : Real → M)
    (halpha : ContMDiffOn (modelWithCornersSelf Real Real) I 1 alpha (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    IntervalIntegrable (lRegSpeedSq S T alpha) volume a b := by
  have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab alpha halpha hreg
  have hcarrier : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.carrier := by
    intro s hs
    exact D.regular_subset (hreg s (by simpa only [uIcc_of_le hab] using hs))
  have hpot : IntervalIntegrable
      (fun s ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) volume a b :=
    lScalar_int (I := I) S hSc T a b alpha hcarrier (by
      simpa only [uIcc_of_le hab] using halpha.continuousOn)
  have hhalf : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegSpeedSq S T alpha s) volume a b := by
    change IntervalIntegrable (fun s ↦ (1 / 2 : Real) *
      (S.base.metric (T - s ^ 2)).inner (alpha s)
        (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) volume a b
    rw [show (fun s ↦ (1 / 2 : Real) *
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s)) =
      (fun s ↦ lRegLag S T alpha s -
        2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)) by
      funext s
      simp only [lRegLag]
      ring]
    exact hLag.sub hpot
  have htwice := hhalf.const_mul 2
  convert htwice using 1
  funext s
  ring

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem lRegRef_int_c1
    (gRef : SmoothRiemannianMetric I M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (a b : Real) :
    IntegrableOn
      (fun s ↦ gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) (Icc a b) := by
  have hv : ContMDiff (modelWithCornersSelf Real Real)
      (I.prod (modelWithCornersSelf Real E)) 0
      (fun s ↦ TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s)) := by
    have ht := halpha.contMDiff_tangentMap (m := 0) (by norm_num)
    have hone : ContMDiff (modelWithCornersSelf Real Real)
        (modelWithCornersSelf Real Real).tangent 0
        (fun s : Real ↦
          (⟨s, (1 : Real)⟩ : TangentBundle (modelWithCornersSelf Real Real) Real)) := by
      exact (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    have h := ht.comp hone
    change ContMDiff (modelWithCornersSelf Real Real)
      (I.prod (modelWithCornersSelf Real E)) 0
      (fun s ↦ TotalSpace.mk' E (alpha s) (lVelocity (I := I) alpha s)) at h
    exact h
  let cg : ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) := gRef.toContinuousRiemannianMetric
  let rb : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨cg.toRiemannianMetric⟩
  have hq : Continuous (fun s ↦
      gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) := by
    have hinner := Continuous.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _))
      (b := alpha) (v := fun s ↦ lVelocity (I := I) alpha s)
      (w := fun s ↦ lVelocity (I := I) alpha s) hv.continuous hv.continuous
    exact hinner.congr fun _ ↦ rfl
  exact hq.continuousOn.integrableOn_compact isCompact_Icc

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] in
omit [SigmaCompactSpace M] in
theorem lRmChartH1_fin
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (K T a b : Real) (ha : 0 ≤ a)
    {m : Nat} (t : Fin (m + 1) → Real)
    (htmono : Monotone t) (ht0 : t 0 = a) (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (alpha n) (Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (u : (i : Fin m) → Nat → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i n, MapsTo (alpha n) (Icc (t i.castSucc) (t i.succ))
      (chartAt H (p i)).source)
    (hrep : ∀ i n, EqOn (u i n).toFun
      (fun r ↦ extChartAt I (p i) (alpha n (t i.castSucc + r)))
      (Icc (0 : Real) (partitionIntervalLength t i)))
    (Kcoord : Fin m → Set E) (hKc : ∀ i, IsCompact (Kcoord i))
    (hKchart : ∀ i, Kcoord i ⊆ interior (extChartAt I (p i)).target)
    (huK : ∀ i n (r : Icc (0 : Real) (partitionIntervalLength t i)),
      (u i n).toFun r.1 ∈ Kcoord i)
    {A : Real} (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (phi : Nat → Nat)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      StrictMono phi ∧
        (∀ i (z : timeL2 E (partitionIntervalLength t i)),
          Tendsto (fun n ↦ inner Real (u i (phi n)).deriv z) atTop
            (nhds (inner Real (uLim i).deriv z))) ∧
        (∀ i, TendstoUniformly
          (fun n (r : Icc (0 : Real) (partitionIntervalLength t i)) ↦
            (u i (phi n)).toFun r.1)
          (fun r ↦ (uLim i).toFun r.1) atTop) := by
  classical
  have hab : a ≤ b := by
    rw [← ht0, ← htlast]
    exact htmono (Fin.zero_le _)
  have hb : 0 ≤ b := ha.trans hab
  let C : Real := -2 * b ^ 2 * rmFactor E K
  let B : Real := A - C * (b - a)
  have hspeed (n : Nat) :
      (∫ s in a..b, lRegSpeedSq S T (alpha n) s) ≤ 2 * B := by
    exact lRegKinetic_le (I := I) S T (alpha n) a b A C hab
      (fun s hs ↦ lRegPot_lower_rm (I := I) S K T b hb hRm s
        ⟨ha.trans hs.1, hs.2⟩ (alpha n s))
      (hkin n) (hLag n) (hact n)
  have hhalfInt (n : Nat) : IntervalIntegrable
      (fun s ↦ (1 / 2 : Real) * lRegSpeedSq S T (alpha n) s) volume a b :=
    (hkin n).const_mul (1 / 2 : Real)
  have hhalf (n : Nat) :
      (∫ s in a..b, (1 / 2 : Real) * lRegSpeedSq S T (alpha n) s) ≤ B := by
    rw [intervalIntegral.integral_const_mul]
    linarith [hspeed n]
  have hnonneg (n : Nat) :
      ∀ᵐ s ∂volume.restrict (Ioc a b),
        0 ≤ (1 / 2 : Real) * lRegSpeedSq S T (alpha n) s :=
    Eventually.of_forall fun s ↦ mul_nonneg (by norm_num)
      (lRegSpeedSq_nonneg (I := I) S T (alpha n) s)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ :=
    htmono Fin.castSucc_lt_succ.le
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← ht0]
    exact htmono (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htlast]
    exact htmono (Fin.le_last _)
  have hdiff (i : Fin m) (n : Nat) :
      ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
        MDifferentiableAt (modelWithCornersSelf Real Real) I
          (alpha n) (t i.castSucc + r) := by
    have hmem : ∀ᵐ r ∂timeMeasure (partitionIntervalLength t i),
        r ∈ Ioo (0 : Real) (partitionIntervalLength t i) := by
      unfold timeMeasure
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hmem] with r hr
    change r ∈ Ioo (0 : Real) (t i.succ - t i.castSucc) at hr
    have hsIoo : t i.castSucc + r ∈ Ioo a b := by
      constructor <;> linarith [hr.1, hr.2, hleft i, hright i]
    have hsWithin := halpha n (t i.castSucc + r) ⟨hsIoo.1.le, hsIoo.2.le⟩
    exact (hsWithin.contMDiffAt
      (Icc_mem_nhds hsIoo.1 hsIoo.2)).mdifferentiableAt (by norm_num)
  have hpiece (i : Fin m) (n : Nat) :
      (∫ s in t i.castSucc..t i.succ,
        (1 / 2 : Real) * lRegSpeedSq S T (alpha n) s) ≤ B := by
    exact (intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
      (hnonneg n) (hhalfInt n)).trans (hhalf n)
  have hchart (i : Fin m) (n : Nat) :
      (∫ r in (0 : Real)..partitionIntervalLength t i, (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
        ((u i n).deriv r)) ≤ B := by
    change (∫ r in (0 : Real)..t i.succ - t i.castSucc, (1 / 2 : Real) * inner Real
      (chartGramOp (I := I) S.family (p i)
        (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
      ((u i n).deriv r)) ≤ B
    have heq :=
      (lKinetic_local S T (alpha n) (p i) (t i.castSucc) (t i.succ)
        (hseg i) (u i n) (hsrc i n) (hrep i n) (hdiff i n)).symm
    rw [show (∫ r in (0 : Real)..t i.succ - t i.castSucc,
        (1 / 2 : Real) * inner Real
        (chartGramOp (I := I) S.family (p i)
          (T - (t i.castSucc + r) ^ 2, (u i n).toFun r) ((u i n).deriv r))
        ((u i n).deriv r)) =
        ∫ s in t i.castSucc..t i.succ,
          (1 / 2 : Real) * lRegSpeedSq S T (alpha n) s by
      calc
        _ = ∫ r in (0 : Real)..t i.succ - t i.castSucc,
            inner Real
              (((1 / 2 : Real) • chartGramOp (I := I) S.family (p i)
                (T - (t i.castSucc + r) ^ 2, (u i n).toFun r))
                ((u i n).deriv r)) ((u i n).deriv r) := by
          apply intervalIntegral.integral_congr
          intro r _hr
          change (1 / 2 : Real) * inner Real
              ((chartGramOp (I := I) S.family (p i)
                (T - (t i.castSucc + r) ^ 2, (u i n).toFun r))
                ((u i n).deriv r)) ((u i n).deriv r) =
            inner Real ((1 / 2 : Real) •
              (chartGramOp (I := I) S.family (p i)
                (T - (t i.castSucc + r) ^ 2, (u i n).toFun r))
                ((u i n).deriv r)) ((u i n).deriv r)
          rw [real_inner_smul_left]
        _ = _ := by
          convert heq using 1 <;> rfl]
    exact hpiece i n
  have htimeCont (i : Fin m) : ContinuousOn
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (Icc (0 : Real) (partitionIntervalLength t i)) :=
    (continuous_const.sub ((continuous_const.add continuous_id).pow 2)).continuousOn
  have htimeReg (i : Fin m) : MapsTo
      (fun r : Real ↦ T - (t i.castSucc + r) ^ 2)
      (Icc (0 : Real) (partitionIntervalLength t i)) D.regular := by
    intro r hr
    change r ∈ Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    apply hreg (t i.castSucc + r)
    exact ⟨by linarith [hleft i, hr.1], by linarith [hr.2, hright i]⟩
  exact chartH1_fin (I := I) hMet p
    (fun i ↦ partitionIntervalLength t i) (fun i ↦ sub_nonneg.mpr (hseg i))
    (fun i r ↦ T - (t i.castSucc + r) ^ 2) htimeCont htimeReg
    Kcoord hKc hKchart u (fun _ ↦ B) huK hchart

theorem lRmAction_subseq
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b A : Real) (ha : 0 ≤ a) (hab : a ≤ b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    (alpha : Nat → Real → M)
    (halpha : ∀ n, ContMDiffOn (modelWithCornersSelf Real Real) I 1
      (alpha n) (Icc a b))
    (hE : ∀ n, IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) (Icc a b))
    (hkin : ∀ n, IntervalIntegrable (lRegSpeedSq S T (alpha n)) volume a b)
    (hLag : ∀ n, IntervalIntegrable (lRegLag S T (alpha n)) volume a b)
    (hact : ∀ n, lRegAction S T (alpha n) a b ≤ A)
    (x y : M) (hfixa : ∀ n, alpha n a = x) (hfixb : ∀ n, alpha n b = y) :
    ∃ (Cpt : Set M) (phi : Nat → Nat) (g : C(Icc a b, M)),
      IsCompact Cpt ∧ StrictMono phi ∧
        (∀ n (s : Icc a b), alpha (phi n) s.1 ∈ Cpt) ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ alpha (phi n) s.1) g atTop ∧
        g ⟨a, le_rfl, hab⟩ = x ∧ g ⟨b, hab, le_rfl⟩ = y := by
  classical
  let C : Real := -2 * b ^ 2 * rmFactor E K
  let Q : Real := Real.exp (2 * rmFactor E K * b ^ 2)
  let B : Real := Q * (2 * (A - C * (b - a)))
  let R : Real := Real.sqrt (b - a) * Real.sqrt B
  let Cpt : Set M :=
    {z : M | riemannianEDistOf (I := I) (S.base.metric T) x z ≤ ENNReal.ofReal R}
  have hb : 0 ≤ b := ha.trans hab
  have hQ : 0 ≤ Q := (Real.exp_pos _).le
  have henergy (n : Nat) :
      curveEnergy (I := I) (S.base.metric T) (alpha n) a b ≤ B := by
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
      (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      riemannianEDistOf (I := I) (S.base.metric T) (alpha n s) (alpha n t) ≤
        ENNReal.ofReal (Real.sqrt (t - s) * Real.sqrt B) := by
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
    have hsubE : curveEnergy (I := I) (S.base.metric T) (alpha n) s t ≤
        curveEnergy (I := I) (S.base.metric T) (alpha n) a b :=
      curveEnergy_mono (I := I) (S.base.metric T) has hst htb (hE n)
    exact edistOf_le_budget (I := I) (S.base.metric T) hst
      ((halpha n).mono hsub) ((hE n).mono_set hsub)
      (hsubE.trans (henergy n))
  have hCpt : IsCompact Cpt :=
    RiemannianMetricComplete.closedEBall_isCompact (I := I) hg x R
  have hval (n : Nat) (s : Icc a b) : alpha n s.1 ∈ Cpt := by
    have hdist := hriedist n (s := a) (t := s.1) le_rfl s.2.1 s.2.2
    have htime : Real.sqrt (s.1 - a) ≤ Real.sqrt (b - a) :=
      Real.sqrt_le_sqrt (by linarith [s.2.2])
    have hradius : Real.sqrt (s.1 - a) * Real.sqrt B ≤ R :=
      mul_le_mul_of_nonneg_right htime (Real.sqrt_nonneg B)
    rw [hfixa n] at hdist
    exact hdist.trans (ENNReal.ofReal_le_ofReal hradius)
  let f : Nat → C(Icc a b, M) := fun n ↦
    ⟨fun s ↦ alpha n s.1, (halpha n).continuousOn.domRestrict⟩
  have hmod : Tendsto (fun r : Real ↦ Real.sqrt r * Real.sqrt B) (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun r : Real ↦ Real.sqrt r * Real.sqrt B) :=
      Real.continuous_sqrt.mul continuous_const
    simpa only [Real.sqrt_zero, zero_mul] using hcont.tendsto (0 : Real)
  have hequi : Equicontinuous (fun n ↦ (f n : Icc a b → M)) := by
    have hunif : UniformEquicontinuous (fun n ↦ (f n : Icc a b → M)) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      obtain ⟨ρ, hρ, htoDist⟩ :=
        dist_lt_riedist_cpt (I := I) (S.base.metric T) Cpt hCpt hε
      obtain ⟨δ, hδ, hmodδ⟩ := Metric.tendsto_nhds_nhds.1 hmod ρ hρ
      refine ⟨δ, hδ, ?_⟩
      intro s t hst n
      have hsmall : Real.sqrt (dist s t) * Real.sqrt B < ρ := by
        have h := hmodδ (x := dist s t) (by simpa using hst)
        simpa only [Real.dist_eq, sub_zero,
          abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] using h
      have hofReal : ENNReal.ofReal (Real.sqrt (dist s t) * Real.sqrt B) <
          ENNReal.ofReal ρ := (ENNReal.ofReal_lt_ofReal_iff hρ).2 hsmall
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
        change dist (alpha n s.1) (alpha n t.1) < ε
        rw [dist_comm]
        exact hout
    exact hunif.equicontinuous
  obtain ⟨phi, g, hphi, hconv⟩ :=
    DifferentialGeometry.Analysis.arzela_subseq_cpt Cpt hCpt f hval
      hequi
  refine ⟨Cpt, phi, g, hCpt, hphi, (fun n s ↦ hval (phi n) s), ?_, ?_, ?_⟩
  · change TendstoUniformly (fun n s ↦ alpha (phi n) s.1)
      (fun s ↦ g s) atTop
    exact hconv
  · have hlim := hconv.tendsto_at (⟨a, le_rfl, hab⟩ : Icc a b)
    change Tendsto (fun n ↦ alpha (phi n) a) atTop
      (nhds (g ⟨a, le_rfl, hab⟩)) at hlim
    have hlim' : Tendsto (fun _ : Nat ↦ x) atTop
        (nhds (g ⟨a, le_rfl, hab⟩)) := by
      simpa only [hfixa] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds
  · have hlim := hconv.tendsto_at (⟨b, hab, le_rfl⟩ : Icc a b)
    change Tendsto (fun n ↦ alpha (phi n) b) atTop
      (nhds (g ⟨b, hab, le_rfl⟩)) at hlim
    have hlim' : Tendsto (fun _ : Nat ↦ y) atTop
        (nhds (g ⟨b, hab, le_rfl⟩)) := by
      simpa only [hfixb] using hlim
    exact tendsto_nhds_unique hlim' tendsto_const_nhds

theorem lRmAction_chart_lsc
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
    (x y : M) (hfixa : ∀ n, alpha n a = x) (hfixb : ∀ n, alpha n b = y) :
    ∃ (m : Nat) (t : Fin (m + 1) → Real) (p : Fin m → M)
      (chi : Nat → Nat) (gamma : Real → M)
      (uLim : (i : Fin m) → timeH1 E (partitionIntervalLength t i)),
      StrictMono chi ∧ Continuous gamma ∧ gamma a = x ∧ gamma b = y ∧
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
  obtain ⟨Cpt, phi0, g, hCpt, hphi0, hval0, hconv0, hga, hgb⟩ :=
    lRmAction_subseq (I := I) S hS K T hg a b A ha hab hreg hRm
      alpha halpha hE hkin hLag hact x y hfixa hfixb
  let gamma : Real → M := IccExtend hab g
  have hgamma : Continuous gamma := by
    dsimp only [gamma, IccExtend, Function.comp_apply]
    exact g.continuous.comp continuous_projIcc
  have hgamma_eq (s : Icc a b) : gamma s.1 = g s :=
    IccExtend_of_mem hab g s.2
  have hga' : gamma a = x := by
    rw [hgamma_eq ⟨a, le_rfl, hab⟩]
    exact hga
  have hgb' : gamma b = y := by
    rw [hgamma_eq ⟨b, hab, le_rfl⟩]
    exact hgb
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
  exact ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga', hgb', hconv,
    htmono, ht0, htlast, hgammaSrc, hlimRep, hlsc⟩

theorem exists_lRegMin_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b : Real) (ha : 0 ≤ a) (hab : a < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    ∃ gamma : Real → M,
      Continuous gamma ∧
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma (Icc a b) ∧
      gamma a = x ∧ gamma b = y ∧
      lRegAction S T gamma a b = lRegCostC1 S T a b x y ∧
      (∀ delta : Real → M,
          ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
          delta a = x → delta b = y →
          lRegAction S T gamma a b ≤ lRegAction S T delta a b) ∧
      ∀ s ∈ Ioo a b,
        MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  classical
  let costs : Set Real := {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r}
  have hcosts : costs.Nonempty :=
    ⟨lRegAction S T alpha0 a b, alpha0, halpha0, h0a, h0b, rfl⟩
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hb : 0 ≤ b := ha.trans hab.le
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  let C : Real := -2 * b ^ 2 * rmFactor E K
  have hcosts_bdd : BddBelow costs := by
    refine ⟨C * (b - a), ?_⟩
    intro r hr
    obtain ⟨alpha, halpha, _ha, _hb, rfl⟩ := hr
    have hkin := lRegSpeed_int_c1 (I := I) S hMet hSc T a b hab.le alpha
      halpha.contMDiffOn hregBack
    have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab.le alpha
      halpha.contMDiffOn hregBack
    have hbound := lRegKinetic_le (I := I) S T alpha a b
      (lRegAction S T alpha a b) C hab.le
      (fun s hs ↦ lRegPot_lower_rm (I := I) S K T b hb hRm s
        ⟨ha.trans hs.1, hs.2⟩ (alpha s))
      hkin hLag le_rfl
    have hnonneg : 0 ≤ ∫ s in a..b, lRegSpeedSq S T alpha s := by
      apply intervalIntegral.integral_nonneg hab.le
      intro s _hs
      exact lRegSpeedSq_nonneg (I := I) S T alpha s
    linarith
  obtain ⟨v, _hvanti, hvlim, hv⟩ :=
    exists_seq_tendsto_sInf hcosts hcosts_bdd
  choose alpha halpha hfixa hfixb hval using fun n ↦ hv n
  have hE (n : Nat) : IntegrableOn (fun s ↦
      (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s)) (Icc a b) :=
    lRegRef_int_c1 (I := I) (S.base.metric T) (alpha n) (halpha n) a b
  have hkin (n : Nat) : IntervalIntegrable
      (lRegSpeedSq S T (alpha n)) volume a b :=
    lRegSpeed_int_c1 (I := I) S hMet hSc T a b hab.le (alpha n)
      (halpha n).contMDiffOn hregBack
  have hLag (n : Nat) : IntervalIntegrable
      (lRegLag S T (alpha n)) volume a b :=
    lRegLag_int_c1 (I := I) S hMet hSc T a b hab.le (alpha n)
      (halpha n).contMDiffOn hregBack
  have hact (n : Nat) : lRegAction S T (alpha n) a b ≤ v 0 := by
    rw [hval n]
    exact _hvanti (Nat.zero_le n)
  obtain ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga, hgb, _hconv,
      htmono, ht0, htlast, hsrc, hrep, hlsc⟩ :=
    lRmAction_chart_lsc (I := I) S hS K T hg a b (v 0) ha hab.le hreg hRm
      alpha (fun n ↦ (halpha n).contMDiffOn) hE hkin hLag hact
      x y hfixa hfixb
  have hsubseq : Tendsto
      (fun n ↦ lRegAction S T (alpha (chi n)) a b) atTop
      (nhds (sInf costs)) := by
    have h := hvlim.comp hchi.tendsto_atTop
    rw [show (fun n ↦ lRegAction S T (alpha (chi n)) a b) =
      (fun n ↦ v (chi n)) by
      funext n
      exact hval (chi n)]
    exact h
  have hupper : lRegAction S T gamma a b ≤ sInf costs := by
    have hraw : lRegAction S T gamma a b ≤
        liminf (fun n ↦ lRegAction S T (alpha (chi n)) a b) atTop := by
      rw [lRegAction_chart S hMet hSc T a b t htmono ht0 htlast p gamma
        uLim hsrc hrep hregBack]
      exact hlsc
    simpa only [hsubseq.liminf_eq] using hraw
  obtain ⟨beta, _u, hbeta, hbetaa, hbetab, _hsrcBeta, _hrepBeta, _hu,
      _hunifBeta, hbetaAct⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p gamma
      uLim hsrc hrep hregBack
  have hlower : sInf costs ≤ lRegAction S T gamma a b := by
    apply ge_of_tendsto hbetaAct
    exact Eventually.of_forall fun n ↦ csInf_le hcosts_bdd
      ⟨beta n, hbeta n, (hbetaa n).trans hga, (hbetab n).trans hgb, rfl⟩
  have heq : lRegAction S T gamma a b = lRegCostC1 S T a b x y := by
    change lRegAction S T gamma a b = sInf costs
    exact le_antisymm hupper hlower
  have hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = x → delta b = y →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b := by
    intro delta hdelta hda hdb
    rw [heq]
    change sInf costs ≤ lRegAction S T delta a b
    exact csInf_le hcosts_bdd ⟨delta, hdelta, hda, hdb, rfl⟩
  have hmin' : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b := by
    intro delta hdelta hda hdb
    exact hmin delta hdelta (hda.trans hga) (hdb.trans hgb)
  have hc1 : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a b) :=
    lMinCurve_c1 (I := I) S hS T a b hab t htmono ht0 htlast p gamma
      hgamma uLim hsrc hrep hregBack hmin'
  have hsol : ∀ s ∈ Ioo a b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I gamma s ∧
        DifferentiableAt Real
          (chartRepAt (I := I) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s) s ∧
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
            (fun r ↦ lVelocity (I := I) gamma r) s =
          lRegAccel S T s (gamma s) (lVelocity (I := I) gamma s) :=
    lMinCurve_reg (I := I) S hS T a b hab t htmono ht0 htlast p gamma
      hgamma uLim hsrc hrep hregBack hmin'
  exact ⟨gamma, hgamma, hc1, hga, hgb, heq, hmin, hsol⟩

theorem exists_lMin_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (tau : Real) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y) :
    ∃ (alpha : Real → M) (Z : TangentSpace I x),
      IsLRegCurveOn S T alpha (Icc (0 : Real) (Real.sqrt tau)) x Z ∧
        Set.EqOn (lRegCurve S T x Z) alpha
            (Icc (0 : Real) (Real.sqrt tau)) ∧
          (Z, tau) ∈ lExpPosDom S T x ∧
            lExp S T x Z tau = y ∧
              alpha (Real.sqrt tau) = y ∧
              lLength S T (sqrtReparam alpha) 0 tau = lCost S T x y tau ∧
              ∀ delta : Real → M,
                ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
                delta 0 = x → delta (Real.sqrt tau) = y →
                lLength S T (sqrtReparam alpha) 0 tau ≤
                  lLength S T (sqrtReparam delta) 0 tau := by
  have hsqrt : 0 < Real.sqrt tau := Real.sqrt_pos.2 htau
  have hsq : (Real.sqrt tau) ^ 2 = tau := Real.sq_sqrt htau.le
  have hregSq : Icc (T - (Real.sqrt tau) ^ 2) T ⊆ D.regular := by
    simpa only [hsq] using hreg
  have hRmSq : ∀ q ∈ Icc (T - (Real.sqrt tau) ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K := by
    simpa only [hsq] using hRm
  obtain ⟨gamma, hgamma, hc1, hga, hgb, hcost, hmin, hsol⟩ :=
    exists_lRegMin_rm (I := I) S hS K T hg 0 (Real.sqrt tau) le_rfl
      hsqrt hregSq hRmSq x y alpha0 halpha0 h00 h0t
  have hregBack : ∀ s ∈ Icc (0 : Real) (Real.sqrt tau),
      T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hregSq
    have hs2 : s ^ 2 ≤ (Real.sqrt tau) ^ 2 :=
      (sq_le_sq₀ hs.1 (Real.sqrt_nonneg tau)).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  obtain ⟨alpha, halpha, e, he, halphaSol⟩ :=
    exists_lRegExtOn (I := I) S hS T 0 (Real.sqrt tau) hsqrt gamma hc1
      hregBack hsol
  have ha0 : alpha 0 = x :=
    (halpha ⟨le_rfl, hsqrt.le⟩).trans hga
  have hat : alpha (Real.sqrt tau) = y :=
    (halpha ⟨hsqrt.le, le_rfl⟩).trans hgb
  have haction : lRegAction S T alpha 0 (Real.sqrt tau) =
      lRegAction S T gamma 0 (Real.sqrt tau) := by
    apply lRegAction_congr (I := I) S T alpha gamma 0 (Real.sqrt tau)
    intro s hs
    have hs' : s ∈ Ioo (0 : Real) (Real.sqrt tau) := by
      simpa only [uIoo_of_le hsqrt.le] using hs
    exact halpha ⟨hs'.1.le, hs'.2.le⟩
  let Z : TangentSpace I x := (2 : Real)⁻¹ • lVelocity (I := I) alpha 0
  have hvel : lVelocity (I := I) alpha 0 = 2 • Z := by
    have hreal : lVelocity (I := I) alpha 0 = (2 : Real) • Z := by
      simp only [Z]
      exact (smul_inv_smul₀ (by norm_num : (2 : Real) ≠ 0) _).symm
    exact hreal.trans (Nat.cast_smul_eq_nsmul Real 2 Z)
  have hcurve : IsLRegCurveOn S T alpha
      (Icc (0 : Real) (Real.sqrt tau)) x Z :=
    ⟨ha0, hvel, fun s hs ↦ halphaSol s
      ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
  have hcurveOpen : IsLRegCurveOn S T alpha
      (Ioo (-e) (Real.sqrt tau + e)) x Z := by
    refine ⟨ha0, hvel, ?_⟩
    simpa only [zero_sub] using halphaSol
  have h0Open : (0 : Real) ∈ Ioo (-e) (Real.sqrt tau + e) := by
    constructor <;> linarith
  have htOpen : Real.sqrt tau ∈ Ioo (-e) (Real.sqrt tau + e) := by
    constructor <;> linarith
  have htDom : Real.sqrt tau ∈ lRegDomain S T x Z :=
    ⟨alpha, Ioo (-e) (Real.sqrt tau + e), isOpen_Ioo, isPreconnected_Ioo,
      h0Open, htOpen, hcurveOpen⟩
  have hmax : Set.EqOn (lRegCurve S T x Z) alpha
      (Icc (0 : Real) (Real.sqrt tau)) :=
    lRegCurve_eqIcc S hS T (Real.sqrt tau) e hsqrt.le he hcurveOpen
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x Z tau).2 ⟨htau, htau.le, htDom⟩
  have hExp : lExp S T x Z tau = y := by
    have heq := hmax ⟨Real.sqrt_nonneg tau, le_rfl⟩
    have heq' : lExp S T x Z tau = alpha (Real.sqrt tau) := by
      simpa only [lExp] using heq
    exact heq'.trans hat
  refine ⟨alpha, Z, hcurve, hmax, hdom, hExp, hat, ?_, ?_⟩
  · calc
      lLength S T (sqrtReparam alpha) 0 tau =
          lRegAction S T alpha 0 (Real.sqrt tau) :=
        lLength_sqrt (I := I) S T alpha tau htau.le
      _ = lRegCostC1 S T 0 (Real.sqrt tau) x y := haction.trans hcost
      _ = lCost S T x y tau :=
        (lCost_eq_reg (I := I) S T x y tau htau.le).symm
  · intro delta hdelta hd0 hdt
    rw [lLength_sqrt (I := I) S T alpha tau htau.le,
      lLength_sqrt (I := I) S T delta tau htau.le]
    rw [haction]
    exact hmin delta hdelta hd0 hdt

theorem exists_lMinVec_rm
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : Real)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (tau : Real) (htau : 0 < tau)
    (hreg : Icc (T - tau) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - tau) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h00 : alpha0 0 = x) (h0t : alpha0 (Real.sqrt tau) = y) :
    ∃ Z : TangentSpace I x,
      (Z, tau) ∈ lMinDomain S T x ∧ lExp S T x Z tau = y := by
  obtain ⟨alpha, Z, _hcurve, hmax, hdom, hExp, _hend, hcost, _hmin⟩ :=
    exists_lMin_rm (I := I) S hS K T hg tau htau hreg hRm
      x y alpha0 halpha0 h00 h0t
  refine ⟨Z, (mem_lMinDomain S T x Z tau).2 ⟨hdom, ?_⟩, hExp⟩
  calc
    lLength S T (fun r : Real ↦ lExp S T x Z r) 0 tau =
        lRegAction S T (lRegCurve S T x Z) 0 (Real.sqrt tau) := by
      change lLength S T
          (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) 0 tau = _
      rw [show (fun r : Real ↦ lRegCurve S T x Z (Real.sqrt r)) =
        sqrtReparam (lRegCurve S T x Z) by rfl]
      exact lLength_sqrt (I := I) S T (lRegCurve S T x Z) tau htau.le
    _ = lRegAction S T alpha 0 (Real.sqrt tau) := by
      apply lRegAction_congr (I := I) S T
      intro s hs
      have hs' : s ∈ Ioo (0 : Real) (Real.sqrt tau) := by
        simpa only [uIoo_of_le (Real.sqrt_nonneg tau)] using hs
      exact hmax ⟨hs'.1.le, hs'.2.le⟩
    _ = lLength S T (sqrtReparam alpha) 0 tau :=
      (lLength_sqrt (I := I) S T alpha tau htau.le).symm
    _ = lCost S T x y tau := hcost
    _ = lCost S T x (lExp S T x Z tau) tau := by rw [hExp]

end DifferentialGeometry.PDE.RicciFlow.Perelman
