import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionCapstone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionC1
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ActionDensity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Function MeasureTheory Set
open scoped ContDiff Manifold Topology Interval

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

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem c1_ref_int
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
          (TotalSpace.mk' Real s (1 : Real) :
            TangentBundle (modelWithCornersSelf Real Real) Real)) :=
      (contMDiff_vectorSpace_iff_contDiff
        (V := fun _ : Real ↦ (1 : Real))).mpr contDiff_const
    exact (ht.comp hone).congr fun _ ↦ rfl
  let cg : Bundle.ContinuousRiemannianMetric E
      (TangentSpace I : M → Type _) := gRef.toContinuousRiemannianMetric
  let rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
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

def lRegCostC1
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (x y : M) : Real :=
  sInf {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r}

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
theorem lRegCostC1_le_bdd
    (S : SolutionOn (I := I) (M := M) D) (T a b : Real) (x y : M)
    (hbdd : BddBelow {r : Real | ∃ alpha : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
        alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r})
    (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lRegCostC1 S T a b x y ≤ lRegAction S T alpha a b := by
  unfold lRegCostC1
  exact csInf_le hbdd ⟨alpha, halpha, hxa, hyb, rfl⟩

omit [NeZero (Module.finrank Real E)] in
theorem exists_lRegMinC1
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real)
    (a b : Real) (hab : a ≤ b)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha0 : Real → M)
    (halpha0 : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    ∃ (gamma : Real → M) (m : Nat) (t : Fin (m + 1) → Real)
      (p : Fin m → M) (uLim : (i : Fin m) → timeH1 E (lSegLen t i))
      (beta : Nat → Real → M)
      (u : (i : Fin m) → Nat → timeH1 E (lSegLen t i)),
      Continuous gamma ∧ gamma a = x ∧ gamma b = y ∧
        lRegAction S T gamma a b = lRegCostC1 S T a b x y ∧
        (∀ delta : Real → M,
          ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
          delta a = x → delta b = y →
          lRegAction S T gamma a b ≤ lRegAction S T delta a b) ∧
        Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
        (∀ i, MapsTo gamma (Icc (t i.castSucc) (t i.succ))
          (chartAt H (p i)).source) ∧
        (∀ i, EqOn (uLim i).toFun
        (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
          (Icc (0 : Real) (lSegLen t i))) ∧
        (∀ n, ContMDiff (modelWithCornersSelf Real Real) I 1 (beta n)) ∧
        (∀ n, beta n a = x) ∧ (∀ n, beta n b = y) ∧
        (∀ i n, MapsTo (beta n) (Icc (t i.castSucc) (t i.succ))
          (chartAt H (p i)).source) ∧
        (∀ i n, EqOn (u i n).toFun
          (fun r ↦ extChartAt I (p i) (beta n (t i.castSucc + r)))
          (Icc (0 : Real) (lSegLen t i))) ∧
        (∀ i, Tendsto (u i) atTop (nhds (uLim i))) ∧
        TendstoUniformly
          (fun n (s : Icc a b) ↦ beta n s.1)
          (fun s ↦ gamma s.1) atTop ∧
        Tendsto (fun n ↦ lRegAction S T (beta n) a b) atTop
          (nhds (lRegAction S T gamma a b)) := by
  classical
  let costs : Set Real := {r : Real | ∃ alpha : Real → M,
    ContMDiff (modelWithCornersSelf Real Real) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegAction S T alpha a b = r}
  have hcosts : costs.Nonempty := by
    refine ⟨lRegAction S T alpha0 a b, alpha0, halpha0, h0a, h0b, rfl⟩
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  let gRef : SmoothRiemannianMetric I M := S.family.metric t0
  obtain ⟨c, C, hc, hcoerc⟩ :=
    lAction_consts (I := I) S hS T t0 t1 gRef a b hab htime hback
  have hcosts_bdd : BddBelow costs := by
    refine ⟨C * (b - a), ?_⟩
    intro r hr
    obtain ⟨alpha, halpha, _ha, _hb, rfl⟩ := hr
    have hE := c1_ref_int (I := I) gRef alpha halpha a b
    have href : IntervalIntegrable
        (fun s ↦ gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s)) volume a b := by
      apply IntegrableOn.intervalIntegrable
      simpa only [uIcc_of_le hab] using hE
    have hLag := lRegLag_int_c1 (I := I) S hMet hSc T a b hab alpha
      halpha.contMDiffOn hreg
    have hkin : 0 ≤ ∫ s in a..b, (c / 2) *
        gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s) := by
      apply intervalIntegral.integral_nonneg hab
      intro s _hs
      apply mul_nonneg (div_nonneg hc.le (by norm_num))
      let vel := lVelocity (I := I) alpha s
      rcases eq_or_ne vel 0 with hvel | hvel
      · simp only [vel, hvel, map_zero]
        exact le_rfl
      · exact (gRef.pos (alpha s) vel hvel).le
    linarith [hcoerc alpha href hLag]
  obtain ⟨v, _hvanti, hvlim, hv⟩ :=
    exists_seq_tendsto_sInf hcosts hcosts_bdd
  choose alpha halpha hfixa hfixb hval using fun n ↦ hv n
  have hE (n : Nat) : IntegrableOn
      (fun s ↦ gRef.inner (alpha n s) (lVelocity (I := I) (alpha n) s)
        (lVelocity (I := I) (alpha n) s)) (Icc a b) :=
    c1_ref_int (I := I) gRef (alpha n) (halpha n) a b
  have hLag (n : Nat) : IntervalIntegrable
      (lRegLag S T (alpha n)) volume a b :=
    lRegLag_int_c1 (I := I) S hMet hSc T a b hab (alpha n)
      (halpha n).contMDiffOn hreg
  have hact (n : Nat) : lRegAction S T (alpha n) a b ≤ v 0 := by
    rw [hval n]
    exact _hvanti (Nat.zero_le n)
  obtain ⟨m, t, p, chi, gamma, uLim, hchi, hgamma, hga, hgb, _hconv,
      htmono, ht0, htlast, hsrc, hrep, hlsc⟩ :=
    lAction_chart_lsc (I := I) S hS T t0 t1 gRef a b (v 0) hab htime
      hback alpha (fun n ↦ (halpha n).contMDiffOn) hE hLag hact
      x y hfixa hfixb hreg
  have hsubseq : Tendsto
      (fun n ↦ lRegAction S T (alpha (chi n)) a b) atTop
      (nhds (sInf costs)) := by
    have h := hvlim.comp hchi.tendsto_atTop
    exact h.congr' (Eventually.of_forall fun n ↦ (hval (chi n)).symm)
  have hupper : lRegAction S T gamma a b ≤ sInf costs := by
    have hraw : lRegAction S T gamma a b ≤
        liminf (fun n ↦ lRegAction S T (alpha (chi n)) a b) atTop := by
      rw [lRegAction_chart S hMet hSc T a b t htmono ht0 htlast p gamma
        uLim hsrc hrep hreg]
      exact hlsc
    simpa only [hsubseq.liminf_eq] using hraw
  obtain ⟨beta, u, hbeta, hbetaa, hbetab, hsrcBeta, hrepBeta, hu,
      hunifBeta, hbetaAct⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p gamma
      uLim hsrc hrep hreg
  have hlower : sInf costs ≤ lRegAction S T gamma a b := by
    apply ge_of_tendsto hbetaAct
    exact Eventually.of_forall fun n ↦ csInf_le hcosts_bdd
      ⟨beta n, hbeta n, (hbetaa n).trans hga, (hbetab n).trans hgb, rfl⟩
  have heq : lRegAction S T gamma a b = lRegCostC1 S T a b x y := by
    change lRegAction S T gamma a b = sInf costs
    exact le_antisymm hupper hlower
  refine ⟨gamma, m, t, p, uLim, beta, u, hgamma, hga, hgb, heq, ?_, htmono,
    ht0, htlast, hsrc, hrep, hbeta, ?_, ?_, hsrcBeta, hrepBeta, hu,
    hunifBeta, hbetaAct⟩
  · intro delta hdelta hda hdb
    rw [heq]
    change sInf costs ≤ lRegAction S T delta a b
    exact csInf_le hcosts_bdd ⟨delta, hdelta, hda, hdb, rfl⟩
  · intro n
    simpa only [hga] using hbetaa n
  · intro n
    simpa only [hgb] using hbetab n

omit [NeZero (Module.finrank Real E)] in
theorem lRegCostC1_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (a b : Real) (hab : a ≤ b)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I 1 alpha)
    (hxa : alpha a = x) (hyb : alpha b = y)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular) :
    lRegCostC1 S T a b x y ≤ lRegAction S T alpha a b := by
  obtain ⟨gamma, _, _, _, _, _, _, _, _, _, heq, hmin, _⟩ :=
    exists_lRegMinC1 (I := I) S hS T t0 t1 a b hab htime hback x y alpha
      halpha hxa hyb hreg
  rw [← heq]
  exact hmin alpha halpha hxa hyb

end DifferentialGeometry.PDE.RicciFlow.Perelman
