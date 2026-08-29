import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MinMaxCompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.RayGlobalize
import DifferentialGeometry.Geometry.Operator.MetricFamilyGram

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRegSpeed_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) {B : Real}
    (hB : 0 < B) (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular) :
    ∃ Q : Real, 0 ≤ Q ∧
      ∀ s ∈ Set.Icc (0 : Real) B, s ∈ lRegDomain S T x Z →
        lRegSpeedSq S T (lRegCurve S T x Z) s ≤ Q := by
  let alpha : Real → M := lRegCurve S T x Z
  have hback : ∀ s ∈ Set.Icc (0 : Real) B,
      T - s ^ 2 ∈ Set.Icc (T - B ^ 2) T := by
    intro s hs
    have hsq : s ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hs.1 hB.le).2 hs.2
    exact ⟨sub_le_sub_left hsq T, sub_le_self T (sq_nonneg s)⟩
  obtain ⟨Cg, hCg, hgrad⟩ := lGrad_bound (I := I) S hS hslab
  obtain ⟨Cr, hCr, hric⟩ := lRicci_bound (I := I) S hS hslab
  let C : Real := max Cg Cr
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg Cr)
  let k : Real := 1 + 2 * C * B ^ 2 + 4 * C * B
  let d : Real := 1 + 2 * C * B ^ 2
  have hk : 0 < k := by
    dsimp only [k]
    nlinarith [mul_nonneg hC (sq_nonneg B), mul_nonneg hC hB.le]
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_nonneg hC (sq_nonneg B)]
  let U0 : Real := lRegSpeedSq S T alpha 0
  let Q : Real := Real.exp (k * B) * (U0 + 1)
  have hU0 : 0 ≤ U0 := lRegSpeedSq_nonneg (I := I) S T alpha 0
  have hQ : 0 ≤ Q :=
    mul_nonneg (Real.exp_pos _).le (add_nonneg hU0 zero_le_one)
  refine ⟨Q, hQ, ?_⟩
  intro s hs hsdom
  by_cases hs0 : s = 0
  · subst s
    have hexp : 1 ≤ Real.exp (k * B) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg hk.le hB.le)
    calc
      lRegSpeedSq S T alpha 0 = U0 := rfl
      _ ≤ 1 * (U0 + 1) := by linarith
      _ ≤ Real.exp (k * B) * (U0 + 1) :=
        mul_le_mul_of_nonneg_right hexp (add_nonneg hU0 zero_le_one)
      _ = Q := rfl
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have halpha : IsLRegCurveOn S T alpha (Set.Icc (0 : Real) s) x Z := by
      simpa only [alpha, Set.uIcc_of_le hspos.le] using
        lRegCurve_isReg (I := I) S hS T x Z hspos hsdom
    have hsub : Set.uIcc (0 : Real) s ⊆ Set.Icc (0 : Real) B := by
      simpa only [Set.uIcc_of_le hspos.le] using Set.Icc_subset_Icc_right hs.2
    have hgr := lRegSpeed_gron (I := I) S hS T halpha 0 s C B hC hB.le
      (fun _ hr ↦ by simpa only [Set.uIcc_of_le hspos.le] using hr)
      (fun r hr ↦ by
        have hrI := hsub hr
        rw [abs_of_nonneg hrI.1]
        exact hrI.2)
      (fun r hr ↦ by
        have h := hgrad (T - r ^ 2) (hback r (hsub hr)) (alpha r)
          (lVelocity (I := I) alpha r)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_left Cg Cr)
          (Real.sqrt_nonneg _)))
      (fun r hr ↦ by
        have h := hric (T - r ^ 2) (hback r (hsub hr)) (alpha r)
          (lVelocity (I := I) alpha r)
        exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg Cr)
          (lRegSpeedSq_nonneg (I := I) S T alpha r)))
    have hratio : d / k ≤ 1 := by
      rw [div_le_one hk]
      dsimp only [d, k]
      nlinarith [mul_nonneg hC hB.le]
    have hdist : |s - 0| ≤ B := by
      rw [sub_zero, abs_of_nonneg hs.1]
      exact hs.2
    have hexp : Real.exp (k * |s - 0|) ≤ Real.exp (k * B) := by
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hdist hk.le)
    have hterm : 0 ≤ U0 + d / k :=
      add_nonneg hU0 (div_nonneg hd.le hk.le)
    calc
      lRegSpeedSq S T alpha s ≤
          Real.exp (k * |s - 0|) * (U0 + d / k) := by
        simpa only [alpha, U0, k, d] using hgr
      _ ≤ Real.exp (k * B) * (U0 + d / k) :=
        mul_le_mul_of_nonneg_right hexp hterm
      _ ≤ Real.exp (k * B) * (U0 + 1) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        simpa only [add_comm] using add_le_add_left hratio U0
      _ = Q := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegDomain_of_slab
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (x : M) (Z : TangentSpace I x) (B : Real)
    (hB : 0 ≤ B) (hslab : Set.Icc (T - B ^ 2) T ⊆ D.regular) :
    B ∈ lRegDomain S T x Z := by
  classical
  by_cases hB0 : B = 0
  · subst B
    apply zero_mem_lRegDomain (I := I) S hS T x Z
    apply hslab
    simp
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  let U : Set Real := lRegDomain S T x Z
  have hUopen : IsOpen U := lRegDomain_isOpen S T x Z
  have h0U : (0 : Real) ∈ U := by
    apply zero_mem_lRegDomain (I := I) S hS T x Z
    apply hslab
    simpa only [zero_pow, sub_zero] using
      (show T ∈ Set.Icc (T - B ^ 2) T from
        ⟨sub_le_self T (sq_nonneg B), le_rfl⟩)
  obtain ⟨Q, hQ, hspeed⟩ :=
    lRegSpeed_le (I := I) S hS T x Z hBpos hslab
  have hclosed : closure U ∩ Set.Icc (0 : Real) B ⊆ U := by
    rintro s ⟨hscl, hsIcc⟩
    by_cases hsU : s ∈ U
    · exact hsU
    have hspos : 0 < s := lt_of_le_of_ne hsIcc.1 (fun h ↦ hsU (h ▸ h0U))
    obtain ⟨t, htU, htlim⟩ := mem_closure_iff_seq_limit.mp hscl
    let gamma : Real → M := lRegCurve S T x Z
    obtain ⟨y, _hy, phi, hphi, hylim⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).tendsto_subseq
        (x := fun n ↦ gamma (t n)) (fun _ ↦ Set.mem_univ _)
    let tn : Nat → Real := fun n ↦ t (phi n)
    have htnU : ∀ n, tn n ∈ U := fun n ↦ htU (phi n)
    have htnlim : Tendsto tn atTop (nhds s) := by
      change Tendsto (t ∘ phi) atTop (nhds s)
      exact htlim.comp hphi.tendsto_atTop
    have hbaselim : Tendsto (fun n ↦ gamma (tn n)) atTop (nhds y) := by
      change Tendsto ((fun n ↦ gamma (t n)) ∘ phi) atTop (nhds y)
      exact hylim
    have htnlt : ∀ n, 0 ≤ tn n → tn n < s := by
      intro n hn0
      apply lt_of_not_ge
      intro hst
      have hnDom : tn n ∈ lRegDomain S T x Z := by
        simpa only [U] using htnU n
      exact hsU (show s ∈ U from by
        simpa only [U] using lRegDomain_seg S T x Z hnDom hsIcc.1 hst)
    have htnpos : ∀ᶠ n in atTop, 0 < tn n :=
      Filter.Tendsto.eventually_const_lt hspos htnlim
    have htnIcc : ∀ᶠ n in atTop, tn n ∈ Set.Icc (0 : Real) B := by
      filter_upwards [htnpos] with n hn
      exact ⟨hn.le, (htnlt n hn.le).le.trans hsIcc.2⟩
    have hySrc : y ∈ (chartAt H y).source := mem_chart_source H y
    have hyExt : y ∈ (extChartAt I y).source := by
      rw [extChartAt_source]
      exact hySrc
    have hyTarget : extChartAt I y y ∈ interior (extChartAt I y).target := by
      rw [(isOpen_extChartAt_target (I := I) y).interior_eq]
      exact (extChartAt I y).map_source hyExt
    obtain ⟨rho, hrho, hrhoSub⟩ :=
      Metric.isOpen_iff.mp isOpen_interior _ hyTarget
    let K : Set E := Metric.closedBall (extChartAt I y y) (rho / 2)
    have hKcompact : IsCompact K := isCompact_closedBall _ _
    have hKchart : K ⊆ interior (extChartAt I y).target := by
      intro z hz
      apply hrhoSub
      rw [Metric.mem_ball]
      have hz' : dist z (extChartAt I y y) ≤ rho / 2 := by
        simpa only [K, Metric.mem_closedBall, dist_comm] using hz
      linarith
    have hposlim : Tendsto (fun n ↦ extChartAt I y (gamma (tn n))) atTop
        (nhds (extChartAt I y y)) :=
      (continuousAt_extChartAt (I := I) y).tendsto.comp hbaselim
    have hposK : ∀ᶠ n in atTop, extChartAt I y (gamma (tn n)) ∈ K := by
      apply hposlim
      exact Metric.closedBall_mem_nhds _ (half_pos hrho)
    have hbaseSrc : ∀ᶠ n in atTop, gamma (tn n) ∈ (chartAt H y).source := by
      exact hbaselim ((chartAt H y).open_source.mem_nhds hySrc)
    have hmetricSmooth : MetricFamilySmoothOn (I := I) (M := M) D
        S.family.metric := hS.smoothMetric
    have htimeCompact : IsCompact (Set.Icc (T - B ^ 2) T) := isCompact_Icc
    obtain ⟨c, hc, hcLower⟩ :=
      chartGramOp_lower (E := E) (I := I) (M := M) (D := D)
        (G := S.family) hmetricSmooth (J := Set.Icc (T - B ^ 2) T)
        hslab htimeCompact y (K := K) hKchart hKcompact
    let R : Real := Real.sqrt (Q / c)
    have hR : 0 ≤ R := Real.sqrt_nonneg _
    let vel : Nat → E := fun n ↦
      trivToE (I := I) y (gamma (tn n))
        (lVelocity (I := I) gamma (tn n))
    have hvelR : ∀ᶠ n in atTop, ‖vel n‖ ≤ R := by
      filter_upwards [htnIcc, hposK, hbaseSrc] with n hn hpn hsrc
      have htime : T - tn n ^ 2 ∈ Set.Icc (T - B ^ 2) T := by
        have hsq : tn n ^ 2 ≤ B ^ 2 :=
          (sq_le_sq₀ hn.1 hB).2 hn.2
        exact ⟨sub_le_sub_left hsq T, sub_le_self T (sq_nonneg (tn n))⟩
      have hlow := hcLower
        (T - tn n ^ 2, extChartAt I y (gamma (tn n))) ⟨htime, hpn⟩ (vel n)
      have hbase : gamma (tn n) ∈
          (trivializationAt E (TangentSpace I) y).baseSet := by
        simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
      have hsrc' : gamma (tn n) ∈ (extChartAt I y).source := by
        simpa only [extChartAt_source] using hsrc
      have hsymm : (extChartAt I y).symm (extChartAt I y (gamma (tn n))) =
          gamma (tn n) := (extChartAt I y).left_inv hsrc'
      have htriv :
          Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) y (gamma (tn n)) (vel n) =
          lVelocity (I := I) gamma (tn n) := by
        change trivFromE (I := I) y (gamma (tn n))
          (trivToE (I := I) y (gamma (tn n))
            (lVelocity (I := I) gamma (tn n))) = _
        exact trivFromE_trivToE (I := I) y hbase _
      have hmetric : inner Real
          (chartGramOp (I := I) S.family y
            (T - tn n ^ 2, extChartAt I y (gamma (tn n))) (vel n)) (vel n) =
          lRegSpeedSq S T gamma (tn n) := by
        calc
          _ = (S.family.metric (T - tn n ^ 2)).inner
              ((extChartAt I y).symm (extChartAt I y (gamma (tn n))))
              (Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
                (I := I) (M := M) y
                ((extChartAt I y).symm (extChartAt I y (gamma (tn n)))) (vel n))
              (Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
                (I := I) (M := M) y
                ((extChartAt I y).symm (extChartAt I y (gamma (tn n)))) (vel n)) :=
            chartGramOp_inner (I := I) S.family y _ _ _
          _ = (S.family.metric (T - tn n ^ 2)).inner (gamma (tn n))
              (lVelocity (I := I) gamma (tn n))
              (lVelocity (I := I) gamma (tn n)) := by rw [hsymm, htriv]
          _ = lRegSpeedSq S T gamma (tn n) := by
            simp only [lRegSpeedSq, SolutionOn.family_metric]
      rw [hmetric] at hlow
      have hsq : ‖vel n‖ ^ 2 ≤ Q / c := by
        rw [le_div_iff₀ hc]
        simpa only [mul_comm] using hlow.trans (hspeed (tn n) hn (htnU n))
      have hsqrt := Real.sqrt_le_sqrt hsq
      simpa only [R, Real.sqrt_sq (norm_nonneg (vel n))] using hsqrt
    let C : Set (Real × (E × E)) :=
      Set.Icc (0 : Real) B ×ˢ (K ×ˢ Metric.closedBall (0 : E) R)
    have hCcompact : IsCompact C :=
      isCompact_Icc.prod (hKcompact.prod (isCompact_closedBall _ _))
    have hCreg : C ⊆ {p : Real × (E × E) |
        T - p.1 ^ 2 ∈ D.regular ∧
          p.2.1 ∈ interior (extChartAt I y).target} := by
      rintro p ⟨hpTime, hpPos, _hpVel⟩
      have hsq : p.1 ^ 2 ≤ B ^ 2 :=
        (sq_le_sq₀ hpTime.1 hB).2 hpTime.2
      exact ⟨hslab ⟨sub_le_sub_left hsq T,
        sub_le_self T (sq_nonneg p.1)⟩, hKchart hpPos⟩
    obtain ⟨epsilon, hepsilon, hflow⟩ :=
      exists_lPhaseComp S hS T y hCcompact hCreg
    have hseedC : ∀ᶠ n in atTop,
        (tn n, extChartAt I y (gamma (tn n)), vel n) ∈ C := by
      filter_upwards [htnIcc, hposK, hvelR] with n hn hp hv
      exact ⟨hn, hp, by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩
    have hnear : ∀ᶠ n in atTop, s ∈ Set.Ioo (tn n - epsilon) (tn n + epsilon) := by
      have hnhds : Set.Ioo (s - epsilon) (s + epsilon) ∈ nhds s :=
        Ioo_mem_nhds (sub_lt_self s hepsilon) (lt_add_of_pos_right s hepsilon)
      filter_upwards [htnlim hnhds] with n hn
      exact ⟨by linarith [hn.2], by linarith [hn.1]⟩
    obtain ⟨n, hnC, hnNear, hnSrc⟩ :=
      (hseedC.and (hnear.and hbaseSrc)).exists
    let t0 : Real := tn n
    have ht0U : t0 ∈ U := htnU n
    obtain ⟨curve, J, hJopen, hJconn, h0J, ht0J, hcurve⟩ := ht0U
    obtain ⟨V, hVopen, hZV, L, hLopen, hLconn, h0L, ht0L,
      alpha, halpha, hcurves⟩ :=
      lRegFamily_extend (I := I) S hS T hJopen hJconn h0J ht0J hcurve
    have hEq : Set.EqOn (lRegCurve S T x Z) (fun r ↦ alpha (Z, r)) L :=
      lRegCurve_eqOn S hS T hLopen hLconn h0L (hcurves Z hZV)
    have hpos : alpha (Z, t0) = gamma t0 := (hEq ht0L).symm
    have heqGerm : (fun r ↦ alpha (Z, r)) =ᶠ[nhds t0] gamma :=
      Filter.EventuallyEq.symm <| hEq.eventuallyEq_of_mem (hLopen.mem_nhds ht0L)
    have hvel : lVelocity (I := I) (fun r ↦ alpha (Z, r)) t0 =
        lVelocity (I := I) gamma t0 := by
      unfold lVelocity
      rw [heqGerm.mfderiv_eq (I := modelWithCornersSelf Real Real) (I' := I)]
      rfl
    have ht0src : alpha (Z, t0) ∈ (chartAt H y).source := by
      rw [hpos]
      exact hnSrc
    have hseedEq :
        (extChartAt I y (alpha (Z, t0)),
          fderiv Real (fun r : Real ↦ extChartAt I y (alpha (Z, r))) t0
            (1 : Real)) =
        (extChartAt I y (gamma t0), vel n) := by
      apply Prod.ext
      · rw [hpos]
      · have hseedVel := lPhaseSeed_vel (I := I) y
          ((hcurves Z hZV).2.2 t0 ht0L).2.1 ht0src
        calc
          fderiv Real (fun r : Real ↦ extChartAt I y (alpha (Z, r))) t0
              (1 : Real) =
            trivToE (I := I) y (alpha (Z, t0))
              (lVelocity (I := I) (fun r ↦ alpha (Z, r)) t0) := hseedVel
          _ = vel n := by rw [hpos, hvel]
    obtain ⟨O, hOopen, hseedO, Phi, hPhi0, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
      hflow (tn n, extChartAt I y (gamma (tn n)), vel n) hnC
    have hseedO' :
        (extChartAt I y (alpha (Z, t0)),
          fderiv Real (fun r : Real ↦ extChartAt I y (alpha (Z, r))) t0
            (1 : Real)) ∈ O := by
      rw [hseedEq]
      exact hseedO
    obtain ⟨W, hWopen, hZW, _hWV, beta, hbeta, hbetaCurves⟩ :=
      lRegFamily_step_of (I := I) S hS T x y hVopen hZV
        hLopen hLconn h0L ht0L halpha hcurves ht0src epsilon hepsilon
        hOopen hseedO' Phi hPhi0 hPhiSmooth hPhiDeriv hPhiMap
    have ht0I : t0 ∈ Set.Ioo (t0 - epsilon) (t0 + epsilon) :=
      ⟨by linarith, by linarith⟩
    exact ⟨fun r ↦ beta (Z, r), L ∪ Set.Ioo (t0 - epsilon) (t0 + epsilon),
      hLopen.union isOpen_Ioo,
      hLconn.union t0 ht0L ht0I isPreconnected_Ioo,
      Or.inl h0L, Or.inr hnNear, hbetaCurves Z hZW⟩
  have hall : Set.Icc (0 : Real) B ⊆ U :=
    isPreconnected_Icc.subset_of_closure_inter_subset hUopen
      ⟨0, ⟨⟨le_rfl, hB⟩, h0U⟩⟩ hclosed
  exact hall ⟨hB, le_rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
