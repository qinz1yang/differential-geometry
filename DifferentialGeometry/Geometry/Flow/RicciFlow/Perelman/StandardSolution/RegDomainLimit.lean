import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.InitialVectorBound
import DifferentialGeometry.Geometry.Operator.Family.Gram.Basic
import Mathlib.Topology.Sequences
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs

set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem original_domain_step_of_phase
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (Z : TangentSpace I x) (p : M) {s₀ s epsilon : ℝ}
    (hs₀ : s₀ ∈ lRegularizedDomain S T x Z)
    (hsrc : lRegularizedCurve S T x Z s₀ ∈ (chartAt H p).source)
    (hepsilon : 0 < epsilon)
    (hs : s ∈ Ioo (s₀ - epsilon) (s₀ + epsilon))
    {U : Set (E × E)} (hUopen : IsOpen U)
    (hseed :
      (extChartAt I p (lRegularizedCurve S T x Z s₀),
        trivToE (I := I) p (lRegularizedCurve S T x Z s₀)
          (lVelocity (I := I) (lRegularizedCurve S T x Z) s₀)) ∈ U)
    (Phi : (E × E) × ℝ → E × E)
    (hPhi₀ : ∀ z ∈ U, Phi (z, s₀) = z)
    (hPhiSmooth : ContDiffOn ℝ ∞ Phi
      (U ×ˢ Ioo (s₀ - epsilon) (s₀ + epsilon)))
    (hPhiDeriv : ∀ z ∈ U, ∀ r ∈ Ioo (s₀ - epsilon) (s₀ + epsilon),
      HasDerivAt (fun q ↦ Phi (z, q))
        (lPhaseField S T p r (Phi (z, r))) r)
    (hPhiMap : MapsTo (fun q : (E × E) × ℝ ↦ (q.2, Phi q))
      (U ×ˢ Ioo (s₀ - epsilon) (s₀ + epsilon))
      {q : ℝ × (E × E) | T - q.1 ^ 2 ∈ D.regular ∧
        q.2.1 ∈ interior (extChartAt I p).target}) :
    s ∈ lRegularizedDomain S T x Z := by
  obtain ⟨J, hJopen, hJconn, h₀J, hs₀J, hchosen⟩ :=
    lRegularizedChosen_spec S T x Z hs₀
  obtain ⟨V, hVopen, hZV, L, hLopen, hLconn, h₀L, hs₀L,
      alpha, halpha, hcurves⟩ :=
    lRegularizedFamily_extend S hS T hJopen hJconn h₀J hs₀J hchosen
  have heq : EqOn (lRegularizedCurve S T x Z) (fun r ↦ alpha (Z, r)) L :=
    lRegularizedCurve_eqOn S hS T hLopen hLconn h₀L (hcurves Z hZV)
  have hpos : alpha (Z, s₀) = lRegularizedCurve S T x Z s₀ :=
    (heq hs₀L).symm
  have hgerm : (fun r ↦ alpha (Z, r)) =ᶠ[𝓝 s₀] lRegularizedCurve S T x Z :=
    (heq.eventuallyEq_of_mem (hLopen.mem_nhds hs₀L)).symm
  have hvel : lVelocity (I := I) (fun r ↦ alpha (Z, r)) s₀ =
      lVelocity (I := I) (lRegularizedCurve S T x Z) s₀ := by
    unfold lVelocity
    rw [hgerm.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := I)]
    rfl
  have hsrc' : alpha (Z, s₀) ∈ (chartAt H p).source := by
    rw [hpos]
    exact hsrc
  have hseed' :
      (extChartAt I p (alpha (Z, s₀)),
        fderiv ℝ (fun r : ℝ ↦ extChartAt I p (alpha (Z, r))) s₀ 1) ∈ U := by
    have hseedVel := lPhaseSeed_velocity (I := I) p
      ((hcurves Z hZV).2.2 s₀ hs₀L).2.1 hsrc'
    rw [hseedVel, hpos, hvel]
    exact hseed
  obtain ⟨W, _hWopen, hZW, _hWV, beta, _hbeta, hbetaCurves⟩ :=
    lRegularizedFamily_step_of S hS T x p hVopen hZV
      hLopen hLconn h₀L hs₀L halpha hcurves hsrc'
      epsilon hepsilon hUopen hseed' Phi hPhi₀ hPhiSmooth hPhiDeriv hPhiMap
  have hs₀I : s₀ ∈ Ioo (s₀ - epsilon) (s₀ + epsilon) :=
    ⟨sub_lt_self _ hepsilon, lt_add_of_pos_right _ hepsilon⟩
  exact ⟨fun r ↦ beta (Z, r), L ∪ Ioo (s₀ - epsilon) (s₀ + epsilon),
    hLopen.union isOpen_Ioo,
    hLconn.union s₀ hs₀L hs₀I isPreconnected_Ioo,
    Or.inl h₀L, Or.inr hs, hbetaCurves Z hZW⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem original_domain_of_compact_range_speed
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ) (x : M)
    (Z : TangentSpace I x) (b : ℝ) (hb : 0 < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (Cpt : Set M) (hCpt : IsCompact Cpt)
    (hrange : ∀ s ∈ Icc (0 : ℝ) b,
      s ∈ lRegularizedDomain S T x Z → lRegularizedCurve S T x Z s ∈ Cpt)
    (Q : ℝ)
    (hspeed : ∀ s ∈ Icc (0 : ℝ) b,
      s ∈ lRegularizedDomain S T x Z →
        lRegularizedSpeedSq S T (lRegularizedCurve S T x Z) s ≤ Q) :
    b ∈ lRegularizedDomain S T x Z := by
  classical
  let U := lRegularizedDomain S T x Z
  let gamma := lRegularizedCurve S T x Z
  have hUopen : IsOpen U := lRegularizedDomain_isOpen S T x Z
  have h₀U : (0 : ℝ) ∈ U := by
    apply zero_mem_lRegularizedDomain S hS T x Z
    exact hreg ⟨sub_le_self T (sq_nonneg b), le_rfl⟩
  have hback (r : ℝ) (hr : r ∈ Icc (0 : ℝ) b) :
      T - r ^ 2 ∈ Icc (T - b ^ 2) T := by
    have hr2 := (sq_le_sq₀ hr.1 hb.le).2 hr.2
    exact ⟨sub_le_sub_left hr2 T, sub_le_self T (sq_nonneg r)⟩
  have hclosed : closure U ∩ Icc (0 : ℝ) b ⊆ U := by
    rintro s ⟨hscl, hsIcc⟩
    by_cases hsU : s ∈ U
    · exact hsU
    have hspos : 0 < s :=
      lt_of_le_of_ne hsIcc.1 (fun h ↦ hsU (h ▸ h₀U))
    have hsclpos : s ∈ closure (U ∩ Ioi (0 : ℝ)) :=
      isOpen_Ioi.closure_inter ⟨hscl, hspos⟩
    obtain ⟨t, ht, htlim⟩ := mem_closure_iff_seq_limit.mp hsclpos
    have htlt (n : ℕ) : t n < s := by
      apply lt_of_not_ge
      intro hst
      exact hsU (lRegularizedDomain_segment S T x Z (ht n).1 hsIcc.1 hst)
    have htIcc (n : ℕ) : t n ∈ Icc (0 : ℝ) b :=
      ⟨(ht n).2.le, (htlt n).le.trans hsIcc.2⟩
    obtain ⟨p, _hpCpt, phi, hphi, hplim⟩ :=
      hCpt.tendsto_subseq
        (x := fun n ↦ gamma (t n))
        (fun n ↦ hrange (t n) (htIcc n) (ht n).1)
    let tn : ℕ → ℝ := fun n ↦ t (phi n)
    have htnU (n : ℕ) : tn n ∈ U := (ht (phi n)).1
    have htnIcc (n : ℕ) : tn n ∈ Icc (0 : ℝ) b := htIcc (phi n)
    have htnlim : Tendsto tn atTop (𝓝 s) :=
      htlim.comp hphi.tendsto_atTop
    have hbaselim : Tendsto (fun n ↦ gamma (tn n)) atTop (𝓝 p) :=
      hplim
    have hpSrc : p ∈ (chartAt H p).source := mem_chart_source H p
    have hpExt : p ∈ (extChartAt I p).source := by
      simpa only [extChartAt_source] using hpSrc
    have hpTarget : extChartAt I p p ∈ interior (extChartAt I p).target := by
      rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
      exact (extChartAt I p).map_source hpExt
    obtain ⟨rho, hrho, hrhoSub⟩ :=
      Metric.isOpen_iff.mp isOpen_interior _ hpTarget
    let Kchart : Set E := Metric.closedBall (extChartAt I p p) (rho / 2)
    have hKcompact : IsCompact Kchart := isCompact_closedBall _ _
    have hKchart : Kchart ⊆ interior (extChartAt I p).target := by
      intro z hz
      apply hrhoSub
      have hz' : dist z (extChartAt I p p) ≤ rho / 2 := by
        simpa only [Kchart, Metric.mem_closedBall, dist_comm] using hz
      exact hz'.trans_lt (half_lt_self hrho)
    have hposlim : Tendsto
        (fun n ↦ extChartAt I p (gamma (tn n))) atTop
        (𝓝 (extChartAt I p p)) :=
      (continuousAt_extChartAt (I := I) p).tendsto.comp hbaselim
    have hposK : ∀ᶠ n in atTop, extChartAt I p (gamma (tn n)) ∈ Kchart :=
      hposlim (Metric.closedBall_mem_nhds _ (half_pos hrho))
    have hbaseSrc : ∀ᶠ n in atTop, gamma (tn n) ∈ (chartAt H p).source :=
      hbaselim ((chartAt H p).open_source.mem_nhds hpSrc)
    obtain ⟨c, hc, hcLower⟩ :=
      chartGramOp_lower (I := I) (G := S.family) hS.smoothMetric
        hreg isCompact_Icc p hKchart hKcompact
    let R : ℝ := Real.sqrt (Q / c)
    let vel : ℕ → E := fun n ↦
      trivToE (I := I) p (gamma (tn n))
        (lVelocity (I := I) gamma (tn n))
    have hvelR : ∀ᶠ n in atTop, ‖vel n‖ ≤ R := by
      filter_upwards [hposK, hbaseSrc] with n hpn hsrc
      have hlow := hcLower
        (T - tn n ^ 2, extChartAt I p (gamma (tn n)))
        ⟨hback (tn n) (htnIcc n), hpn⟩ (vel n)
      have hbase : gamma (tn n) ∈
          (trivializationAt E (TangentSpace I) p).baseSet := by
        simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
      have hsrc' : gamma (tn n) ∈ (extChartAt I p).source := by
        simpa only [extChartAt_source] using hsrc
      have htriv :
          Tensor.Tensor0SRiemannian.chartTrivializationLinearMapSymm
            (I := I) (M := M) p (gamma (tn n)) (vel n) =
          lVelocity (I := I) gamma (tn n) := by
        change trivFromE (I := I) p (gamma (tn n))
          (trivToE (I := I) p (gamma (tn n))
            (lVelocity (I := I) gamma (tn n))) = _
        exact trivFromE_trivToE (I := I) p hbase _
      rw [chartGramOp_inner, (extChartAt I p).left_inv hsrc', htriv] at hlow
      have hlow' : c * ‖vel n‖ ^ 2 ≤ lRegularizedSpeedSq S T gamma (tn n) := by
        simpa only [lRegularizedSpeedSq, SolutionOn.family_metric] using hlow
      have hsq : ‖vel n‖ ^ 2 ≤ Q / c := by
        apply (le_div_iff₀ hc).2
        simpa only [mul_comm] using
          hlow'.trans (hspeed (tn n) (htnIcc n) (htnU n))
      simpa only [R, Real.sqrt_sq (norm_nonneg (vel n))] using
        Real.sqrt_le_sqrt hsq
    let PhaseCpt : Set (ℝ × (E × E)) :=
      Icc (0 : ℝ) b ×ˢ (Kchart ×ˢ Metric.closedBall (0 : E) R)
    have hPhaseCompact : IsCompact PhaseCpt :=
      isCompact_Icc.prod (hKcompact.prod (isCompact_closedBall _ _))
    have hPhaseReg : PhaseCpt ⊆
        {q : ℝ × (E × E) | T - q.1 ^ 2 ∈ D.regular ∧
          q.2.1 ∈ interior (extChartAt I p).target} := by
      rintro q ⟨hqTime, hqPos, _hqVel⟩
      exact ⟨hreg (hback q.1 hqTime), hKchart hqPos⟩
    obtain ⟨epsilon, hepsilon, hflow⟩ :=
      exists_lPhaseComp S hS T p hPhaseCompact hPhaseReg
    have hseedC : ∀ᶠ n in atTop,
        (tn n, extChartAt I p (gamma (tn n)), vel n) ∈ PhaseCpt := by
      filter_upwards [hposK, hvelR] with n hp hv
      exact ⟨htnIcc n, hp,
        by simpa only [Metric.mem_closedBall, dist_zero_right] using hv⟩
    have hnear : ∀ᶠ n in atTop,
        s ∈ Ioo (tn n - epsilon) (tn n + epsilon) := by
      have hnhds : Ioo (s - epsilon) (s + epsilon) ∈ 𝓝 s :=
        Ioo_mem_nhds (sub_lt_self _ hepsilon) (lt_add_of_pos_right _ hepsilon)
      filter_upwards [htnlim hnhds] with n hn
      exact ⟨by linarith [hn.2], by linarith [hn.1]⟩
    obtain ⟨n, hnC, hnNear, hnSrc⟩ :=
      (hseedC.and (hnear.and hbaseSrc)).exists
    obtain ⟨O, hOopen, hseedO, Phi, hPhi₀, hPhiSmooth, hPhiDeriv, hPhiMap⟩ :=
      hflow (tn n, extChartAt I p (gamma (tn n)), vel n) hnC
    exact original_domain_step_of_phase S hS T x Z p (htnU n)
      hnSrc hepsilon hnNear hOopen hseedO
      Phi hPhi₀ hPhiSmooth hPhiDeriv hPhiMap
  have hall : Icc (0 : ℝ) b ⊆ U :=
    isPreconnected_Icc.subset_of_closure_inter_subset hUopen
      ⟨0, ⟨⟨le_rfl, hb.le⟩, h₀U⟩⟩ hclosed
  exact hall ⟨hb.le, le_rfl⟩

variable [NeZero (Module.finrank ℝ E)]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegDomain_lim_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (K T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M) (b A : ℝ) (hb : 0 < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ t ∈ Icc (T - b ^ 2) T, ∀ y : M,
      normSq0S (I := I) (S.base.metric t) y 4
        (S.base.rm04 t y) ≤ K)
    {Z : ℕ → TangentSpace I x} {Z₀ : TangentSpace I x}
    (hdom : ∀ n, b ∈ lRegularizedDomain S T x (Z n))
    (hact : ∀ n, lRegularizedAction S T (lRegularizedCurve S T x (Z n)) 0 b ≤ A)
    (hZ : Tendsto Z atTop (𝓝 Z₀)) :
    b ∈ lRegularizedDomain S T x Z₀ := by
  classical
  let alpha : ℕ → ℝ → M := fun n ↦ lRegularizedCurve S T x (Z n)
  let gamma : ℝ → M := lRegularizedCurve S T x Z₀
  have hback (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ Icc (T - b ^ 2) T := by
    have hs2 := (sq_le_sq₀ hs.1 hb.le).2 hs.2
    exact ⟨sub_le_sub_left hs2 T, sub_le_self T (sq_nonneg s)⟩
  have hclock (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b) :
      T - s ^ 2 ∈ D.regular := hreg (hback s hs)
  have hcurve (n : ℕ) :
      IsLRegularizedCurveOn S T (alpha n) (Icc (0 : ℝ) b) x (Z n) := by
    simpa only [alpha, uIcc_of_le hb.le] using
      lRegularizedCurve_isLRegularizedCurveOn S hS T x (Z n) hb (hdom n)
  have hc1 (n : ℕ) :
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 (alpha n) (Icc (0 : ℝ) b) :=
    lRegularizedCurve_c1On S hS T x (Z n) (hdom n)
  have hE (n : ℕ) : MeasureTheory.IntegrableOn
      (fun s ↦ (S.base.metric T).inner (alpha n s)
        (lVelocity (I := I) (alpha n) s) (lVelocity (I := I) (alpha n) s))
      (Icc (0 : ℝ) b) :=
    lRegCurve_reference_integrable (S.base.metric T) (hcurve n)
  have hkin (n : ℕ) :
      IntervalIntegrable (lRegularizedSpeedSq S T (alpha n)) MeasureTheory.volume 0 b :=
    intervalIntegrable_lRegularizedSpeedSq_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  have hLag (n : ℕ) :
      IntervalIntegrable (lRegularizedLagrangian S T (alpha n)) MeasureTheory.volume 0 b :=
    intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one S hS.smoothMetric ⟨hS.scalarCont⟩
      T 0 b hb.le (alpha n) (hc1 n) hclock
  obtain ⟨Cpt, hCpt, himage⟩ :=
    lRegularizedRanges_of_rm S hS K T hg alpha x 0 b A
      (by norm_num) hb.le hreg hRm
      (fun n ↦ by simp only [alpha, lRegularizedCurve_zero])
      hc1 hE hkin hLag (fun n ↦ hact n)
  have hpartial (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b)
      (hsdom : s ∈ lRegularizedDomain S T x Z₀) : gamma s ∈ Cpt := by
    have hlim : Tendsto (fun n ↦ alpha n s) atTop (𝓝 (gamma s)) :=
      (lRegularizedCurve_smooth S hS T x hsdom).continuousAt.tendsto.comp
        (hZ.prodMk_nhds tendsto_const_nhds)
    exact hCpt.isClosed.mem_of_tendsto hlim
      (Eventually.of_forall fun n ↦ himage n ⟨s, hs, rfl⟩)
  obtain ⟨Cg, hCg, hgrad⟩ :=
    lScalarGradient_bound_on_compact S hS hreg hCpt
  let P : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  let C : ℝ := max Cg P
  have hC : 0 ≤ C := hCg.trans (le_max_left Cg P)
  have hquad := twoTensorQuadBound_of_solutions (I := I)
    (fun _ : ℕ ↦ S) univ (T - b ^ 2) T K
    (fun _ t ht y _ ↦ hRm t ht y)
  have hgradRay (r : ℝ) (hr : r ∈ Icc (0 : ℝ) b)
      (hrdom : r ∈ lRegularizedDomain S T x Z₀) :
      |(S.base.metric (T - r ^ 2)).inner (gamma r)
          (gradientFun (I := I) (S.base.metric (T - r ^ 2))
            (S.scalar (T - r ^ 2)) (gamma r))
          (lVelocity (I := I) gamma r)| ≤
        C * Real.sqrt (lRegularizedSpeedSq S T gamma r) := by
    have h := hgrad (T - r ^ 2) (hback r hr) (gamma r)
      (hpartial r hr hrdom) (lVelocity (I := I) gamma r)
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_max_left Cg P) (Real.sqrt_nonneg _))
  have hricRay (r : ℝ) (hr : r ∈ Icc (0 : ℝ) b) :
      |S.ricciAt (T - r ^ 2) (gamma r)
          (vec2 (lVelocity (I := I) gamma r) (lVelocity (I := I) gamma r))| ≤
        C * lRegularizedSpeedSq S T gamma r := by
    have h := hquad.2 0 (T - r ^ 2) (hback r hr)
      (gamma r) (mem_univ _) (lVelocity (I := I) gamma r)
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right Cg P)
      (lRegularizedSpeedSq_nonneg S T gamma r))
  let k : ℝ := 1 + 2 * C * b ^ 2 + 4 * C * b
  let d : ℝ := 1 + 2 * C * b ^ 2
  have hk : 0 < k := by
    dsimp only [k]
    nlinarith [mul_nonneg hC (sq_nonneg b), mul_nonneg hC hb.le]
  have hd : 0 < d := by
    dsimp only [d]
    nlinarith [mul_nonneg hC (sq_nonneg b)]
  let U₀ : ℝ := lRegularizedSpeedSq S T gamma 0
  have hU₀ : 0 ≤ U₀ := lRegularizedSpeedSq_nonneg S T gamma 0
  have hterm : 0 ≤ U₀ + d / k := add_nonneg hU₀ (div_nonneg hd.le hk.le)
  let Q : ℝ := Real.exp (k * b) * (U₀ + d / k)
  have hspeed (s : ℝ) (hs : s ∈ Icc (0 : ℝ) b)
      (hsdom : s ∈ lRegularizedDomain S T x Z₀) :
      lRegularizedSpeedSq S T gamma s ≤ Q := by
    by_cases hs₀ : s = 0
    · subst s
      have hExp : 1 ≤ Real.exp (k * b) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonneg hk.le hb.le)
      calc
        lRegularizedSpeedSq S T gamma 0 = U₀ := rfl
        _ ≤ U₀ + d / k := le_add_of_nonneg_right (div_nonneg hd.le hk.le)
        _ = 1 * (U₀ + d / k) := by ring
        _ ≤ Real.exp (k * b) * (U₀ + d / k) :=
          mul_le_mul_of_nonneg_right hExp hterm
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs₀)
      have hsub : uIcc (0 : ℝ) s ⊆ Icc (0 : ℝ) b := by
        simpa only [uIcc_of_le hspos.le] using
          (Icc_subset_Icc_right hs.2 : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) b)
      have hgr := lRegularizedSpeedSq_le_of_gradient_ricci_bounds S hS T
        (lRegularizedCurve_isLRegularizedCurveOn S hS T x Z₀ hspos hsdom)
        0 s C C b hC hC
        (fun _ hr ↦ hr)
        (fun r hr ↦ by
          rw [abs_of_nonneg (hsub hr).1]
          exact (hsub hr).2)
        (fun r hr ↦ by
          have hr' : r ∈ Icc (0 : ℝ) s := by
            simpa only [uIcc_of_le hspos.le] using hr
          exact hgradRay r (hsub hr)
            (lRegularizedDomain_segment S T x Z₀ hsdom hr'.1 hr'.2))
        (fun r hr ↦ hricRay r (hsub hr))
      have hExp : Real.exp (k * s) ≤ Real.exp (k * b) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hk.le)
      calc
        lRegularizedSpeedSq S T gamma s ≤ Real.exp (k * s) * (U₀ + d / k) := by
          simpa only [gamma, U₀, k, d, sub_zero, abs_of_nonneg hs.1] using hgr
        _ ≤ Real.exp (k * b) * (U₀ + d / k) :=
          mul_le_mul_of_nonneg_right hExp hterm
  exact original_domain_of_compact_range_speed S hS T x Z₀ b hb hreg
    Cpt hCpt hpartial Q hspeed

end DifferentialGeometry.PDE.RicciFlow

end
