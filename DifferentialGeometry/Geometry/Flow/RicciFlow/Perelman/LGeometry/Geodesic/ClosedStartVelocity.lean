import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.WindowSolutionMap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge
import DifferentialGeometry.Geometry.Metric.Comparison.CompactLowerBound
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection (trivToE trivFromE_trivToE)
open DifferentialGeometry.Geometry.Operator (gradientFun inner_gradientFun)

section ChartLowerBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_pos_mul_norm_sq_le_chart_inner_of_contMDiffOn
    {g : ℝ → SmoothRiemannianMetric I M} {A : Set ℝ}
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (A ×ˢ (univ : Set M)))
    {J : Set ℝ} (hJ : J ⊆ A) (hJc : IsCompact J) (α : M) {K : Set E}
    (hK : K ⊆ (extChartAt I α).target) (hKc : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ p ∈ J ×ˢ K, ∀ v : E,
      c * ‖v‖ ^ 2 ≤ (g p.1).inner ((extChartAt I α).symm p.2)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm p.2) v)
        ((trivializationAt E (TangentSpace I) α).symmL ℝ ((extChartAt I α).symm p.2) v) := by
  classical
  let e := trivializationAt E (TangentSpace I) α
  let b : ℝ × E → M := fun p => (extChartAt I α).symm p.2
  let B : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] ℝ) α (b p) α (b p) ((g p.1).inner (b p))
  have hb (p : ℝ × E) (hp : p ∈ J ×ˢ K) : b p ∈ e.baseSet := by
    have hs := (extChartAt I α).map_target (hK hp.2)
    rwa [extChartAt_source] at hs
  have hBeval (p : ℝ × E) (hp : p ∈ J ×ˢ K) (v w : E) :
      B p v w = (g p.1).inner (b p) (e.symmL ℝ (b p) v) (e.symmL ℝ (b p) w) := by
    dsimp only [B]
    have hR : b p ∈ (trivializationAt ℝ (Bundle.Trivial M ℝ) α).baseSet := mem_univ _
    rw [inCoordinates_apply_eq₂ (𝕜 := ℝ)
      (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := TangentSpace I) (E₂ := TangentSpace I) (E₃ := Bundle.Trivial M ℝ)
      (x₀ := α) (x := b p) (ϕ := (g p.1).inner (b p)) (v := v) (w := w)
      (hb p hp) (hb p hp) hR]
    rw [(trivializationAt ℝ (Bundle.Trivial M ℝ) α).coe_linearMapAt_of_mem hR]
    simp only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e (hb p hp) v,
      ← Bundle.Trivialization.symmL_apply (R := ℝ) e (hb p hp) w]
  have hB : ContinuousOn B (J ×ˢ K) := by
    intro p hp
    let em := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) α
    have hbc : ContinuousWithinAt b (J ×ˢ K) p :=
      ((continuousOn_extChartAt_symm (I := I) α).comp continuousOn_snd
        (fun _ hq => hK hq.2)) p hp
    have hmc : ContinuousWithinAt (fun q : ℝ × E =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b q) ((g q.1).inner (b q))) (J ×ˢ K) p := by
      have h1 := hg.continuousOn (p.1, b p) ⟨hJ hp.1, mem_univ _⟩
      have h2 : ContinuousWithinAt (fun q : ℝ × E => (q.1, b q)) (J ×ˢ K) p :=
        continuousWithinAt_fst.prodMk hbc
      exact ContinuousWithinAt.comp (x := p) (f := fun q : ℝ × E => (q.1, b q)) h1 h2
        (fun q hq => ⟨hJ hq.1, mem_univ _⟩)
    have hsrc : (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (b p) ((g p.1).inner (b p))) ∈
        em.source := by
      simpa only [em, e, Trivialization.mem_source, hom_trivializationAt_baseSet,
        TangentBundle.trivializationAt_baseSet, Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.trivialization_baseSet, mem_inter_iff, mem_univ, and_true, and_self]
        using hb p hp
    have hc := em.toOpenPartialHomeomorph.continuousAt hsrc
    have hcoord : ContinuousWithinAt (fun q : ℝ × E => em
        (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b q) ((g q.1).inner (b q)))) (J ×ˢ K) p :=
      hc.comp_continuousWithinAt (f := fun q : ℝ × E =>
        TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun y : M => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
          (b q) ((g q.1).inner (b q))) hmc
    exact hcoord.snd
  have hpos : ∀ p ∈ J ×ˢ K, ∀ v : E, v ≠ 0 → 0 < B p v v := by
    intro p hp v hv
    rw [hBeval p hp]
    apply (g p.1).pos
    intro hz
    have hleft := e.continuousLinearMapAt_symmL (R := ℝ) (hb p hp) v
    rw [hz, map_zero] at hleft
    exact hv hleft.symm
  obtain ⟨c, hc, hbound⟩ :=
    exists_pos_mul_norm_sq_le_bilinear_of_isCompact (hJc.prod hKc) B hB hpos
  exact ⟨c, hc, fun p hp v => by simpa only [hBeval p hp] using hbound p hp v⟩

end ChartLowerBound

section ClosedStart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_slab_gradient_ricci_bounds [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) {a b : ℝ}
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ G K : ℝ, 0 ≤ G ∧ 0 ≤ K ∧ ∀ t ∈ Icc a b, ∀ x : M, ∀ V : TangentSpace I x,
      |(S.base.metric t).inner x (gradientFun (S.base.metric t) (S.scalar t) x) V| ≤
          G * Real.sqrt ((S.base.metric t).inner x V V) ∧
        |S.ricciAt t x (vec2 V V)| ≤ K * (S.base.metric t).inner x V V := by
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I)
          (S.base.metric p.1) x₀ p.2 i j)
        (Icc a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := fun x₀ i j =>
    chartGramMatrix_joint_contMDiffOn S.base.metric (Icc a b) hmetric x₀ i j
  obtain ⟨BR, -, hric⟩ := ricciSlabSup (a := a) (c := b) S.base.metric S.base.metric hgram hgram
  obtain ⟨B1, -, hnab⟩ :=
    nablaKRmSlabSup (a := a) (c := b) S.base.metric S.base.metric hgram hgram 1
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt B1, (Module.finrank ℝ E : ℝ) * Real.sqrt BR,
    by positivity, by positivity, fun t ht x V => ⟨?_, ?_⟩⟩
  · have hfirst : CheegerGromovCompactness.curvDerivNormSq 1 (S.base.metric t) x ≤ B1 := by
      have heq := CheegerGromovCompactness.curvNormSq_eq
        (solutionOfMetric (D := RealTimeInterval.univ 0) S.base.metric) 1 t x
      change CheegerGromovCompactness.curvDerivNormSq 1 (S.base.metric t) x = _ at heq
      rw [heq]
      exact hnab t ht x
    have h := abs_scalarDifferential_le_of_curvature_jet S x hfirst V
    rw [inner_gradientFun, DifferentialGeometry.mvfderiv_real_eq_mfderiv]
    exact h
  · have h := tensor02_quadForm_abs_le_normSq0S (S.base.metric t) (S.ricciAt t x) V
    have hroot : Real.sqrt (Tensor0SBundle.normSq0S (S.base.metric t) x 2 (S.ricciAt t x)) ≤
        Real.sqrt BR := Real.sqrt_le_sqrt (hric t ht x)
    have hV := metric_inner_self_nonneg (S.base.metric t) x V
    refine h.trans ?_
    change (Module.finrank ℝ E : ℝ) * _ * _ ≤ _
    gcongr

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_lRegularizedSpeedSq_le_of_closedStart [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {a b : ℝ}
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M)))
    {T s₁ s₂ v : ℝ} (hs₁ : 0 < s₁) (hs₁₂ : s₁ < s₂) (hs₂v : s₂ < v) (hstart : T - v ^ 2 = a)
    (hs₂b : T - s₂ ^ 2 ≤ b) {γ : ℝ → M} (hγ : IsLRegularizedGeodesicOn S T γ (Ioo s₁ v)) :
    ∃ Q : ℝ, ∀ s ∈ Ico s₂ v, lRegularizedSpeedSq S T γ s ≤ Q := by
  obtain ⟨G, K, hG, hK, hbd⟩ := exists_slab_gradient_ricci_bounds S hmetric
  have hcurve : IsLRegularizedCurveOn S T γ (Ioo s₁ v) (γ 0)
      ((2 : ℝ)⁻¹ • lVelocity (I := I) γ 0) := by
    refine ⟨rfl, ?_, hγ⟩
    rw [two_nsmul, ← add_smul]
    norm_num
  set k : ℝ := 1 + 2 * G * v ^ 2 + 4 * K * v
  set d : ℝ := 1 + 2 * G * v ^ 2
  have hv : 0 < v := hs₁.trans (hs₁₂.trans hs₂v)
  have hkpos : 0 < k := by positivity
  have hdpos : 0 < d := by positivity
  refine ⟨Real.exp (k * v) * (lRegularizedSpeedSq S T γ s₂ + d / k), fun s hs => ?_⟩
  have hsub : uIcc s₂ s ⊆ Icc s₂ s := by rw [uIcc_of_le hs.1]
  have htime : ∀ r ∈ uIcc s₂ s, T - r ^ 2 ∈ Icc a b := by
    intro r hr
    have hr' := hsub hr
    have h0 : 0 ≤ s₂ := (hs₁.trans hs₁₂).le
    have h1 : s₂ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hr'.1 2
    have h2 : r ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (h0.trans hr'.1) (hr'.2.trans hs.2.le) 2
    constructor <;> linarith
  have h := lRegularizedSpeedSq_le_of_gradient_ricci_bounds S hS T hcurve s₂ s G K v hG hK
    (fun r hr => ⟨hs₁₂.trans_le (hsub hr).1, (hsub hr).2.trans_lt hs.2⟩)
    (fun r hr => by
      rw [abs_of_nonneg ((hs₁.trans hs₁₂).le.trans (hsub hr).1)]
      exact ((hsub hr).2.trans hs.2.le))
    (fun r hr => (hbd _ (htime r hr) _ _).1) (fun r hr => (hbd _ (htime r hr) _ _).2)
  refine h.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
    (add_nonneg (lRegularizedSpeedSq_nonneg S T γ s₂) (div_pos hdpos hkpos).le))
  refine mul_le_mul_of_nonneg_left ?_ hkpos.le
  rw [abs_of_nonneg (sub_nonneg.2 hs.1)]
  linarith [hs.2, hs₁.trans hs₁₂]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_tendsto_lVelocity_of_isLRegularizedGeodesicOn_of_closedStart [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) {a c : ℝ} (hac : a < c)
    (hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (S.base.metric q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Ico a c ×ˢ (univ : Set M)))
    {T s₁ v : ℝ} (hs₁ : 0 < s₁) (hs₁v : s₁ < v) (hstart : T - v ^ 2 = a)
    (hreg : ∀ s ∈ Ioo s₁ v, T - s ^ 2 ∈ D.regular) {γ : ℝ → M}
    (hγ : IsLRegularizedGeodesicOn S T γ (Ioo s₁ v)) :
    ∃ ξ : TangentBundle I M,
      Tendsto (fun s => (TotalSpace.mk' E (γ s) (lVelocity (I := I) γ s) : TangentBundle I M))
        (𝓝[<] v) (𝓝 ξ) := by
  classical
  have hv : 0 < v := hs₁.trans hs₁v
  set b : ℝ := (a + c) / 2 with hbdef
  have hab : a < b := by linarith
  have hbc : b < c := by linarith
  have hmetricb := hmetric.mono
    (prod_mono (fun t (ht : t ∈ Icc a b) => ⟨ht.1, ht.2.trans_lt hbc⟩) subset_rfl)
  have hev : ∀ᶠ s in 𝓝[<] v, s₁ < s ∧ T - s ^ 2 < b := by
    have hc : ContinuousAt (fun s : ℝ => T - s ^ 2) v := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (hc.eventually_lt continuousAt_const
      (by rw [hstart]; exact hab)), Ioo_mem_nhdsLT hs₁v] with s h hs
    exact ⟨hs.1, h⟩
  obtain ⟨s₂, ⟨hs₁₂, hs₂b⟩, hs₂v⟩ := (hev.and self_mem_nhdsWithin).exists
  have hs₂v' : s₂ < v := hs₂v
  obtain ⟨Q, hQ⟩ :=
    exists_lRegularizedSpeedSq_le_of_closedStart S hS hmetricb hs₁ hs₁₂ hs₂v' hstart hs₂b.le hγ
  have htime : ∀ s ∈ Ico s₂ v, T - s ^ 2 ∈ Icc a b := by
    intro s hs
    have h0 : 0 ≤ s₂ := (hs₁.trans hs₁₂).le
    have h1 : s₂ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ h0 hs.1 2
    have h2 : s ^ 2 ≤ v ^ 2 := pow_le_pow_left₀ (h0.trans hs.1) hs.2.le 2
    constructor <;> linarith
  obtain ⟨y, -, hy⟩ := isCompact_univ.exists_clusterPt (f := map γ (𝓝[<] v))
    (le_principal_iff.2 univ_mem)
  have hyExt : y ∈ (extChartAt I y).source := by
    rw [extChartAt_source]
    exact mem_chart_source H y
  have hyTarget : extChartAt I y y ∈ interior (extChartAt I y).target := by
    rw [(isOpen_extChartAt_target (I := I) y).interior_eq]
    exact (extChartAt I y).map_source hyExt
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp isOpen_interior _ hyTarget
  set Kc : Set E := Metric.closedBall (extChartAt I y y) (ρ / 2)
  have hKc : IsCompact Kc := isCompact_closedBall _ _
  have hKint : Kc ⊆ interior (extChartAt I y).target := by
    intro w hw
    apply hρsub
    rw [Metric.mem_ball]
    have hw' : dist w (extChartAt I y y) ≤ ρ / 2 := hw
    linarith
  obtain ⟨c₀, hc₀, hlow⟩ := exists_pos_mul_norm_sq_le_chart_inner_of_contMDiffOn hmetricb
    subset_rfl isCompact_Icc y (fun w hw => interior_subset (hKint hw)) hKc
  set R : ℝ := Real.sqrt (Q / c₀)
  let z : ℝ → E × E := fun s =>
    (extChartAt I y (γ s), trivToE (I := I) y (γ s) (lVelocity (I := I) γ s))
  let P : ℝ → Prop := fun s =>
    s ∈ Ico s₂ v ∧ γ s ∈ (chartAt H y).source ∧ extChartAt I y (γ s) ∈ Kc
  have hPz : ∀ s, P s → z s ∈ Kc ×ˢ Metric.closedBall (0 : E) R := by
    intro s hs
    refine ⟨hs.2.2, ?_⟩
    have hsrc' : γ s ∈ (extChartAt I y).source := by
      rw [extChartAt_source]
      exact hs.2.1
    have hbase : γ s ∈ (trivializationAt E (TangentSpace I) y).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact hs.2.1
    have hsymm : (extChartAt I y).symm (extChartAt I y (γ s)) = γ s :=
      (extChartAt I y).left_inv hsrc'
    have hl := hlow (T - s ^ 2, extChartAt I y (γ s)) ⟨htime s hs.1, hs.2.2⟩ (z s).2
    have htriv : (trivializationAt E (TangentSpace I) y).symmL ℝ (γ s) (z s).2 =
        lVelocity (I := I) γ s := trivFromE_trivToE (I := I) y hbase _
    have hmet : ∀ x : M, x = γ s → (S.base.metric (T - s ^ 2)).inner x
        ((trivializationAt E (TangentSpace I) y).symmL ℝ x (z s).2)
        ((trivializationAt E (TangentSpace I) y).symmL ℝ x (z s).2) =
        lRegularizedSpeedSq S T γ s := by
      rintro x rfl
      rw [htriv]
      rfl
    rw [hmet _ hsymm] at hl
    have hsq : ‖(z s).2‖ ^ 2 ≤ Q / c₀ := by
      rw [le_div_iff₀ hc₀]
      linarith [hQ s hs.1]
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa only [R, Real.sqrt_sq (norm_nonneg _)] using Real.sqrt_le_sqrt hsq
  have hN : (chartAt H y).source ∩ (extChartAt I y) ⁻¹' Metric.ball (extChartAt I y y) (ρ / 2) ∈
      𝓝 y := inter_mem ((chartAt H y).open_source.mem_nhds (mem_chart_source H y))
    ((continuousAt_extChartAt (I := I) y).preimage_mem_nhds
      (Metric.ball_mem_nhds _ (half_pos hρ)))
  have hfreq : ∃ᶠ s in 𝓝[<] v, P s := by
    have h1 : ∃ᶠ s in 𝓝[<] v, γ s ∈ (chartAt H y).source ∩
        (extChartAt I y) ⁻¹' Metric.ball (extChartAt I y y) (ρ / 2) :=
      Filter.frequently_map.1 (hy.frequently hN)
    refine (h1.and_eventually (Ioo_mem_nhdsLT hs₂v')).mono fun s hs => ?_
    exact ⟨⟨hs.2.1.le, hs.2.2⟩, hs.1.1, Metric.ball_subset_closedBall hs.1.2⟩
  let F : Filter ℝ := 𝓝[<] v ⊓ 𝓟 {s | P s}
  have : F.NeBot := Filter.frequently_iff_neBot.1 hfreq
  have hFP : ∀ᶠ s in F, P s := mem_inf_of_right (mem_principal_self _)
  obtain ⟨zl, hzlC, hzl⟩ := (hKc.prod (isCompact_closedBall (0 : E) R)).exists_clusterPt
    (f := map z F) (le_principal_iff.2 (Filter.mem_map.2 (mem_of_superset hFP hPz)))
  have hzlint : zl.1 ∈ interior (extChartAt I y).target := hKint hzlC.1
  obtain ⟨ε, hε, W, hWo, hvW, -, Ψ, hΨ0, hΨsm, hΨd⟩ :=
    exists_lPhaseFlow_of_start S hac hmetric hv hstart y zl hzlint
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 (hWo.mem_nhds hvW)
  have hfV : ∃ᶠ s in F, z s ∈ V := Filter.frequently_map.1 (hzl.frequently hV)
  have hmaxv : max s₁ (v - ε) < v := max_lt hs₁v (by linarith)
  have hevF : ∀ᶠ s in F, s ∈ U ∧ s ∈ Ioo (max s₁ (v - ε)) v ∧ P s := by
    have hle : F ≤ 𝓝[<] v := inf_le_left
    filter_upwards [hle (nhdsWithin_le_nhds hU), hle (Ioo_mem_nhdsLT hmaxv), hFP]
      with s h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨s, hsV, hsU, hsL, hsP⟩ := (hfV.and_eventually hevF).exists
  set p : ℝ × (E × E) := (s, z s)
  have hp : p ∈ W := hUV ⟨hsU, hsV⟩
  have hLsub : ∀ r ∈ Ioo (max s₁ (v - ε)) v, r ∈ Ioc (v - ε) v ∧ r ∈ Ioo s₁ v := fun r hr =>
    ⟨⟨(le_max_right _ _).trans_lt hr.1, hr.2.le⟩, ⟨(le_max_left _ _).trans_lt hr.1, hr.2⟩⟩
  have hz : ∀ r ∈ Ioo (max s₁ (v - ε)) v,
      HasDerivAt (fun r' => Ψ (p, r')) (lPhaseField S T y r (Ψ (p, r))) r ∧
        T - r ^ 2 ∈ D.regular ∧ (Ψ (p, r)).1 ∈ interior (extChartAt I y).target := fun r hr =>
    ⟨(hΨd p hp r (hLsub r hr).1).1, hreg r (hLsub r hr).2, (hΨd p hp r (hLsub r hr).1).2.2⟩
  have heqOn := eqOn_lPhaseCurve_of_isLRegularizedGeodesicOn S hS T y isOpen_Ioo
    isPreconnected_Ioo hγ isOpen_Ioo isPreconnected_Ioo hz (hLsub s hsL).2 hsL hsP.2.1 (hΨ0 p hp)
  have hsm : ContDiffOn ℝ ∞ (fun r => Ψ (p, r)) (Ioo (v - ε) (v + ε)) :=
    hΨsm.comp (contDiffOn_const.prodMk contDiffOn_id) (fun r hr => ⟨hp, hr⟩)
  have hvI : v ∈ Ioo (v - ε) (v + ε) := ⟨by linarith, by linarith⟩
  have hvint : (Ψ (p, v)).1 ∈ interior (extChartAt I y).target :=
    (hΨd p hp v ⟨by linarith, le_rfl⟩).2.2
  have hcont : ContinuousAt (fun r => (Ψ (p, r)).1) v :=
    (hsm.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hvI)).fst
  obtain ⟨δ', hδ', hδ'int⟩ := Metric.eventually_nhds_iff.1
    (hcont.preimage_mem_nhds (isOpen_interior.mem_nhds hvint))
  set δ : ℝ := min δ' (min ε (v - max s₁ (v - ε)))
  have hδ : 0 < δ := lt_min hδ' (lt_min hε (by linarith))
  have hδ1 : δ ≤ δ' := min_le_left _ _
  have hδ2 : δ ≤ ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ v - max s₁ (v - ε) := (min_le_right _ _).trans (min_le_right _ _)
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (lPhaseCurve (I := I) y (fun r => Ψ (p, r)))
      (Ioo (v - δ) (v + δ)) := by
    have hsub : Ioo (v - δ) (v + δ) ⊆ Ioo (v - ε) (v + ε) := fun r hr =>
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have h1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun r => (Ψ (p, r)).1) (Ioo (v - δ) (v + δ)) :=
      (hsm.fst.mono hsub).contMDiffOn
    refine (contMDiffOn_extChartAt_symm (I := I) (n := ∞) y).comp h1 fun r hr => ?_
    have hr' : dist r v < δ' := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hr.1, hr.2]
    exact interior_subset (s := (extChartAt I y).target) (hδ'int hr')
  refine ⟨_, tendsto_lVelocity_lift_of_family hδ hβ fun r hr => ?_⟩
  have hrL : r ∈ Ioo (max s₁ (v - ε)) v := ⟨by linarith [hr.1], hr.2⟩
  exact (heqOn ⟨(hLsub r hrL).2, hrL⟩).symm

end ClosedStart

end DifferentialGeometry.PDE.RicciFlow.Perelman
