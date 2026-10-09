import DifferentialGeometry.Geometry.Exponential.FiniteMetric

/-!
# Homogeneity of the geodesic flow of a finite-regularity metric (CM1.a)

For `g : ContMDiffRiemannianMetric I (r + 1)` with `1 ≤ r`, the maximal geodesic flow `g.geodesicFlow`
(ported from the Della branch) is fibrewise homogeneous: the geodesic with initial velocity `s • v`
at time `t` is the geodesic with initial velocity `v` at time `s * t`, rescaled by `s`.

The proof: the geodesic spray is quadratic in the fibre variable in every tangent chart
(`metricSpray_smul_snd`), so `u ↦ m_s (γ (s * u))` is an integral curve of the spray whenever `γ` is
(`hasMFDerivAt_smul_geodesicSpray`); uniqueness of maximal integral curves concludes.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.MetricKoszul

/-- The metric spray is quadratic in the fibre variable. -/
theorem metricSpray_smul_snd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ContinuousDualEquiv E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) (y w : E) (s : ℝ) :
    metricSpray b (y, s • w) =
      (s • (metricSpray b (y, w)).1, (s * s) • (metricSpray b (y, w)).2) := by
  simp [metricSpray, smul_smul]

end DifferentialGeometry.MetricKoszul

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The geodesic spray is quadratic in the fibre variable. -/
theorem geodesicSpray_smul {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (q : TangentBundle I M) (s : ℝ) :
    g.geodesicSpray (⟨q.proj, s • q.snd⟩ : TangentBundle I M) =
      ((s • (g.geodesicSpray q).1, (s * s) • (g.geodesicSpray q).2) : E × E) := by
  unfold geodesicSpray
  exact DifferentialGeometry.MetricKoszul.metricSpray_smul_snd _ _ _ _

omit [FiniteDimensional ℝ E] in
/-- Fibre scaling is linear in a tangent-bundle chart. -/
theorem extChartAt_tangent_smul (q p : TangentBundle I M)
    (hp : p.proj ∈ (chartAt H q.proj).source) (s : ℝ) :
    extChartAt I.tangent q (⟨p.proj, s • p.snd⟩ : TangentBundle I M) =
      ((extChartAt I.tangent q p).1, s • (extChartAt I.tangent q p).2) := by
  apply Prod.ext
  · rw [TangentBundle.extChartAt_tangent_apply_fst, TangentBundle.extChartAt_tangent_apply_fst]
  · rw [TangentBundle.extChartAt_tangent_apply_snd q (p := ⟨p.proj, s • p.snd⟩) hp,
      TangentBundle.extChartAt_tangent_apply_snd q hp, map_smul]

variable [I.Boundaryless]

/-- If `γ` is an integral curve of the geodesic spray at time `s * u`, then the fibre-rescaled and
time-rescaled curve `v ↦ m_s (γ (s * v))` is an integral curve of the spray at time `u`. -/
theorem hasMFDerivAt_smul_geodesicSpray {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {γ : ℝ → TangentBundle I M} {s u : ℝ}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent γ (s * u)
      ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicSpray (γ (s * u))))) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I.tangent
      (fun v => (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M)) u
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (g.geodesicSpray (⟨(γ (s * u)).proj, s • (γ (s * u)).snd⟩ : TangentBundle I M))) := by
  set q := γ (s * u) with hq
  set p : TangentBundle I M := ⟨q.proj, s • q.snd⟩ with hp
  set κ := extChartAt I.tangent q with hκ
  have hκp : extChartAt I.tangent p = κ := rfl
  have hcont : ContinuousAt (fun v => γ (s * v)) u :=
    hγ.continuousAt.comp (continuous_const.mul continuous_id).continuousAt
  have hsrc : ∀ᶠ v in 𝓝 u, (γ (s * v)).proj ∈ (chartAt H q.proj).source :=
    ((FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).continuousAt.comp hcont).preimage_mem_nhds
      ((chartAt H q.proj).open_source.mem_nhds (mem_chart_source H q.proj))
  have hchart : HasDerivAt (κ ∘ γ) (g.geodesicSpray q) (s * u) := by
    have h := TauCeti.Manifold.hasDerivAt_comp_curve
      (mdifferentiableAt_extChartAt (I := I.tangent) (mem_chart_source (ModelProd H E) q)) hγ
    rw [← hq] at h
    have hid : mfderiv I.tangent 𝓘(ℝ, E × E) (extChartAt I.tangent q) q =
        ContinuousLinearMap.id ℝ _ := mfderiv_extChartAt_self
    have key : mvfderiv I.tangent (extChartAt I.tangent q) q (g.geodesicSpray q) =
        g.geodesicSpray q := by
      simp only [mvfderiv, hid]
      rfl
    rw [key] at h
    exact h
  let L : E × E →L[ℝ] E × E := (ContinuousLinearMap.id ℝ E).prodMap (s • ContinuousLinearMap.id ℝ E)
  set σ : ℝ → E × E := fun v => L (κ (γ (s * v))) with hσ
  have hσd : HasDerivAt σ (L (s • g.geodesicSpray q)) u := by
    have hlin : HasDerivAt (fun v : ℝ => s * v) s u := by
      simpa using (hasDerivAt_id u).const_mul s
    have h1 : HasDerivAt (fun v => κ (γ (s * v))) (s • g.geodesicSpray q) u :=
      hchart.scomp u hlin
    exact L.hasFDerivAt.comp_hasDerivAt u h1
  have hσu : σ u = κ p := by
    simp only [hσ, L, hp]
    rw [extChartAt_tangent_smul q q (mem_chart_source H q.proj) s]
    rfl
  have heq : (fun v => (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M)) =ᶠ[𝓝 u]
      κ.symm ∘ σ := by
    filter_upwards [hsrc] with v hv
    have hmem : (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M) ∈ κ.source := by
      rw [hκ, extChartAt_source, TangentBundle.mem_chart_source_iff]
      exact hv
    rw [Function.comp_apply, ← κ.left_inv hmem, hσ]
    congr 1
    rw [extChartAt_tangent_smul q (γ (s * v)) hv s]
    rfl
  have hsymm : HasMFDerivAt 𝓘(ℝ, E × E) I.tangent κ.symm (σ u)
      (ContinuousLinearMap.id ℝ (E × E)) := by
    have hpt : σ u = extChartAt I.tangent p p := by rw [hσu, hκp]
    have hmd := mdifferentiableWithinAt_extChartAt_symm (I := I.tangent) (x := p)
      (mem_extChartAt_target p)
    rw [I.tangent.range_eq_univ, mdifferentiableWithinAt_univ] at hmd
    have hid := mfderivWithin_range_extChartAt_symm (I := I.tangent) (x := p)
    rw [I.tangent.range_eq_univ, mfderivWithin_univ] at hid
    rw [hpt]
    exact hmd.hasMFDerivAt.congr_mfderiv hid
  have hcomp := hsymm.comp u (hσd.hasFDerivAt.hasMFDerivAt)
  have hfin := hcomp.congr_of_eventuallyEq heq
  apply hfin.congr_mfderiv
  rw [geodesicSpray_smul g q s]
  ext1
  change (1 : ℝ) • L (s • g.geodesicSpray q) =
    (1 : ℝ) • ((s • q.snd, (s * s) • (g.geodesicSpray q).2) : E × E)
  rw [one_smul, one_smul]
  apply Prod.ext
  · change s • (g.geodesicSpray q).1 = s • q.snd
    rfl
  · change s • (s • (g.geodesicSpray q).2) = (s * s) • (g.geodesicSpray q).2
    rw [smul_smul]

/-- The time-rescaled and fibre-rescaled curve of an integral curve of the spray is an integral
curve of the spray. -/
theorem isMIntegralCurveOn_smul {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {γ : ℝ → TangentBundle I M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ g.geodesicSpray (Ioo a b)) (s : ℝ) :
    IsMIntegralCurveOn
      (fun v => (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M))
      g.geodesicSpray {v | s * v ∈ Ioo a b} := by
  intro v hv
  have h := (hγ (s * v) hv).hasMFDerivAt (Ioo_mem_nhds hv.1 hv.2)
  exact (hasMFDerivAt_smul_geodesicSpray g h).hasMFDerivWithinAt

private theorem exists_Ioo_iff_mul_mem_Ioo {s : ℝ} (hs : s ≠ 0) (a b : ℝ) :
    ∃ a' b' : ℝ, ∀ v : ℝ, v ∈ Ioo a' b' ↔ s * v ∈ Ioo a b := by
  rcases lt_or_gt_of_ne hs with h | h
  · refine ⟨b / s, a / s, fun v => ?_⟩
    simp only [mem_Ioo, div_lt_iff_of_neg h, lt_div_iff_of_neg h, mul_comm v s]
    exact and_comm
  · refine ⟨a / s, b / s, fun v => ?_⟩
    simp only [mem_Ioo, div_lt_iff₀ h, lt_div_iff₀ h, mul_comm v s]

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

private theorem smul_mem_and_eq (hr : 1 ≤ r) (p : TangentBundle I M) {s t : ℝ} (hs : s ≠ 0)
    (h : (p, s * t) ∈ g.geodesicFlowDomain) :
    ((⟨p.proj, s • p.snd⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ∧
      g.geodesicFlow ⟨p.proj, s • p.snd⟩ t =
        ⟨(g.geodesicFlow p (s * t)).proj, s • (g.geodesicFlow p (s * t)).snd⟩ := by
  have hv : ContMDiff I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, g.geodesicSpray q⟩ : TangentBundle I.tangent (TangentBundle I M))) :=
    g.contMDiff_geodesicSpray.of_le (by exact_mod_cast hr)
  obtain ⟨γ, a, b, hγ, hγ0, h0, hst⟩ := h
  obtain ⟨a', b', hab'⟩ := exists_Ioo_iff_mul_mem_Ioo hs a b
  have hδ : IsMIntegralCurveOn
      (fun v => (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M))
      g.geodesicSpray (Ioo a' b') := by
    have h1 := isMIntegralCurveOn_smul g hγ s
    have hset : {v | s * v ∈ Ioo a b} = Ioo a' b' := by
      ext v
      exact (hab' v).symm
    rwa [hset] at h1
  have h0' : (0 : ℝ) ∈ Ioo a' b' := (hab' 0).mpr (by simpa using h0)
  have ht' : t ∈ Ioo a' b' := (hab' t).mpr hst
  have hδ0 : (fun v => (⟨(γ (s * v)).proj, s • (γ (s * v)).snd⟩ : TangentBundle I M)) 0 =
      ⟨p.proj, s • p.snd⟩ := by
    have hγ0' : γ 0 = p := hγ0
    change (⟨(γ (s * 0)).proj, s • (γ (s * 0)).snd⟩ : TangentBundle I M) = _
    rw [mul_zero, hγ0']
  refine ⟨hδ.subset_maximalIntegralCurveInterval h0' hδ0 ht', ?_⟩
  have hδeq := hδ.eqOn_maximalIntegralCurve hv h0' hδ0 ht'
  have hγeq := hγ.eqOn_maximalIntegralCurve hv h0 hγ0 hst
  change maximalIntegralCurve g.geodesicSpray _ t = _
  rw [hδeq]
  change (⟨(γ (s * t)).proj, s • (γ (s * t)).snd⟩ : TangentBundle I M) =
    ⟨(maximalIntegralCurve g.geodesicSpray p (s * t)).proj,
      s • (maximalIntegralCurve g.geodesicSpray p (s * t)).snd⟩
  rw [hγeq]

variable {g} in
/-- **CM1.a** Homogeneity of the domain of the geodesic flow: the flow from `s • v` is defined at
time `t` iff the flow from `v` is defined at time `s * t`. (`g`, `p`, `s`, `t` are implicit, as the
`explicitVarsOfIff` linter requires.) -/
theorem geodesicFlow_smul (hr : 1 ≤ r) {p : TangentBundle I M} {s t : ℝ} :
    ((⟨p.proj, s • p.snd⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain ↔
      (p, s * t) ∈ g.geodesicFlowDomain := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    simp only [zero_smul, zero_mul]
    exact ⟨fun _ => g.mem_geodesicFlowDomain_zero hr p,
      fun _ => g.mem_geodesicFlowDomain_zeroSection p.proj t⟩
  · refine ⟨fun h => ?_, fun h => (smul_mem_and_eq g hr p hs h).1⟩
    have hinv := (smul_mem_and_eq g hr (⟨p.proj, s • p.snd⟩ : TangentBundle I M)
      (inv_ne_zero hs) (s := s⁻¹) (t := s * t) (by rwa [inv_mul_cancel_left₀ hs])).1
    simpa only [smul_smul, inv_mul_cancel₀ hs, one_smul] using hinv

/-- **CM1.a** Homogeneity of the geodesic flow. -/
theorem geodesicFlow_smul_eq (hr : 1 ≤ r) (p : TangentBundle I M) (s t : ℝ)
    (h : (p, s * t) ∈ g.geodesicFlowDomain) :
    g.geodesicFlow ⟨p.proj, s • p.snd⟩ t =
      ⟨(g.geodesicFlow p (s * t)).proj, s • (g.geodesicFlow p (s * t)).snd⟩ := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have h1 : g.geodesicFlow p (0 * t) = p := by
      rw [zero_mul]
      exact g.geodesicFlow_zero hr p
    rw [h1, zero_smul]
    exact g.geodesicFlow_zeroSection hr p.proj t
  · exact (smul_mem_and_eq g hr p hs h).2

variable {g} in
/-- `t • v` lies in the domain of `exp_x` iff the geodesic flow from `v` is defined at time `t`. -/
theorem mem_expDomain_smul_iff (hr : 1 ≤ r) {x : M} {v : TangentSpace I x} {t : ℝ} :
    (⟨x, t • v⟩ : TangentBundle I M) ∈ g.expDomain ↔
      ((⟨x, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain := by
  have h := geodesicFlow_smul (g := g) hr (p := (⟨x, v⟩ : TangentBundle I M)) (s := t) (t := 1)
  rw [mul_one] at h
  exact h

/-- The exponential map along a ray: `exp_x (t • v)` is the base point of the geodesic flow from
`v` at time `t`. -/
theorem expMap_smul_eq_proj_geodesicFlow (hr : 1 ≤ r) (x : M) (v : TangentSpace I x) (t : ℝ)
    (h : ((⟨x, v⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain) :
    g.expMap (⟨x, t • v⟩ : TangentBundle I M) =
      (g.geodesicFlow (⟨x, v⟩ : TangentBundle I M) t).proj := by
  have h' : ((⟨x, v⟩ : TangentBundle I M), t * 1) ∈ g.geodesicFlowDomain := by rwa [mul_one]
  have heq := g.geodesicFlow_smul_eq hr (⟨x, v⟩ : TangentBundle I M) t 1 h'
  rw [mul_one] at heq
  unfold expMap
  rw [heq]

end Bundle.ContMDiffRiemannianMetric
