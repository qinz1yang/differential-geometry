import DifferentialGeometry.Geometry.Comparison.FiniteSoul.TransverseShiftRegularity

/-!
# Local continuous unit normals along a geodesic of a surface (S-SHIFT2, existence part 1)

* `continuousAt_negFiber`: fibrewise negation `(x, v) ↦ (x, -v)` of the tangent bundle is continuous;
  hence the negative of a continuous field along a curve is continuous (`continuousOn_neg_field`).
* `exists_local_unitNormal_dim_two`: in dimension two, near every time `t₀` there is a continuous unit
  vector field along the unit geodesic `γ t = π φ_t(p)` orthogonal to `γ'` (the Gram–Schmidt normal of a
  chart vector `W ∉ span γ'(t₀)`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- **Fibrewise negation of the tangent bundle is continuous.** -/
theorem continuousAt_negFiber (v : TangentBundle I M) :
    ContinuousAt (fun u : TangentBundle I M => (⟨u.proj, -u.snd⟩ : TangentBundle I M)) v := by
  set ψ := extChartAt I.tangent v with hψ
  have hsrc_iff : ∀ u : TangentBundle I M, u ∈ ψ.source ↔ u.proj ∈ (chartAt H v.proj).source := by
    intro u
    rw [hψ, extChartAt_source, TangentBundle.mem_chart_source_iff]
  have hvsrc : v ∈ ψ.source := (hsrc_iff v).mpr (mem_chart_source H v.proj)
  have hneg : ∀ u : TangentBundle I M, u ∈ ψ.source →
      ψ (⟨u.proj, -u.snd⟩ : TangentBundle I M) = ((ψ u).1, -(ψ u).2) := by
    intro u hu
    have hu' := (hsrc_iff u).mp hu
    refine Prod.ext ?_ ?_
    · rw [hψ, TangentBundle.extChartAt_tangent_apply_fst v, TangentBundle.extChartAt_tangent_apply_fst v]
    · rw [hψ, TangentBundle.extChartAt_tangent_apply_snd v (p := ⟨u.proj, -u.snd⟩) hu',
        TangentBundle.extChartAt_tangent_apply_snd v hu']
      exact map_neg _ _
  have heq : (fun u : TangentBundle I M => (⟨u.proj, -u.snd⟩ : TangentBundle I M)) =ᶠ[𝓝 v]
      fun u => ψ.symm ((ψ u).1, -(ψ u).2) := by
    filter_upwards [extChartAt_source_mem_nhds (I := I.tangent) v] with u hu
    have hu' : (⟨u.proj, -u.snd⟩ : TangentBundle I M) ∈ ψ.source :=
      (hsrc_iff _).mpr ((hsrc_iff u).mp hu)
    rw [← hneg u hu, ψ.left_inv hu']
  have htarget : ((ψ v).1, -(ψ v).2) ∈ ψ.target := by
    rw [← hneg v hvsrc]
    exact ψ.map_source ((hsrc_iff _).mpr ((hsrc_iff v).mp hvsrc))
  have h1 : ContinuousAt (fun u => ((ψ u).1, -(ψ u).2)) v :=
    (continuousAt_extChartAt (I := I.tangent) v).fst.prodMk
      (continuousAt_extChartAt (I := I.tangent) v).snd.neg
  have hc : ContinuousAt (fun u => ψ.symm ((ψ u).1, -(ψ u).2)) v :=
    ContinuousAt.comp (f := fun u => ((ψ u).1, -(ψ u).2))
      (continuousAt_extChartAt_symm'' htarget) h1
  exact hc.congr heq.symm

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- The negative of a continuous field along a curve is continuous. -/
theorem continuousOn_neg_field {s : Set ℝ} {γ : ℝ → M} {N : ℝ → E}
    (h : ContinuousOn (fun t => (⟨γ t, N t⟩ : TangentBundle I M)) s) :
    ContinuousOn (fun t => (⟨γ t, -N t⟩ : TangentBundle I M)) s := fun t ht =>
  ContinuousAt.comp_continuousWithinAt
    (g := fun u : TangentBundle I M => (⟨u.proj, -u.snd⟩ : TangentBundle I M))
    (f := fun t => (⟨γ t, N t⟩ : TangentBundle I M))
    (continuousAt_negFiber (I := I) (⟨γ t, N t⟩ : TangentBundle I M)) (h t ht)

omit [I.Boundaryless] [FiniteDimensional ℝ E] in
/-- In dimension two every nonzero vector has a vector outside its span. -/
theorem exists_not_mem_span_singleton_dim_two (hdim : Module.finrank ℝ E = 2) {U : E}
    (hU : U ≠ 0) : ∃ W : E, LinearIndependent ℝ ![U, W] := by
  by_contra hne
  push Not at hne
  have htop : Submodule.span ℝ {U} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro W
    have h := hne W
    rw [LinearIndependent.pair_iff' hU] at h
    push Not at h
    obtain ⟨a, ha⟩ := h
    rw [← ha]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self U)
  have h1 := finrank_span_singleton (K := ℝ) hU
  rw [htop, finrank_top, hdim] at h1
  norm_num at h1

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
/-- Points `(y, v)` with `y` in the chart target are in the target of the tangent-bundle chart. -/
theorem mem_extChartAt_tangent_target (q : TangentBundle I M) (y v : E)
    (hy : y ∈ (extChartAt I q.proj).target) : (y, v) ∈ (extChartAt I.tangent q).target := by
  simp only [extChartAt, OpenPartialHomeomorph.extend, PartialEquiv.trans_target] at hy ⊢
  simp only [ModelWithCorners.target_eq, ModelWithCorners.toPartialEquiv_coe_symm,
    Set.mem_inter_iff, Set.mem_range, Set.mem_preimage, modelWithCorners_prod_toPartialEquiv,
    modelWithCornersSelf_partialEquiv, PartialEquiv.prod_target, PartialEquiv.refl_target,
    FiberBundle.chartedSpace_chartAt, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.prod_toPartialHomeomorph, OpenPartialHomeomorph.refl_partialEquiv,
    PartialEquiv.trans_target, TangentBundle.trivializationAt_target, Set.preimage_inter,
    Set.mem_prod, Set.mem_univ, and_true] at hy ⊢
  exact ⟨hy.1, ⟨hy.2, Set.mem_univ _⟩, (chartAt H q.proj).map_target hy.2⟩

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- The normalized Gram–Schmidt vector of `W` against a unit `U` is a unit vector orthogonal to `U`. -/
theorem gramSchmidt_unit (B : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ a b, B a b = B b a) {U W : E}
    (hUU : B U U = 1) (hd : 0 < B W W - (B W U) ^ 2) :
    B ((Real.sqrt (B W W - (B W U) ^ 2))⁻¹ • (W - B W U • U)) U = 0 ∧
      B ((Real.sqrt (B W W - (B W U) ^ 2))⁻¹ • (W - B W U • U))
        ((Real.sqrt (B W W - (B W U) ^ 2))⁻¹ • (W - B W U • U)) = 1 := by
  have hUW : B U W = B W U := hsymm U W
  have hsq := Real.sq_sqrt hd.le
  have hsp := Real.sqrt_pos.mpr hd
  constructor
  · simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul, hUU]
    ring
  · simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul, hUU, hUW]
    field_simp
    nlinarith [hsq]

variable [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- **Local unit normal (dimension two).** -/
theorem exists_local_unitNormal_dim_two (hr : 1 ≤ r) (hdim : Module.finrank ℝ E = 2)
    (p : TangentBundle I M) (hdom : ∀ t, (p, t) ∈ g.geodesicFlowDomain)
    (hp : g.inner p.proj p.snd p.snd = 1) (t₀ : ℝ) :
    ∃ δ > 0, ∃ N : ℝ → E,
      ContinuousOn (fun t => (⟨(g.geodesicFlow p t).proj, N t⟩ : TangentBundle I M))
        (Ioo (t₀ - δ) (t₀ + δ)) ∧
      ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), g.inner (g.geodesicFlow p t).proj (N t) (N t) = 1 ∧
        g.inner (g.geodesicFlow p t).proj (N t) (g.geodesicFlow p t).snd = 0 := by
  set Fl : ℝ → TangentBundle I M := fun t => g.geodesicFlow p t with hFl
  set q₀ := Fl t₀ with hq₀
  set x₀ := q₀.proj with hx₀
  set ψ := extChartAt I.tangent q₀ with hψ
  have hFlc : ∀ t, ContinuousAt Fl t := by
    intro t
    have hin : ContMDiff 𝓘(ℝ, ℝ) (I.tangent.prod 𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => (p, s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (((g.contMDiffOn_geodesicFlow hr).contMDiffAt
      ((g.isOpen_geodesicFlowDomain hr).mem_nhds (hdom t))).comp t
      ((hin t).of_le (by exact_mod_cast le_top))).continuousAt
  have hsrc_iff : ∀ u : TangentBundle I M, u ∈ ψ.source ↔ u.proj ∈ (chartAt H x₀).source := by
    intro u
    rw [hψ, extChartAt_source, TangentBundle.mem_chart_source_iff]
  set Y : ℝ → E := fun t => (ψ (Fl t)).1 with hY
  set U : ℝ → E := fun t => (ψ (Fl t)).2 with hU
  have hYeq : ∀ t, Y t = extChartAt I x₀ (g.geodesicFlow p t).proj := fun t =>
    TangentBundle.extChartAt_tangent_apply_fst q₀
  have hUeq : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      U t = mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p t).proj
        (g.geodesicFlow p t).snd := by
    intro t ht
    simp only [hU, hψ]
    rw [TangentBundle.extChartAt_tangent_apply_snd q₀ ht,
      TangentBundle.continuousLinearMapAt_trivializationAt ht]
    rfl
  set B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun t => g.chartInner x₀ (Y t) with hB
  have hspeed : ∀ t, g.inner (g.geodesicFlow p t).proj (g.geodesicFlow p t).snd
      (g.geodesicFlow p t).snd = 1 := fun t => by
    rw [g.inner_geodesicFlow_eq hr p t (hdom t), hp]
  have hread : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → ∀ a b : E,
      g.inner (g.geodesicFlow p t).proj a b = B t (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)
        (g.geodesicFlow p t).proj a) (mfderiv I 𝓘(ℝ, E) (extChartAt I x₀)
        (g.geodesicFlow p t).proj b) := by
    intro t ht a b
    simp only [hB]
    rw [hYeq]
    exact g.inner_eq_chartInner ht a b
  have hBUU : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → B t (U t) (U t) = 1 :=
    fun t ht => by
      have h := hread t ht (g.geodesicFlow p t).snd (g.geodesicFlow p t).snd
      rw [hspeed t] at h
      rw [hUeq t ht]; exact h.symm
  have hBsymm : ∀ t (a b : E), B t a b = B t b a := fun t a b => g.chartInner_symm x₀ _ a b
  have hS₀ : (g.geodesicFlow p t₀).proj ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hYt : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      Y t ∈ (extChartAt I x₀).target := fun t ht => by
    rw [hYeq]
    exact (extChartAt I x₀).map_source (by rwa [extChartAt_source])
  -- a chart vector off the velocity line
  have hU₀ : U t₀ ≠ 0 := by
    intro h0
    have h := hBUU t₀ hS₀
    rw [h0, map_zero] at h
    exact zero_ne_one h
  obtain ⟨W, hW⟩ := exists_not_mem_span_singleton_dim_two hdim hU₀
  have hco₀ : IsCoercive (B t₀) := g.isCoercive_chartInner x₀ (hYt t₀ hS₀)
  have hgram := DifferentialGeometry.Analysis.bilin_gram_pos_of_linearIndependent (hBsymm t₀)
    hco₀ hW
  rw [hBUU t₀ hS₀, one_mul, hBsymm t₀ (U t₀) W] at hgram
  -- continuity of the chart data near `t₀`
  have hψFl : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source →
      ContinuousAt (fun s => ψ (Fl s)) t := fun t ht =>
    (continuousAt_extChartAt' (by
      rw [extChartAt_source, TangentBundle.mem_chart_source_iff]; exact ht)).comp (hFlc t)
  have hBc : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → ContinuousAt B t :=
    fun t ht => ((g.contDiffOn_chartInner x₀).continuousOn.continuousAt
      ((isOpen_extChartAt_target x₀).mem_nhds (hYt t ht))).comp (hψFl t ht).fst
  set d : ℝ → ℝ := fun t => B t W W - (B t W (U t)) ^ 2 with hd
  have hdc : ∀ t, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source → ContinuousAt d t :=
    fun t ht => (((hBc t ht).clm_apply continuousAt_const).clm_apply continuousAt_const).sub
      ((((hBc t ht).clm_apply continuousAt_const).clm_apply (hψFl t ht).snd).pow 2)
  -- the interval
  have hγc : Continuous fun t => (g.geodesicFlow p t).proj :=
    (FiberBundle.continuous_proj E (TangentSpace I : M → Type _)).comp
      (continuous_iff_continuousAt.mpr hFlc)
  have hev : ∀ᶠ t in 𝓝 t₀, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source ∧ 0 < d t :=
    (show ∀ᶠ t in 𝓝 t₀, (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source from
      hγc.continuousAt.preimage_mem_nhds ((chartAt H x₀).open_source.mem_nhds hS₀)).and
      (continuousAt_const.eventually_lt (hdc t₀ hS₀) hgram)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hIoo : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ), (g.geodesicFlow p t).proj ∈ (chartAt H x₀).source ∧
      0 < d t := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1, ht.2]
  -- the Gram–Schmidt normal, in the chart and on the manifold
  set Nc : ℝ → E := fun t => (Real.sqrt (d t))⁻¹ • (W - B t W (U t) • U t) with hNc
  set VN : ℝ → TangentBundle I M := fun t => ψ.symm (Y t, Nc t) with hVN
  have hfacts : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      (⟨(g.geodesicFlow p t).proj, (VN t).snd⟩ : TangentBundle I M) = VN t ∧
      mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (g.geodesicFlow p t).proj (VN t).snd = Nc t ∧
      (Y t, Nc t) ∈ ψ.target := by
    intro t ht
    obtain ⟨hts, -⟩ := hIoo t ht
    have htarget : (Y t, Nc t) ∈ ψ.target := mem_extChartAt_tangent_target q₀ _ _ (hYt t hts)
    have hVNsrc : VN t ∈ ψ.source := ψ.map_target htarget
    have hψVN : ψ (VN t) = (Y t, Nc t) := ψ.right_inv htarget
    have hVNsrc' : (VN t).proj ∈ (chartAt H x₀).source := (hsrc_iff _).mp hVNsrc
    have hproj : (VN t).proj = (g.geodesicFlow p t).proj := by
      have h1 : extChartAt I x₀ (VN t).proj = Y t := by
        rw [← TangentBundle.extChartAt_tangent_apply_fst q₀, hψVN]
      rw [hYeq] at h1
      exact (extChartAt I x₀).injOn (by rwa [extChartAt_source])
        (by rwa [extChartAt_source]) h1
    have hDc : ∀ (x x' : M) (u u' : E), x = x' → u = u' →
        mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x u = mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x' u' := by
      rintro x x' u u' rfl rfl
      rfl
    have hsnd : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) (VN t).proj (VN t).snd = Nc t := by
      have h2 := TangentBundle.extChartAt_tangent_apply_snd q₀ (p := VN t) hVNsrc'
      rw [TangentBundle.continuousLinearMapAt_trivializationAt hVNsrc', hψVN] at h2
      exact h2.symm
    refine ⟨Bundle.TotalSpace.ext hproj.symm HEq.rfl, ?_, htarget⟩
    exact (hDc _ _ _ _ hproj.symm rfl).trans hsnd
  refine ⟨δ, hδ, fun t => (VN t).snd, ?_, ?_⟩
  · intro t ht
    obtain ⟨hts, hdt⟩ := hIoo t ht
    obtain ⟨heq, -, htarget⟩ := hfacts t ht
    have hNcc : ContinuousAt Nc t :=
      (((hdc t hts).sqrt).inv₀ (Real.sqrt_pos.mpr hdt).ne').smul
        (continuousAt_const.sub ((((hBc t hts).clm_apply continuousAt_const).clm_apply
          (hψFl t hts).snd).smul (hψFl t hts).snd))
    have hVNc : ContinuousAt VN t :=
      ContinuousAt.comp (f := fun t => (Y t, Nc t)) (continuousAt_extChartAt_symm'' htarget)
        ((hψFl t hts).fst.prodMk hNcc)
    refine hVNc.continuousWithinAt.congr (fun s hs => (hfacts s hs).1) heq
  · intro t ht
    obtain ⟨hts, hdt⟩ := hIoo t ht
    obtain ⟨-, hD, -⟩ := hfacts t ht
    have hgs := gramSchmidt_unit (B t) (hBsymm t) (hBUU t hts) hdt
    have h1 := hread t hts (VN t).snd (VN t).snd
    have h2 := hread t hts (VN t).snd (g.geodesicFlow p t).snd
    rw [hD] at h1 h2
    rw [← hUeq t hts] at h2
    exact ⟨h1.trans hgs.2, h2.trans hgs.1⟩

end DifferentialGeometry.Geometry.FiniteSoul
