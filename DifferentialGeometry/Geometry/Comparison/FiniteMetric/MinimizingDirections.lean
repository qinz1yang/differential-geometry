import DifferentialGeometry.Geometry.Exponential.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Homogeneity
import DifferentialGeometry.Geometry.Metric.Path.RiemannianHopfRinow
import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Completeness
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.ChartDistanceDini

/-!
# Minimizing directions to a closed set for a metric of finite order (CM3.a, CM3.b)

For `g : ContMDiffRiemannianMetric I (r + 1)` (`2 ≤ r`) whose Riemannian distance is the distance
of `M` (`hnorm`) and a closed set `S`, `finiteMinimizingDirectionsTo g S q` is the set of unit
`u ∈ T_qM` whose geodesic reaches `S` at time `d_S(q)`.

* `finiteMinimizingDirectionsTo_nonempty_isCompact` (CM3.a): nonempty and compact off `S` (`M`
  complete).
* `mem_finiteMinimizingDirectionsTo_of_tendsto` (CM3.b): closed graph in the tangent bundle.
* `infDist_expMap_smul_le_finite`: along `t ↦ exp_q(t u)`, `u ∈ V_q(S)`, the distance to `S`
  drops at unit rate.
* `exists_nhds_chart_geodesicFlow_expansion`: uniform first-order expansion of the geodesic flow
  in a chart (the analytic input of the first variation, CM3.c).
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Collapse

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

/-- CM3: minimizing unit directions from `q` to a set `S` for a metric of finite order (the
finite-order analogue of `minimizingDirectionsTo`; frozen D-FOUND definition).

The endpoint is read through the totalised `expMap`, which is meaningful only on `expDomain`.
Every theorem about this set below assumes `[CompleteSpace M]` (with `2 ≤ r` and `hnorm`), where
`expDomain = univ` (finite Hopf–Rinow), so `t ↦ exp_q(t u)` is then an honest unit-speed
geodesic reaching `S` at time `d_S(q)`. Do not use it for incomplete metrics. -/
def finiteMinimizingDirectionsTo {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (S : Set M) (q : M) :
    Set (TangentSpace I q) :=
  {u | g.inner q u u = 1 ∧ g.expMap (⟨q, Metric.infDist q S • u⟩ : TangentBundle I M) ∈ S}

section Flow

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- The chart reading of a tangent vector at the chart centre is the vector itself. -/
theorem trivializationAt_mk_self_snd (x : M) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) x ⟨x, v⟩).2 = v := by
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _
      (by rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source H x),
    TangentBundle.continuousLinearMapAt_trivializationAt (mem_chart_source H x),
    mfderiv_extChartAt_self]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
/-- Uniform first-order expansion of the geodesic flow in the chart at `p₀.proj`: for `p` near
`p₀` and small `s ≥ 0`, `φ(γ_p(s)) = φ(p.proj) + s · (chart reading of p) + O(ε s)`. -/
theorem exists_nhds_chart_geodesicFlow_expansion
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 1 ≤ r) (p₀ : TangentBundle I M) {ε : ℝ} (hε : 0 < ε) :
    ∃ W ∈ 𝓝 p₀, ∃ δ > 0, ∀ p ∈ W, ∀ s ∈ Icc (0 : ℝ) δ,
      (p, s) ∈ g.geodesicFlowDomain ∧ (g.geodesicFlow p s).proj ∈ (chartAt H p₀.proj).source ∧
      ‖extChartAt I p₀.proj (g.geodesicFlow p s).proj - extChartAt I p₀.proj p.proj -
        s • (trivializationAt E (TangentSpace I) p₀.proj p).2‖ ≤ ε * s := by
  set x := p₀.proj with hx
  set T := trivializationAt E (TangentSpace I) x with hT
  set D := g.geodesicFlowDomain with hDdef
  have hD : IsOpen D := g.isOpen_geodesicFlowDomain hr
  have h0 : (p₀, (0 : ℝ)) ∈ D := g.mem_geodesicFlowDomain_zero hr p₀
  have hflow : ContinuousAt (fun q : TangentBundle I M × ℝ => g.geodesicFlow q.1 q.2) (p₀, 0) :=
    (g.contMDiffOn_geodesicFlow hr).continuousOn.continuousAt (hD.mem_nhds h0)
  have hflow0 : g.geodesicFlow p₀ 0 = p₀ := g.geodesicFlow_zero hr p₀
  have hbase : ∀ z : M, z ∈ T.baseSet ↔ z ∈ (chartAt H x).source := by
    intro z; rw [hT, TangentBundle.trivializationAt_baseSet]
  have hsrc0 : g.geodesicFlow p₀ 0 ∈ T.source := by
    rw [hflow0, T.mem_source, hbase]; exact mem_chart_source H x
  set F : TangentBundle I M × ℝ → E := fun q => (T (g.geodesicFlow q.1 q.2)).2 with hFdef
  have hF : ContinuousAt F (p₀, 0) := by
    have hTc : ContinuousAt T (g.geodesicFlow p₀ 0) :=
      T.continuousOn.continuousAt (T.open_source.mem_nhds hsrc0)
    exact continuous_snd.continuousAt.comp (ContinuousAt.comp_of_eq hTc hflow rfl)
  have hev : ∀ᶠ q in 𝓝 (p₀, (0 : ℝ)), q ∈ D ∧ g.geodesicFlow q.1 q.2 ∈ T.source ∧
      ‖F q - F (p₀, 0)‖ < ε / 2 := by
    filter_upwards [hD.mem_nhds h0, hflow.preimage_mem_nhds (T.open_source.mem_nhds hsrc0),
      hF.eventually (Metric.ball_mem_nhds (F (p₀, 0)) (half_pos hε))] with q h1 h2 hq
    refine ⟨h1, h2, ?_⟩
    rwa [dist_eq_norm] at hq
  obtain ⟨W, hW, V, hV, hWV⟩ := mem_nhds_prod_iff.mp hev
  obtain ⟨δ', hδ', hball⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨W, hW, δ' / 2, by positivity, fun p hp s hs => ?_⟩
  have hgood : ∀ σ ∈ Icc (0 : ℝ) s, (p, σ) ∈ D ∧ g.geodesicFlow p σ ∈ T.source ∧
      ‖F (p, σ) - F (p₀, 0)‖ < ε / 2 := by
    intro σ hσ
    refine hWV ⟨hp, hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hσ.1]
    linarith [hσ.2, hs.2]
  have hp0 : g.geodesicFlow p 0 = p := g.geodesicFlow_zero hr p
  have hF0 : F (p, 0) = (T p).2 := by simp only [hFdef, hp0]
  have hs0 : (0 : ℝ) ∈ Icc (0 : ℝ) s := ⟨le_rfl, hs.1⟩
  have hderiv : ∀ σ ∈ Icc (0 : ℝ) s,
      HasDerivAt (fun σ => extChartAt I x (g.geodesicFlow p σ).proj) (F (p, σ)) σ := by
    intro σ hσ
    obtain ⟨hdom, hsrc, -⟩ := hgood σ hσ
    have hz : (g.geodesicFlow p σ).proj ∈ (chartAt H x).source := by
      rw [← hbase]; exact T.mem_source.mp hsrc
    have h1 := g.hasMFDerivAt_geodesicFlow_proj hr hdom
    have h2 : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I x) (g.geodesicFlow p σ).proj
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (g.geodesicFlow p σ).proj) :=
      (mdifferentiableAt_extChartAt hz).hasMFDerivAt
    have h3 : HasFDerivAt (fun σ => extChartAt I x (g.geodesicFlow p σ).proj)
        (show ℝ →L[ℝ] E from (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (g.geodesicFlow p σ).proj).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p σ).snd)) σ :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h2.comp σ h1)
    have h4 := h3.hasDerivAt
    convert h4 using 1
    change _ = (mfderiv I 𝓘(ℝ, E) (extChartAt I x) (g.geodesicFlow p σ).proj)
      (((1 : ℝ →L[ℝ] ℝ).smulRight (g.geodesicFlow p σ).snd) 1)
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul,
      ← TangentBundle.continuousLinearMapAt_trivializationAt hz]
    exact (Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ)
      (trivializationAt E (TangentSpace I) x) ((hbase _).mpr hz) (g.geodesicFlow p σ).snd).symm
  set f : ℝ → E := fun σ => extChartAt I x (g.geodesicFlow p σ).proj - σ • F (p, 0) with hf
  have hfd : ∀ σ ∈ Icc (0 : ℝ) s, HasDerivWithinAt f (F (p, σ) - F (p, 0)) (Icc 0 s) σ := by
    intro σ hσ
    have h1 : HasDerivAt (fun σ : ℝ => σ • F (p, 0)) (F (p, 0)) σ := by
      simpa using (hasDerivAt_id σ).smul_const (F (p, 0))
    exact ((hderiv σ hσ).sub h1).hasDerivWithinAt
  have hbound : ∀ σ ∈ Ico (0 : ℝ) s, ‖F (p, σ) - F (p, 0)‖ ≤ ε := by
    intro σ hσ
    have h1 := (hgood σ (Ico_subset_Icc_self hσ)).2.2
    have h2 := (hgood 0 hs0).2.2
    calc ‖F (p, σ) - F (p, 0)‖ = ‖(F (p, σ) - F (p₀, 0)) - (F (p, 0) - F (p₀, 0))‖ := by
          congr 1; abel
      _ ≤ ‖F (p, σ) - F (p₀, 0)‖ + ‖F (p, 0) - F (p₀, 0)‖ := norm_sub_le _ _
      _ ≤ ε := by linarith
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hfd hbound s ⟨hs.1, le_rfl⟩
  obtain ⟨hdom, hsrc, -⟩ := hgood s ⟨hs.1, le_rfl⟩
  refine ⟨hdom, (hbase _).mp (T.mem_source.mp hsrc), ?_⟩
  have hf0 : f 0 = extChartAt I x p.proj := by simp only [hf, hp0, zero_smul, sub_zero]
  rw [hf0, sub_zero] at hmv
  calc ‖extChartAt I x (g.geodesicFlow p s).proj - extChartAt I x p.proj - s • (T p).2‖
      = ‖f s - extChartAt I x p.proj‖ := by
        rw [← hF0]; simp only [hf]; congr 1; abel
    _ ≤ ε * s := hmv

end Flow

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

variable {r : ℕ∞}

omit [NeZero (Module.finrank ℝ E)] in
/-- On a complete manifold the exponential map of the finite metric is continuous on `TM`. -/
theorem continuous_expMap_of_completeSpace [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))) :
    Continuous g.expMap := by
  have hdom : g.expDomain = univ := by
    ext p
    simp only [expDomain, g.geodesicFlowDomain_eq_univ hr hnorm, preimage_univ]
  have h := (g.contMDiffOn_expMap (one_le_two.trans hr)).continuousOn
  rw [hdom] at h
  exact continuousOn_univ.mp h

/-- **CM3.a** The minimizing directions to a closed set are nonempty and compact (strengthened:
the frozen hypothesis `q ∉ S` is not needed). -/
theorem finiteMinimizingDirectionsTo_nonempty_isCompact [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) (q : M) :
    (finiteMinimizingDirectionsTo g S q).Nonempty ∧
      IsCompact (finiteMinimizingDirectionsTo g S q) := by
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy, hd⟩ := hS.exists_infDist_eq_dist hSne q
    obtain ⟨u, hu, -, hend⟩ := exists_unit_segment_expMap g hr hnorm q y
    refine ⟨u, hu, ?_⟩
    rw [hd]
    convert hy using 1
    exact hend
  · have hmk : Continuous (fun u : TangentSpace I q => (⟨q, u⟩ : TangentBundle I M)) :=
      (FiberBundle.totalSpaceMk_isInducing E (TangentSpace I) q).continuous
    have hc : Continuous (fun u : TangentSpace I q =>
        g.expMap (⟨q, Metric.infDist q S • u⟩ : TangentBundle I M)) :=
      (continuous_expMap_of_completeSpace g hr hnorm).comp
        (hmk.comp (continuous_const.smul continuous_id))
    exact (isCompact_finite_unitSphere g q).inter_right (hS.preimage hc)

/-- The frozen form of CM3.a (with the unused hypothesis `q ∉ S`). -/
example [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) (hSne : S.Nonempty) {q : M} (_hq : q ∉ S) :
    (finiteMinimizingDirectionsTo g S q).Nonempty ∧
      IsCompact (finiteMinimizingDirectionsTo g S q) :=
  finiteMinimizingDirectionsTo_nonempty_isCompact g hr hnorm hS hSne q

omit [NeZero (Module.finrank ℝ E)] in
/-- **CM3.b** Closed graph of the minimizing directions in the tangent bundle (strengthened: the
frozen hypothesis `pInf.proj ∉ S` is not needed). -/
theorem mem_finiteMinimizingDirectionsTo_of_tendsto [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) {p : ℕ → TangentBundle I M} {pInf : TangentBundle I M}
    (hp : ∀ k, (p k).snd ∈ finiteMinimizingDirectionsTo g S (p k).proj)
    (hlim : Tendsto p atTop (𝓝 pInf)) :
    pInf.snd ∈ finiteMinimizingDirectionsTo g S pInf.proj := by
  have hinner : Continuous (fun q : TangentBundle I M => g.inner q.proj q.snd q.snd) :=
    continuousOn_univ.mp (continuousOn_finiteInner_of_bundle (g := g)
      (b := fun q : TangentBundle I M => q.proj) (v := fun q => q.snd) (w := fun q => q.snd)
      continuousOn_id continuousOn_id)
  have hend : Continuous (fun q : TangentBundle I M =>
      g.expMap (⟨q.proj, Metric.infDist q.proj S • q.snd⟩ : TangentBundle I M)) :=
    (continuous_expMap_of_completeSpace g hr hnorm).comp
      (continuous_tangentBundle_smul (b := fun q : TangentBundle I M => q.proj)
        (v := fun q => q.snd) continuous_id
        ((continuous_infDist_pt S).comp (FiberBundle.continuous_proj E (TangentSpace I))))
  exact ⟨(isClosed_eq hinner continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall fun k => (hp k).1),
    (hS.preimage hend).mem_of_tendsto hlim (Eventually.of_forall fun k => (hp k).2)⟩

/-- The frozen form of CM3.b (with the unused hypothesis `hout`). -/
example [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} (hS : IsClosed S) {p : ℕ → TangentBundle I M} {pInf : TangentBundle I M}
    (hp : ∀ k, (p k).snd ∈ finiteMinimizingDirectionsTo g S (p k).proj)
    (hlim : Tendsto p atTop (𝓝 pInf)) (_hout : pInf.proj ∉ S) :
    pInf.snd ∈ finiteMinimizingDirectionsTo g S pInf.proj :=
  mem_finiteMinimizingDirectionsTo_of_tendsto g hr hnorm hS hp hlim

omit [NeZero (Module.finrank ℝ E)] in
/-- Along the geodesic of a minimizing direction the distance to `S` drops at unit rate:
`d_S(exp_q(s u)) ≤ d_S(q) - s` and `dist q (exp_q(s u)) ≤ s` for `s ∈ [0, d_S(q)]`. -/
theorem infDist_expMap_smul_le_finite [CompleteSpace M]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {S : Set M} {q : M} {u : TangentSpace I q} (hu : u ∈ finiteMinimizingDirectionsTo g S q)
    {s : ℝ} (hs : s ∈ Icc 0 (Metric.infDist q S)) :
    Metric.infDist (g.expMap (⟨q, s • u⟩ : TangentBundle I M)) S ≤ Metric.infDist q S - s ∧
      dist q (g.expMap (⟨q, s • u⟩ : TangentBundle I M)) ≤ s := by
  have h1 := g.dist_expMap_smul_le_of_completeSpace (one_le_two.trans hr) hnorm u s (Metric.infDist q S)
  rw [hu.1, Real.sqrt_one, one_mul, abs_of_nonneg (by linarith [hs.2])] at h1
  have h2 := g.dist_expMap_smul_le_of_completeSpace (one_le_two.trans hr) hnorm u 0 s
  rw [hu.1, Real.sqrt_one, one_mul, sub_zero, abs_of_nonneg hs.1, zero_smul,
    g.expMap_zero (one_le_two.trans hr)] at h2
  exact ⟨(Metric.infDist_le_dist_of_mem hu.2).trans h1, h2⟩

end Bundle.ContMDiffRiemannianMetric
