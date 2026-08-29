import DifferentialGeometry.Analysis.Parabolic.DeTurckRicci.DeTurckChartRegularityFromJoint
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.GaugeRecovery.ConjugatingDiffeoFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.GaugeRecovery.RicciFlowPdeAtZero
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.ConjugatingFlow.Properties

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.Analysis.ODE
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Connection

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem neg_tangent_cmdwa
    (X : ℝ → ∀ x : M, TangentSpace I x)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (-(X q.1 q.2)) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) q₀.2
  have hfib := hXfib.neg
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 q₀.2 :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with q hq
    simpa using (e.linear ℝ hq).map_neg (X q.1 q.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).map_neg (X q₀.1 q₀.2)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem full_gauge
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (hT : 0 < T)
    (h_smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) :
    ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      (∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x))))) ∧
      (∀ x : M,
        ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M))
          (Set.Ici (0 : ℝ)) 0) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M => (Φ_fam p.1 : M → M) p.2)
        (Set.Ico (0 : ℝ) T ×ˢ Set.univ) := by
  set X_DT : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x)
  have hsmoothX : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ) :=
    fun q hq => neg_tangent_cmdwa
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x))
      (h_smooth q hq)
  obtain ⟨Φ, hΦ0, hdiffeo, hflow, hΦcont0,
      hΦbundle0, _hΦorbit, _hΦsection, lo, hi, hlo, hhi, hΦsmooth⟩ :=
    forward_flow_existence_smooth_neighborhood_of_jointsmooth_field
      (I := I) X_DT T hT hsmoothX
  obtain ⟨Φ_fam, hfam0, hfameq, hfamode⟩ :=
    time_dependent_vf_bare_flow_family (I := I) X_DT T Φ
      (fun t ht htT => hdiffeo t ⟨ht, htT⟩)
      (fun t ht htT x => hflow t ⟨ht, htT⟩ x)
  have hfun_eqOn : ∀ s ∈ Set.Ico (0 : ℝ) T,
      (Φ_fam s : M → M) = fun y : M => Φ s y := by
    intro s hs
    funext y
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hfam0, hΦ0]
      rfl
    · exact hfameq s h0 hs.2 y
  refine ⟨Φ_fam, hfam0, ?_, ?_, ?_, ?_⟩
  · intro x s hs
    exact hfamode s hs.1 hs.2 x
  · intro x
    have heqOn : Set.EqOn (fun s : ℝ => (Φ_fam s : M → M) x)
        (fun s : ℝ => Φ s x) (Set.Ico 0 T) := by
      intro s hs
      change (Φ_fam s : M → M) x = Φ s x
      rw [hfun_eqOn s hs]
    refine (hΦcont0 x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hT) heqOn) ?_
    rw [hfun_eqOn 0 ⟨le_rfl, hT⟩]
  · intro x v
    have heqOn : Set.EqOn
        (fun s : ℝ => (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M))
        (fun s : ℝ => (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M))
        (Set.Ico 0 T) := by
      intro s hs
      change (TotalSpace.mk' E ((Φ_fam s : M → M) x)
          (mfderiv I I (Φ_fam s : M → M) x v) : TangentBundle I M) =
        (TotalSpace.mk' E (Φ s x)
          (mfderiv I I (fun y : M => Φ s y) x v) : TangentBundle I M)
      rw [hfun_eqOn s hs]
    refine (hΦbundle0 x v).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hT) heqOn) ?_
    change (TotalSpace.mk' E ((Φ_fam 0 : M → M) x)
        (mfderiv I I (Φ_fam 0 : M → M) x v) : TangentBundle I M) =
      (TotalSpace.mk' E (Φ 0 x)
        (mfderiv I I (fun y : M => Φ 0 y) x v) : TangentBundle I M)
    rw [hfun_eqOn 0 ⟨le_rfl, hT⟩]
  · have hIco : Set.Ico (0 : ℝ) T ⊆ Set.Ioo lo hi := fun t ht =>
      ⟨lt_of_lt_of_le hlo ht.1, lt_trans ht.2 hhi⟩
    have hraw : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
        (fun p : ℝ × M => Φ p.1 p.2) (Set.Ico (0 : ℝ) T ×ˢ Set.univ) :=
      hΦsmooth.mono (Set.prod_mono hIco (subset_refl _))
    refine hraw.congr ?_
    rintro ⟨s, x⟩ ⟨hs, -⟩
    change (Φ_fam s : M → M) x = Φ s x
    rw [hfun_eqOn s hs]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem ricci_gauge_of_dt
    (g₀ g_bg : SmoothRiemannianMetric I M) {T : ℝ}
    (g_DT : ℝ → SmoothRiemannianMetric I M)
    (hDT : IsQuasilinearMetricParabolicSolution (I := I)
      (deTurckRicciRHS (I := I) g_bg) g₀ T g_DT)
    (hJ : JointChartGramSmooth (I := I) T g_DT) :
    ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      (∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
          (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x))))) ∧
      ∃ g_RF : ℝ → SmoothRiemannianMetric I M,
        (∀ s : ℝ, g_RF s = Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) ∧
        g_RF 0 = g₀ ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ
              (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        (∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
          ContinuousOn
            (fun p : ℝ × M =>
              Integral.Measure.chartGramMatrix (I := I) (g_RF p.1) x₀ p.2 i j)
            (Set.Ico (0 : ℝ) T ×ˢ
              (trivializationAt E (TangentSpace I) x₀).baseSet)) ∧
        ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ x : M, ∀ v w : TangentSpace I x,
          HasDerivWithinAt (fun s : ℝ => (g_RF s).inner x v w)
            ((-2 : ℝ) * ricciTensor (I := I) (g_RF t) x v w)
            (Set.Ici 0) t := by
  obtain ⟨hT, hinit, hderiv⟩ := hDT
  obtain ⟨hreg, hsmooth, hgram, -, hgramE, hC2⟩ :=
    deTurckRicci_chartRegularity_of_jointChartGramSmooth
      (I := I) g_bg T g_DT hJ
  obtain ⟨Φ_fam, hΦ0, hΦode, hΦorbit0, hΦmfderiv0, hΦjoint⟩ :=
    full_gauge (I := I) g_DT g_bg T hT hsmooth
  obtain ⟨hΦorbit, hΦtotal⟩ :=
    conjugating_flow_orbit_pushforward_continuity_data
      (I := I) g_DT g_bg T Φ_fam hΦode hreg hΦorbit0 hΦmfderiv0
  have hgramRF :=
    conjugating_flow_pullback_jointGram_onesided
      (I := I) g_DT T Φ_fam hΦjoint hJ
  have hinterior :=
    conjugating_flow_flat_data
      (I := I) g_DT g_bg T Φ_fam hderiv hΦode hreg hgram
  refine ⟨Φ_fam, hΦ0, hΦode,
    fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s), fun _ => rfl, ?_, ?_, ?_, ?_⟩
  · change Diffeomorph.pullbackMetric (g_DT 0) (Φ_fam 0) = g₀
    rw [hΦ0, Diffeomorph.pullbackMetric_refl, hinit]
  · exact hgramRF
  · intro x₀ i j
    exact (hgramRF x₀ i j).continuousOn
  · intro t ht x v w
    rcases eq_or_lt_of_le ht.1 with hzero | hpos
    · subst t
      have hcont :=
        gfam_inner_continuous_on
          (I := I) g_DT T Φ_fam x v w hgramE hΦorbit hΦtotal
      have hric : ContinuousOn
          (fun s : ℝ => ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
          (Set.Ico 0 T) :=
        ricci_gfam_continuous_on
          (I := I) g_DT T Φ_fam x v w hC2 hΦorbit hΦtotal
      have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
      have hricIoo : ContinuousWithinAt
          (fun s : ℝ => ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
          (Set.Ioo 0 T) 0 :=
        (hric.continuousWithinAt h0mem).mono Set.Ioo_subset_Ico_self
      have hricIoi : ContinuousWithinAt
          (fun s : ℝ => ricciTensor (I := I)
            (Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s)) x v w)
          (Set.Ioi 0) 0 :=
        hricIoo.mono_of_mem_nhdsWithin (Ioo_mem_nhdsGT hT)
      exact ricci_flow_pde_at_zero
        (I := I) (fun s => Diffeomorph.pullbackMetric (g_DT s) (Φ_fam s))
        hT x v w hcont (hricIoi.const_mul (-2 : ℝ))
        (fun s hs => hinterior s hs x v w)
    · exact hinterior t ⟨hpos, ht.2⟩ x v w

end DifferentialGeometry.PDE.RicciFlow
