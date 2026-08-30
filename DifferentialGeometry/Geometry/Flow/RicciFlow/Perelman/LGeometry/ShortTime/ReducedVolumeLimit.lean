import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.ReducedJacobianLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ShortTime.InjectivityExhaustion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lRedPull_contOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    ContinuousOn
      (fun Z : E ↦ lRedJac S T x Z tau * lSrcDensity S T x)
      (lInjDomain S T x tau) := by
  let U : Set E := lInjDomain S T x tau
  let Ψ := lExpPartial S hS T x tau htau
  have hsource : Ψ.source = U :=
    lExpPartial_source S hS T x tau htau
  have hden : ContinuousOn (fun Z : E ↦ lExpDensity S T x Z tau) U := by
    have hpd : ContinuousOn
        (paramDensity (S.base.metric (T - tau)) Ψ) U := by
      simpa only [hsource] using
        (paramDensity_contOn (I := I) (S.base.metric (T - tau)) Ψ)
    apply hpd.congr
    intro Z hZ
    exact (lExpPartial_density S hS T x tau htau hZ).symm
  have hred : ContinuousOn
      (fun Z : E ↦ redDensity S T x (lExp S T x Z tau) tau) U := by
    have hΨ : ContinuousOn (Ψ : E → M) U := by
      simpa only [← hsource] using Ψ.contMDiffOn_toFun.continuousOn
    have hl : ContinuousOn
        (fun Z : E ↦ redLength S T x (Ψ Z) tau) U := by
      intro Z hZ
      have hZ' : Z ∈ lInjDomain (E := E) (I := I) S T x tau := hZ
      obtain ⟨V, hVopen, hΨV, hsmooth⟩ :=
        redLength_smooth S hS T x htau hZ'
      have hΨeq : Ψ Z = lExp S T x Z tau :=
        lExpPartial_apply S hS T x tau htau hZ'
      rw [← hΨeq] at hΨV
      exact (hsmooth.continuousOn.continuousAt
        (hVopen.mem_nhds hΨV)).comp_continuousWithinAt
        (hΨ Z hZ)
    have hcore : ContinuousOn
        (fun Z : E ↦
          -redLength S T x (Ψ Z) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) U :=
      (hl.neg.sub continuousOn_const).sub continuousOn_const
    have hexp : ContinuousOn
        (fun Z : E ↦ redDensity S T x (Ψ Z) tau) U := by
      change ContinuousOn
        (Real.exp ∘ fun Z : E ↦
          -redLength S T x (Ψ Z) tau -
            ((Module.finrank Real E : Real) / 2) * Real.log tau -
            ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi)) U
      exact Real.continuous_exp.comp_continuousOn hcore
    apply hexp.congr
    intro Z hZ
    dsimp only [Ψ]
    rw [lExpPartial_apply S hS T x tau htau hZ]
  exact (hden.mul hred).congr fun Z hZ ↦
    lRedJac_mul_src S hS T x htau hZ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_le_one
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau)
    (hslab : Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau ≤ 1 := by
  rw [redVolume_lint S hS T x tau htau hslab]
  calc
    (∫⁻ Z in lInjDomain S T x tau,
        ENNReal.ofReal (lRedJac S T x Z tau * lSrcDensity S T x)
        ∂modelHaar (E := E)) ≤
        ∫⁻ Z in lInjDomain S T x tau,
          ENNReal.ofReal (lSrcGauss S T x Z)
          ∂modelHaar (E := E) := by
      refine MeasureTheory.setLIntegral_mono'
        (lInj_isOpen S hS T x tau).measurableSet ?_
      intro Z hZ
      apply ENNReal.ofReal_le_ofReal
      rw [lSrcGauss_eq]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right
          (lRedJac_le_gauss S hS T x htau hZ)
          (lSrcDensity_pos S T x).le
    _ ≤ ∫⁻ Z : E, ENNReal.ofReal (lSrcGauss S T x Z)
          ∂modelHaar (E := E) := by
      simpa using MeasureTheory.lintegral_mono_set
        (Set.subset_univ (lInjDomain S T x tau))
    _ = 1 := lSrcGauss_mass S T x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem redVolume_zero_lim
    [ConnectedSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (hT : T ∈ D.regular) :
    Tendsto (fun tau : Real ↦ redVolume S T x tau)
      (𝓝[>] (0 : Real)) (𝓝 (1 : ENNReal)) := by
  classical
  let F : Real → E → ENNReal := fun tau Z ↦
    (lInjDomain S T x tau).indicator
      (fun W ↦ ENNReal.ofReal
        (lRedJac S T x W tau * lSrcDensity S T x)) Z
  let G : E → ENNReal := fun Z ↦ ENNReal.ofReal (lSrcGauss S T x Z)
  obtain ⟨a, b, hTab, hreg⟩ := D.exists_Icc_regular hT
  have hsmall : ∀ᶠ tau in 𝓝[>] (0 : Real), tau < T - a := by
    have hTa : 0 < T - a := sub_pos.mpr hTab.1
    exact (tendsto_order.1
      (tendsto_id.mono_left nhdsWithin_le_nhds)).2 (T - a) hTa
  have hslab : ∀ᶠ tau in 𝓝[>] (0 : Real),
      Set.Icc (T - tau) T ⊆ D.regular := by
    filter_upwards [hsmall] with tau htau
    exact (Set.Icc_subset_Icc (by linarith) hTab.2.le).trans hreg
  have hmeas : ∀ᶠ tau in 𝓝[>] (0 : Real), Measurable (F tau) := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    have hU := (lInj_isOpen S hS T x tau).measurableSet
    have hcont := lRedPull_contOn S hS T x tau htau
    change Measurable ((lInjDomain S T x tau).piecewise
      (ENNReal.ofReal ∘ fun Z ↦ lRedJac S T x Z tau * lSrcDensity S T x) 0)
    exact ContinuousOn.measurable_piecewise
      (ENNReal.continuous_ofReal.comp_continuousOn hcont)
      continuous_zero.continuousOn hU
  have hbound : ∀ᶠ tau in 𝓝[>] (0 : Real),
      ∀ᵐ Z ∂modelHaar (E := E), F tau Z ≤ G Z := by
    filter_upwards [self_mem_nhdsWithin] with tau htau
    apply MeasureTheory.ae_of_all
    intro Z
    by_cases hZ : Z ∈ lInjDomain (E := E) (I := I) S T x tau
    · simp only [F, G, Set.indicator_of_mem hZ]
      apply ENNReal.ofReal_le_ofReal
      rw [lSrcGauss_eq]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right
          (lRedJac_le_gauss S hS T x htau hZ)
          (lSrcDensity_pos S T x).le
    · simp only [F, Set.indicator_of_notMem hZ, zero_le]
  have hfin : ∫⁻ Z : E, G Z ∂modelHaar (E := E) ≠ (⊤ : ENNReal) := by
    rw [show (∫⁻ Z : E, G Z ∂modelHaar (E := E)) = 1 by
      simpa only [G] using lSrcGauss_mass S T x]
    simp
  have hlim : ∀ᵐ Z ∂modelHaar (E := E),
      Tendsto (fun tau : Real ↦ F tau Z)
        (𝓝[>] (0 : Real)) (𝓝 (G Z)) := by
    apply MeasureTheory.ae_of_all
    intro Z
    have hZev := lInj_eventually S hS T x Z hT
    obtain ⟨rho, hZrho⟩ := hZev.exists
    have hraw := (lRedJac_tau_lim S hS T x Z hZrho).mul_const
      (lSrcDensity S T x)
    have hof := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hraw
    have hFeq : (fun tau : Real ↦ F tau Z) =ᶠ[𝓝[>] (0 : Real)]
        (fun tau ↦ ENNReal.ofReal
          (lRedJac S T x Z tau * lSrcDensity S T x)) := by
      filter_upwards [hZev] with tau hZ
      change (lInjDomain S T x tau).indicator
          (fun W ↦ ENNReal.ofReal
            (lRedJac S T x W tau * lSrcDensity S T x)) Z = _
      exact Set.indicator_of_mem hZ _
    simpa only [G, lSrcGauss_eq, Function.comp_apply, mul_assoc,
      mul_comm, mul_left_comm] using
      hof.congr' hFeq.symm
  have hDCT : Tendsto (fun tau : Real ↦
      ∫⁻ Z : E, F tau Z ∂modelHaar (E := E))
      (𝓝[>] (0 : Real))
      (𝓝 (∫⁻ Z : E, G Z ∂modelHaar (E := E))) :=
    MeasureTheory.tendsto_lintegral_filter_of_dominated_convergence
      G hmeas hbound hfin hlim
  have hmass : (∫⁻ Z : E, G Z ∂modelHaar (E := E)) = 1 :=
    by simpa only [G] using lSrcGauss_mass S T x
  rw [hmass] at hDCT
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin, hslab] with tau htau hslab_tau
  rw [redVolume_lint S hS T x tau htau hslab_tau]
  exact MeasureTheory.lintegral_indicator
    (lInj_isOpen S hS T x tau).measurableSet _

end DifferentialGeometry.PDE.RicciFlow.Perelman
