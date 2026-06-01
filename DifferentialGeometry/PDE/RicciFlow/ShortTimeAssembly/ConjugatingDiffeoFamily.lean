import DifferentialGeometry.PDE.RicciFlow.HamiltonDeTurckPullbackFlat
import DifferentialGeometry.PDE.RicciFlow.Pullback.EvaluationFormChainRule
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckRemainderStrongExists
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.DeTurckGeometricNonlinearity
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.EigenCombination
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartLocalPicard
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.ChartOverlapUniqueness
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.BareFlowFromJointC1
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothInSpace.VariationalLiftFlatIdentity
import DifferentialGeometry.PDE.RicciFlow.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold
import DifferentialGeometry.PDE.RicciFlow.ShortTimeFlow.ForwardFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff NNReal ENNReal Topology BigOperators
open DifferentialGeometry
open DifferentialGeometry.PDE
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.PDE.RicciFlow.ODE
open DifferentialGeometry.PDE.RicciFlow.Pullback
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral
open DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompactSpace M]
  [BoundarylessManifold I M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
/-- **Fibrewise negation of a tangent-bundle map (pointwise).** If the geometric map
`q ↦ ⟨q.2, X q.1 q.2⟩` is `C^∞` within `u` at `q₀`, then so is the negated map
`q ↦ ⟨q.2, -(X q.1 q.2)⟩`.  The fibre coordinate of a tangent-bundle trivialization is
fibre-linear, so it commutes with negation, reducing the goal to `ContMDiffWithinAt.neg`
of the fibre coordinate (the analogue of `smul_tangentMap_cmdwa` for the scalar `-1`). -/
private theorem neg_tangentMap_cmdwa
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
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hXfib.neg
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).map_neg (X x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).map_neg (X q₀.1 q₀.2)

theorem conjugating_diffeo_family
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T_DT : ℝ) (hDT : 0 < T_DT)
    (h_reg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (deTurckVF (I := I) (g_DT q.1) g_bg q.2)
        : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T_DT ×ˢ Set.univ))
    (h_cont0 : ContinuousOn
      (fun q : ℝ × M => (deTurckVF (I := I) (g_DT q.1) g_bg q.2 : TangentSpace I q.2))
      (Set.Icc 0 T_DT ×ˢ Set.univ))
    (h_grad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (fun x => deTurckVF (I := I) (g_DT q.1) g_bg x))
            (extChartAt I α q.2))
        (Set.Icc 0 T_DT ×ˢ Set.univ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T_DT ∧ ∃ Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M),
      Φ_fam 0 = _root_.Diffeomorph.refl I M ∞ ∧
      (∀ x : M, ∀ s ∈ Set.Ioo (0 : ℝ) T,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x)
          (Set.Ici (0 : ℝ)) s
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-(deTurckVF (I := I) (g_DT s) g_bg ((Φ_fam s : M → M) x))))) ∧
      (∀ x : M,
        ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) ∧
      (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
          (Set.Ici (0 : ℝ)) 0) := by
  set X_DT : ℝ → ∀ x : M, TangentSpace I x :=
    fun s x => -(deTurckVF (I := I) (g_DT s) g_bg x) with hXDT
  have hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X_DT q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T_DT ×ˢ Set.univ) :=
    fun q hq => neg_tangentMap_cmdwa
      (fun s x => (deTurckVF (I := I) (g_DT s) g_bg x : TangentSpace I x)) (h_reg q hq)
  have hcont0 : ContinuousOn
      (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T_DT ×ˢ Set.univ) := h_cont0.neg
  have hgrad0 : ∀ α : M, ContinuousOn
      (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
      (Set.Icc (0 : ℝ) T_DT ×ˢ Set.univ) := by
    intro α
    have hfun :
        (fun q : ℝ × M => fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
          = (fun q : ℝ × M => -(fderiv ℝ (chartRawRepr (I := I) α
              (fun x => (deTurckVF (I := I) (g_DT q.1) g_bg x : TangentSpace I x)))
              (extChartAt I α q.2))) := by
      funext q
      have hcr : chartRawRepr (I := I) α (X_DT q.1)
          = (fun z => -(chartRawRepr (I := I) α
              (fun x => (deTurckVF (I := I) (g_DT q.1) g_bg x : TangentSpace I x)) z)) := rfl
      rw [hcr, fderiv_fun_neg]
    rw [hfun]
    exact (h_grad0 α).neg
  obtain ⟨Φ, hΦ0, hdiffeo, hflow, hΦcont0, hΦmfderiv0⟩ :=
    forward_flow_existence_onesided_of_jointsmooth_field (I := I) X_DT T_DT hDT hint hcont0 hgrad0
  obtain ⟨Φ_fam, hfam0, hfameq, hfamode⟩ :=
    time_dependent_vf_bare_flow_family (I := I) X_DT T_DT hDT Φ hΦ0
      (fun t ht htT => hdiffeo t ⟨ht, htT⟩)
      (fun t ht htT x => hflow t ⟨ht, htT⟩ x)
  have hfun_eqOn : ∀ s ∈ Set.Ico (0 : ℝ) T_DT, (Φ_fam s : M → M) = fun y : M => Φ s y := by
    intro s hs
    funext y
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, hfam0, hΦ0]; rfl
    · exact hfameq s h0 hs.2 y
  refine ⟨T_DT, hDT, le_refl _, Φ_fam, hfam0, ?_, ?_, ?_⟩
  · intro x s hs
    exact hfamode s hs.1 hs.2 x
  · intro x
    have heqOn : Set.EqOn (fun s : ℝ => (Φ_fam s : M → M) x) (fun s : ℝ => Φ s x)
        (Set.Ico 0 T_DT) := by
      intro s hs
      change (Φ_fam s : M → M) x = Φ s x
      rw [hfun_eqOn s hs]
    refine (hΦcont0 x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hDT) heqOn) ?_
    rw [hfun_eqOn 0 ⟨le_rfl, hDT⟩]
  · intro x v
    have hmfeq : Set.EqOn
        (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
        (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E)) (Set.Ico 0 T_DT) := by
      intro s hs
      change (mfderiv I I (Φ_fam s : M → M) x v : E)
        = (mfderiv I I (fun y : M => Φ s y) x v : E)
      rw [hfun_eqOn s hs]
    refine (hΦmfderiv0 x v).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hDT) hmfeq) ?_
    change (mfderiv I I (Φ_fam 0 : M → M) x v : E)
      = (mfderiv I I (fun y : M => Φ 0 y) x v : E)
    rw [hfun_eqOn 0 ⟨le_rfl, hDT⟩]

end DifferentialGeometry.PDE.RicciFlow
