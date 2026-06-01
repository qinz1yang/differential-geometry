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
import DifferentialGeometry.PDE.RicciFlow.ShortTimeFlow.CutoffExtension
import DifferentialGeometry.PDE.RicciFlow.ShortTimeAssembly.FlatVariationalData

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

theorem flow_pushforward_continuous_in_time
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (T : ℝ) (hT : 0 < T)
    (hΦ0 : Φ_fam 0 = Diffeomorph.refl I M ∞)
    (hbare : ∀ s : ℝ, 0 < s → s ≤ T → ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ici (0 : ℝ)) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))))
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M))
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (hfwd_uniq : ∀ Ψ : ℝ → M → M, (∀ x : M, Ψ 0 x = x) →
      (∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Ψ s x) (Set.Ici (0 : ℝ)) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Ψ t x)))) →
      ∃ δ : ℝ, 0 < δ ∧ δ < T ∧
        ∀ s ∈ Set.Ioo (0 : ℝ) δ, ∀ x : M, (Φ_fam s : M → M) x = Ψ s x)
    (hΦfam_mfderiv_cont : ∀ (x : M) (v : TangentSpace I x), ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ContinuousAt (fun r : ℝ => (mfderiv I I (Φ_fam r : M → M) x v : E)) s) :
    (∀ (x : M) (v : TangentSpace I x), ContinuousOn
      (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E)) (Set.Ico 0 T))
    ∧ (∀ x : M, ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0) := by
  obtain ⟨Φ, hΦ0', hdiffeo, hΦflow, hΦcont0, hΦmfderiv0⟩ :=
    forward_flow_existence_onesided_of_jointsmooth_field X T hT hint hcont0 hgrad0
  have hΦfam_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))) := by
    intro s hs x
    exact (hbare s hs.1 (le_of_lt hs.2) x).mono
      (Set.Ioo_subset_Ico_self.trans Set.Ico_subset_Ici_self)
  have hΦ_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ s x))) := by
    intro s hs x
    exact (hΦflow s hs x).mono (Set.Ioo_subset_Ico_self.trans Set.Ico_subset_Ici_self)
  have hwin : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        s ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
          AutonomizedFieldJointC1 (I := I) Xt ∧
          (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) := by
    intro s hs
    obtain ⟨a', ha'0, ha's⟩ := exists_between hs.1
    obtain ⟨b', hsb', hb'T⟩ := exists_between hs.2
    obtain ⟨Xt, δ, hδ, hXteq, _hXtsmooth, hXtauto⟩ :=
      interior_field_global_cutoff_extension X T hint ha'0 (lt_trans ha's hsb') hb'T
    refine ⟨a', b', Xt, ⟨ha's, hsb'⟩,
      Set.Ioo_subset_Ioo (le_of_lt ha'0) (le_of_lt hb'T), hXtauto, ?_⟩
    intro t ht x
    refine hXteq t ?_ x
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwindow : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ (a b : ℝ)
      (Xt : ℝ → ∀ x : M, TangentSpace I x),
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T → AutonomizedFieldJointC1 (I := I) Xt →
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) →
      ∀ t₀ ∈ Set.Ioo a b, (∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) →
      ∀ t ∈ Set.Ioo a b, ∀ x : M, (Φ_fam t : M → M) x = Φ t x := by
    intro s _ a b Xt hsub hXtauto hXteq t₀ ht₀ hagree t ht x
    have hΦfamXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r ((Φ_fam r : M → M) x))) := by
      intro r hr
      have hode := (hΦfam_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr ((Φ_fam r : M → M) x)]; exact hode
    have hΦXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r (Φ r x))) := by
      intro r hr
      have hode := (hΦ_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr (Φ r x)]; exact hode
    exact bare_integral_flow_eqOn_of_jointC1 (a := a) (b := b) (t₀ := t₀)
      Xt hXtauto (fun u : ℝ => (Φ_fam u : M → M)) Φ x x ht₀ hΦfamXt hΦXt (hagree x) t ht
  have hstart : ∃ t₀ ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x := by
    obtain ⟨δ, hδ0, hδT, hagreeδ⟩ := hfwd_uniq Φ hΦ0' hΦflow
    refine ⟨δ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    intro x
    exact hagreeδ (δ / 2) ⟨by linarith, by linarith⟩ x
  have hident : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam s : M → M) x = Φ s x := by
    set Agree : ℝ → Prop := fun r => ∀ x : M, (Φ_fam r : M → M) x = Φ r x with hAgree
    set u : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
        AutonomizedFieldJointC1 (I := I) Xt ∧
        (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
        (∀ t ∈ Set.Ioo a b, Agree t)} with hu
    set v : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
        AutonomizedFieldJointC1 (I := I) Xt ∧
        (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
        (∀ t ∈ Set.Ioo a b, ¬ Agree t)} with hv
    have hu_open : IsOpen u := by
      rw [hu, isOpen_iff_forall_mem_open]
      rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
      exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
    have hv_open : IsOpen v := by
      rw [hv, isOpen_iff_forall_mem_open]
      rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
      exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
    have huv_disj : Disjoint u v := by
      rw [Set.disjoint_left]
      rintro r ⟨a, b, Xt, hr, _, _, _, hall⟩ ⟨a', b', Xt', hr', hsub', hauto', heq', hnall'⟩
      have hAgree_r : Agree r := hall r hr
      exact hnall' r hr'
        (hwindow r (hsub' hr') a' b' Xt' hsub' hauto' heq' r hr' hAgree_r r hr')
    have hcover : Set.Ioo (0 : ℝ) T ⊆ u ∪ v := by
      intro r hr
      obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin r hr
      by_cases hcase : ∀ t ∈ Set.Ioo a b, Agree t
      · exact Or.inl ⟨a, b, Xt, hr', hsub, hauto, heq, hcase⟩
      · right
        refine ⟨a, b, Xt, hr', hsub, hauto, heq, ?_⟩
        intro t ht hAgree_t
        exact hcase fun t' ht' => hwindow r hr a b Xt hsub hauto heq t ht hAgree_t t' ht'
    obtain ⟨t₀, ht₀, hagree0⟩ := hstart
    have ht₀u : t₀ ∈ u := by
      obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin t₀ ht₀
      exact ⟨a, b, Xt, hr', hsub, hauto, heq,
        fun t ht => hwindow t₀ ht₀ a b Xt hsub hauto heq t₀ hr' hagree0 t ht⟩
    have hsubu : Set.Ioo (0 : ℝ) T ⊆ u :=
      (isPreconnected_Ioo).subset_left_of_subset_union hu_open hv_open huv_disj hcover
        ⟨t₀, ht₀, ht₀u⟩
    intro s hs x
    obtain ⟨a, b, Xt, hr', _, _, _, hall⟩ := hsubu hs
    exact hall s hr' x
  have hB : ∀ x : M,
      ContinuousWithinAt (fun s : ℝ => (Φ_fam s : M → M) x) (Set.Ici (0 : ℝ)) 0 := by
    intro x
    have heqOn : Set.EqOn (fun s : ℝ => (Φ_fam s : M → M) x) (fun s : ℝ => Φ s x)
        (Set.Ico 0 T) := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h0 | h0
      · change (Φ_fam s : M → M) x = Φ s x
        rw [← h0, hΦ0', hΦ0]; rfl
      · exact hident s ⟨h0, hs.2⟩ x
    refine (hΦcont0 x).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (Ico_mem_nhdsGE hT) heqOn) ?_
    change (Φ_fam 0 : M → M) x = Φ 0 x
    rw [hΦ0', hΦ0]; rfl
  refine ⟨?_, hB⟩
  intro x v s hs
  rcases eq_or_lt_of_le hs.1 with h0 | h0
  · subst_vars
    have hmfeq : Set.EqOn
        (fun s : ℝ => (mfderiv I I (Φ_fam s : M → M) x v : E))
        (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E)) (Set.Ico 0 T) := by
      intro s hs
      have hfun : (Φ_fam s : M → M) = (fun y : M => Φ s y) := by
        funext y
        rcases eq_or_lt_of_le hs.1 with h0 | h0
        · rw [← h0, hΦ0', hΦ0]; rfl
        · exact hident s ⟨h0, hs.2⟩ y
      simp only []
      rw [hfun]
    have hΦm : ContinuousWithinAt
        (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E)) (Set.Ico 0 T) 0 :=
      (hΦmfderiv0 x v).mono Set.Ico_subset_Ici_self
    refine hΦm.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hmfeq) ?_
    have hfun0 : (Φ_fam 0 : M → M) = (fun y : M => Φ 0 y) := by
      funext y; rw [hΦ0', hΦ0]; rfl
    change (mfderiv I I (Φ_fam 0 : M → M) x v : E) = (mfderiv I I (fun y : M => Φ 0 y) x v : E)
    rw [hfun0]
  · exact (hΦfam_mfderiv_cont x v s ⟨h0, hs.2⟩).continuousWithinAt

set_option linter.unusedVariables false in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
theorem flow_family_identification
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g₀ : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M)) (Φ : ℝ → M → M)
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hΦfam_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s ((Φ_fam s : M → M) x))))
    (hΦ_ode : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo (0 : ℝ) T) s
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X s (Φ s x))))
    (hwin : ∀ s ∈ Set.Ioo (0 : ℝ) T,
      ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
        s ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
          AutonomizedFieldJointC1 (I := I) Xt ∧
          (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x))
    (hstart : ∃ t₀ ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) :
    ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ x : M, (Φ_fam s : M → M) x = Φ s x := by
  have hwindow : ∀ s ∈ Set.Ioo (0 : ℝ) T, ∀ (a b : ℝ)
      (Xt : ℝ → ∀ x : M, TangentSpace I x),
      Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T → AutonomizedFieldJointC1 (I := I) Xt →
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) →
      ∀ t₀ ∈ Set.Ioo a b, (∀ x : M, (Φ_fam t₀ : M → M) x = Φ t₀ x) →
      ∀ t ∈ Set.Ioo a b, ∀ x : M, (Φ_fam t : M → M) x = Φ t x := by
    intro s _ a b Xt hsub hXtauto hXteq t₀ ht₀ hagree t ht x
    have hΦfamXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => (Φ_fam u : M → M) x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r ((Φ_fam r : M → M) x))) := by
      intro r hr
      have hode := (hΦfam_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr ((Φ_fam r : M → M) x)]; exact hode
    have hΦXt : ∀ r ∈ Set.Ioo a b,
        HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun u : ℝ => Φ u x) (Set.Ioo a b) r
          ((1 : ℝ →L[ℝ] ℝ).smulRight (Xt r (Φ r x))) := by
      intro r hr
      have hode := (hΦ_ode r (hsub hr) x).mono hsub
      rw [hXteq r hr (Φ r x)]; exact hode
    exact bare_integral_flow_eqOn_of_jointC1 (a := a) (b := b) (t₀ := t₀)
      Xt hXtauto (fun u : ℝ => (Φ_fam u : M → M)) Φ x x ht₀ hΦfamXt hΦXt (hagree x) t ht
  set Agree : ℝ → Prop := fun r => ∀ x : M, (Φ_fam r : M → M) x = Φ r x with hAgree
  set u : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
      r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
      AutonomizedFieldJointC1 (I := I) Xt ∧
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
      (∀ t ∈ Set.Ioo a b, Agree t)} with hu
  set v : Set ℝ := {r : ℝ | ∃ (a b : ℝ) (Xt : ℝ → ∀ x : M, TangentSpace I x),
      r ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ Set.Ioo (0 : ℝ) T ∧
      AutonomizedFieldJointC1 (I := I) Xt ∧
      (∀ t ∈ Set.Ioo a b, ∀ x : M, Xt t x = X t x) ∧
      (∀ t ∈ Set.Ioo a b, ¬ Agree t)} with hv
  have hu_open : IsOpen u := by
    rw [hu, isOpen_iff_forall_mem_open]
    rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
    exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
  have hv_open : IsOpen v := by
    rw [hv, isOpen_iff_forall_mem_open]
    rintro r ⟨a, b, Xt, hr, hsub, hauto, heq, hall⟩
    exact ⟨Set.Ioo a b, fun r' hr' => ⟨a, b, Xt, hr', hsub, hauto, heq, hall⟩, isOpen_Ioo, hr⟩
  have huv_disj : Disjoint u v := by
    rw [Set.disjoint_left]
    rintro r ⟨a, b, Xt, hr, _, _, _, hall⟩ ⟨a', b', Xt', hr', hsub', hauto', heq', hnall'⟩
    have hAgree_r : Agree r := hall r hr
    exact hnall' r hr'
      (hwindow r (hsub' hr') a' b' Xt' hsub' hauto' heq' r hr' hAgree_r r hr')
  have hcover : Set.Ioo (0 : ℝ) T ⊆ u ∪ v := by
    intro r hr
    obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin r hr
    by_cases hcase : ∀ t ∈ Set.Ioo a b, Agree t
    · exact Or.inl ⟨a, b, Xt, hr', hsub, hauto, heq, hcase⟩
    · right
      refine ⟨a, b, Xt, hr', hsub, hauto, heq, ?_⟩
      intro t ht hAgree_t
      exact hcase fun t' ht' => hwindow r hr a b Xt hsub hauto heq t ht hAgree_t t' ht'
  obtain ⟨t₀, ht₀, hagree0⟩ := hstart
  have ht₀u : t₀ ∈ u := by
    obtain ⟨a, b, Xt, hr', hsub, hauto, heq⟩ := hwin t₀ ht₀
    exact ⟨a, b, Xt, hr', hsub, hauto, heq,
      fun t ht => hwindow t₀ ht₀ a b Xt hsub hauto heq t₀ hr' hagree0 t ht⟩
  have hsubu : Set.Ioo (0 : ℝ) T ⊆ u :=
    (isPreconnected_Ioo).subset_left_of_subset_union hu_open hv_open huv_disj hcover
      ⟨t₀, ht₀, ht₀u⟩
  intro s hs x
  obtain ⟨a, b, Xt, hr', _, _, _, hall⟩ := hsubu hs
  exact hall s hr' x

theorem joint_smooth_moving_mfderiv_continuous
    (X_DT : ℝ → ∀ x : M, TangentSpace I x) (T : ℝ) (hT : 0 < T)
    (Φ : ℝ → M → M) (hΦ0 : ∀ x : M, Φ 0 x = x)
    (hcont0 : ContinuousOn
      (fun q : ℝ × M => (X_DT q.1 q.2 : TangentSpace I q.2))
      (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hgrad0 : ∀ α : M,
      ContinuousOn
        (fun q : ℝ × M =>
          fderiv ℝ (chartRawRepr (I := I) α (X_DT q.1)) (extChartAt I α q.2))
        (Set.Icc (0 : ℝ) T ×ˢ Set.univ))
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) T, ∀ x : M,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X_DT t (Φ t x))))
    (hpicard : ∀ x : M, ∃ α : M, ∃ δ : ℝ, 0 < δ ∧ x ∈ (chartAt H α).source ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T), Φ s x ∈ (chartAt H α).source ∧
        extChartAt I α (Φ s x)
          = extChartAt I α x + ∫ r in (0 : ℝ)..s,
              chartRawRepr (I := I) α (X_DT r) (extChartAt I α (Φ r x)))
    (hvarpicard : ∀ (x : M) (v : TangentSpace I x), ∃ α : M, ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        (mfderiv I I (fun y : M => Φ s y) x v : E)
          = (@id E (mfderiv I I (fun y : M => Φ 0 y) x v))
            + ∫ r in (0 : ℝ)..s,
                (fderiv ℝ (chartRawRepr (I := I) α (X_DT r))
                    (extChartAt I α (Φ r x)))
                  (mfderiv I I (fun y : M => Φ r y) x v : E))
    (hJbound : ∀ (x : M) (v : TangentSpace I x), ∃ δ : ℝ, ∃ B : ℝ, 0 < δ ∧
      ∀ s ∈ Set.Ico (0 : ℝ) (min δ T),
        ‖(mfderiv I I (fun y : M => Φ s y) x v : E)‖ ≤ B) :
    (∀ x : M, ContinuousWithinAt (fun s : ℝ => Φ s x) (Set.Ici (0 : ℝ)) 0)
    ∧ (∀ (x : M) (v : TangentSpace I x),
        ContinuousWithinAt (fun s : ℝ => (mfderiv I I (fun y : M => Φ s y) x v : E))
          (Set.Ici (0 : ℝ)) 0) :=
  flow_t0_continuity_extension X_DT T hT Φ hΦ0 hcont0 hgrad0 hinterior hpicard
    hvarpicard hJbound

end DifferentialGeometry.PDE.RicciFlow
