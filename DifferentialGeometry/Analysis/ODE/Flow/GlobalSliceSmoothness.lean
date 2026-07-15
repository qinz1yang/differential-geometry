import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothInSpace.VariationalODE.BanachIC

/-!
# Smooth time slices of an exact ODE family

This file propagates smooth dependence on initial data along a compact time
interval.  The local input is the existing smooth Picard flow; compactness of
one reference orbit supplies a uniform restart window.
-/

noncomputable section

open Filter Function Metric Set
open scoped ContDiff NNReal Topology

namespace DifferentialGeometry
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two solutions of a `C¹` autonomous ODE that meet inside an open interval
agree throughout that interval. -/
theorem orbit_unique_smooth
    {v : E → E} (hv : ContDiff ℝ 1 v)
    {f g : ℝ → E} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (v (f t)) t)
    (hg : ∀ t ∈ Ioo a b, HasDerivAt g (v (g t)) t)
    (h₀ : f t₀ = g t₀) :
    EqOn f g (Ioo a b) := by
  set u : Set ℝ := {t | f t = g t} ∩ Ioo a b with hu
  suffices hsub : Ioo a b ⊆ u from fun t ht ↦ (hsub ht).1
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := u) _
    ⟨t₀, ht₀, h₀, ht₀⟩
  · rw [hu, inter_comm, ← Subtype.image_preimage_val, inter_comm,
      ← Subtype.image_preimage_val, image_subset_image_iff Subtype.val_injective,
      preimage_setOf_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hf t ht).continuousAt.comp continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨t, ht⟩
      exact (hg t ht).continuousAt.comp continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    rintro t ⟨hfg, ht⟩
    have htime : Ioo a b ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
    obtain ⟨K, s, hs, hlip⟩ :=
      (show ContDiffAt ℝ 1 v (f t) from hv.contDiffAt).exists_lipschitzOnWith
    have hfmem : f ⁻¹' s ∈ nhds t := (hf t ht).continuousAt.preimage_mem_nhds hs
    have hs' : s ∈ nhds (g t) := by
      rw [← hfg]
      exact hs
    have hgmem : g ⁻¹' s ∈ nhds t := (hg t ht).continuousAt.preimage_mem_nhds hs'
    have hfEventually : ∀ᶠ τ in nhds t, HasDerivAt f (v (f τ)) τ ∧ f τ ∈ s := by
      filter_upwards [htime, hfmem] with τ hτ hτs
      exact ⟨hf τ hτ, hτs⟩
    have hgEventually : ∀ᶠ τ in nhds t, HasDerivAt g (v (g τ)) τ ∧ g τ ∈ s := by
      filter_upwards [htime, hgmem] with τ hτ hτs
      exact ⟨hg τ hτ, hτs⟩
    have heq : f =ᶠ[nhds t] g := ODE_solution_unique_of_eventually
      (Filter.Eventually.of_forall fun _ ↦ hlip)
      hfEventually hgEventually hfg
    exact (heq.and htime).mono fun _ h ↦ ⟨h.1, h.2⟩

section UniformRestart

variable [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A smooth autonomous field has one positive restart window over any compact
set of possible anchor points. -/
theorem exists_uniform_flow
    {v : E → E} (hv : ContDiff ℝ ∞ v) {K : Set E} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ (U : Set E), IsOpen U ∧ y ∈ U ∧
        ∃ Ψ : E × ℝ → E,
          (∀ z ∈ U, Ψ (z, 0) = z) ∧
          ContDiffOn ℝ ∞ Ψ (U ×ˢ Ioo (-ε) ε) ∧
          ∀ z ∈ U, ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun s ↦ Ψ (z, s)) (v (Ψ (z, t))) t := by
  have hvTime : ContDiff ℝ ∞ (uncurry (fun _ : ℝ ↦ v)) := by
    simpa only [uncurry_apply_pair] using hv.comp contDiff_snd
  choose r δ hr hδ Ψ hΨ ρ T hρ hT hρr hTδ hΨsm using
    fun y : E ↦
      DifferentialGeometry.PDE.RicciFlow.ODE.exists_isLocalFlow_contDiffOn_top
        (E := E) (f := fun _ : ℝ ↦ v) (t₀ := 0) (x₀ := y) hvTime
  let U : E → Set E := fun y ↦ ball y (ρ y)
  have hcover : K ⊆ ⋃ y, U y := by
    intro y _
    exact mem_iUnion.mpr ⟨y, mem_ball_self (hρ y)⟩
  obtain ⟨sf, hsf⟩ := hK.elim_finite_subcover U (fun _ ↦ isOpen_ball) hcover
  let ε : ℝ := if h : sf.Nonempty then sf.inf' h T else 1
  have hε : 0 < ε := by
    rw [show ε = if h : sf.Nonempty then sf.inf' h T else 1 by rfl]
    split
    · next h => rw [Finset.lt_inf'_iff]; exact fun y _ ↦ hT y
    · exact one_pos
  have hεT : ∀ y ∈ sf, ε ≤ T y := by
    intro y hy
    rw [show ε = if h : sf.Nonempty then sf.inf' h T else 1 by rfl]
    split
    · next h => exact Finset.inf'_le _ hy
    · next h => exact absurd ⟨y, hy⟩ h
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hymem := hsf hy
  rw [mem_iUnion₂] at hymem
  obtain ⟨p, hp, hyp⟩ := hymem
  refine ⟨U p, isOpen_ball, hyp, Ψ p, ?_, ?_, ?_⟩
  · intro z hz
    have hz' : z ∈ closedBall p (r p : ℝ) := by
      rw [mem_closedBall]
      exact (mem_ball.mp hz).le.trans (hρr p)
    simpa using (hΨ p).apply_initial z hz'
  · exact (hΨsm p).mono (Set.prod_mono (Subset.rfl) fun t ht ↦
      ⟨by linarith [ht.1, hεT p hp], by linarith [ht.2, hεT p hp]⟩)
  · intro z hz t ht
    have hz' : z ∈ closedBall p (r p : ℝ) := by
      rw [mem_closedBall]
      exact (mem_ball.mp hz).le.trans (hρr p)
    have ht' : t ∈ Ioo ((0 : ℝ) - δ p) (0 + δ p) :=
      ⟨by linarith [ht.1, hεT p hp, hTδ p],
        by linarith [ht.2, hεT p hp, hTδ p]⟩
    simpa using ((hΨ p).hasDerivWithinAt z hz' t (Ioo_subset_Icc_self ht')).hasDerivAt
      (Icc_mem_nhds ht'.1 ht'.2)

/-- If a family consists of exact trajectories of a smooth autonomous field
on a common compact time interval and is the identity at one interior time,
then every interior time slice depends smoothly on the initial point. -/
theorem flow_slice_smooth
    {v : E → E} (hv : ContDiff ℝ ∞ v)
    {D : Set E} (hD : IsOpen D) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {F : E → ℝ → E}
    (hinit : ∀ x ∈ D, F x t₀ = x)
    (hcont : ∀ x ∈ D, ContinuousOn (F x) (Icc a b))
    (hderiv : ∀ x ∈ D, ∀ t ∈ Ioo a b, HasDerivAt (F x) (v (F x t)) t) :
    ∀ t ∈ Ioo a b, ContDiffOn ℝ ∞ (fun x ↦ F x t) D := by
  intro target htarget x hx
  let K : Set E := F x '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn (hcont x hx)
  obtain ⟨ε, hε, hlocal⟩ := exists_uniform_flow hv hK
  have hstep : ∀ s₀ ∈ Ioo a b,
      ContDiffAt ℝ ∞ (fun y ↦ F y s₀) x →
      ∀ s ∈ Ioo a b, |s - s₀| < ε →
        ContDiffAt ℝ ∞ (fun y ↦ F y s) x := by
    intro s₀ hs₀ hsmooth s hs hss₀
    have hyK : F x s₀ ∈ K :=
      ⟨s₀, ⟨le_of_lt hs₀.1, le_of_lt hs₀.2⟩, rfl⟩
    obtain ⟨U, hU, hyU, Ψ, hΨ0, hΨsm, hΨderiv⟩ := hlocal (F x s₀) hyK
    have hτ : s - s₀ ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt]
      exact hss₀
    have hp_mem : (F x s₀, s - s₀) ∈ U ×ˢ Ioo (-ε) ε := ⟨hyU, hτ⟩
    have hΨat : ContDiffAt ℝ ∞ Ψ (F x s₀, s - s₀) :=
      (hΨsm _ hp_mem).contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp_mem)
    have hpair : ContDiffAt ℝ ∞ (fun y ↦ (F y s₀, s - s₀)) x :=
      hsmooth.prodMk contDiffAt_const
    have hcand : ContDiffAt ℝ ∞ (fun y ↦ Ψ (F y s₀, s - s₀)) x :=
      hΨat.comp x hpair
    have hstate : (fun y ↦ F y s₀) ⁻¹' U ∈ nhds x :=
      hsmooth.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    have heq : (fun y ↦ Ψ (F y s₀, s - s₀)) =ᶠ[nhds x] (fun y ↦ F y s) := by
      filter_upwards [hD.mem_nhds hx, hstate] with y hyD hyState
      let left : ℝ → E := fun t ↦ Ψ (F y s₀, t - s₀)
      let lo : ℝ := max a (s₀ - ε)
      let hi : ℝ := min b (s₀ + ε)
      have hs₀J : s₀ ∈ Ioo lo hi := by
        dsimp only [lo, hi]
        exact ⟨max_lt hs₀.1 (sub_lt_self _ hε),
          lt_min hs₀.2 (lt_add_of_pos_right _ hε)⟩
      have hsJ : s ∈ Ioo lo hi := by
        rw [abs_lt] at hss₀
        dsimp only [lo, hi]
        exact ⟨max_lt hs.1 (by linarith [hss₀.1]),
          lt_min hs.2 (by linarith [hss₀.2])⟩
      have hleft : ∀ t ∈ Ioo lo hi, HasDerivAt left (v (left t)) t := by
        intro t ht
        have htτ : t - s₀ ∈ Ioo (-ε) ε := by
          have htleft : s₀ - ε < t :=
            lt_of_le_of_lt (le_max_right a (s₀ - ε)) ht.1
          have htright : t < s₀ + ε :=
            lt_of_lt_of_le ht.2 (min_le_right b (s₀ + ε))
          constructor <;> linarith
        have houter := hΨderiv (F y s₀) hyState (t - s₀) htτ
        simpa only [left] using houter.comp_sub_const t s₀
      have hright : ∀ t ∈ Ioo lo hi, HasDerivAt (F y) (v (F y t)) t := by
        intro t ht
        exact hderiv y hyD t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
          lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
      have hstart : left s₀ = F y s₀ := by
        simpa only [left, sub_self] using hΨ0 (F y s₀) hyState
      exact orbit_unique_smooth (hv.of_le (by simp)) hs₀J hleft hright hstart hsJ
    exact hcand.congr_of_eventuallyEq heq.symm
  let good : Set ℝ :=
    {s | ContDiffAt ℝ ∞ (fun y ↦ F y s) x} ∩ Ioo a b
  have hgood_open : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    rintro s₀ ⟨hsmooth, hs₀⟩
    change ContDiffAt ℝ ∞ (fun y ↦ F y s₀) x at hsmooth
    have hwin : Ioo (s₀ - ε) (s₀ + ε) ∩ Ioo a b ∈ nhds s₀ :=
      inter_mem (Ioo_mem_nhds (sub_lt_self _ hε) (lt_add_of_pos_right _ hε))
        (Ioo_mem_nhds hs₀.1 hs₀.2)
    apply mem_of_superset hwin
    rintro s ⟨hswin, hs⟩
    refine ⟨hstep s₀ hs₀ hsmooth s hs ?_, hs⟩
    rw [abs_lt]
    constructor <;> linarith [hswin.1, hswin.2]
  have ht₀_smooth : ContDiffAt ℝ ∞ (fun y ↦ F y t₀) x := by
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [hD.mem_nhds hx] with y hy
    exact hinit y hy
  have ht₀_good : t₀ ∈ good := ⟨ht₀_smooth, ht₀⟩
  have hgood_closed : closure good ∩ Ioo a b ⊆ good := by
    rintro sstar ⟨hsstar_cl, hsstar⟩
    have hnhd : Ioo (sstar - ε) (sstar + ε) ∩ Ioo a b ∈ nhds sstar :=
      inter_mem (Ioo_mem_nhds (sub_lt_self _ hε) (lt_add_of_pos_right _ hε))
        (Ioo_mem_nhds hsstar.1 hsstar.2)
    obtain ⟨sn, ⟨hsn_ball, _⟩, hsn_smooth, hsn⟩ :=
      mem_closure_iff_nhds.mp hsstar_cl _ hnhd
    change ContDiffAt ℝ ∞ (fun y ↦ F y sn) x at hsn_smooth
    have hdist : |sstar - sn| < ε := by
      rw [abs_lt]
      constructor <;> linarith [hsn_ball.1, hsn_ball.2]
    exact ⟨hstep sn hsn hsn_smooth sstar hsstar hdist, hsstar⟩
  have hsub : Ioo a b ⊆ good :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hgood_open
      ⟨t₀, ht₀, ht₀_good⟩ hgood_closed
  exact (show ContDiffAt ℝ ∞ (fun y ↦ F y target) x from
    (hsub htarget).1).contDiffWithinAt

end UniformRestart

end Flow
end ODE
end Analysis
end DifferentialGeometry
