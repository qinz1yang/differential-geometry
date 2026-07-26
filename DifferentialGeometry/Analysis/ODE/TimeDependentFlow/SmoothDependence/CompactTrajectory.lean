import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.SmoothDependence.GlobalClosedManifold

/-!
# Smooth dependence along compact manifold trajectories

This file upgrades local smooth manifold flows to a uniform restart window
along one compact trajectory, then propagates smooth dependence of any selected
exact trajectory family from its identity slice to every interior time.

Unlike the closed-manifold flow theorem, compactness is required only for the
single reference orbit used at the point where smoothness is checked.
-/

noncomputable section

open Set Function Filter Metric Bundle
open scoped Topology NNReal ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M] [T2Space M]

/-- A smooth time-dependent vector field has a common positive local-flow
window over a compact set of initial points at one anchor time. -/
theorem exists_flow_compact [CompleteSpace E] [I.Boundaryless]
    (X : ℝ → ∀ x : M, TangentSpace I x)
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)))
    (t₀ : ℝ) {K : Set M} (hK : IsCompact K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∈ K,
      ∃ (U : Set M), IsOpen U ∧ y ∈ U ∧
        ∃ Φ : M → ℝ → M,
          (∀ z ∈ U, Φ z t₀ = z) ∧
          ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.2 q.1)
            (Set.Ioo (t₀ - ε) (t₀ + ε) ×ˢ U) ∧
          (∀ z ∈ U, ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
            HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Φ z s) t
              ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Φ z t)))) := by
  classical
  have hlocal : ∀ p₀ : M, ∃ (U : Set M) (_ : IsOpen U) (_ : p₀ ∈ U)
      (T : ℝ) (_ : 0 < T) (Phi : M → ℝ → M),
      (∀ p ∈ U, Phi p t₀ = p) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Phi q.2 q.1)
        (Set.Ioo (t₀ - T) (t₀ + T) ×ˢ U) ∧
      (∀ p ∈ U, ∀ t ∈ Set.Ioo (t₀ - T) (t₀ + T),
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => Phi p s) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (X t (Phi p t)))) :=
    fun p₀ => local_flow_jointSmooth_and_integralCurve X hX t₀ p₀
  choose U hU_open hU_mem Tloc hTloc_pos Phi hPhi_init hPhi_smooth hPhi_bare
    using hlocal
  have hcover : K ⊆ ⋃ p, U p := fun x hx => Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨s, hs_cover⟩ := hK.elim_finite_subcover U hU_open hcover
  by_cases hs_ne : s.Nonempty
  · let ε : ℝ := s.inf' hs_ne Tloc
    have hε : 0 < ε := by
      rw [show ε = s.inf' hs_ne Tloc by rfl, Finset.lt_inf'_iff]
      exact fun i _ => hTloc_pos i
    have hε_le : ∀ i ∈ s, ε ≤ Tloc i := fun i hi => Finset.inf'_le _ hi
    refine ⟨ε, hε, ?_⟩
    intro y hy
    have hymem := hs_cover hy
    rw [Set.mem_iUnion₂] at hymem
    obtain ⟨i, hi, hyU⟩ := hymem
    refine ⟨U i, hU_open i, hyU, Phi i, hPhi_init i, ?_, ?_⟩
    · exact (hPhi_smooth i).mono (Set.prod_mono
        (Set.Ioo_subset_Ioo (by linarith [hε_le i hi]) (by linarith [hε_le i hi]))
        (subset_refl _))
    · intro z hz t ht
      exact hPhi_bare i z hz t
        ((Set.Ioo_subset_Ioo (by linarith [hε_le i hi])
          (by linarith [hε_le i hi])) ht)
  · refine ⟨1, one_pos, ?_⟩
    intro y hy
    have hymem := hs_cover hy
    rw [Set.mem_iUnion₂] at hymem
    exact (hs_ne ⟨hymem.choose, hymem.choose_spec.1⟩).elim

/-- Exact trajectories of a globally smooth autonomous manifold field depend
smoothly on their initial point at every interior time. -/
theorem flow_slice_smooth [CompleteSpace E] [I.Boundaryless]
    (v : ∀ x : M, TangentSpace I x)
    (hv : ContMDiff I I.tangent ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)))
    {D : Set M} (hD : IsOpen D) {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    {F : M → ℝ → M}
    (hinit : ∀ x ∈ D, F x t₀ = x)
    (hcont : ∀ x ∈ D, ContinuousOn (F x) (Icc a b))
    (hderiv : ∀ x ∈ D, ∀ t ∈ Ioo a b,
      HasMFDerivAt 𝓘(ℝ, ℝ) I (F x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (v (F x t)))) :
    ∀ t ∈ Ioo a b, ContMDiffOn I I ∞ (fun x => F x t) D := by
  let X : ℝ → ∀ x : M, TangentSpace I x := fun _ x => v x
  have hX : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M =>
        (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) := by
    exact hv.comp contMDiff_snd
  have hXauto : AutonomizedFieldJointC1 (I := I) X :=
    autonomizedFieldJointC1_of_contMDiff X hX
  intro target htarget x hx
  let K : Set M := F x '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn (hcont x hx)
  obtain ⟨ε, hε, hlocal⟩ := exists_flow_compact X hX 0 hK
  have hstep : ∀ s₀ ∈ Ioo a b,
      ContMDiffAt I I ∞ (fun y => F y s₀) x →
      ∀ s ∈ Ioo a b, |s - s₀| < ε →
        ContMDiffAt I I ∞ (fun y => F y s) x := by
    intro s₀ hs₀ hsmooth s hs hss₀
    have hyK : F x s₀ ∈ K :=
      ⟨s₀, ⟨le_of_lt hs₀.1, le_of_lt hs₀.2⟩, rfl⟩
    obtain ⟨U, hU, hyU, Phi, hPhi₀, hPhi_smooth, hPhi_bare⟩ :=
      hlocal (F x s₀) hyK
    have htau : s - s₀ ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt]
      exact hss₀
    have hp_mem : (s - s₀, F x s₀) ∈ Ioo (-ε) ε ×ˢ U := ⟨htau, hyU⟩
    have hp_mem' : (s - s₀, F x s₀) ∈ Ioo ((0 : ℝ) - ε) (0 + ε) ×ˢ U := by
      simpa only [zero_sub, zero_add] using hp_mem
    have hPhi_at : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I ∞
        (fun q : ℝ × M => Phi q.2 q.1) (s - s₀, F x s₀) :=
      (hPhi_smooth _ hp_mem').contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds hp_mem')
    have hpair : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ∞
        (fun y => (s - s₀, F y s₀)) x :=
      contMDiffAt_const.prodMk hsmooth
    have hcand : ContMDiffAt I I ∞
        (fun y => Phi (F y s₀) (s - s₀)) x :=
      hPhi_at.comp x hpair
    have hstate : (fun y => F y s₀) ⁻¹' U ∈ nhds x :=
      hsmooth.continuousAt.preimage_mem_nhds (hU.mem_nhds hyU)
    have heq : (fun y => Phi (F y s₀) (s - s₀)) =ᶠ[nhds x]
        (fun y => F y s) := by
      filter_upwards [hD.mem_nhds hx, hstate] with y hyD hyState
      let left : ℝ → M := fun t => Phi (F y s₀) (t - s₀)
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
      have hleft : ∀ t ∈ Ioo lo hi,
          HasMFDerivAt 𝓘(ℝ, ℝ) I left t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (left t))) := by
        intro t ht
        have httau : t - s₀ ∈ Ioo (-ε) ε := by
          have htleft : s₀ - ε < t :=
            lt_of_le_of_lt (le_max_right a (s₀ - ε)) ht.1
          have htright : t < s₀ + ε :=
            lt_of_lt_of_le ht.2 (min_le_right b (s₀ + ε))
          constructor <;> linarith
        have httau' : t - s₀ ∈ Ioo ((0 : ℝ) - ε) (0 + ε) := by
          simpa only [zero_sub, zero_add] using httau
        have houter := hPhi_bare (F y s₀) hyState (t - s₀) httau'
        have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
            (fun u : ℝ => u - s₀) t (1 : ℝ →L[ℝ] ℝ) := by
          rw [hasMFDerivAt_iff_hasFDerivAt]
          have hfd := ((hasDerivAt_id t).sub_const s₀).hasFDerivAt
          have hid : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) =
              (1 : ℝ →L[ℝ] ℝ) := by
            ext1
            simp
          rwa [hid] at hfd
        have hcomp := houter.comp t hshift
        simpa only [left, X] using hcomp
      have hright : ∀ t ∈ Ioo lo hi,
          HasMFDerivAt 𝓘(ℝ, ℝ) I (F y) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight (v (F y t))) := by
        intro t ht
        exact hderiv y hyD t ⟨lt_of_le_of_lt (le_max_left _ _) ht.1,
          lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
      have hleft_on : ∀ t ∈ Ioo lo hi,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (fun _ : M => left u) y) (Ioo lo hi) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (X t ((fun _ : M => left t) y))) := by
        intro t ht
        simpa only [X] using (hleft t ht).hasMFDerivWithinAt
      have hright_on : ∀ t ∈ Ioo lo hi,
          HasMFDerivWithinAt 𝓘(ℝ, ℝ) I
            (fun u : ℝ => (fun _ : M => F y u) y) (Ioo lo hi) t
            ((1 : ℝ →L[ℝ] ℝ).smulRight
              (X t ((fun _ : M => F y t) y))) := by
        intro t ht
        simpa only [X] using (hright t ht).hasMFDerivWithinAt
      have hstart : left s₀ = F y s₀ := by
        simpa only [left, sub_self] using hPhi₀ (F y s₀) hyState
      have hunique := bare_integral_flow_eqOn_of_jointC1
        (a := lo) (b := hi) (t₀ := s₀) X hXauto
        (fun t _ => left t) (fun t _ => F y t) y y hs₀J
        hleft_on hright_on hstart s hsJ
      simpa only [left] using hunique
    exact hcand.congr_of_eventuallyEq heq.symm
  let good : Set ℝ :=
    {s | ContMDiffAt I I ∞ (fun y => F y s) x} ∩ Ioo a b
  have hgood_open : IsOpen good := by
    rw [isOpen_iff_mem_nhds]
    rintro s₀ ⟨hsmooth, hs₀⟩
    change ContMDiffAt I I ∞ (fun y => F y s₀) x at hsmooth
    have hwin : Ioo (s₀ - ε) (s₀ + ε) ∩ Ioo a b ∈ nhds s₀ :=
      inter_mem (Ioo_mem_nhds (sub_lt_self _ hε) (lt_add_of_pos_right _ hε))
        (Ioo_mem_nhds hs₀.1 hs₀.2)
    apply mem_of_superset hwin
    rintro s ⟨hswin, hs⟩
    refine ⟨hstep s₀ hs₀ hsmooth s hs ?_, hs⟩
    rw [abs_lt]
    constructor <;> linarith [hswin.1, hswin.2]
  have ht₀_smooth : ContMDiffAt I I ∞ (fun y => F y t₀) x := by
    apply contMDiffAt_id.congr_of_eventuallyEq
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
    change ContMDiffAt I I ∞ (fun y => F y sn) x at hsn_smooth
    have hdist : |sstar - sn| < ε := by
      rw [abs_lt]
      constructor <;> linarith [hsn_ball.1, hsn_ball.2]
    exact ⟨hstep sn hsn hsn_smooth sstar hsstar hdist, hsstar⟩
  have hsub : Ioo a b ⊆ good :=
    isPreconnected_Ioo.subset_of_closure_inter_subset hgood_open
      ⟨t₀, ht₀, ht₀_good⟩ hgood_closed
  exact (show ContMDiffAt I I ∞ (fun y => F y target) x from
    (hsub htarget).1).contMDiffWithinAt

end DifferentialGeometry.PDE.RicciFlow.ODE

end
