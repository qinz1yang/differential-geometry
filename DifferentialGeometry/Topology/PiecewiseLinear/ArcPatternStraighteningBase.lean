/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningStep

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

private theorem exists_coreSegment_of_increasing_lift {S D : Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A}
    (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω))
    (h0 : (0 : (ℝ × ℝ) × ℝ) ∈ V) (hψ0 : ψ 0 = γ 0)
    (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0)
    {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    (hγmem : ∀ r ∈ Icc 0 s, γ r ∈ S ∩ Ω)
    (hdir : (Function.invFunOn ψ V (γ 0)).2 < (Function.invFunOn ψ V (γ s)).2) :
    ∃ τ : ℝ, 0 < τ ∧ coreSegment τ ⊆ V ∧
      ψ '' coreSegment τ = γ '' Icc 0 s ∧ ψ ((0, 0), τ) = γ s := by
  have hIcc : ∀ r ∈ Icc 0 s, r ∈ Icc (0 : ℝ) 1 :=
    fun r hr => ⟨hr.1, hr.2.trans hs1⟩
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → (ℝ × ℝ) × ℝ, w = fun r => Function.invFunOn ψ V (γ r) :=
    ⟨_, rfl⟩
  have hwV : ∀ r ∈ Icc 0 s, w r ∈ V := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.surjOn.mapsTo_invFunOn (hγmem r hr)
  have hψw : ∀ r ∈ Icc 0 s, ψ (w r) = γ r := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.invOn_invFunOn.2 (hγmem r hr)
  have hwax : ∀ r ∈ Icc 0 s, (w r).1 = 0 := fun r hr =>
    (hψD (w r) (hwV r hr)).mp (by rw [hψw r hr]; exact hγD r (hIcc r hr))
  have hweq : ∀ r ∈ Icc 0 s, w r = ((0, 0), (w r).2) := fun r hr =>
    Prod.ext ((hwax r hr).trans Prod.mk_zero_zero.symm) rfl
  have hw0 : w 0 = 0 := by
    have h := hψ.bijOn.injOn.leftInvOn_invFunOn h0
    rw [hwdef]
    change Function.invFunOn ψ V (γ 0) = 0
    rw [← hψ0]
    exact h
  have hνc : ContinuousOn (fun r => (w r).2) (Icc 0 s) := by
    have h1 : ContinuousOn (Function.invFunOn ψ V) (S ∩ Ω) :=
      hψ.isPiecewiseAffineOn_invFunOn.continuousOn
    have h2 : ContinuousOn γ (Icc 0 s) := hγc.mono fun r hr => hIcc r hr
    rw [hwdef]
    exact continuous_snd.comp_continuousOn (h1.comp h2 fun r hr => hγmem r hr)
  have hνi : InjOn (fun r => (w r).2) (Icc 0 s) := by
    intro r₁ hr₁ r₂ hr₂ h
    apply hγi (hIcc r₁ hr₁) (hIcc r₂ hr₂)
    rw [← hψw r₁ hr₁, ← hψw r₂ hr₂, hweq r₁ hr₁, hweq r₂ hr₂]
    exact congrArg (fun t => ψ ((0, 0), t)) h
  have h0mem : (0 : ℝ) ∈ Icc 0 s := ⟨le_rfl, hs.le⟩
  have hsmem : s ∈ Icc 0 s := ⟨hs.le, le_rfl⟩
  have hw0' : (w 0).2 = 0 := by rw [hw0]; rfl
  have hle : (w 0).2 ≤ (w s).2 := by
    rw [hwdef]
    exact hdir.le
  have hmono : StrictMonoOn (fun r => (w r).2) (Icc 0 s) :=
    hνc.strictMonoOn_of_injOn_Icc hs.le hle hνi
  have hτ : 0 < (w s).2 := by
    have := hmono h0mem hsmem hs
    simp only at this
    rwa [hw0'] at this
  have hseg : ∀ p ∈ coreSegment (w s).2, ∃ r ∈ Icc 0 s, w r = p := by
    rintro p ⟨hp1, hp2, hp3⟩
    have hmem : p.2 ∈ Icc (w 0).2 (w s).2 := ⟨by rw [hw0']; exact hp2, hp3⟩
    obtain ⟨r, hr, hνr⟩ := intermediate_value_Icc hs.le hνc hmem
    simp only at hνr
    exact ⟨r, hr, by rw [hweq r hr, hνr]; exact Prod.ext (Prod.mk_zero_zero.trans hp1.symm) rfl⟩
  have hnonneg (r : ℝ) (hr : r ∈ Icc 0 s) : 0 ≤ (w r).2 := by
    rw [← hw0']
    exact hmono.monotoneOn h0mem hr hr.1
  refine ⟨(w s).2, hτ, fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hseg p hp
    exact hwV r hr
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨r, hr, rfl⟩ := hseg p hp
      exact ⟨r, hr, (hψw r hr).symm⟩
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨w r, ⟨hwax r hr, hnonneg r hr, ?_⟩, hψw r hr⟩
      rcases hr.2.eq_or_lt with h | h
      · rw [h]
      · exact (hmono hr hsmem h).le
  · rw [← hψw s hsmem, hweq s hsmem]

theorem exists_arcPatternStraightening_base {ι : Type*} (P : ι → Set (ℝ × ℝ))
    {S D : Set A} {Z : ι → Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγS : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ S) (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω))
    (hγ0Ω : γ 0 ∈ Ω) (hψZ : ∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i))
    (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0) :
    ∃ (Φ : (ℝ × ℝ) × ℝ → A) (N : Set ((ℝ × ℝ) × ℝ)) (s τ : ℝ),
      IsOpen N ∧ IsPLHomeomorphOn Φ N (S ∩ Ω) ∧ 0 < s ∧ s < 1 ∧ 0 < τ ∧
      coreSegment τ ⊆ N ∧ Φ '' coreSegment τ = γ '' Icc 0 s ∧
      Φ 0 = γ 0 ∧ Φ ((0, 0), τ) = γ s ∧
      (∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i)) ∧
      ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 := by
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  let w₀ := Function.invFunOn ψ V (γ 0)
  have hw₀V : w₀ ∈ V := hψ.bijOn.surjOn.mapsTo_invFunOn ⟨hγS 0 hzero, hγ0Ω⟩
  have hψw₀ : ψ w₀ = γ 0 := hψ.bijOn.invOn_invFunOn.2 ⟨hγS 0 hzero, hγ0Ω⟩
  have hw₀axis : w₀.1 = 0 := (hψD w₀ hw₀V).mp (hψw₀.symm ▸ hγD 0 hzero)
  let T : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => p + w₀
  let N := T ⁻¹' V
  have hTcont : Continuous T := continuous_id.add continuous_const
  have hN : IsOpen N := hV.preimage hTcont
  have hTsurj : Function.Surjective T := fun y => ⟨y - w₀, sub_add_cancel y w₀⟩
  have hTimage : T '' N = V := image_preimage_eq V hTsurj
  have hT : IsPLHomeomorphOn T N V := by
    have h := (isPLHomeomorphOn_add_const w₀).restrict_isOpen hN (subset_univ N)
      (hTimage.symm ▸ hV)
    rwa [hTimage] at h
  let φ := ψ ∘ T
  have hφ : IsPLHomeomorphOn φ N (S ∩ Ω) := hT.trans hψ
  have h0N : (0 : (ℝ × ℝ) × ℝ) ∈ N := by
    change 0 + w₀ ∈ V
    simpa only [zero_add] using hw₀V
  have hφ0 : φ 0 = γ 0 := by
    change ψ (0 + w₀) = γ 0
    rwa [zero_add]
  have hφZ (i : ι) (p : (ℝ × ℝ) × ℝ) (hp : p ∈ N) : φ p ∈ Z i ↔ p.1 ∈ P i := by
    change ψ (p + w₀) ∈ Z i ↔ p.1 ∈ P i
    rw [hψZ i _ hp, Prod.fst_add, hw₀axis, add_zero]
  have hφD (p : (ℝ × ℝ) × ℝ) (hp : p ∈ N) : φ p ∈ D ↔ p.1 = 0 := by
    change ψ (p + w₀) ∈ D ↔ p.1 = 0
    rw [hψD _ hp, Prod.fst_add, hw₀axis, add_zero]
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.mp hγc Ω hΩ
  have h0u : (0 : ℝ) ∈ u := by
    have h : (0 : ℝ) ∈ γ ⁻¹' Ω ∩ Icc 0 1 := ⟨hγ0Ω, hzero⟩
    rw [hueq] at h
    exact h.1
  obtain ⟨δ, hδ, hδu⟩ := Metric.isOpen_iff.mp hu 0 h0u
  let s := min (δ / 2) (1 / 2)
  have hs : 0 < s := lt_min (half_pos hδ) (by norm_num)
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hIcc : ∀ r ∈ Icc 0 s, r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hr.1, hr.2.trans hs1.le⟩
  have hγmem : ∀ r ∈ Icc 0 s, γ r ∈ S ∩ Ω := by
    intro r hr
    refine ⟨hγS r (hIcc r hr), ?_⟩
    have hru : r ∈ u := hδu (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact lt_of_le_of_lt (hr.2.trans (min_le_left _ _)) (half_lt_self hδ))
    have h : r ∈ u ∩ Icc 0 1 := ⟨hru, hIcc r hr⟩
    rw [← hueq] at h
    exact h.1
  have h0s : (0 : ℝ) ∈ Icc (0 : ℝ) s := ⟨le_rfl, hs.le⟩
  have hss : s ∈ Icc (0 : ℝ) s := ⟨hs.le, le_rfl⟩
  have haxis (r : ℝ) (hr : r ∈ Icc 0 s) :
      (Function.invFunOn φ N (γ r)).1 = 0 := by
    apply (hφD _ (hφ.bijOn.surjOn.mapsTo_invFunOn (hγmem r hr))).mp
    rw [hφ.bijOn.invOn_invFunOn.2 (hγmem r hr)]
    exact hγD r (hIcc r hr)
  have hne : (Function.invFunOn φ N (γ 0)).2 ≠ (Function.invFunOn φ N (γ s)).2 := by
    intro heq
    have hi : Function.invFunOn φ N (γ 0) = Function.invFunOn φ N (γ s) :=
      Prod.ext ((haxis 0 h0s).trans (haxis s hss).symm) heq
    have hγeq := congrArg φ hi
    rw [hφ.bijOn.invOn_invFunOn.2 (hγmem 0 h0s),
      hφ.bijOn.invOn_invFunOn.2 (hγmem s hss)] at hγeq
    exact hs.ne' (hγi hzero (hIcc s hss) hγeq).symm
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨τ, hτ, hcore, himage, htip⟩ :=
      exists_coreSegment_of_increasing_lift hγc hγi hγD hφ h0N hφ0 hφD hs hs1.le hγmem hlt
    exact ⟨φ, N, s, τ, hN, hφ, hs, hs1, hτ, hcore, himage, hφ0, htip, hφZ, hφD⟩
  · have hfcont : Continuous axisFlip := continuous_fst.prodMk continuous_snd.neg
    have hφf : IsPLHomeomorphOn (φ ∘ axisFlip) (axisFlip ⁻¹' N) (S ∩ Ω) :=
      (isPLHomeomorphOn_axisFlip hN).trans hφ
    have hinvf : ∀ z ∈ S ∩ Ω, Function.invFunOn (φ ∘ axisFlip) (axisFlip ⁻¹' N) z =
        axisFlip (Function.invFunOn φ N z) := by
      intro z hz
      have ha := hφ.bijOn.surjOn.mapsTo_invFunOn hz
      have hφa := hφ.bijOn.invOn_invFunOn.2 hz
      have hfa : axisFlip (Function.invFunOn φ N z) ∈ axisFlip ⁻¹' N := by
        rw [mem_preimage, axisFlip_axisFlip]
        exact ha
      apply hφf.bijOn.injOn (hφf.bijOn.surjOn.mapsTo_invFunOn hz) hfa
      rw [hφf.bijOn.invOn_invFunOn.2 hz, Function.comp_apply, axisFlip_axisFlip, hφa]
    have hf0 : (φ ∘ axisFlip) 0 = γ 0 := by simpa only [Function.comp_apply, axisFlip,
      Prod.fst_zero, Prod.snd_zero, neg_zero, Prod.mk_zero_zero] using hφ0
    have h0f : (0 : (ℝ × ℝ) × ℝ) ∈ axisFlip ⁻¹' N := by
      simpa only [mem_preimage, axisFlip, Prod.fst_zero, Prod.snd_zero, neg_zero,
        Prod.mk_zero_zero] using h0N
    have hdir : (Function.invFunOn (φ ∘ axisFlip) (axisFlip ⁻¹' N) (γ 0)).2 <
        (Function.invFunOn (φ ∘ axisFlip) (axisFlip ⁻¹' N) (γ s)).2 := by
      rw [hinvf _ (hγmem 0 h0s), hinvf _ (hγmem s hss)]
      simp only [axisFlip]
      linarith
    obtain ⟨τ, hτ, hcore, himage, htip⟩ :=
      exists_coreSegment_of_increasing_lift hγc hγi hγD hφf h0f hf0
        (fun p hp => hφD (axisFlip p) hp) hs hs1.le hγmem hdir
    exact ⟨φ ∘ axisFlip, axisFlip ⁻¹' N, s, τ, hN.preimage hfcont, hφf, hs, hs1, hτ,
      hcore, himage, hf0, htip, fun i p hp => hφZ i (axisFlip p) hp,
      fun p hp => hφD (axisFlip p) hp⟩

end DifferentialGeometry.Topology.PiecewiseLinear
