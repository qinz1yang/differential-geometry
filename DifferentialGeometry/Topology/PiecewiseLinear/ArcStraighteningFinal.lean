/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningEnds

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcStraightening_final {S Z D W Bd : Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D) (hγ1 : γ 1 ∈ Bd)
    {Φ : (ℝ × ℝ) × ℝ → A} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A} {τ s : ℝ}
    (hN : IsOpen N) (hΩ : IsOpen Ω) (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω))
    (hτ : 0 < τ) (hs0 : 0 ≤ s) (hs1 : s < 1) (hcore : coreSegment τ ⊆ N)
    (hΦcore : Φ '' coreSegment τ = γ '' Icc 0 s) (hΦtip : Φ ((0, 0), τ) = γ s)
    (hZ : ∀ p ∈ N, Φ p ∈ Z ↔ p ∈ crossPlanes ∧ 0 ≤ p.2)
    (hD : ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2)
    (hW : ∀ p ∈ N, Φ p ∈ W ↔ 0 ≤ p.2) (hBd : ∀ p ∈ N, Φ p ∈ Bd ↔ p.2 = 0)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω' : Set A}
    (hV : IsOpen V) (hΩ' : IsOpen Ω') (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hψZ : ∀ p ∈ V, ψ p ∈ Z ↔ p ∈ crossPlanes ∧ p.2 ≤ 0)
    (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0 ∧ p.2 ≤ 0)
    (hψW : ∀ p ∈ V, ψ p ∈ W ↔ p.2 ≤ 0) (hψBd : ∀ p ∈ V, ψ p ∈ Bd ↔ p.2 = 0)
    (hcov : γ '' Icc s 1 ⊆ S ∩ Ω') :
    ∃ (Φ' : (ℝ × ℝ) × ℝ → A) (N' : Set ((ℝ × ℝ) × ℝ)) (Ω'' : Set A) (τ' : ℝ),
      IsOpen N' ∧ IsOpen Ω'' ∧ IsPLHomeomorphOn Φ' N' (S ∩ Ω'') ∧ 0 < τ' ∧
      coreSegment τ' ⊆ N' ∧ Φ' '' coreSegment τ' = γ '' Icc 0 1 ∧
      (∀ p ∈ N', Φ' p ∈ Z ↔ p ∈ crossPlanes ∧ 0 ≤ p.2 ∧ p.2 ≤ τ') ∧
      (∀ p ∈ N', Φ' p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2 ∧ p.2 ≤ τ') ∧
      (∀ p ∈ N', Φ' p ∈ W ↔ 0 ≤ p.2 ∧ p.2 ≤ τ') ∧
      (∀ p ∈ N', Φ' p ∈ Bd ↔ p.2 = 0 ∨ p.2 = τ') := by
  classical
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → (ℝ × ℝ) × ℝ, w = fun r => Function.invFunOn ψ V (γ r) :=
    ⟨_, rfl⟩
  have hγSΩ : ∀ r ∈ Icc s 1, γ r ∈ S ∩ Ω' := fun r hr => hcov ⟨r, hr, rfl⟩
  have hIcc : ∀ r ∈ Icc s 1, r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hs0.trans hr.1, hr.2⟩
  have hwV : ∀ r ∈ Icc s 1, w r ∈ V := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.surjOn.mapsTo_invFunOn (hγSΩ r hr)
  have hψw : ∀ r ∈ Icc s 1, ψ (w r) = γ r := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.invOn_invFunOn.2 (hγSΩ r hr)
  have hwax : ∀ r ∈ Icc s 1, (w r).1 = 0 ∧ (w r).2 ≤ 0 := fun r hr =>
    (hψD (w r) (hwV r hr)).mp (by rw [hψw r hr]; exact hγD r (hIcc r hr))
  have hweq : ∀ r ∈ Icc s 1, w r = ((0, 0), (w r).2) := fun r hr =>
    Prod.ext ((hwax r hr).1.trans Prod.mk_zero_zero.symm) rfl
  have hνc : ContinuousOn (fun r => (w r).2) (Icc s 1) := by
    have h1 : ContinuousOn (Function.invFunOn ψ V) (S ∩ Ω') :=
      hψ.isPiecewiseAffineOn_invFunOn.continuousOn
    have h2 : ContinuousOn γ (Icc s 1) := hγc.mono fun r hr => hIcc r hr
    rw [hwdef]
    exact continuous_snd.comp_continuousOn (h1.comp h2 fun r hr => hγSΩ r hr)
  have hνi : InjOn (fun r => (w r).2) (Icc s 1) := by
    intro r₁ hr₁ r₂ hr₂ h
    apply hγi (hIcc r₁ hr₁) (hIcc r₂ hr₂)
    rw [← hψw r₁ hr₁, ← hψw r₂ hr₂, hweq r₁ hr₁, hweq r₂ hr₂]
    exact congrArg (fun t => ψ ((0, 0), t)) h
  have hsmem : s ∈ Icc s 1 := ⟨le_rfl, hs1.le⟩
  have h1mem : (1 : ℝ) ∈ Icc s 1 := ⟨hs1.le, le_rfl⟩
  have hw1 : (w 1).2 = 0 := (hψBd (w 1) (hwV 1 h1mem)).mp (by rw [hψw 1 h1mem]; exact hγ1)
  have hlt : (w s).2 < (w 1).2 := by
    rcases (hwax s hsmem).2.lt_or_eq with h | h
    · rwa [hw1]
    · exact absurd (hνi hsmem h1mem (h.trans hw1.symm)) hs1.ne
  have hνmono : StrictMonoOn (fun r => (w r).2) (Icc s 1) :=
    hνc.strictMonoOn_of_injOn_Icc hs1.le hlt.le hνi
  set v' := (w 1).2 - (w s).2 with hv'def
  have hv' : 0 < v' := sub_pos.mpr hlt
  have hws : (w s).2 = -v' := by rw [hv'def, hw1]; ring
  have hcoreψ : ∀ v ∈ Icc (0 : ℝ) v', ∃ r ∈ Icc s 1,
      (w r).2 = (w s).2 + v ∧ w s + ((0, 0), v) = w r := by
    intro v hv
    have hmem : (w s).2 + v ∈ Icc (w s).2 (w 1).2 :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    obtain ⟨r, hr, hνr⟩ := intermediate_value_Icc hs1.le hνc hmem
    simp only at hνr
    refine ⟨r, hr, hνr, ?_⟩
    rw [hweq r hr, hweq s hsmem, hνr]
    ext <;> simp
  have hq₀N : ((0, 0), τ) ∈ N := hcore ⟨rfl, hτ.le, le_rfl⟩
  have hw₀eq : Function.invFunOn ψ V (Φ ((0, 0), τ)) = w s := by rw [hΦtip, hwdef]
  have hori : ∀ v : ℝ, 0 < v → v ≤ v' → ∀ u : ℝ, 0 < u → u ≤ τ →
      Φ ((0, 0), τ - u) ≠ ψ (Function.invFunOn ψ V (Φ ((0, 0), τ)) + ((0, 0), v)) := by
    intro v hv hvv u hu huτ heq
    obtain ⟨r, hr, hνr, hwr⟩ := hcoreψ v ⟨hv.le, hvv⟩
    rw [hw₀eq, hwr, hψw r hr] at heq
    have hmem : Φ ((0, 0), τ - u) ∈ γ '' Icc 0 s := by
      rw [← hΦcore]
      exact ⟨_, ⟨rfl, by linarith, by linarith⟩, rfl⟩
    obtain ⟨r₁, hr₁, hγr₁⟩ := hmem
    have hrr : r₁ = r := hγi ⟨hr₁.1, hr₁.2.trans hs1.le⟩ (hIcc r hr) (hγr₁.trans heq)
    have hrs : r ≠ s := by
      intro hrs
      rw [hrs] at hνr
      linarith
    exact hrs (le_antisymm (hrr ▸ hr₁.2) hr.1)
  obtain ⟨G, ρ, μ, hρ, hμ, hG, hballN, hGloc, hGX, hGL, hGq₀, hGhom, hGcore⟩ :=
    exists_junction hN hV hΩ hΩ' hΦ hψ
      (fun p hp hp2 => by rw [hZ p hp]; exact and_iff_left hp2.le)
      (fun p hp hp2 => by rw [hD p hp]; exact and_iff_left hp2.le)
      (c := 0) (fun p hp hp2 => by rw [hψZ p hp]; exact and_iff_left hp2.le)
      (fun p hp hp2 => by rw [hψD p hp]; exact and_iff_left hp2.le)
      hτ hq₀N (by rw [hΦtip]; exact (hγSΩ s hsmem).2) (by rw [hw₀eq]; linarith)
      hv' hτ hori
  rw [hw₀eq] at hGq₀
  set τ₁ := τ + μ * v' with hτ₁def
  have hμv : 0 < μ * v' := mul_pos hμ hv'
  have hττ₁ : τ < τ₁ := by rw [hτ₁def]; linarith
  have hGq₀' : G ((0, 0), τ) = ((0, 0), -v') := by rw [hGq₀, hweq s hsmem, hws]
  have hGqf : G ((0, 0), τ₁) = 0 := by
    rw [hτ₁def, hGcore (μ * v') hμv.le, hGq₀, mul_div_cancel_left₀ v' hμ.ne', hweq s hsmem,
      hws]
    ext <;> simp
  have hGc : Continuous G := continuousOn_univ.mp hG.isPiecewiseAffineOn.continuousOn
  obtain ⟨Wf, ρf, hρf, -, hWf, hWfG, hWfhom⟩ :=
    hG.exists_isPLHomeomorphOn_univ_homogeneous isOpen_univ isOpen_univ
      (mem_univ ((0, 0), τ₁))
  have hWfq : Wf ((0, 0), τ₁) = 0 := (hWfG (mem_ball_self hρf)).trans hGqf
  have hcyl := add_axis_of_homogeneous hμ hv' hτ₁def hρf hGhom hGq₀' hWfG hWfq hWfhom
  have hflat : ∀ p : (ℝ × ℝ) × ℝ,
      Wf p = Wf (p.1, τ₁) + ((0, 0), (p.2 - τ₁) / μ) := by
    intro p
    have h := hcyl (p.1, 0) (p.2 - τ₁)
    have e1 : ((0, 0), τ₁) + (p.1, (0 : ℝ)) = (p.1, τ₁) := by ext <;> simp
    have e2 : ((0, 0), τ₁) + (p.1, (0 : ℝ)) + ((0, 0), p.2 - τ₁) = p := by ext <;> simp
    rwa [e2, e1] at h
  set lam : ℝ × ℝ → ℝ := fun a => (Wf (a, τ₁)).2 with hlamdef
  have hlamPA : IsPiecewiseAffineOn lam univ := by
    let emb : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) × ℝ :=
      (LinearMap.inl ℝ (ℝ × ℝ) ℝ).toAffineMap + AffineMap.const ℝ (ℝ × ℝ) ((0, 0), τ₁)
    have hemb : IsPiecewiseAffineOn emb univ := isPiecewiseAffineOn_of_affine emb isOpen_univ
    have h := (hWf.isPiecewiseAffineOn.comp hemb).affine_comp
      (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap
    rw [preimage_univ, inter_univ] at h
    refine h.congr fun a _ => ?_
    simp only [hlamdef, Function.comp_apply, emb]
    congr 2
    ext <;> simp
  have hlam0 : lam 0 = 0 := by
    change (Wf ((0, 0), τ₁)).2 = 0
    rw [hWfq]
    rfl
  set cf : ℝ × ℝ → ℝ := fun a => -μ * lam a with hcfdef
  have hcfPA : IsPiecewiseAffineOn cf univ :=
    (isPiecewiseAffineOn_real_affine hlamPA (-μ) 0).congr fun a _ => by simp [hcfdef]
  have hcf0 : cf 0 = 0 := by simp [hcfdef, hlam0]
  set t₁ := τ + μ * v' / 2 with ht₁def
  set Sc := verticalClamp cf t₁ with hScdef
  have hSc : IsPLHomeomorphOn Sc univ univ := isPLHomeomorphOn_verticalClamp hcfPA t₁
  set G' := G ∘ Sc with hG'def
  have hG' : IsPLHomeomorphOn G' univ univ := hSc.trans hG
  have hG'c : Continuous G' := continuousOn_univ.mp hG'.isPiecewiseAffineOn.continuousOn
  have hScfst : ∀ p, (Sc p).1 = p.1 := fun p => rfl
  have hG'X : ∀ p, p ∈ crossPlanes ↔ G' p ∈ crossPlanes := fun p =>
    Iff.trans Iff.rfl (hGX (Sc p))
  have hG'L : ∀ p, p.1 = 0 ↔ (G' p).1 = 0 := fun p => Iff.trans Iff.rfl (hGL (Sc p))
  have hG'axis : ∀ t, G' ((0, 0), t) = G ((0, 0), t) := fun t => by
    simp only [hG'def, Function.comp_apply, hScdef, verticalClamp_axis hcf0]
  set ρ' := min ρ (μ * v' / 2) with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ (by positivity)
  have hball' : ball (((0 : ℝ), (0 : ℝ)), τ) ρ' ⊆ ball ((0, 0), τ) ρ :=
    ball_subset_ball (min_le_left _ _)
  have hScball : ∀ p ∈ ball (((0 : ℝ), (0 : ℝ)), τ) ρ', Sc p = p := by
    intro p hp
    apply verticalClamp_of_le
    have h1 : dist p.2 τ < ρ' := lt_of_le_of_lt (le_max_right _ _) (mem_ball.mp hp)
    rw [Real.dist_eq] at h1
    have h2 := le_abs_self (p.2 - τ)
    have h3 : ρ' ≤ μ * v' / 2 := min_le_right _ _
    rw [ht₁def]
    linarith
  have hG'loc : ∀ p ∈ ball (((0 : ℝ), (0 : ℝ)), τ) ρ', G' p ∈ V ∧ ψ (G' p) = Φ p := by
    intro p hp
    simp only [hG'def, Function.comp_apply, hScball p hp]
    exact hGloc p (hball' hp)
  have hG'core : ∀ u : ℝ, 0 ≤ u → u ≤ μ * v' → ∃ r ∈ Icc s 1,
      G' ((0, 0), τ + u) = w r ∧ (w r).2 = (w s).2 + u / μ := by
    intro u hu huv
    have hmem : u / μ ∈ Icc (0 : ℝ) v' :=
      ⟨div_nonneg hu hμ.le, by rw [div_le_iff₀ hμ]; linarith⟩
    obtain ⟨r, hr, hνr, hwr⟩ := hcoreψ (u / μ) hmem
    exact ⟨r, hr, by rw [hG'axis, hGcore u hu, hGq₀, hwr], hνr⟩
  have hGsurj' : Function.Surjective G' := fun y => by
    obtain ⟨x, -, hx⟩ := hG'.bijOn.surjOn (mem_univ y)
    exact ⟨x, hx⟩
  have hN₂ : IsOpen (G' ⁻¹' V) := hV.preimage hG'c
  have hGimg : G' '' (G' ⁻¹' V) = V := image_preimage_eq V hGsurj'
  have hGN₂ : IsPLHomeomorphOn G' (G' ⁻¹' V) V := by
    have h := hG'.restrict_isOpen hN₂ (subset_univ _) (by rw [hGimg]; exact hV)
    rwa [hGimg] at h
  have hΞ : IsPLHomeomorphOn (ψ ∘ G') (G' ⁻¹' V) (S ∩ Ω') := hGN₂.trans hψ
  set Φ' : (ℝ × ℝ) × ℝ → A := fun p => if p.2 ≤ τ then Φ p else ψ (G' p) with hΦ'def
  set N₁ : Set ((ℝ × ℝ) × ℝ) := (N ∩ {p | p.2 < τ}) ∪ ball ((0, 0), τ) ρ' with hN₁def
  set N₃ : Set ((ℝ × ℝ) × ℝ) := G' ⁻¹' V ∩ {p | τ < p.2} with hN₃def
  have hN₁o : IsOpen N₁ :=
    (hN.inter (isOpen_lt continuous_snd continuous_const)).union isOpen_ball
  have hN₃o : IsOpen N₃ := hN₂.inter (isOpen_lt continuous_const continuous_snd)
  have hN₁N : N₁ ⊆ N := union_subset inter_subset_left fun p hp => (hballN (hball' hp)).1
  have hN₃N₂ : N₃ ⊆ G' ⁻¹' V := inter_subset_left
  have hEq₁ : EqOn Φ' Φ N₁ := by
    rintro p (hp | hp)
    · exact ite_eq_left (le_of_lt hp.2)
    · by_cases h : p.2 ≤ τ
      · exact ite_eq_left h
      · change (if p.2 ≤ τ then Φ p else ψ (G' p)) = Φ p
        rw [ite_eq_right h]
        exact (hG'loc p hp).2
  have hEq₃ : EqOn Φ' (ψ ∘ G') N₃ := fun p hp => ite_eq_right (not_le.mpr hp.2)
  have hpt : ∀ p : (ℝ × ℝ) × ℝ, p.1 = 0 → p = ((0, 0), τ + (p.2 - τ)) := fun p hp =>
    Prod.ext (hp.trans Prod.mk_zero_zero.symm) (by ring)
  have hKlow : ∀ p ∈ coreSegment τ₁, p.2 ≤ τ → p ∈ N₁ := by
    rintro p ⟨hp1, hp2, -⟩ h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl ⟨hcore ⟨hp1, hp2, h.le⟩, h⟩
    · refine Or.inr ?_
      rw [show p = ((0, 0), τ) from Prod.ext (hp1.trans Prod.mk_zero_zero.symm) h]
      exact mem_ball_self hρ'
  have hKhigh : ∀ p ∈ coreSegment τ₁, τ < p.2 →
      p ∈ N₃ ∧ ∃ r ∈ Icc s 1, s < r ∧ Φ' p = γ r := by
    rintro p ⟨hp1, hp2, hp3⟩ h
    obtain ⟨r, hr, hGr, hνr⟩ :=
      hG'core (p.2 - τ) (by linarith) (by rw [hτ₁def] at hp3; linarith)
    have hGp : G' p = w r := by rw [hpt p hp1, hGr]
    have hrs : s < r := by
      rcases hr.1.eq_or_lt with hrs | hrs
      · exfalso
        rw [← hrs] at hνr
        have h0 : (p.2 - τ) / μ = 0 := by linarith
        rw [div_eq_zero_iff] at h0
        rcases h0 with h' | h'
        · linarith
        · exact hμ.ne' h'
      · exact hrs
    refine ⟨⟨?_, h⟩, r, hr, hrs, ?_⟩
    · change G' p ∈ V
      rw [hGp]
      exact hwV r hr
    · change (if p.2 ≤ τ then Φ p else ψ (G' p)) = γ r
      rw [ite_eq_right (not_le.mpr h), hGp, hψw r hr]
  have hKN : coreSegment τ₁ ⊆ N₁ ∪ N₃ := by
    intro p hp
    by_cases h : p.2 ≤ τ
    · exact Or.inl (hKlow p hp h)
    · exact Or.inr (hKhigh p hp (not_le.mp h)).1
  have hΦcont : ContinuousOn Φ N := hΦ.isPiecewiseAffineOn.continuousOn
  have hΞcont : ContinuousOn (ψ ∘ G') (G' ⁻¹' V) := hΞ.isPiecewiseAffineOn.continuousOn
  have hΦ'cont : ContinuousOn Φ' (N₁ ∪ N₃) := by
    refine continuousOn_of_forall_continuousAt fun p hp => ?_
    rcases hp with hp | hp
    · exact (hΦcont.continuousAt (hN.mem_nhds (hN₁N hp))).congr
        (Filter.eventuallyEq_of_mem (hN₁o.mem_nhds hp) fun q hq => (hEq₁ hq).symm)
    · exact (hΞcont.continuousAt (hN₂.mem_nhds (hN₃N₂ hp))).congr
        (Filter.eventuallyEq_of_mem (hN₃o.mem_nhds hp) fun q hq => (hEq₃ hq).symm)
  have hinj₁ : InjOn Φ' N₁ := (hΦ.bijOn.injOn.mono hN₁N).congr hEq₁.symm
  have hinj₃ : InjOn Φ' N₃ := (hΞ.bijOn.injOn.mono hN₃N₂).congr hEq₃.symm
  have hlowimg : ∀ p ∈ coreSegment τ₁, p.2 ≤ τ → Φ' p ∈ γ '' Icc 0 s := by
    intro p hp h
    rw [← hΦcore]
    exact ⟨p, ⟨hp.1, hp.2.1, h⟩, (ite_eq_left h).symm⟩
  have hinjK : InjOn Φ' (coreSegment τ₁) := by
    intro p hp q hq hpq
    by_cases hp2 : p.2 ≤ τ <;> by_cases hq2 : q.2 ≤ τ
    · exact hinj₁ (hKlow p hp hp2) (hKlow q hq hq2) hpq
    · exfalso
      obtain ⟨-, rq, hrq, hsrq, hrqeq⟩ := hKhigh q hq (not_le.mp hq2)
      obtain ⟨r₁, hr₁, hγr₁⟩ := hlowimg p hp hp2
      have := hγi ⟨hr₁.1, hr₁.2.trans hs1.le⟩ (hIcc rq hrq) (hγr₁.trans (hpq.trans hrqeq))
      linarith [hr₁.2]
    · exfalso
      obtain ⟨-, rp, hrp, hsrp, hrpeq⟩ := hKhigh p hp (not_le.mp hp2)
      obtain ⟨r₁, hr₁, hγr₁⟩ := hlowimg q hq hq2
      have := hγi ⟨hr₁.1, hr₁.2.trans hs1.le⟩ (hIcc rp hrp)
        (hγr₁.trans (hpq.symm.trans hrpeq))
      linarith [hr₁.2]
    · exact hinj₃ (hKhigh p hp (not_le.mp hp2)).1 (hKhigh q hq (not_le.mp hq2)).1 hpq
  obtain ⟨N'', hN''o, hKN'', hN''sub, hinjN''⟩ :=
    exists_isOpen_injOn_of_isCompact (hN₁o.union hN₃o) hΦ'cont (isCompact_coreSegment τ₁)
      hKN hinjK (fun p hp => by
        rcases hKN hp with h | h
        · exact ⟨N₁, hN₁o.mem_nhds h, hinj₁⟩
        · exact ⟨N₃, hN₃o.mem_nhds h, hinj₃⟩)
  have hsplit : N'' = (N'' ∩ N₁) ∪ (N'' ∩ N₃) := by
    rw [← inter_union_distrib_left, inter_eq_left.mpr hN''sub]
  obtain ⟨Ω'', hΩ''o, hΦ'PL⟩ := isPLHomeomorphOn_union_of_eqOn hΦ hΞ hΩ hΩ'
    (hN''o.inter hN₁o) (hN''o.inter hN₃o) (inter_subset_right.trans hN₁N)
    (inter_subset_right.trans hN₃N₂) (hEq₁.mono inter_subset_right)
    (hEq₃.mono inter_subset_right) (by rw [← hsplit]; exact hinjN'')
  rw [← hsplit] at hΦ'PL
  have hcase : ∀ p ∈ N'', (p.2 ≤ τ ∧ p ∈ N ∧ Φ' p = Φ p) ∨
      (τ < p.2 ∧ G' p ∈ V ∧ Φ' p = ψ (G' p)) := by
    intro p hp
    by_cases h : p.2 ≤ τ
    · refine Or.inl ⟨h, ?_, ite_eq_left h⟩
      rcases hN''sub hp with h1 | h1
      · exact hN₁N h1
      · exact absurd h1.2 (not_lt.mpr h)
    · refine Or.inr ⟨not_le.mp h, ?_, ite_eq_right h⟩
      rcases hN''sub hp with h1 | h1
      · rcases h1 with h1 | h1
        · exact absurd h1.2 (not_lt.mpr (not_le.mp h).le)
        · exact (hG'loc p h1).1
      · exact h1.1
  set δ₀ := μ * v' / 2 with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hlamc : Continuous lam := continuousOn_univ.mp hlamPA.continuousOn
  obtain ⟨r₁, hr₁, hr₁lam⟩ : ∃ r₁ > 0, ∀ a : ℝ × ℝ, ‖a‖ < r₁ →
      μ * |lam a| < min (δ₀ / 4) (ρf / 4) := by
    have hm : 0 < min (δ₀ / 4) (ρf / 4) / μ :=
      div_pos (lt_min (by positivity) (by positivity)) hμ
    obtain ⟨r, hr, hball⟩ := Metric.continuous_iff.mp hlamc 0 _ hm
    refine ⟨r, hr, fun a ha => ?_⟩
    have h := hball a (by rw [dist_zero_right]; exact ha)
    rw [Real.dist_eq, hlam0, sub_zero, lt_div_iff₀ hμ] at h
    linarith [mul_comm μ |lam a|]
  set rT := min (min (δ₀ / 2) (ρf / 2)) r₁ with hrTdef
  have hrT : 0 < rT := lt_min (lt_min (by positivity) (by positivity)) hr₁
  have hrTδ : rT ≤ δ₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hrTρ : rT ≤ ρf / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hTprop : ∀ p ∈ ball (((0 : ℝ), (0 : ℝ)), τ₁) rT, (G' p).2 = (p.2 - τ₁) / μ := by
    intro p hp
    have hd := mem_ball.mp hp
    rw [Prod.dist_eq] at hd
    have hp1 : ‖p.1‖ < rT := by
      have h := lt_of_le_of_lt (le_max_left _ _) hd
      rwa [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, dist_zero_right] at h
    have hp2 : |p.2 - τ₁| < rT := by
      have h := lt_of_le_of_lt (le_max_right _ _) hd
      rwa [Real.dist_eq] at h
    have hcfp := hr₁lam p.1 (lt_of_lt_of_le hp1 (min_le_right _ _))
    have hcfabs : |cf p.1| = μ * |lam p.1| := by
      rw [hcfdef]
      simp only
      rw [abs_mul, abs_neg, abs_of_pos hμ]
    have hc1 : μ * |lam p.1| < δ₀ / 4 := lt_of_lt_of_le hcfp (min_le_left _ _)
    have hc2 : μ * |lam p.1| < ρf / 4 := lt_of_lt_of_le hcfp (min_le_right _ _)
    have hge : 2 * |cf p.1| ≤ p.2 - t₁ := by
      rw [hcfabs, ht₁def]
      have h3 := neg_abs_le (p.2 - τ₁)
      have h4 : τ₁ = τ + 2 * δ₀ := by rw [hτ₁def, hδ₀def]; ring
      linarith
    have hSp : Sc p = (p.1, p.2 + cf p.1) := verticalClamp_of_ge hge
    have hSball : Sc p ∈ ball (((0 : ℝ), (0 : ℝ)), τ₁) ρf := by
      rw [hSp, mem_ball, Prod.dist_eq]
      apply max_lt
      · rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, dist_zero_right]
        linarith
      · rw [Real.dist_eq]
        calc |p.2 + cf p.1 - τ₁| = |(p.2 - τ₁) + cf p.1| := by ring_nf
          _ ≤ |p.2 - τ₁| + |cf p.1| := abs_add_le _ _
          _ < ρf := by rw [hcfabs]; linarith
    have hG'p : G' p = Wf (Sc p) := by
      simp only [hG'def, Function.comp_apply]
      exact (hWfG hSball).symm
    rw [hG'p, hflat (Sc p), hSp, Prod.snd_add]
    change lam p.1 + ((p.2 + -μ * lam p.1 - τ₁) / μ) = (p.2 - τ₁) / μ
    field_simp
    ring
  set Mset : Set ((ℝ × ℝ) × ℝ) := {p | (G' p).2 < 0 ∧ p.2 < τ₁ - rT / 2} with hMdef
  have hMo : IsOpen Mset := (isOpen_lt (continuous_snd.comp hG'c) continuous_const).inter
    (isOpen_lt continuous_snd continuous_const)
  set Nf := N'' ∩ (({p | p.2 < τ} ∪ Mset) ∪ ball (((0 : ℝ), (0 : ℝ)), τ₁) rT) with hNfdef
  have hNfo : IsOpen Nf := hN''o.inter
    (((isOpen_lt continuous_snd continuous_const).union hMo).union isOpen_ball)
  have hNfsub : Nf ⊆ N'' := inter_subset_left
  have hKNf : coreSegment τ₁ ⊆ Nf := by
    intro p hp
    refine ⟨hKN'' hp, ?_⟩
    obtain ⟨hp1, hp2, hp3⟩ := hp
    by_cases h1 : p.2 < τ
    · exact Or.inl (Or.inl h1)
    by_cases h2 : p.2 < τ₁ - rT / 2
    · refine Or.inl (Or.inr ⟨?_, h2⟩)
      obtain ⟨r, hr, hGr, hνr⟩ :=
        hG'core (p.2 - τ) (by linarith) (by rw [hτ₁def] at hp3; linarith)
      rw [hpt p hp1, hGr, hνr, hws]
      have h3 : p.2 - τ < μ * v' := by rw [hτ₁def] at h2; linarith
      have h4 : (p.2 - τ) / μ < v' := by rw [div_lt_iff₀ hμ]; linarith
      linarith
    · refine Or.inr ?_
      rw [show p = ((0, 0), p.2) from Prod.ext (hp1.trans Prod.mk_zero_zero.symm) rfl,
        mem_ball, dist_corePoint, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
  have hheight : ∀ p ∈ Nf, τ < p.2 →
      ((G' p).2 ≤ 0 ↔ p.2 ≤ τ₁) ∧ ((G' p).2 = 0 ↔ p.2 = τ₁) := by
    rintro p ⟨-, hp⟩ hpτ
    rcases hp with (hp | hp) | hp
    · exact absurd hp (not_lt.mpr hpτ.le)
    · have h3 : p.2 < τ₁ := by linarith [hp.2]
      exact ⟨iff_of_true hp.1.le h3.le, iff_of_false hp.1.ne h3.ne⟩
    · rw [hTprop p hp]
      refine ⟨?_, ?_⟩
      · rw [div_le_iff₀ hμ, zero_mul]
        constructor <;> intro h <;> linarith
      · rw [div_eq_zero_iff, sub_eq_zero]
        exact ⟨fun h => h.resolve_right hμ.ne', Or.inl⟩
  obtain ⟨O₃, hO₃, himg₃⟩ := hΦ'PL.exists_image_eq_inter hNfo
  rw [inter_eq_right.mpr hNfsub] at himg₃
  have hΦ'Nf := hΦ'PL.restrict_of_image_eq_inter hNfo hNfsub hO₃ (by rw [himg₃, inter_assoc])
  rw [inter_assoc] at hΦ'Nf
  refine ⟨Φ', Nf, Ω'' ∩ O₃, τ₁, hNfo, hΩ''o.inter hO₃, hΦ'Nf, by linarith, hKNf, ?_, ?_, ?_,
    ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      by_cases h : p.2 ≤ τ
      · exact image_mono (Icc_subset_Icc le_rfl hs1.le) (hlowimg p hp h)
      · obtain ⟨-, r, hr, -, heq⟩ := hKhigh p hp (not_le.mp h)
        exact ⟨r, ⟨hs0.trans hr.1, hr.2⟩, heq.symm⟩
    · rintro _ ⟨r, hr, rfl⟩
      by_cases hrs : r ≤ s
      · have hmem : γ r ∈ Φ '' coreSegment τ := by
          rw [hΦcore]
          exact ⟨r, ⟨hr.1, hrs⟩, rfl⟩
        obtain ⟨p, hp, hpeq⟩ := hmem
        exact ⟨p, ⟨hp.1, hp.2.1, hp.2.2.trans hττ₁.le⟩, by rw [← hpeq]; exact ite_eq_left hp.2.2⟩
      · rw [not_le] at hrs
        have hrmem : r ∈ Icc s 1 := ⟨hrs.le, hr.2⟩
        have hv : 0 < (w r).2 - (w s).2 := sub_pos.mpr (hνmono hsmem hrmem hrs)
        have hvle : (w r).2 - (w s).2 ≤ v' := by
          have h1 := hνmono.monotoneOn hrmem h1mem hr.2
          rw [hv'def]
          linarith
        obtain ⟨r', hr', hGr', hνr'⟩ :=
          hG'core (μ * ((w r).2 - (w s).2)) (by positivity)
            (mul_le_mul_of_nonneg_left hvle hμ.le)
        have hr'r : r' = r := by
          apply hνi hr' hrmem
          simp only
          rw [hνr', mul_div_cancel_left₀ _ hμ.ne']
          ring
        have hmem : ((0, 0), τ + μ * ((w r).2 - (w s).2)) ∈ coreSegment τ₁ :=
          ⟨rfl, by nlinarith, by rw [hτ₁def]; nlinarith⟩
        refine ⟨_, hmem, ?_⟩
        change (if τ + μ * ((w r).2 - (w s).2) ≤ τ then Φ _ else ψ (G' _)) = γ r
        rw [ite_eq_right (by nlinarith), hGr', hr'r, hψw r hrmem]
  · intro p hp
    rcases hcase p (hNfsub hp) with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq, hZ p hpN]
      exact ⟨fun ⟨a, b⟩ => ⟨a, b, by linarith⟩, fun ⟨a, b, _⟩ => ⟨a, b⟩⟩
    · rw [heq, hψZ _ hGV, ← hG'X p, (hheight p hp h).1]
      exact ⟨fun ⟨a, b⟩ => ⟨a, by linarith, b⟩, fun ⟨a, _, b⟩ => ⟨a, b⟩⟩
  · intro p hp
    rcases hcase p (hNfsub hp) with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq, hD p hpN]
      exact ⟨fun ⟨a, b⟩ => ⟨a, b, by linarith⟩, fun ⟨a, b, _⟩ => ⟨a, b⟩⟩
    · rw [heq, hψD _ hGV, ← hG'L p, (hheight p hp h).1]
      exact ⟨fun ⟨a, b⟩ => ⟨a, by linarith, b⟩, fun ⟨a, _, b⟩ => ⟨a, b⟩⟩
  · intro p hp
    rcases hcase p (hNfsub hp) with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq, hW p hpN]
      exact ⟨fun a => ⟨a, by linarith⟩, fun ⟨a, _⟩ => a⟩
    · rw [heq, hψW _ hGV, (hheight p hp h).1]
      exact ⟨fun b => ⟨by linarith, b⟩, fun ⟨_, b⟩ => b⟩
  · intro p hp
    rcases hcase p (hNfsub hp) with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq, hBd p hpN]
      exact ⟨Or.inl, fun h' => h'.resolve_right (by linarith)⟩
    · rw [heq, hψBd _ hGV, (hheight p hp h).2]
      exact ⟨Or.inr, fun h' => h'.resolve_left (by linarith)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
