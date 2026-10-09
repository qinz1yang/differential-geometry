/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcPatternStraighteningJunction
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningStep

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcPatternStraightening_step_of_lt {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    {S D : Set A} {Z : ι → Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    {Φ : (ℝ × ℝ) × ℝ → A} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A} {τ s : ℝ}
    (hN : IsOpen N) (hΩ : IsOpen Ω) (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω))
    (hτ : 0 < τ) (hs0 : 0 ≤ s) (hcore : coreSegment τ ⊆ N)
    (hΦcore : Φ '' coreSegment τ = γ '' Icc 0 s) (hΦtip : Φ ((0, 0), τ) = γ s)
    (hZ : ∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i))
    (hD : ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω' : Set A}
    (hV : IsOpen V) (hΩ' : IsOpen Ω') (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hψZ : ∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0)
    {s' : ℝ} (hss' : s < s') (hs'1 : s' ≤ 1) (hcov : γ '' Icc s s' ⊆ S ∩ Ω')
    (horient : (Function.invFunOn ψ V (γ s)).2 < (Function.invFunOn ψ V (γ s')).2) :
    ∃ (Φ' : (ℝ × ℝ) × ℝ → A) (N' : Set ((ℝ × ℝ) × ℝ)) (Ω'' : Set A) (τ' : ℝ),
      IsOpen N' ∧ IsOpen Ω'' ∧ IsPLHomeomorphOn Φ' N' (S ∩ Ω'') ∧ τ < τ' ∧
      coreSegment τ' ⊆ N' ∧ Φ' '' coreSegment τ' = γ '' Icc 0 s' ∧ Φ' ((0, 0), τ') = γ s' ∧
      (∀ i p, p ∈ N' → (Φ' p ∈ Z i ↔ p.1 ∈ P i)) ∧
      (∀ p ∈ N', Φ' p ∈ D ↔ p.1 = 0) ∧
      ∀ p ∈ N', p.2 < τ → Φ' p = Φ p := by
  classical
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → (ℝ × ℝ) × ℝ, w = fun r => Function.invFunOn ψ V (γ r) :=
    ⟨_, rfl⟩
  have hγSΩ : ∀ r ∈ Icc s s', γ r ∈ S ∩ Ω' := fun r hr => hcov ⟨r, hr, rfl⟩
  have hIcc : ∀ r ∈ Icc s s', r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hs0.trans hr.1, hr.2.trans hs'1⟩
  have hwV : ∀ r ∈ Icc s s', w r ∈ V := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.surjOn.mapsTo_invFunOn (hγSΩ r hr)
  have hψw : ∀ r ∈ Icc s s', ψ (w r) = γ r := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.invOn_invFunOn.2 (hγSΩ r hr)
  have hwaxis : ∀ r ∈ Icc s s', (w r).1 = 0 := fun r hr =>
    (hψD (w r) (hwV r hr)).mp (by rw [hψw r hr]; exact hγD r (hIcc r hr))
  have hweq : ∀ r ∈ Icc s s', w r = ((0, 0), (w r).2) := fun r hr =>
    Prod.ext ((hwaxis r hr).trans Prod.mk_zero_zero.symm) rfl
  have hνc : ContinuousOn (fun r => (w r).2) (Icc s s') := by
    have h1 : ContinuousOn (Function.invFunOn ψ V) (S ∩ Ω') :=
      hψ.isPiecewiseAffineOn_invFunOn.continuousOn
    have h2 : ContinuousOn γ (Icc s s') := hγc.mono fun r hr => hIcc r hr
    rw [hwdef]
    exact continuous_snd.comp_continuousOn (h1.comp h2 fun r hr => hγSΩ r hr)
  have hνi : InjOn (fun r => (w r).2) (Icc s s') := by
    intro r₁ hr₁ r₂ hr₂ h
    apply hγi (hIcc r₁ hr₁) (hIcc r₂ hr₂)
    rw [← hψw r₁ hr₁, ← hψw r₂ hr₂, hweq r₁ hr₁, hweq r₂ hr₂]
    exact congrArg (fun t => ψ ((0, 0), t)) h
  have hsmem : s ∈ Icc s s' := ⟨le_rfl, hss'.le⟩
  have hs'mem : s' ∈ Icc s s' := ⟨hss'.le, le_rfl⟩
  have hlt : (w s).2 < (w s').2 := by rw [hwdef]; exact horient
  have hνmono : StrictMonoOn (fun r => (w r).2) (Icc s s') :=
    hνc.strictMonoOn_of_injOn_Icc hss'.le hlt.le hνi
  set v' := (w s').2 - (w s).2 with hv'def
  have hv' : 0 < v' := sub_pos.mpr hlt
  have hcoreψ : ∀ v ∈ Icc (0 : ℝ) v', ∃ r ∈ Icc s s',
      (w r).2 = (w s).2 + v ∧ w s + ((0, 0), v) = w r := by
    intro v hv
    have hmem : (w s).2 + v ∈ Icc (w s).2 (w s').2 :=
      ⟨by linarith [hv.1], by linarith [hv.2]⟩
    obtain ⟨r, hr, hνr⟩ := intermediate_value_Icc hss'.le hνc hmem
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
    have hrr : r₁ = r := hγi ⟨hr₁.1, hr₁.2.trans (hss'.le.trans hs'1)⟩ (hIcc r hr)
      (hγr₁.trans heq)
    have hrs : r ≠ s := by
      intro hrs
      rw [hrs] at hνr
      linarith
    exact hrs (le_antisymm (hrr ▸ hr₁.2) hr.1)
  obtain ⟨G, ρ, μ, hρ, hμ, hG, hballN, hGloc, hGX, hGL, hGq₀, -, hGcore⟩ :=
    exists_arcPatternJunction P hP hN hV hΩ hΩ' hΦ hψ hZ hD hψZ hψD
      hq₀N (by rw [hΦtip]; exact (hγSΩ s hsmem).2) hv' hτ hori
  rw [hw₀eq] at hGq₀
  have hGc : Continuous G := continuousOn_univ.mp hG.isPiecewiseAffineOn.continuousOn
  have hGsurj : Function.Surjective G := fun y => by
    obtain ⟨x, -, hx⟩ := hG.bijOn.surjOn (mem_univ y)
    exact ⟨x, hx⟩
  have hN₂ : IsOpen (G ⁻¹' V) := hV.preimage hGc
  have hGimg : G '' (G ⁻¹' V) = V := image_preimage_eq V hGsurj
  have hGN₂ : IsPLHomeomorphOn G (G ⁻¹' V) V := by
    have h := hG.restrict_isOpen hN₂ (subset_univ _) (by rw [hGimg]; exact hV)
    rwa [hGimg] at h
  have hΞ : IsPLHomeomorphOn (ψ ∘ G) (G ⁻¹' V) (S ∩ Ω') := hGN₂.trans hψ
  have hGcore' : ∀ u : ℝ, 0 ≤ u → u ≤ μ * v' → ∃ r ∈ Icc s s',
      G ((0, 0), τ + u) = w r ∧ (w r).2 = (w s).2 + u / μ := by
    intro u hu huv
    have hmem : u / μ ∈ Icc (0 : ℝ) v' :=
      ⟨div_nonneg hu hμ.le, by rw [div_le_iff₀ hμ]; linarith⟩
    obtain ⟨r, hr, hνr, hwr⟩ := hcoreψ (u / μ) hmem
    exact ⟨r, hr, by rw [hGcore u hu, hGq₀, hwr], hνr⟩
  set τ' := τ + μ * v' with hτ'def
  have hττ' : τ < τ' := by rw [hτ'def]; linarith [mul_pos hμ hv']
  set Φ' : (ℝ × ℝ) × ℝ → A := fun p => if p.2 ≤ τ then Φ p else ψ (G p) with hΦ'def
  set N₁ : Set ((ℝ × ℝ) × ℝ) := (N ∩ {p | p.2 < τ}) ∪ ball ((0, 0), τ) ρ with hN₁def
  set N₃ : Set ((ℝ × ℝ) × ℝ) := G ⁻¹' V ∩ {p | τ < p.2} with hN₃def
  have hN₁o : IsOpen N₁ :=
    (hN.inter (isOpen_lt continuous_snd continuous_const)).union isOpen_ball
  have hN₃o : IsOpen N₃ := hN₂.inter (isOpen_lt continuous_const continuous_snd)
  have hN₁N : N₁ ⊆ N := union_subset inter_subset_left fun p hp => (hballN hp).1
  have hN₃N₂ : N₃ ⊆ G ⁻¹' V := inter_subset_left
  have hEq₁ : EqOn Φ' Φ N₁ := by
    rintro p (hp | hp)
    · exact ite_eq_left (le_of_lt hp.2)
    · by_cases h : p.2 ≤ τ
      · exact ite_eq_left h
      · change (if p.2 ≤ τ then Φ p else ψ (G p)) = Φ p
        rw [ite_eq_right h]
        exact (hGloc p hp).2
  have hEq₃ : EqOn Φ' (ψ ∘ G) N₃ := fun p hp => ite_eq_right (not_le.mpr hp.2)
  have hpt : ∀ p : (ℝ × ℝ) × ℝ, p.1 = 0 → p = ((0, 0), τ + (p.2 - τ)) := fun p hp =>
    Prod.ext (hp.trans Prod.mk_zero_zero.symm) (by ring)
  have hKlow : ∀ p ∈ coreSegment τ', p.2 ≤ τ → p ∈ N₁ := by
    rintro p ⟨hp1, hp2, -⟩ h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl ⟨hcore ⟨hp1, hp2, h.le⟩, h⟩
    · refine Or.inr ?_
      rw [show p = ((0, 0), τ) from Prod.ext (hp1.trans Prod.mk_zero_zero.symm) h]
      exact mem_ball_self hρ
  have hKhigh : ∀ p ∈ coreSegment τ', τ < p.2 →
      p ∈ N₃ ∧ ∃ r ∈ Icc s s', s < r ∧ Φ' p = γ r := by
    rintro p ⟨hp1, hp2, hp3⟩ h
    obtain ⟨r, hr, hGr, hνr⟩ :=
      hGcore' (p.2 - τ) (by linarith) (by rw [hτ'def] at hp3; linarith)
    have hGp : G p = w r := by rw [hpt p hp1, hGr]
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
    · change G p ∈ V
      rw [hGp]
      exact hwV r hr
    · change (if p.2 ≤ τ then Φ p else ψ (G p)) = γ r
      rw [ite_eq_right (not_le.mpr h), hGp, hψw r hr]
  have hKN : coreSegment τ' ⊆ N₁ ∪ N₃ := by
    intro p hp
    by_cases h : p.2 ≤ τ
    · exact Or.inl (hKlow p hp h)
    · exact Or.inr (hKhigh p hp (not_le.mp h)).1
  have hΦcont : ContinuousOn Φ N := hΦ.isPiecewiseAffineOn.continuousOn
  have hΞcont : ContinuousOn (ψ ∘ G) (G ⁻¹' V) := hΞ.isPiecewiseAffineOn.continuousOn
  have hΦ'cont : ContinuousOn Φ' (N₁ ∪ N₃) := by
    refine continuousOn_of_forall_continuousAt fun p hp => ?_
    rcases hp with hp | hp
    · exact (hΦcont.continuousAt (hN.mem_nhds (hN₁N hp))).congr
        (Filter.eventuallyEq_of_mem (hN₁o.mem_nhds hp) fun q hq => (hEq₁ hq).symm)
    · exact (hΞcont.continuousAt (hN₂.mem_nhds (hN₃N₂ hp))).congr
        (Filter.eventuallyEq_of_mem (hN₃o.mem_nhds hp) fun q hq => (hEq₃ hq).symm)
  have hinj₁ : InjOn Φ' N₁ := (hΦ.bijOn.injOn.mono hN₁N).congr hEq₁.symm
  have hinj₃ : InjOn Φ' N₃ := (hΞ.bijOn.injOn.mono hN₃N₂).congr hEq₃.symm
  have hlowimg : ∀ p ∈ coreSegment τ', p.2 ≤ τ → Φ' p ∈ γ '' Icc 0 s := by
    intro p hp h
    rw [← hΦcore]
    exact ⟨p, ⟨hp.1, hp.2.1, h⟩, (ite_eq_left h).symm⟩
  have hinjK : InjOn Φ' (coreSegment τ') := by
    intro p hp q hq hpq
    by_cases hp2 : p.2 ≤ τ <;> by_cases hq2 : q.2 ≤ τ
    · exact hinj₁ (hKlow p hp hp2) (hKlow q hq hq2) hpq
    · exfalso
      obtain ⟨-, rq, hrq, hsrq, hrqeq⟩ := hKhigh q hq (not_le.mp hq2)
      obtain ⟨r₁, hr₁, hγr₁⟩ := hlowimg p hp hp2
      have := hγi ⟨hr₁.1, hr₁.2.trans (hss'.le.trans hs'1)⟩ (hIcc rq hrq)
        (hγr₁.trans (hpq.trans hrqeq))
      linarith [hr₁.2]
    · exfalso
      obtain ⟨-, rp, hrp, hsrp, hrpeq⟩ := hKhigh p hp (not_le.mp hp2)
      obtain ⟨r₁, hr₁, hγr₁⟩ := hlowimg q hq hq2
      have := hγi ⟨hr₁.1, hr₁.2.trans (hss'.le.trans hs'1)⟩ (hIcc rp hrp)
        (hγr₁.trans (hpq.symm.trans hrpeq))
      linarith [hr₁.2]
    · exact hinj₃ (hKhigh p hp (not_le.mp hp2)).1 (hKhigh q hq (not_le.mp hq2)).1 hpq
  obtain ⟨N'', hN''o, hKN'', hN''sub, hinjN''⟩ :=
    exists_isOpen_injOn_of_isCompact (hN₁o.union hN₃o) hΦ'cont (isCompact_coreSegment τ')
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
      (τ < p.2 ∧ G p ∈ V ∧ Φ' p = ψ (G p)) := by
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
        · exact (hGloc p h1).1
      · exact h1.1
  have htip : Φ' ((0, 0), τ') = γ s' := by
    have hmem : ((0, 0), τ') ∈ coreSegment τ' := ⟨rfl, by linarith, le_rfl⟩
    obtain ⟨-, r, hr, -, hreq⟩ := hKhigh _ hmem hττ'
    obtain ⟨r', hr', hGr', hνr'⟩ := hGcore' (μ * v') (by positivity) le_rfl
    have hwr' : (w r').2 = (w s').2 := by
      rw [hνr', mul_div_cancel_left₀ v' hμ.ne', hv'def]
      ring
    have hr's : r' = s' := hνi hr' hs'mem hwr'
    rw [← hr's, ← hψw r' hr', ← hGr']
    change (if τ' ≤ τ then Φ _ else ψ (G _)) = _
    rw [ite_eq_right (not_le.mpr hττ'), hτ'def]
  refine ⟨Φ', N'', Ω'', τ', hN''o, hΩ''o, hΦ'PL, hττ', hKN'', ?_, htip, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      by_cases h : p.2 ≤ τ
      · exact image_mono (Icc_subset_Icc le_rfl hss'.le) (hlowimg p hp h)
      · obtain ⟨-, r, hr, -, heq⟩ := hKhigh p hp (not_le.mp h)
        exact ⟨r, ⟨hs0.trans hr.1, hr.2⟩, heq.symm⟩
    · rintro _ ⟨r, hr, rfl⟩
      by_cases hrs : r ≤ s
      · have hmem : γ r ∈ Φ '' coreSegment τ := by
          rw [hΦcore]
          exact ⟨r, ⟨hr.1, hrs⟩, rfl⟩
        obtain ⟨p, hp, hpeq⟩ := hmem
        exact ⟨p, ⟨hp.1, hp.2.1, hp.2.2.trans hττ'.le⟩, by rw [← hpeq]; exact ite_eq_left hp.2.2⟩
      · rw [not_le] at hrs
        have hrmem : r ∈ Icc s s' := ⟨hrs.le, hr.2⟩
        have hv : 0 < (w r).2 - (w s).2 := sub_pos.mpr (hνmono hsmem hrmem hrs)
        have hvle : (w r).2 - (w s).2 ≤ v' := by
          have h1 := hνmono.monotoneOn hrmem hs'mem hr.2
          rw [hv'def]
          linarith
        obtain ⟨r', hr', hGr', hνr'⟩ :=
          hGcore' (μ * ((w r).2 - (w s).2)) (by positivity)
            (mul_le_mul_of_nonneg_left hvle hμ.le)
        have hr'r : r' = r := by
          apply hνi hr' hrmem
          simp only
          rw [hνr', mul_div_cancel_left₀ _ hμ.ne']
          ring
        have hmem : ((0, 0), τ + μ * ((w r).2 - (w s).2)) ∈ coreSegment τ' :=
          ⟨rfl, by nlinarith, by rw [hτ'def]; nlinarith⟩
        refine ⟨_, hmem, ?_⟩
        change (if τ + μ * ((w r).2 - (w s).2) ≤ τ then Φ _ else ψ (G _)) = γ r
        rw [ite_eq_right (by nlinarith), hGr', hr'r, hψw r hrmem]
  · intro i p hp
    rcases hcase p hp with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq]
      exact hZ i p hpN
    · rw [heq, hψZ i _ hGV, ← hGX i p]
  · intro p hp
    rcases hcase p hp with ⟨h, hpN, heq⟩ | ⟨h, hGV, heq⟩
    · rw [heq]
      exact hD p hpN
    · rw [heq, hψD _ hGV, ← hGL p]
  · intro p _ h
    exact ite_eq_left h.le

theorem exists_arcPatternStraightening_step {ι : Type*} (P : ι → Set (ℝ × ℝ))
    (hP : ∀ i v (t : ℝ), 0 < t → (t • v ∈ P i ↔ v ∈ P i))
    {S D : Set A} {Z : ι → Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    {Φ : (ℝ × ℝ) × ℝ → A} {N : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A} {τ s : ℝ}
    (hN : IsOpen N) (hΩ : IsOpen Ω) (hΦ : IsPLHomeomorphOn Φ N (S ∩ Ω))
    (hτ : 0 < τ) (hs0 : 0 ≤ s) (hcore : coreSegment τ ⊆ N)
    (hΦcore : Φ '' coreSegment τ = γ '' Icc 0 s) (hΦtip : Φ ((0, 0), τ) = γ s)
    (hZ : ∀ i p, p ∈ N → (Φ p ∈ Z i ↔ p.1 ∈ P i))
    (hD : ∀ p ∈ N, Φ p ∈ D ↔ p.1 = 0)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω' : Set A}
    (hV : IsOpen V) (hΩ' : IsOpen Ω') (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω'))
    (hψZ : ∀ i p, p ∈ V → (ψ p ∈ Z i ↔ p.1 ∈ P i)) (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0)
    {s' : ℝ} (hss' : s < s') (hs'1 : s' ≤ 1) (hcov : γ '' Icc s s' ⊆ S ∩ Ω') :
    ∃ (Φ' : (ℝ × ℝ) × ℝ → A) (N' : Set ((ℝ × ℝ) × ℝ)) (Ω'' : Set A) (τ' : ℝ),
      IsOpen N' ∧ IsOpen Ω'' ∧ IsPLHomeomorphOn Φ' N' (S ∩ Ω'') ∧ τ < τ' ∧
      coreSegment τ' ⊆ N' ∧ Φ' '' coreSegment τ' = γ '' Icc 0 s' ∧ Φ' ((0, 0), τ') = γ s' ∧
      (∀ i p, p ∈ N' → (Φ' p ∈ Z i ↔ p.1 ∈ P i)) ∧
      (∀ p ∈ N', Φ' p ∈ D ↔ p.1 = 0) ∧
      ∀ p ∈ N', p.2 < τ → Φ' p = Φ p := by
  classical
  have hsmem : s ∈ Icc s s' := ⟨le_rfl, hss'.le⟩
  have hs'mem : s' ∈ Icc s s' := ⟨hss'.le, le_rfl⟩
  have hγmem : ∀ r ∈ Icc s s', γ r ∈ S ∩ Ω' := fun r hr => hcov ⟨r, hr, rfl⟩
  have hIcc : ∀ r ∈ Icc s s', r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hs0.trans hr.1, hr.2.trans hs'1⟩
  have haxis : ∀ r ∈ Icc s s',
      Function.invFunOn ψ V (γ r) = ((0, 0), (Function.invFunOn ψ V (γ r)).2) := by
    intro r hr
    have h1 := hψ.bijOn.surjOn.mapsTo_invFunOn (hγmem r hr)
    have h2 := hψ.bijOn.invOn_invFunOn.2 (hγmem r hr)
    have h3 : (Function.invFunOn ψ V (γ r)).1 = 0 :=
      (hψD _ h1).mp (by rw [h2]; exact hγD r (hIcc r hr))
    exact Prod.ext (h3.trans Prod.mk_zero_zero.symm) rfl
  have hne : (Function.invFunOn ψ V (γ s)).2 ≠ (Function.invFunOn ψ V (γ s')).2 := by
    intro h
    have heq : Function.invFunOn ψ V (γ s) = Function.invFunOn ψ V (γ s') := by
      rw [haxis s hsmem, haxis s' hs'mem, h]
    have h1 := hψ.bijOn.invOn_invFunOn.2 (hγmem s hsmem)
    have h2 := hψ.bijOn.invOn_invFunOn.2 (hγmem s' hs'mem)
    have hγ : γ s = γ s' := by rw [← h1, ← h2, heq]
    exact hss'.ne (hγi (hIcc s hsmem) (hIcc s' hs'mem) hγ)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact exists_arcPatternStraightening_step_of_lt P hP hγc hγi hγD hN hΩ hΦ
      hτ hs0 hcore hΦcore hΦtip
      hZ hD hV hΩ' hψ hψZ hψD hss' hs'1 hcov hlt
  · have hcont : Continuous axisFlip := continuous_fst.prodMk continuous_snd.neg
    have hψf : IsPLHomeomorphOn (ψ ∘ axisFlip) (axisFlip ⁻¹' V) (S ∩ Ω') :=
      (isPLHomeomorphOn_axisFlip hV).trans hψ
    have hinvf : ∀ z ∈ S ∩ Ω', Function.invFunOn (ψ ∘ axisFlip) (axisFlip ⁻¹' V) z =
        axisFlip (Function.invFunOn ψ V z) := by
      intro z hz
      have ha := hψ.bijOn.surjOn.mapsTo_invFunOn hz
      have hψa := hψ.bijOn.invOn_invFunOn.2 hz
      have hfa : axisFlip (Function.invFunOn ψ V z) ∈ axisFlip ⁻¹' V := by
        rw [mem_preimage, axisFlip_axisFlip]
        exact ha
      apply hψf.bijOn.injOn (hψf.bijOn.surjOn.mapsTo_invFunOn hz) hfa
      rw [hψf.bijOn.invOn_invFunOn.2 hz, Function.comp_apply, axisFlip_axisFlip, hψa]
    refine exists_arcPatternStraightening_step_of_lt P hP hγc hγi hγD hN hΩ hΦ
      hτ hs0 hcore hΦcore hΦtip
      hZ hD (hV.preimage hcont) hΩ' hψf
      (fun i p hp => hψZ i (axisFlip p) hp) (fun p hp => hψD (axisFlip p) hp) hss' hs'1 hcov ?_
    rw [hinvf _ (hγmem s hsmem), hinvf _ (hγmem s' hs'mem)]
    simp only [axisFlip]
    linarith

end DifferentialGeometry.Topology.PiecewiseLinear
