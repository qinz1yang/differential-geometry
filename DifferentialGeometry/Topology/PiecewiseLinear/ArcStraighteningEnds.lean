/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArcStraighteningStep

open Set Topology Metric Filter

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Base

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]

theorem exists_arcStraightening_base {S D : Set A} {γ : ℝ → A}
    (hγc : ContinuousOn γ (Icc 0 1)) (hγi : InjOn γ (Icc 0 1))
    (hγS : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ S) (hγD : ∀ r ∈ Icc (0 : ℝ) 1, γ r ∈ D)
    {ψ : (ℝ × ℝ) × ℝ → A} {V : Set ((ℝ × ℝ) × ℝ)} {Ω : Set A}
    (hΩ : IsOpen Ω) (hψ : IsPLHomeomorphOn ψ V (S ∩ Ω))
    (h0 : (0 : (ℝ × ℝ) × ℝ) ∈ V) (hψ0 : ψ 0 = γ 0)
    (hψD : ∀ p ∈ V, ψ p ∈ D ↔ p.1 = 0 ∧ 0 ≤ p.2) :
    ∃ s τ : ℝ, 0 < s ∧ s < 1 ∧ 0 < τ ∧ coreSegment τ ⊆ V ∧
      ψ '' coreSegment τ = γ '' Icc 0 s ∧ ψ ((0, 0), τ) = γ s := by
  have hγ0 : γ 0 ∈ Ω := by
    rw [← hψ0]
    exact (hψ.bijOn.mapsTo h0).2
  have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨u, hu, hueq⟩ := continuousOn_iff'.mp hγc Ω hΩ
  have h0u : (0 : ℝ) ∈ u := by
    have : (0 : ℝ) ∈ γ ⁻¹' Ω ∩ Icc 0 1 := ⟨hγ0, hmem0⟩
    rw [hueq] at this
    exact this.1
  obtain ⟨δ, hδ, hδu⟩ := Metric.isOpen_iff.mp hu 0 h0u
  set s := min (δ / 2) (1 / 2) with hsdef
  have hs : 0 < s := lt_min (half_pos hδ) (by norm_num)
  have hs1' : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hs1 : s ≤ 1 := hs1'.le
  have hIcc : ∀ r ∈ Icc 0 s, r ∈ Icc (0 : ℝ) 1 := fun r hr => ⟨hr.1, hr.2.trans hs1⟩
  have hγmem : ∀ r ∈ Icc 0 s, γ r ∈ S ∩ Ω := by
    intro r hr
    refine ⟨hγS r (hIcc r hr), ?_⟩
    have hru : r ∈ u := hδu (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hr.1]
      exact lt_of_le_of_lt (hr.2.trans (min_le_left _ _)) (half_lt_self hδ))
    have : r ∈ u ∩ Icc 0 1 := ⟨hru, hIcc r hr⟩
    rw [← hueq] at this
    exact this.1
  obtain ⟨w, hwdef⟩ : ∃ w : ℝ → (ℝ × ℝ) × ℝ, w = fun r => Function.invFunOn ψ V (γ r) :=
    ⟨_, rfl⟩
  have hwV : ∀ r ∈ Icc 0 s, w r ∈ V := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.surjOn.mapsTo_invFunOn (hγmem r hr)
  have hψw : ∀ r ∈ Icc 0 s, ψ (w r) = γ r := fun r hr => by
    rw [hwdef]
    exact hψ.bijOn.invOn_invFunOn.2 (hγmem r hr)
  have hwax : ∀ r ∈ Icc 0 s, (w r).1 = 0 ∧ 0 ≤ (w r).2 := fun r hr =>
    (hψD (w r) (hwV r hr)).mp (by rw [hψw r hr]; exact hγD r (hIcc r hr))
  have hweq : ∀ r ∈ Icc 0 s, w r = ((0, 0), (w r).2) := fun r hr =>
    Prod.ext ((hwax r hr).1.trans Prod.mk_zero_zero.symm) rfl
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
  have hle : (w 0).2 ≤ (w s).2 := by rw [hw0']; exact (hwax s hsmem).2
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
  refine ⟨s, (w s).2, hs, hs1', hτ, fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨r, hr, rfl⟩ := hseg p hp
    exact hwV r hr
  · apply Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      obtain ⟨r, hr, rfl⟩ := hseg p hp
      exact ⟨r, hr, (hψw r hr).symm⟩
    · rintro _ ⟨r, hr, rfl⟩
      refine ⟨w r, ⟨(hwax r hr).1, (hwax r hr).2, ?_⟩, hψw r hr⟩
      rcases hr.2.eq_or_lt with h | h
      · rw [h]
      · exact (hmono hr hsmem h).le
  · rw [← hψw s hsmem, hweq s hsmem]

end Base

noncomputable def clampShift (c x : ℝ) : ℝ := max 0 (min c (x / 2)) + min 0 (max c (-x / 2))

noncomputable def clampShiftInv (c y : ℝ) : ℝ := max 0 (min c (y / 3)) + min 0 (max c (-y))

theorem clampShift_of_nonpos (c : ℝ) {x : ℝ} (hx : x ≤ 0) : clampShift c x = 0 := by
  unfold clampShift
  rw [max_eq_left (min_le_of_right_le (by linarith)),
    min_eq_left (le_max_of_le_right (by linarith)), add_zero]

theorem clampShift_of_le (c : ℝ) {x : ℝ} (hx : 2 * |c| ≤ x) : clampShift c x = c := by
  unfold clampShift
  rcases le_total 0 c with hc | hc
  · rw [abs_of_nonneg hc] at hx
    rw [min_eq_left (by linarith), max_eq_right hc,
      min_eq_left (le_max_of_le_left hc), add_zero]
  · rw [abs_of_nonpos hc] at hx
    rw [max_eq_left (min_le_of_left_le hc), max_eq_left (by linarith), min_eq_right hc,
      zero_add]

theorem clampShift_of_mid_nonneg {c x : ℝ} (hc : 0 ≤ c) (hx0 : 0 ≤ x) (hxc : x ≤ 2 * c) :
    clampShift c x = x / 2 := by
  unfold clampShift
  rw [min_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
    min_eq_left hc, add_zero]

theorem clampShift_of_mid_nonpos {c x : ℝ} (hc : c ≤ 0) (hx0 : 0 ≤ x) (hxc : x ≤ -2 * c) :
    clampShift c x = -x / 2 := by
  unfold clampShift
  rw [min_eq_left (by linarith), max_eq_left hc, max_eq_right (by linarith),
    min_eq_right (by linarith), zero_add]

theorem clampShiftInv_of_nonpos (c : ℝ) {y : ℝ} (hy : y ≤ 0) : clampShiftInv c y = 0 := by
  unfold clampShiftInv
  rw [max_eq_left (min_le_of_right_le (by linarith)),
    min_eq_left (le_max_of_le_right (by linarith)), add_zero]

theorem clampShiftInv_of_mid_nonneg {c y : ℝ} (hc : 0 ≤ c) (hy0 : 0 ≤ y) (hyc : y ≤ 3 * c) :
    clampShiftInv c y = y / 3 := by
  unfold clampShiftInv
  rw [min_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith),
    min_eq_left hc, add_zero]

theorem clampShiftInv_of_mid_nonpos {c y : ℝ} (hc : c ≤ 0) (hy0 : 0 ≤ y) (hyc : y ≤ -c) :
    clampShiftInv c y = -y := by
  unfold clampShiftInv
  rw [min_eq_left (by linarith), max_eq_left hc, max_eq_right (by linarith),
    min_eq_right (by linarith), zero_add]

theorem clampShiftInv_of_nonneg_le {c y : ℝ} (hc : 0 ≤ c) (hy : 3 * c ≤ y) :
    clampShiftInv c y = c := by
  unfold clampShiftInv
  rw [min_eq_left (by linarith), max_eq_right hc, max_eq_left (by linarith),
    min_eq_left hc, add_zero]

theorem clampShiftInv_of_nonpos_le {c y : ℝ} (hc : c ≤ 0) (hy : -c ≤ y) :
    clampShiftInv c y = c := by
  unfold clampShiftInv
  rw [min_eq_left (by linarith), max_eq_left hc, max_eq_left (by linarith),
    min_eq_right hc, zero_add]

theorem clampShiftInv_add_clampShift (c x : ℝ) :
    clampShiftInv c (x + clampShift c x) = clampShift c x := by
  rcases le_total x 0 with hx | hx
  · rw [clampShift_of_nonpos c hx, add_zero, clampShiftInv_of_nonpos c hx]
  rcases le_total 0 c with hc | hc
  · rcases le_total x (2 * c) with hxc | hxc
    · rw [clampShift_of_mid_nonneg hc hx hxc,
        clampShiftInv_of_mid_nonneg hc (by linarith) (by linarith)]
      ring
    · have h2 : 2 * |c| ≤ x := by rw [abs_of_nonneg hc]; exact hxc
      rw [clampShift_of_le c h2, clampShiftInv_of_nonneg_le hc (by linarith)]
  · rcases le_total x (-2 * c) with hxc | hxc
    · rw [clampShift_of_mid_nonpos hc hx hxc,
        clampShiftInv_of_mid_nonpos hc (by linarith) (by linarith)]
      ring
    · have h2 : 2 * |c| ≤ x := by rw [abs_of_nonpos hc]; linarith
      rw [clampShift_of_le c h2, clampShiftInv_of_nonpos_le hc (by linarith)]

theorem clampShift_sub_clampShiftInv (c y : ℝ) :
    clampShift c (y - clampShiftInv c y) = clampShiftInv c y := by
  rcases le_total y 0 with hy | hy
  · rw [clampShiftInv_of_nonpos c hy, sub_zero, clampShift_of_nonpos c hy]
  rcases le_total 0 c with hc | hc
  · rcases le_total y (3 * c) with hyc | hyc
    · rw [clampShiftInv_of_mid_nonneg hc hy hyc,
        clampShift_of_mid_nonneg hc (by linarith) (by linarith)]
      ring
    · rw [clampShiftInv_of_nonneg_le hc hyc,
        clampShift_of_le c (by rw [abs_of_nonneg hc]; linarith)]
  · rcases le_total y (-c) with hyc | hyc
    · rw [clampShiftInv_of_mid_nonpos hc hy hyc,
        clampShift_of_mid_nonpos hc (by linarith) (by linarith)]
      ring
    · rw [clampShiftInv_of_nonpos_le hc hyc,
        clampShift_of_le c (by rw [abs_of_nonpos hc]; linarith)]

theorem clampShift_zero_left (x : ℝ) : clampShift 0 x = 0 := by
  rcases le_total x 0 with hx | hx
  · exact clampShift_of_nonpos 0 hx
  · exact clampShift_of_le 0 (by rw [abs_zero, mul_zero]; exact hx)

noncomputable def verticalClamp (c : ℝ × ℝ → ℝ) (t₁ : ℝ) (p : (ℝ × ℝ) × ℝ) :
    (ℝ × ℝ) × ℝ :=
  (p.1, p.2 + clampShift (c p.1) (p.2 - t₁))

theorem isPiecewiseAffineOn_real_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {s : Set E} (hf : IsPiecewiseAffineOn f s) (a b : ℝ) :
    IsPiecewiseAffineOn (fun x => a * f x + b) s := by
  let T : ℝ →ᵃ[ℝ] ℝ := ⟨fun x => a * x + b, a • LinearMap.id, fun p v => by
    simp only [vadd_eq_add, LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring⟩
  exact (hf.affine_comp T).congr fun _ _ => rfl

theorem isPiecewiseAffineOn_clampShift_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E} (hf : IsPiecewiseAffineOn f s)
    (hg : IsPiecewiseAffineOn g s) (hs : IsOpen s) :
    IsPiecewiseAffineOn (fun x => clampShift (f x) (g x)) s := by
  have h0 : IsPiecewiseAffineOn (fun _ : E => (0 : ℝ)) s :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : ℝ)) hs
  have h1 := h0.max (hf.min (isPiecewiseAffineOn_real_affine hg (1 / 2) 0))
  have h2 := h0.min (hf.max (isPiecewiseAffineOn_real_affine hg (-1 / 2) 0))
  refine (h1.add h2).congr fun x _ => ?_
  simp only [clampShift]
  ring_nf

theorem isPiecewiseAffineOn_clampShiftInv_comp {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) (hs : IsOpen s) :
    IsPiecewiseAffineOn (fun x => clampShiftInv (f x) (g x)) s := by
  have h0 : IsPiecewiseAffineOn (fun _ : E => (0 : ℝ)) s :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : ℝ)) hs
  have h1 := h0.max (hf.min (isPiecewiseAffineOn_real_affine hg (1 / 3) 0))
  have h2 := h0.min (hf.max (isPiecewiseAffineOn_real_affine hg (-1) 0))
  refine (h1.add h2).congr fun x _ => ?_
  simp only [clampShiftInv]
  ring_nf

theorem isPLHomeomorphOn_verticalClamp {c : ℝ × ℝ → ℝ} (hc : IsPiecewiseAffineOn c univ)
    (t₁ : ℝ) : IsPLHomeomorphOn (verticalClamp c t₁) univ univ := by
  let J : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ := fun p => (p.1, p.2 - clampShiftInv (c p.1) (p.2 - t₁))
  have hJS : ∀ p, J (verticalClamp c t₁ p) = p := by
    intro p
    simp only [J, verticalClamp]
    have h := clampShiftInv_add_clampShift (c p.1) (p.2 - t₁)
    rw [show p.2 + clampShift (c p.1) (p.2 - t₁) - t₁ =
      p.2 - t₁ + clampShift (c p.1) (p.2 - t₁) by ring, h, add_sub_cancel_right]
  have hSJ : ∀ p, verticalClamp c t₁ (J p) = p := by
    intro p
    simp only [J, verticalClamp]
    have h := clampShift_sub_clampShiftInv (c p.1) (p.2 - t₁)
    rw [show p.2 - clampShiftInv (c p.1) (p.2 - t₁) - t₁ =
      p.2 - t₁ - clampShiftInv (c p.1) (p.2 - t₁) by ring, h, sub_add_cancel]
  have hfst : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.1) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ (ℝ × ℝ) ℝ).toAffineMap isOpen_univ
  have hsnd : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.2) univ :=
    isPiecewiseAffineOn_of_affine (LinearMap.snd ℝ (ℝ × ℝ) ℝ).toAffineMap isOpen_univ
  have hcp : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => c p.1) univ := by
    have h := hc.comp hfst
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hdiff : IsPiecewiseAffineOn (fun p : (ℝ × ℝ) × ℝ => p.2 - t₁) univ :=
    (isPiecewiseAffineOn_real_affine hsnd 1 (-t₁)).congr fun p _ => by simp only; ring
  have hS : IsPiecewiseAffineOn (verticalClamp c t₁) univ :=
    (hfst.prod_mk (hsnd.add (isPiecewiseAffineOn_clampShift_comp hcp hdiff isOpen_univ))).congr
      fun _ _ => rfl
  have hJ : IsPiecewiseAffineOn J univ := by
    have h := hsnd.add (isPiecewiseAffineOn_real_affine
      (isPiecewiseAffineOn_clampShiftInv_comp hcp hdiff isOpen_univ) (-1) 0)
    exact (hfst.prod_mk h).congr fun p _ => by simp only [J]; ring_nf
  have hbij : BijOn (verticalClamp c t₁) univ univ :=
    ⟨mapsTo_univ _ _, fun p _ q _ h => by rw [← hJS p, h, hJS q],
      fun q _ => ⟨J q, mem_univ _, hSJ q⟩⟩
  refine ⟨hbij, hS, hJ.congr fun q _ => ?_⟩
  apply hbij.injOn (hbij.surjOn.mapsTo_invFunOn (mem_univ q)) (mem_univ _)
  rw [hbij.invOn_invFunOn.2 (mem_univ q), hSJ q]

theorem verticalClamp_of_le {c : ℝ × ℝ → ℝ} {t₁ : ℝ} {p : (ℝ × ℝ) × ℝ} (hp : p.2 ≤ t₁) :
    verticalClamp c t₁ p = p := by
  simp only [verticalClamp, clampShift_of_nonpos _ (sub_nonpos.mpr hp), add_zero]

theorem verticalClamp_of_ge {c : ℝ × ℝ → ℝ} {t₁ : ℝ} {p : (ℝ × ℝ) × ℝ}
    (hp : 2 * |c p.1| ≤ p.2 - t₁) : verticalClamp c t₁ p = (p.1, p.2 + c p.1) := by
  simp only [verticalClamp, clampShift_of_le _ hp]

theorem verticalClamp_axis {c : ℝ × ℝ → ℝ} (hc : c 0 = 0) (t₁ t : ℝ) :
    verticalClamp c t₁ ((0, 0), t) = ((0, 0), t) := by
  simp only [verticalClamp, Prod.mk_zero_zero, hc, clampShift_zero_left, add_zero]

section Cylinder

theorem add_axis_of_homogeneous {G W : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ} {τ τ₁ μ v' ρ : ℝ}
    (hμ : 0 < μ) (hv' : 0 < v') (hτ₁ : τ₁ = τ + μ * v') (hρ : 0 < ρ)
    (hGhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 ≤ t →
      G (((0, 0), τ) + t • v) = G ((0, 0), τ) + t • (G (((0, 0), τ) + v) - G ((0, 0), τ)))
    (hGq₀ : G ((0, 0), τ) = ((0, 0), -v')) (hWG : EqOn W G (ball ((0, 0), τ₁) ρ))
    (hWq : W ((0, 0), τ₁) = 0)
    (hWhom : ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 ≤ t →
      W (((0, 0), τ₁) + t • v) = W ((0, 0), τ₁) + t • (W (((0, 0), τ₁) + v) - W ((0, 0), τ₁)))
    (x : (ℝ × ℝ) × ℝ) (h : ℝ) :
    W (((0, 0), τ₁) + x + ((0, 0), h)) = W (((0, 0), τ₁) + x) + ((0, 0), h / μ) := by
  subst hτ₁
  set qf : (ℝ × ℝ) × ℝ := ((0, 0), τ + μ * v') with hqf
  set q₀ : (ℝ × ℝ) × ℝ := ((0, 0), τ) with hq₀
  have hWsc : ∀ v : (ℝ × ℝ) × ℝ, ∀ t : ℝ, 0 ≤ t → W (qf + t • v) = t • W (qf + v) := by
    intro v t ht
    rw [hWhom v t ht, hWq, sub_zero, zero_add]
  have hμv : 0 < μ * v' := mul_pos hμ hv'
  have hnormax : ∀ c : ℝ, ‖(((0 : ℝ), (0 : ℝ)), c)‖ = |c| := fun c => by
    rw [Prod.norm_mk, Prod.mk_zero_zero, norm_zero, Real.norm_eq_abs, max_eq_right (abs_nonneg c)]
  have small : ∀ x : (ℝ × ℝ) × ℝ, ∀ h : ℝ, ‖x‖ < ρ / 4 → |h| < ρ / 4 → |h| < μ * v' / 2 →
      W (qf + x + ((0, 0), h)) = W (qf + x) + ((0, 0), h / μ) := by
    intro x h hx hh hh'
    set σ := h / (μ * v') with hσ
    have hσh : σ * (μ * v') = h := by rw [hσ]; field_simp
    have hσv : σ * v' = h / μ := by rw [hσ]; field_simp
    have hσabs : |σ| < 1 / 2 := by
      rw [hσ, abs_div, abs_of_pos hμv, div_lt_iff₀ hμv]
      linarith
    have hσ1 : 0 < 1 + σ := by linarith [neg_abs_le σ]
    set v := (1 + σ)⁻¹ • x with hv
    have hσx : (1 + σ) • v = x := by
      rw [hv, smul_smul, mul_inv_cancel₀ hσ1.ne', one_smul]
    have hvnorm : ‖v‖ < ρ / 2 := by
      rw [hv, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hσ1).le, inv_mul_lt_iff₀ hσ1]
      nlinarith [norm_nonneg x, neg_abs_le σ]
    have hpt : qf + x + ((0, 0), h) = q₀ + (1 + σ) • (qf + v - q₀) := by
      rw [smul_sub, smul_add, hσx, hqf, hq₀]
      refine Prod.ext ?_ ?_
      · simp
      · simp only [Prod.snd_add, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        linear_combination -hσh
    have hball1 : qf + x + ((0, 0), h) ∈ ball qf ρ := by
      rw [mem_ball, dist_eq_norm, add_assoc, add_sub_cancel_left]
      calc ‖x + ((0, 0), h)‖ ≤ ‖x‖ + ‖(((0 : ℝ), (0 : ℝ)), h)‖ := norm_add_le _ _
        _ = ‖x‖ + |h| := by rw [hnormax]
        _ < ρ := by linarith
    have hball2 : qf + v ∈ ball qf ρ := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    have hG1 := hGhom (qf + v - q₀) (1 + σ) hσ1.le
    rw [add_sub_cancel, ← hpt, ← hWG hball1, ← hWG hball2, hGq₀] at hG1
    have hW1 : W (qf + x) = (1 + σ) • W (qf + v) := by
      rw [← hσx, hWsc v (1 + σ) hσ1.le]
    rw [hG1, hW1]
    have hvec : (((0 : ℝ), (0 : ℝ)), -v') - (1 + σ) • (((0 : ℝ), (0 : ℝ)), -v') =
        ((0, 0), h / μ) := by
      refine Prod.ext ?_ ?_
      · ext <;> simp
      · simp only [Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        linear_combination hσv
    rw [← hvec, smul_sub]
    abel
  set B := ‖x‖ + |h| + 1 with hB
  have hBpos : 0 < B := by positivity
  set m := min (ρ / 4) (μ * v' / 2) with hm
  have hmpos : 0 < m := lt_min (by positivity) (by positivity)
  set t := m / (2 * B) with ht
  have htpos : 0 < t := by positivity
  have htB : t * B = m / 2 := by rw [ht]; field_simp
  have htx : ‖t • x‖ < ρ / 4 := by
    rw [norm_smul, Real.norm_of_nonneg htpos.le]
    have h1 : t * ‖x‖ ≤ t * B := mul_le_mul_of_nonneg_left (by rw [hB]; linarith [abs_nonneg h])
      htpos.le
    have h2 : m ≤ ρ / 4 := min_le_left _ _
    linarith
  have hth : |t * h| ≤ m / 2 := by
    rw [abs_mul, abs_of_pos htpos, ← htB]
    exact mul_le_mul_of_nonneg_left (by rw [hB]; linarith [norm_nonneg x]) htpos.le
  have e1 := small (t • x) (t * h) htx
    (lt_of_le_of_lt hth (by linarith [min_le_left (ρ / 4) (μ * v' / 2)]))
    (lt_of_le_of_lt hth (by linarith [min_le_right (ρ / 4) (μ * v' / 2)]))
  have e2 := hWsc (x + ((0, 0), h)) t htpos.le
  have e3 : qf + t • (x + ((0, 0), h)) = qf + t • x + ((0, 0), t * h) := by
    rw [smul_add, add_assoc]
    congr 2
    refine Prod.ext ?_ ?_ <;> simp
  rw [e3, e1, hWsc x t htpos.le] at e2
  have e4 : t • (W (qf + x) + ((0, 0), h / μ)) = t • W (qf + (x + ((0, 0), h))) := by
    rw [← e2, smul_add]
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.smul_snd, smul_eq_mul]
      ring
  rw [add_assoc]
  exact (smul_right_injective _ htpos.ne' e4).symm

end Cylinder

end DifferentialGeometry.Topology.PiecewiseLinear
