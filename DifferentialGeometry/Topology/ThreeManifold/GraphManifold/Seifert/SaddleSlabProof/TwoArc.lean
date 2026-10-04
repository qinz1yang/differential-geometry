import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.TwoArcLift
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Components

/-!
# Two attaching arcs on one circle

Lane RG03c (MD2b). Two arcs `β₁, β₂ : ℝ → ℝ/ℤ` have the attaching type `s = d₁ d₂ = ±1`
(`HasArcType β₁ β₂ T s`) when they have lifts `b₁`, `b₂` on `[-T, T]` whose derivatives have the
constant signs `d₁`, `d₂`; immersed arcs always have a type (`exists_hasArcType`). The type is
the attaching sign (coherent or twisted); the classification never needs to know which value is
which. `exists_addCircle_diffeo_twoArc`: if two
pairs of disjoint arcs, the first arc of each pair injective, have the same type, one
diffeomorphism `k` of the circle carries `β₁` to `β'₁` and `β₂` to `β'₂` on `[-T₁, T₁]`. After
reversing the circle (`signDiffeo`) the first lifts increase; the second arc, read as
`t ↦ β₂ (s t)`, then has an increasing lift, which is shifted into the gap left by the first arc
and joined to it (`exists_two_piece_lift`) into one increasing lift of total increase below `1`
(`exists_concat_lift`), and `exists_addCircle_diffeo_comp_eqOn` matches the two joined lifts.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SaddleSlabProof

def HasArcType (β₁ β₂ : ℝ → AddCircle (1 : ℝ)) (T s : ℝ) : Prop :=
  ∃ b₁ b₂ : ℝ → ℝ, ∃ d₁ d₂ : ℝ, d₁ ^ 2 = 1 ∧ d₂ ^ 2 = 1 ∧ d₁ * d₂ = s ∧
    ContDiffOn ℝ ∞ b₁ (Ioo (-T) T) ∧ ContDiffOn ℝ ∞ b₂ (Ioo (-T) T) ∧
    Continuous b₁ ∧ Continuous b₂ ∧
    (∀ t ∈ Icc (-T) T, (b₁ t : AddCircle (1 : ℝ)) = β₁ t) ∧
    (∀ t ∈ Icc (-T) T, (b₂ t : AddCircle (1 : ℝ)) = β₂ t) ∧
    (∀ t ∈ Ioo (-T) T, 0 < d₁ * deriv b₁ t) ∧ ∀ t ∈ Ioo (-T) T, 0 < d₂ * deriv b₂ t

theorem exists_sign_of_monotone {b : ℝ → ℝ} {T : ℝ}
    (h : (∀ t ∈ Ioo (-T) T, 0 < deriv b t) ∨ (∀ t ∈ Ioo (-T) T, deriv b t < 0)) :
    ∃ d : ℝ, d ^ 2 = 1 ∧ ∀ t ∈ Ioo (-T) T, 0 < d * deriv b t := by
  rcases h with h | h
  · exact ⟨1, by norm_num, fun t ht => by rw [one_mul]; exact h t ht⟩
  · exact ⟨-1, by norm_num, fun t ht => by linarith [h t ht]⟩

theorem exists_hasArcType {β₁ β₂ : ℝ → AddCircle (1 : ℝ)} {T₂ T : ℝ} (hT₂ : 0 ≤ T₂)
    (hT : T₂ < T) (hβ₁ : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β₁ t)
    (himm₁ : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β₁ t ≠ 0)
    (hβ₂ : ∀ t ∈ Ioo (-T) T, ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ β₂ t)
    (himm₂ : ∀ t ∈ Ioo (-T) T, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) β₂ t ≠ 0) :
    ∃ s : ℝ, s ^ 2 = 1 ∧ HasArcType β₁ β₂ T₂ s := by
  obtain ⟨b₁, hb₁, hb₁c, hl₁, hs₁⟩ := exists_lift_of_arc hT₂ hT hβ₁ himm₁
  obtain ⟨b₂, hb₂, hb₂c, hl₂, hs₂⟩ := exists_lift_of_arc hT₂ hT hβ₂ himm₂
  obtain ⟨d₁, hd₁, hp₁⟩ := exists_sign_of_monotone hs₁
  obtain ⟨d₂, hd₂, hp₂⟩ := exists_sign_of_monotone hs₂
  exact ⟨d₁ * d₂, by rw [mul_pow, hd₁, hd₂, one_mul], b₁, b₂, d₁, d₂, hd₁, hd₂, rfl, hb₁, hb₂,
    hb₁c, hb₂c, hl₁, hl₂, hp₁, hp₂⟩

def signDiffeo (d : ℝ) :
    Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞ :=
  if d = 1 then Diffeomorph.refl _ _ _ else addCircleNeg

theorem signDiffeo_coe {d : ℝ} (hd : d ^ 2 = 1) (x : ℝ) :
    signDiffeo d (x : AddCircle (1 : ℝ)) = ((d * x : ℝ) : AddCircle (1 : ℝ)) := by
  rcases sq_eq_one_cases hd with rfl | rfl
  · simp [signDiffeo]
  · rw [signDiffeo, ite_eq_right (by norm_num), addCircleNeg_apply, neg_one_mul, AddCircle.coe_neg]

theorem mul_mem_Icc_of_sq {s t T : ℝ} (hs : s ^ 2 = 1) (ht : t ∈ Icc (-T) T) :
    s * t ∈ Icc (-T) T := by
  rcases sq_eq_one_cases hs with rfl | rfl
  · rwa [one_mul]
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem mul_mem_Ioo_of_sq {s t T : ℝ} (hs : s ^ 2 = 1) (ht : t ∈ Ioo (-T) T) :
    s * t ∈ Ioo (-T) T := by
  rcases sq_eq_one_cases hs with rfl | rfl
  · rwa [one_mul]
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩

theorem sub_lt_one_of_injOn {c : ℝ → ℝ} {γ : ℝ → AddCircle (1 : ℝ)} {T : ℝ}
    (hc : ContinuousOn c (Icc (-T) T)) (hT : 0 ≤ T)
    (hl : ∀ t ∈ Icc (-T) T, (c t : AddCircle (1 : ℝ)) = γ t) (hinj : InjOn γ (Icc (-T) T)) :
    c T - c (-T) < 1 := by
  by_contra hge
  push Not at hge
  have hle : -T ≤ T := by linarith
  obtain ⟨t, ht, hct⟩ := intermediate_value_Icc hle hc
    (show c (-T) + 1 ∈ Icc (c (-T)) (c T) from ⟨by linarith, by linarith⟩)
  have h1 : γ t = γ (-T) := by
    rw [← hl t ht, ← hl (-T) ⟨le_rfl, hle⟩, hct, AddCircle.coe_add, AddCircle.coe_period,
      add_zero]
  rw [hinj ht ⟨le_rfl, hle⟩ h1] at hct
  linarith

theorem hasDerivAt_of_contDiffOn {b : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hb : ContDiffOn ℝ ∞ b J) {t : ℝ} (ht : t ∈ J) : HasDerivAt b (deriv b t) t :=
  ((hb.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

theorem exists_concat_lift {β₁ β₂ : ℝ → AddCircle (1 : ℝ)} {T₃ T₂ s : ℝ} (hT₃ : 0 ≤ T₃)
    (hT₃₂ : T₃ < T₂) (hs : s ^ 2 = 1) (h : HasArcType β₁ β₂ T₂ s)
    (hinj₁ : InjOn β₁ (Icc (-T₂) T₂))
    (hdisj : ∀ t ∈ Icc (-T₂) T₂, ∀ t' ∈ Icc (-T₂) T₂, β₂ t ≠ β₁ t') {L : ℝ}
    (hL : 2 * T₃ < L) :
    ∃ e : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∃ G : ℝ → ℝ, ∃ δ > 0, ContDiff ℝ ∞ G ∧
        (∀ u ∈ Ioo (-T₃ - δ) (L + T₃ + δ), 0 < deriv G u) ∧ G (L + T₃) - G (-T₃) < 1 ∧
        (∀ t ∈ Icc (-T₃) T₃, (G t : AddCircle (1 : ℝ)) = e (β₁ t)) ∧
        ∀ t ∈ Icc (-T₃) T₃, (G (L + s * t) : AddCircle (1 : ℝ)) = e (β₂ t) := by
  obtain ⟨b₁, b₂, d₁, d₂, hd₁, hd₂, hdd, hb₁, hb₂, hb₁c, hb₂c, hl₁, hl₂, hp₁, hp₂⟩ := h
  set e := signDiffeo d₁ with he
  have hIcc₃ : Icc (-T₃) T₃ ⊆ Icc (-T₂) T₂ := Icc_subset_Icc (by linarith) hT₃₂.le
  have hIoo₃ : Icc (-T₃) T₃ ⊆ Ioo (-T₂) T₂ := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set c₁ : ℝ → ℝ := fun t => d₁ * b₁ t with hc₁
  set r₂ : ℝ → ℝ := fun t => d₁ * b₂ (s * t) with hr₂
  have hc₁s : ContDiffOn ℝ ∞ c₁ (Ioo (-T₂) T₂) := contDiffOn_const.mul hb₁
  have hr₂s : ContDiffOn ℝ ∞ r₂ (Ioo (-T₂) T₂) :=
    contDiffOn_const.mul (hb₂.comp (contDiff_const.mul contDiff_id).contDiffOn
      fun t ht => mul_mem_Ioo_of_sq hs ht)
  have hc₁d : ∀ t ∈ Ioo (-T₂) T₂, 0 < deriv c₁ t := by
    intro t ht
    have hd := (hasDerivAt_of_contDiffOn isOpen_Ioo hb₁ ht).const_mul d₁
    rw [hd.deriv]
    exact hp₁ t ht
  have hr₂d : ∀ t ∈ Ioo (-T₂) T₂, 0 < deriv r₂ t := by
    intro t ht
    have hst := mul_mem_Ioo_of_sq hs ht
    have h1 : HasDerivAt (fun y => b₂ (s * y)) (deriv b₂ (s * t) * s) t := by
      have := (hasDerivAt_of_contDiffOn isOpen_Ioo hb₂ hst).comp t
        ((hasDerivAt_id' t).const_mul s)
      rw [mul_one] at this
      exact this
    have hval : deriv r₂ t = d₂ * deriv b₂ (s * t) := by
      have h2 : deriv r₂ t = d₁ * (deriv b₂ (s * t) * s) := (h1.const_mul d₁).deriv
      rw [h2, ← hdd]
      have : d₁ * (deriv b₂ ((d₁ * d₂) * t) * (d₁ * d₂)) =
          d₁ ^ 2 * (d₂ * deriv b₂ ((d₁ * d₂) * t)) := by ring
      rw [this, hd₁, one_mul]
    rw [hval]
    exact hp₂ _ hst
  have hc₁l : ∀ t ∈ Icc (-T₂) T₂, (c₁ t : AddCircle (1 : ℝ)) = e (β₁ t) := fun t ht => by
    rw [he, ← hl₁ t ht, signDiffeo_coe hd₁]
  have hr₂l : ∀ t ∈ Icc (-T₂) T₂, (r₂ t : AddCircle (1 : ℝ)) = e (β₂ (s * t)) := fun t ht => by
    rw [he, ← hl₂ _ (mul_mem_Icc_of_sq hs ht), signDiffeo_coe hd₁]
  have hc₁c : Continuous c₁ := continuous_const.mul hb₁c
  have hr₂c : Continuous r₂ := continuous_const.mul (hb₂c.comp (continuous_const.mul
    continuous_id))
  have hlen : c₁ T₃ - c₁ (-T₃) < 1 :=
    sub_lt_one_of_injOn hc₁c.continuousOn hT₃ (fun t ht => hc₁l t (hIcc₃ ht))
      (fun t ht t' ht' htt => hinj₁ (hIcc₃ ht) (hIcc₃ ht') (e.injective htt))
  have hmono : StrictMonoOn c₁ (Icc (-T₃) T₃) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hc₁c.continuousOn fun t ht => by
      rw [interior_Icc] at ht
      exact hc₁d t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hle₃ : -T₃ ≤ T₃ := by linarith
  set a₀ := c₁ (-T₃) with ha₀
  set a₁ := c₁ T₃ with ha₁
  have hforbid : ∀ t ∈ Icc (-T₃) T₃, ∀ t' ∈ Icc (-T₃) T₃, ∀ n : ℤ, r₂ t ≠ c₁ t' + n := by
    intro t ht t' ht' n hn
    have hn0 : ((n : ℝ) : AddCircle (1 : ℝ)) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    have h1 : e (β₂ (s * t)) = e (β₁ t') := by
      rw [← hr₂l t (hIcc₃ ht), ← hc₁l t' (hIcc₃ ht'), hn, AddCircle.coe_add, hn0, add_zero]
    exact hdisj _ (mul_mem_Icc_of_sq hs (hIcc₃ ht)) t' (hIcc₃ ht') (e.injective h1)
  have hn0 : ∀ m : ℤ, ((m : ℝ) : AddCircle (1 : ℝ)) = 0 := fun m => by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨m, by simp⟩
  set n : ℤ := ⌊a₁ - r₂ (-T₃)⌋ + 1 with hn
  have hfl := Int.floor_le (a₁ - r₂ (-T₃))
  have hfl' := Int.lt_floor_add_one (a₁ - r₂ (-T₃))
  have hncast : (n : ℝ) = (⌊a₁ - r₂ (-T₃)⌋ : ℝ) + 1 := by rw [hn]; push_cast; ring
  have hx₀ : a₁ < r₂ (-T₃) + n := by rw [hncast]; linarith
  have hx₀' : r₂ (-T₃) + n ≤ a₁ + 1 := by rw [hncast]; linarith
  have hm₃ : -T₃ ∈ Icc (-T₃) T₃ := ⟨le_rfl, hle₃⟩
  have hM₃ : T₃ ∈ Icc (-T₃) T₃ := ⟨hle₃, le_rfl⟩
  have hx₁ : r₂ (-T₃) + n < a₀ + 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨t', ht', hct'⟩ := intermediate_value_Icc hle₃ hc₁c.continuousOn
      (show r₂ (-T₃) + n - 1 ∈ Icc a₀ a₁ from ⟨by linarith, by linarith⟩)
    exact hforbid (-T₃) hm₃ t' ht' (1 - n) (by push_cast; linarith)
  set R₂ : ℝ → ℝ := fun t => r₂ t + n with hR₂
  have hR₂c : Continuous R₂ := hr₂c.add continuous_const
  have hR : ∀ t ∈ Icc (-T₃) T₃, a₁ < R₂ t ∧ R₂ t < a₀ + 1 := by
    intro t ht
    constructor
    · by_contra hcon
      push Not at hcon
      obtain ⟨t'', ht'', hct''⟩ := intermediate_value_Icc' ht.1 hR₂c.continuousOn
        (show a₁ ∈ Icc (R₂ t) (R₂ (-T₃)) from ⟨hcon, hx₀.le⟩)
      exact hforbid t'' ⟨ht''.1, ht''.2.trans ht.2⟩ T₃ hM₃ (-n)
        (by simp only [hR₂] at hct''; push_cast; linarith)
    · by_contra hcon
      push Not at hcon
      obtain ⟨t'', ht'', hct''⟩ := intermediate_value_Icc ht.1 hR₂c.continuousOn
        (show a₀ + 1 ∈ Icc (R₂ (-T₃)) (R₂ t) from ⟨hx₁.le, hcon⟩)
      exact hforbid t'' ⟨ht''.1, ht''.2.trans ht.2⟩ (-T₃) hm₃ (1 - n)
        (by simp only [hR₂] at hct''; push_cast; linarith)
  set g₂ : ℝ → ℝ := fun u => R₂ (u - L) with hg₂
  have hg₂s : ContDiffOn ℝ ∞ g₂ (Ioo (L - T₂) (L + T₂)) :=
    (hr₂s.add contDiffOn_const).comp (contDiff_id.sub contDiff_const).contDiffOn
      fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hg₂d : ∀ u ∈ Ioo (L - T₂) (L + T₂), 0 < deriv g₂ u := by
    intro u hu
    have hm : u - L ∈ Ioo (-T₂) T₂ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h1 := ((hasDerivAt_of_contDiffOn isOpen_Ioo hr₂s hm).add_const (n : ℝ)).comp u
      ((hasDerivAt_id' u).sub_const L)
    rw [mul_one] at h1
    have h2 : deriv g₂ u = deriv r₂ (u - L) := h1.deriv
    rw [h2]
    exact hr₂d _ hm
  obtain ⟨G, δ, hδ, hG, hGd, hG1, hG2⟩ := exists_two_piece_lift (g₁ := c₁) (g₂ := g₂)
    (p₀ := -T₃) (p₁ := T₃) (q₀ := L - T₃) (q₁ := L + T₃) isOpen_Ioo isOpen_Ioo hle₃
    (by linarith) (by linarith) hIoo₃ (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    hc₁s hg₂s hc₁d hg₂d (by
      change a₁ < R₂ (L - T₃ - L)
      rw [show L - T₃ - L = -T₃ by ring]
      exact hx₀)
  refine ⟨e, G, δ, hδ, hG, hGd, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · rw [hG1 hm₃, hG2 ⟨by linarith, le_rfl⟩]
    change R₂ (L + T₃ - L) - a₀ < 1
    rw [show L + T₃ - L = T₃ by ring]
    linarith [(hR T₃ hM₃).2]
  · rw [hG1 ht]
    exact hc₁l t (hIcc₃ ht)
  · have hst := mul_mem_Icc_of_sq hs ht
    rw [hG2 ⟨by linarith [hst.1], by linarith [hst.2]⟩]
    change ((r₂ (L + s * t - L) + n : ℝ) : AddCircle (1 : ℝ)) = _
    rw [AddCircle.coe_add, hn0, add_zero, show L + s * t - L = s * t by ring,
      hr₂l _ (hIcc₃ hst), ← mul_assoc, ← sq, hs, one_mul]

theorem exists_addCircle_diffeo_twoArc {β₁ β₂ β'₁ β'₂ : ℝ → AddCircle (1 : ℝ)} {T₁ T₂ s : ℝ}
    (hT₁ : 0 ≤ T₁) (hT : T₁ < T₂) (hs : s ^ 2 = 1) (h : HasArcType β₁ β₂ T₂ s)
    (h' : HasArcType β'₁ β'₂ T₂ s) (hinj : InjOn β₁ (Icc (-T₂) T₂))
    (hinj' : InjOn β'₁ (Icc (-T₂) T₂))
    (hdisj : ∀ t ∈ Icc (-T₂) T₂, ∀ t' ∈ Icc (-T₂) T₂, β₂ t ≠ β₁ t')
    (hdisj' : ∀ t ∈ Icc (-T₂) T₂, ∀ t' ∈ Icc (-T₂) T₂, β'₂ t ≠ β'₁ t') :
    ∃ k : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)) (AddCircle (1 : ℝ)) ∞,
      ∀ t ∈ Icc (-T₁) T₁, k (β₁ t) = β'₁ t ∧ k (β₂ t) = β'₂ t := by
  set T₃ := (T₁ + T₂) / 2 with hT₃
  have hT₃0 : 0 ≤ T₃ := by rw [hT₃]; linarith
  have hT₃₂ : T₃ < T₂ := by rw [hT₃]; linarith
  have hT₁₃ : T₁ < T₃ := by rw [hT₃]; linarith
  set L := 2 * T₃ + 1 with hL
  have hL' : 2 * T₃ < L := by rw [hL]; linarith
  obtain ⟨e, G, δ, hδ, hG, hGd, hGlen, hG1, hG2⟩ :=
    exists_concat_lift hT₃0 hT₃₂ hs h hinj hdisj hL'
  obtain ⟨e', G', δ', hδ', hG', hGd', hGlen', hG1', hG2'⟩ :=
    exists_concat_lift hT₃0 hT₃₂ hs h' hinj' hdisj' hL'
  set δ₀ := min δ δ' with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδ hδ'
  have hJ : Ioo (-T₃ - δ₀) (L + T₃ + δ₀) ⊆ Ioo (-T₃ - δ) (L + T₃ + δ) := fun u hu =>
    ⟨by linarith [hu.1, min_le_left δ δ'], by linarith [hu.2, min_le_left δ δ']⟩
  have hJ' : Ioo (-T₃ - δ₀) (L + T₃ + δ₀) ⊆ Ioo (-T₃ - δ') (L + T₃ + δ') := fun u hu =>
    ⟨by linarith [hu.1, min_le_right δ δ'], by linarith [hu.2, min_le_right δ δ']⟩
  obtain ⟨k₀, hk₀⟩ := exists_addCircle_diffeo_comp_eqOn (b := G) (b' := G') (u₀ := -T₃)
    (u₁ := L + T₃) isOpen_Ioo (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    (by linarith) hG.contDiffOn hG'.contDiffOn (fun u hu => hGd u (hJ hu))
    (fun u hu => hGd' u (hJ' hu)) hGlen hGlen'
  refine ⟨e.trans (k₀.trans e'.symm), fun t ht => ?_⟩
  have ht₃ : t ∈ Icc (-T₃) T₃ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hst := mul_mem_Icc_of_sq hs ht₃
  constructor
  · change e'.symm (k₀ (e (β₁ t))) = β'₁ t
    rw [← hG1 t ht₃, hk₀ t ⟨by linarith [ht.1], by linarith [ht.2]⟩, hG1' t ht₃,
      Diffeomorph.symm_apply_apply]
  · change e'.symm (k₀ (e (β₂ t))) = β'₂ t
    rw [← hG2 t ht₃, hk₀ (L + s * t) ⟨by linarith [hst.1], by linarith [hst.2]⟩, hG2' t ht₃,
      Diffeomorph.symm_apply_apply]

end GC.Seifert.SaddleSlabProof
