import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation

noncomputable section

open Set

namespace DifferentialGeometry.Topology

def HasIncreasingCircleLift (ψ : loopCircle → loopCircle) : Prop :=
  ∃ F : ℝ → ℝ, StrictMono F ∧ (∀ t : ℝ, F (t + 1) = F t + 1) ∧
    ∀ t : ℝ, ((F t : ℝ) : loopCircle) = ψ ((t : ℝ) : loopCircle)

theorem hasIncreasingCircleLift_id : HasIncreasingCircleLift (id : loopCircle → loopCircle) :=
  ⟨id, strictMono_id, fun _ => rfl, fun _ => rfl⟩

theorem HasIncreasingCircleLift.comp {ψ χ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) (hχ : HasIncreasingCircleLift χ) :
    HasIncreasingCircleLift (ψ ∘ χ) := by
  obtain ⟨F, hFm, hFp, hFl⟩ := hψ
  obtain ⟨G, hGm, hGp, hGl⟩ := hχ
  refine ⟨F ∘ G, hFm.comp hGm, fun t => ?_, fun t => ?_⟩
  · change F (G (t + 1)) = F (G t) + 1
    rw [hGp, hFp]
  · change ((F (G t) : ℝ) : loopCircle) = ψ (χ ((t : ℝ) : loopCircle))
    rw [hFl (G t), hGl t]

theorem loopCircle_coe_eq_coe_iff (x y : ℝ) :
    ((x : ℝ) : loopCircle) = ((y : ℝ) : loopCircle) ↔ ∃ n : ℤ, x - y = (n : ℝ) := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using hn.symm⟩

theorem exists_lift_mem_Ico (θ : loopCircle) : ∃ t ∈ Ico (0 : ℝ) 1, ((t : ℝ) : loopCircle) = θ := by
  have hmem : θ ∈ ((↑) : ℝ → loopCircle) '' Ico (0 : ℝ) (0 + 1) := by
    rw [AddCircle.coe_image_Ico_eq]
    exact mem_univ θ
  obtain ⟨t, ht, hθ⟩ := hmem
  exact ⟨t, by simpa using ht, hθ⟩

theorem hasIncreasingCircleLift_of_three_fixed (ψ : loopCircle ≃ₜ loopCircle)
    {a b c : loopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ψ a = a) (hb : ψ b = b) (hc : ψ c = c) :
    HasIncreasingCircleLift ψ := by
  rcases circleHomeomorph_affineLift_or_neg ψ with ⟨F, hp, hm, hval⟩ | ⟨F, hp, hm, hval⟩
  · refine ⟨F, hm, hp, fun t => ?_⟩
    rw [hval ((t : ℝ) : loopCircle)]
    rfl
  · exfalso
    set G : ℝ → ℝ := fun t => t + F t with hGdef
    have hGm : StrictMono G := by
      intro x y hxy
      have hlt := hm hxy
      simp only [hGdef]
      linarith
    have hGone : G 1 = G 0 + 2 := by
      have h := hp 0
      simp only [hGdef]
      rw [zero_add] at h
      rw [h]
      ring
    have hfix : ∀ θ : loopCircle, ψ θ = θ → ∀ t ∈ Ico (0 : ℝ) 1,
        ((t : ℝ) : loopCircle) = θ → ∃ n : ℤ, G t = (n : ℝ) := by
      intro θ hθ t ht htθ
      have hψt : ψ ((t : ℝ) : loopCircle) = ((-F t : ℝ) : loopCircle) := by
        rw [hval ((t : ℝ) : loopCircle)]
        change -(((F t : ℝ)) : loopCircle) = ((-F t : ℝ) : loopCircle)
        rw [QuotientAddGroup.mk_neg]
      have heq : ((-F t : ℝ) : loopCircle) = ((t : ℝ) : loopCircle) := by
        rw [← hψt, htθ, hθ, ← htθ]
      obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff _ _).mp heq
      refine ⟨-n, ?_⟩
      simp only [hGdef]
      push_cast
      linarith
    obtain ⟨ta, hta, htaθ⟩ := exists_lift_mem_Ico a
    obtain ⟨tb, htb, htbθ⟩ := exists_lift_mem_Ico b
    obtain ⟨tc, htc, htcθ⟩ := exists_lift_mem_Ico c
    obtain ⟨na, hna⟩ := hfix a ha ta hta htaθ
    obtain ⟨nb, hnb⟩ := hfix b hb tb htb htbθ
    obtain ⟨nc, hnc⟩ := hfix c hc tc htc htcθ
    set m : ℤ := ⌈G 0⌉ with hmdef
    have hbound : ∀ {t : ℝ}, t ∈ Ico (0 : ℝ) 1 → ∀ {n : ℤ}, G t = (n : ℝ) →
        m ≤ n ∧ n ≤ m + 1 := by
      intro t ht n hn
      have hlow : G 0 ≤ (n : ℝ) := by
        rw [← hn]
        exact hGm.monotone ht.1
      have hhigh : (n : ℝ) < G 0 + 2 := by
        rw [← hn, ← hGone]
        exact hGm ht.2
      have hm1 : (m : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Int.ceil_le.mpr hlow
      have hm2 : G 0 ≤ (m : ℝ) := Int.le_ceil _
      constructor
      · exact_mod_cast hm1
      · have : (n : ℝ) < (m : ℝ) + 2 := by linarith
        have hlt : n < m + 2 := by exact_mod_cast this
        omega
    obtain ⟨hna1, hna2⟩ := hbound hta hna
    obtain ⟨hnb1, hnb2⟩ := hbound htb hnb
    obtain ⟨hnc1, hnc2⟩ := hbound htc hnc
    have hneab : na ≠ nb := by
      intro h
      apply hab
      rw [← htaθ, ← htbθ]
      have : G ta = G tb := by rw [hna, hnb, h]
      rw [hGm.injective this]
    have hneac : na ≠ nc := by
      intro h
      apply hac
      rw [← htaθ, ← htcθ]
      have : G ta = G tc := by rw [hna, hnc, h]
      rw [hGm.injective this]
    have hnebc : nb ≠ nc := by
      intro h
      apply hbc
      rw [← htbθ, ← htcθ]
      have : G tb = G tc := by rw [hnb, hnc, h]
      rw [hGm.injective this]
    omega

theorem hasIncreasingCircleLift_normalized {ψ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) (h0 : ψ ((0 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle)) :
    ∃ F : ℝ → ℝ, StrictMono F ∧ (∀ t : ℝ, F (t + 1) = F t + 1) ∧
      (∀ t : ℝ, ((F t : ℝ) : loopCircle) = ψ ((t : ℝ) : loopCircle)) ∧ F 0 = 0 := by
  obtain ⟨F, hFm, hFp, hFl⟩ := hψ
  have hF0 : ((F 0 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle) := by rw [hFl 0, h0]
  obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff _ _).mp hF0
  refine ⟨fun t => F t - (n : ℝ), fun x y hxy => by simpa using hFm hxy, fun t => by
      simp only [hFp t]; ring, fun t => ?_, by simp only [sub_zero] at hn; linarith⟩
  rw [← hFl t]
  exact (loopCircle_coe_eq_coe_iff _ _).mpr ⟨-n, by push_cast; ring⟩

theorem image_coe_Icc_zero_half_eq_of_hasIncreasingCircleLift {ψ : loopCircle → loopCircle}
    (hψ : HasIncreasingCircleLift ψ) (hsurj : Function.Surjective ψ)
    (h0 : ψ ((0 : ℝ) : loopCircle) = ((0 : ℝ) : loopCircle))
    (hhalf : ψ (((1 : ℝ) / 2 : ℝ) : loopCircle) = (((1 : ℝ) / 2 : ℝ) : loopCircle)) :
    ψ '' ((fun t : ℝ => (t : loopCircle)) '' Icc 0 ((1 : ℝ) / 2)) =
      (fun t : ℝ => (t : loopCircle)) '' Icc 0 ((1 : ℝ) / 2) := by
  obtain ⟨F, hFm, hFp, hFl, hF0⟩ := hasIncreasingCircleLift_normalized hψ h0
  have hF1 : F 1 = 1 := by
    have h := hFp 0
    rw [zero_add, hF0] at h
    rw [h]
    norm_num
  have hFhalf : F ((1 : ℝ) / 2) = (1 : ℝ) / 2 := by
    have hc : ((F ((1 : ℝ) / 2) : ℝ) : loopCircle) = (((1 : ℝ) / 2 : ℝ) : loopCircle) := by
      rw [hFl, hhalf]
    obtain ⟨m, hm⟩ := (loopCircle_coe_eq_coe_iff _ _).mp hc
    have hlow : (0 : ℝ) < F ((1 : ℝ) / 2) := by
      have hlt := hFm (show (0 : ℝ) < (1 : ℝ) / 2 by norm_num)
      rw [hF0] at hlt
      exact hlt
    have hhigh : F ((1 : ℝ) / 2) < 1 := by
      have hlt := hFm (show (1 : ℝ) / 2 < 1 by norm_num)
      rw [hF1] at hlt
      exact hlt
    have hm0 : m = 0 := by
      have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
      have h2 : (m : ℝ) < 1 := by linarith
      have h1' : (-1 : ℤ) < m := by exact_mod_cast h1
      have h2' : m < 1 := by exact_mod_cast h2
      omega
    rw [hm0] at hm
    push_cast at hm
    linarith
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨F t, ⟨?_, ?_⟩, hFl t⟩
    · rw [← hF0]
      exact hFm.monotone ht.1
    · rw [← hFhalf]
      exact hFm.monotone ht.2
  · rintro _ ⟨s, hs, rfl⟩
    obtain ⟨θ, hθ⟩ := hsurj ((s : ℝ) : loopCircle)
    obtain ⟨t, ht, htθ⟩ := exists_lift_mem_Ico θ
    have hFts : ((F t : ℝ) : loopCircle) = ((s : ℝ) : loopCircle) := by
      rw [hFl t, htθ, hθ]
    obtain ⟨k, hk⟩ := (loopCircle_coe_eq_coe_iff _ _).mp hFts
    have hlow : (0 : ℝ) ≤ F t := by
      rw [← hF0]
      exact hFm.monotone ht.1
    have hhigh : F t < 1 := by
      rw [← hF1]
      exact hFm ht.2
    have hk0 : k = 0 := by
      have h1 : (-1 : ℝ) < (k : ℝ) := by linarith [hs.1, hs.2]
      have h2 : (k : ℝ) < 1 := by linarith [hs.1, hs.2]
      have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    rw [hk0] at hk
    push_cast at hk
    have hFt : F t = s := by linarith
    have htmem : t ∈ Icc (0 : ℝ) ((1 : ℝ) / 2) := by
      refine ⟨ht.1, ?_⟩
      by_contra hcon
      have hlt := hFm (not_le.mp hcon)
      rw [hFhalf, hFt] at hlt
      linarith [hs.2]
    exact ⟨((t : ℝ) : loopCircle), ⟨t, htmem, rfl⟩, by rw [← hFl t, hFt]⟩

theorem HasIncreasingCircleLift.congr {ψ χ : loopCircle → loopCircle}
    (h : HasIncreasingCircleLift ψ) (hc : ∀ theta, χ theta = ψ theta) :
    HasIncreasingCircleLift χ := by
  obtain ⟨F, hFm, hFp, hFl⟩ := h
  exact ⟨F, hFm, hFp, fun t => (hFl t).trans (hc _).symm⟩

theorem hasIncreasingCircleLift_of_three_fixed_of_continuous {ψ : loopCircle → loopCircle}
    (hcont : Continuous ψ) (hbij : Function.Bijective ψ)
    {a b c : loopCircle} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ψ a = a) (hb : ψ b = b) (hc : ψ c = c) : HasIncreasingCircleLift ψ :=
  hasIncreasingCircleLift_of_three_fixed
    (Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ψ hbij) hcont)
    hab hac hbc ha hb hc

theorem lift_sub_one {F : ℝ → ℝ} (hFp : ∀ t : ℝ, F (t + 1) = F t + 1) (s : ℝ) :
    F (s - 1) = F s - 1 := by
  have h := hFp (s - 1)
  rw [show s - 1 + 1 = s by ring] at h
  linarith

theorem lift_add_intCast {F : ℝ → ℝ} (hFp : ∀ t : ℝ, F (t + 1) = F t + 1) (n : ℤ) (t : ℝ) :
    F (t + (n : ℝ)) = F t + (n : ℝ) := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      push_cast at ih ⊢
      rw [show t + ((k : ℝ) + 1) = t + (k : ℝ) + 1 by ring, hFp, ih]
      ring
  | pred k ih =>
      push_cast at ih ⊢
      rw [show t + (-(k : ℝ) - 1) = t + -(k : ℝ) - 1 by ring, lift_sub_one hFp, ih]
      ring

theorem lift_surjective_of_surjective {ψ : loopCircle → loopCircle} {F : ℝ → ℝ}
    (hFp : ∀ t : ℝ, F (t + 1) = F t + 1)
    (hFl : ∀ t : ℝ, ((F t : ℝ) : loopCircle) = ψ ((t : ℝ) : loopCircle))
    (hψ : Function.Surjective ψ) : Function.Surjective F := by
  intro y
  obtain ⟨θ, hθ⟩ := hψ ((y : ℝ) : loopCircle)
  obtain ⟨t, -, htθ⟩ := exists_lift_mem_Ico θ
  have hc : ((F t : ℝ) : loopCircle) = ((y : ℝ) : loopCircle) := by rw [hFl t, htθ, hθ]
  obtain ⟨k, hk⟩ := (loopCircle_coe_eq_coe_iff _ _).mp hc
  refine ⟨t + ((-k : ℤ) : ℝ), ?_⟩
  rw [lift_add_intCast hFp]
  push_cast
  linarith

theorem HasIncreasingCircleLift.inv {ψ χ : loopCircle → loopCircle}
    (h : HasIncreasingCircleLift ψ) (hψ : Function.Surjective ψ)
    (hχ : ∀ θ, χ (ψ θ) = θ) : HasIncreasingCircleLift χ := by
  obtain ⟨F, hFm, hFp, hFl⟩ := h
  have hFs : Function.Surjective F := lift_surjective_of_surjective hFp hFl hψ
  have hFr : ∀ t, F (Function.invFun F t) = t := Function.rightInverse_invFun hFs
  have hFli : ∀ t, Function.invFun F (F t) = t := Function.leftInverse_invFun hFm.injective
  refine ⟨Function.invFun F, ?_, ?_, ?_⟩
  · intro x y hxy
    by_contra hcon
    have hle : Function.invFun F y ≤ Function.invFun F x := not_lt.mp hcon
    have := hFm.monotone hle
    rw [hFr, hFr] at this
    exact absurd hxy (not_lt.mpr this)
  · intro t
    have hval : F (Function.invFun F t + 1) = t + 1 := by rw [hFp, hFr]
    have h2 := congrArg (Function.invFun F) hval
    rw [hFli] at h2
    exact h2.symm
  · intro t
    have hval : ψ (((Function.invFun F t : ℝ)) : loopCircle) = ((t : ℝ) : loopCircle) := by
      rw [← hFl, hFr]
    rw [← hχ (((Function.invFun F t : ℝ)) : loopCircle), hval]

theorem HasIncreasingCircleLift.negConj {ψ : loopCircle → loopCircle}
    (h : HasIncreasingCircleLift ψ) :
    HasIncreasingCircleLift (fun θ => -ψ (-θ)) := by
  obtain ⟨F, hFm, hFp, hFl⟩ := h
  refine ⟨fun t => -F (-t), ?_, ?_, ?_⟩
  · intro x y hxy
    simpa using hFm (neg_lt_neg hxy)
  · intro t
    change -F (-(t + 1)) = -F (-t) + 1
    rw [show -(t + 1) = -t - 1 by ring, lift_sub_one hFp]
    ring
  · intro t
    change ((-F (-t) : ℝ) : loopCircle) = -ψ (-((t : ℝ) : loopCircle))
    rw [QuotientAddGroup.mk_neg, hFl (-t), ← QuotientAddGroup.mk_neg]

theorem HasIncreasingCircleLift.conj {ψ : loopCircle → loopCircle}
    (h : HasIncreasingCircleLift ψ) (φ : loopCircle ≃ₜ loopCircle) :
    HasIncreasingCircleLift fun θ => φ.symm (ψ (φ θ)) := by
  rcases circleHomeomorph_affineLift_or_neg φ with ⟨F, hp, hm, hval⟩ | ⟨F, hp, hm, hval⟩
  · have hφ : HasIncreasingCircleLift φ := ⟨F, hm, hp, fun t => by simp [hval]⟩
    have hφs : HasIncreasingCircleLift φ.symm :=
      hφ.inv φ.surjective fun θ => φ.symm_apply_apply θ
    exact (hφs.comp h).comp hφ
  · set η : loopCircle ≃ₜ loopCircle := φ.trans (Homeomorph.neg loopCircle) with hηdef
    have hηval : ∀ θ, η θ = -φ θ := fun _ => rfl
    have hη : HasIncreasingCircleLift η := by
      refine ⟨F, hm, hp, fun t => ?_⟩
      simp [hηval, hval]
    have hηs : HasIncreasingCircleLift η.symm :=
      hη.inv η.surjective fun θ => η.symm_apply_apply θ
    have hsymm : ∀ θ, φ.symm θ = η.symm (-θ) := by
      intro θ
      refine φ.injective ?_
      rw [φ.apply_symm_apply]
      have hval2 : φ (η.symm (-θ)) = -(η (η.symm (-θ))) := by rw [hηval]; rw [neg_neg]
      rw [hval2, η.apply_symm_apply, neg_neg]
    refine ((hηs.comp h.negConj).comp hη).congr fun θ => ?_
    change φ.symm (ψ (φ θ)) = η.symm (-ψ (-η θ))
    rw [hsymm, hηval, neg_neg]

theorem not_hasIncreasingCircleLift_of_neg_lift {ψ : loopCircle → loopCircle} {G : ℝ → ℝ}
    (hGm : StrictMono G) (hGp : ∀ t : ℝ, G (t + 1) = G t + 1)
    (hGl : ∀ t : ℝ, ψ ((t : ℝ) : loopCircle) = ((-G t : ℝ) : loopCircle)) :
    ¬ HasIncreasingCircleLift ψ := by
  rintro ⟨F, hFm, hFp, hFl⟩
  set H : ℝ → ℝ := fun t => F t + G t with hHdef
  have hHm : StrictMono H := by
    intro x y hxy
    have h1 := hFm hxy
    have h2 := hGm hxy
    simp only [hHdef]
    linarith
  have hHint : ∀ t : ℝ, ∃ n : ℤ, H t = (n : ℝ) := by
    intro t
    have hc : ((F t : ℝ) : loopCircle) = ((-G t : ℝ) : loopCircle) := by rw [hFl t, hGl t]
    obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff _ _).mp hc
    exact ⟨n, by simp only [hHdef]; linarith⟩
  have hHstep : H 1 = H 0 + 2 := by
    have h1 := hFp 0
    have h2 := hGp 0
    rw [zero_add] at h1 h2
    simp only [hHdef]
    linarith
  obtain ⟨n0, hn0⟩ := hHint 0
  obtain ⟨n1, hn1⟩ := hHint ((1 : ℝ) / 4)
  obtain ⟨n2, hn2⟩ := hHint ((1 : ℝ) / 2)
  obtain ⟨n3, hn3⟩ := hHint 1
  have h01 : (n0 : ℝ) < (n1 : ℝ) := by rw [← hn0, ← hn1]; exact hHm (by norm_num)
  have h12 : (n1 : ℝ) < (n2 : ℝ) := by rw [← hn1, ← hn2]; exact hHm (by norm_num)
  have h23 : (n2 : ℝ) < (n3 : ℝ) := by rw [← hn2, ← hn3]; exact hHm (by norm_num)
  have h03 : (n3 : ℝ) = (n0 : ℝ) + 2 := by rw [← hn0, ← hn3]; exact hHstep
  have h01' : n0 < n1 := by exact_mod_cast h01
  have h12' : n1 < n2 := by exact_mod_cast h12
  have h23' : n2 < n3 := by exact_mod_cast h23
  have h03' : n3 = n0 + 2 := by exact_mod_cast h03
  omega

theorem not_hasIncreasingCircleLift_neg :
    ¬ HasIncreasingCircleLift (fun θ : loopCircle => -θ) :=
  not_hasIncreasingCircleLift_of_neg_lift strictMono_id (fun _ => rfl)
    fun t => by rw [← QuotientAddGroup.mk_neg]; rfl

end DifferentialGeometry.Topology
