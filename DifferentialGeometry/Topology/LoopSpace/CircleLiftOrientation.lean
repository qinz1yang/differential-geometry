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

end DifferentialGeometry.Topology
