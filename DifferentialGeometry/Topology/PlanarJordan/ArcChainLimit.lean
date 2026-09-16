import DifferentialGeometry.Topology.PlanarJordan.ArcChain
import DifferentialGeometry.Topology.PathConcatenation

open Set Filter Topology

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies

theorem isArcBetween_insert_iUnion_of_tendsto
    {A : ℕ → Set Plane} {p : ℕ → Plane} {q : Plane}
    (hA : ∀ n, IsArcBetween (A n) (p n) (p (n + 1)))
    (hmeet : ∀ n, A n ∩ A (n + 1) = {p (n + 1)})
    (hdis : ∀ n m, n + 1 < m → Disjoint (A n) (A m))
    (hq : ∀ n, q ∉ A n) (hlim : Tendsto A atTop (𝓝 q).smallSets) :
    IsArcBetween (insert q (⋃ n, A n)) q (p 0) := by
  choose f hf hi himage hf0 hf1 using hA
  have hjoin (n : ℕ) : f n 1 = f (n + 1) 0 := (hf1 n).trans (hf0 (n + 1)).symm
  let g := intervalConcatenation f
  have hg : ContinuousOn g (Ici 0) := continuousOn_intervalConcatenation hf hjoin
  have hgq : Tendsto g atTop (𝓝 q) :=
    tendsto_intervalConcatenation (by simpa only [himage] using hlim)
  have hfrac (t : ℝ) (ht : 0 ≤ t) : t - ⌊t⌋₊ ∈ Ico (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le ht), Nat.self_sub_floor_lt_one t⟩
  have hgA (t : ℝ) (ht : 0 ≤ t) : g t ∈ A ⌊t⌋₊ := by
    rw [← himage]
    exact mem_image_of_mem _ ⟨(hfrac t ht).1, (hfrac t ht).2.le⟩
  have hgend (t : ℝ) (ht : 0 ≤ t) : g t ≠ p (⌊t⌋₊ + 1) := by
    intro heq
    have ht1 := hi ⌊t⌋₊ ⟨(hfrac t ht).1, (hfrac t ht).2.le⟩ one_mem_I
      (heq.trans (hf1 ⌊t⌋₊).symm)
    exact (hfrac t ht).2.ne ht1
  have hglt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hlt : ⌊x⌋₊ < ⌊y⌋₊) : g x ≠ g y := by
    intro heq
    have hxA := hgA x hx
    have hyA : g x ∈ A ⌊y⌋₊ := heq.symm ▸ hgA y hy
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hlt) with hmore | hadj
    · exact disjoint_left.mp (hdis _ _ hmore) hxA hyA
    · have hcontact : g x ∈ A ⌊x⌋₊ ∩ A (⌊x⌋₊ + 1) := ⟨hxA, by rw [show ⌊x⌋₊ + 1 = ⌊y⌋₊ from hadj]; exact hyA⟩
      exact hgend x hx ((hmeet ⌊x⌋₊).subset hcontact)
  have hgi : InjOn g (Ici 0) := by
    intro x hx y hy heq
    have hfloor : ⌊x⌋₊ = ⌊y⌋₊ := by
      rcases lt_trichotomy ⌊x⌋₊ ⌊y⌋₊ with hlt | he | hgt
      · exact False.elim (hglt hx hy hlt heq)
      · exact he
      · exact False.elim (hglt hy hx hgt heq.symm)
    have heq' : f ⌊x⌋₊ (x - ⌊x⌋₊) = f ⌊x⌋₊ (y - ⌊x⌋₊) := by
      simpa only [g, intervalConcatenation, ← hfloor] using heq
    have hty : y - ⌊x⌋₊ ∈ unitInterval := by
      simpa only [hfloor] using Ico_subset_Icc_self (hfrac y hy)
    have ht := hi ⌊x⌋₊ (Ico_subset_Icc_self (hfrac x hx)) hty heq'
    linarith
  have hgrange : g '' Ici 0 = ⋃ n, A n := by
    apply Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      exact mem_iUnion.mpr ⟨⌊t⌋₊, hgA t ht⟩
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      obtain ⟨t, ht, rfl⟩ := (himage n).symm ▸ hn
      refine ⟨n + t, add_nonneg (Nat.cast_nonneg n) ht.1, ?_⟩
      have hnt : (n : ℝ) + t ∈ Icc (n : ℝ) (n + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      change intervalConcatenation f (n + t) = f n t
      rw [intervalConcatenation_eq_of_mem_Icc hjoin n hnt]
      congr 1
      ring
  obtain ⟨h, hc, h0, h1, heq⟩ := hg.exists_continuousOn_Icc_of_tendsto_atTop hgq
  have hparam {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : 0 ≤ t⁻¹ - 1 :=
    sub_nonneg.mpr ((one_le_inv₀ ht.1).mpr ht.2)
  have hnot {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : h t ≠ q := by
    rw [heq t ht]
    exact fun he => hq _ (he ▸ hgA _ (hparam ht))
  have hinj : InjOn h unitInterval := by
    intro x hx y hy hxy
    by_cases hx0 : x = 0
    · subst x
      by_cases hy0 : y = 0
      · exact hy0.symm
      · exact False.elim (hnot ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), hy.2⟩ (hxy.symm.trans h0))
    by_cases hy0 : y = 0
    · subst y
      exact False.elim (hnot ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩ (hxy.trans h0))
    have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), hx.2⟩
    have hy' : y ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), hy.2⟩
    rw [heq x hx', heq y hy'] at hxy
    have harg := hgi (hparam hx') (hparam hy') hxy
    exact inv_injective (by linarith : x⁻¹ = y⁻¹)
  refine ⟨h, hc, hinj, ?_, h0, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨t, ht, rfl⟩
      by_cases ht0 : t = 0
      · simp only [ht0, h0, mem_insert_iff, true_or]
      · have ht' : t ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
        exact Or.inr (hgrange.subset ⟨t⁻¹ - 1, hparam ht', (heq t ht').symm⟩)
    · rintro x (rfl | hx)
      · exact ⟨0, zero_mem_I, h0⟩
      obtain ⟨t, ht, rfl⟩ := hgrange.symm.subset hx
      change 0 ≤ t at ht
      have ht1 : 0 < t + 1 := by linarith
      have hu : (t + 1)⁻¹ ∈ Ioc (0 : ℝ) 1 :=
        ⟨inv_pos.mpr ht1, (inv_le_one₀ ht1).mpr (by linarith)⟩
      refine ⟨(t + 1)⁻¹, ⟨hu.1.le, hu.2⟩, ?_⟩
      rw [heq _ hu, inv_inv, add_sub_cancel_right]
  · simpa only [g, intervalConcatenation, Nat.floor_zero, Nat.cast_zero, sub_self, hf0] using h1

end DifferentialGeometry.Topology.PlanarJordan
