import DifferentialGeometry.Topology.PiecewiseLinear.Section34CylindricalSeamRotation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.mem_closure_sides_of_seam_rotation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hg : IsCylindricalDiagram g P S)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hrot : ∀ z, g z =
      if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1))
    {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1)
    {x : E} (hx : x ∈ P)
    (hbelow : (x, r) ∈ closure (((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | y.2 < r}))
    (habove : (x, r) ∈ closure (((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | r < y.2}))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    f (x, r) ∈ closure (J ∩ g '' (P ×ˢ Ioo a 1)) ∧
      f (x, r) ∈ closure (J \ g '' (P ×ˢ Icc a 1)) := by
  let B := ((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | y.2 < r}
  let A := ((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | r < y.2}
  have hB : B ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
    fun _ hy => ⟨hy.1.1.1, hc.trans hy.1.1.2.1, hy.1.1.2.2.trans hd⟩
  have hA : A ⊆ P ×ˢ Icc (0 : ℝ) 1 :=
    fun _ hy => ⟨hy.1.1.1, hc.trans hy.1.1.2.1, hy.1.1.2.2.trans hd⟩
  have hcont := hf.isPiecewiseAffineOn.continuousOn (x, r)
    ⟨hx, hr.1.le, hr.2.le⟩
  have hsnd : Filter.Tendsto (Prod.snd : E × ℝ → ℝ) (𝓝 (x, r)) (𝓝 r) :=
    continuous_snd.continuousAt
  have hxnear : ∀ᶠ y : E × ℝ in 𝓝 (x, r), r + a - 1 < y.2 ∧ 0 < y.2 := by
    have hnear₁ : ∀ᶠ t : ℝ in 𝓝 r, r + a - 1 < t :=
      isOpen_Ioi.mem_nhds (by change r + a - 1 < r; linarith [ha.2])
    have hnear₂ : ∀ᶠ t : ℝ in 𝓝 r, 0 < t := isOpen_Ioi.mem_nhds hr.1
    exact hsnd.eventually (hnear₁.and hnear₂)
  have hynear : ∀ᶠ y : E × ℝ in 𝓝 (x, r), y.2 < r + a :=
    hsnd.eventually (isOpen_Iio.mem_nhds (by change r < r + a; linarith [ha.1]))
  constructor
  · have : (𝓝[B] (x, r)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hbelow
    apply mem_closure_of_tendsto (hcont.mono hB)
    filter_upwards [self_mem_nhdsWithin,
      hxnear.filter_mono nhdsWithin_le_nhds] with y hy hnear
    have hylo : y.2 < r := hy.2
    refine ⟨hy.1.2, (y.1, y.2 - r + 1),
      ⟨hy.1.1.1, by linarith [hnear.1], by linarith⟩, ?_⟩
    rw [hrot]
    have hcut : ¬y.2 - r + 1 ≤ 1 - r := by linarith [hnear.2]
    rw [ite_eq_right hcut]
    congr 1
    ext
    · rfl
    · dsimp
      ring
  · have : (𝓝[A] (x, r)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp habove
    apply mem_closure_of_tendsto (hcont.mono hA)
    filter_upwards [self_mem_nhdsWithin,
      hynear.filter_mono nhdsWithin_le_nhds] with y hy hnear
    have hyhi : r < y.2 := hy.2
    have htime : y.2 - r ∈ Ioo (0 : ℝ) a := ⟨by linarith, by linarith⟩
    have hytime : y.2 ≤ 1 := hy.1.1.2.2.trans hd
    have hgy : g (y.1, y.2 - r) = f y := by
      rw [hrot, ite_eq_left (by linarith : y.2 - r ≤ 1 - r), sub_add_cancel]
    refine ⟨hy.1.2, ?_⟩
    rintro ⟨z, hz, hzy⟩
    rcases hg.eq_or_endpoints (y.1, y.2 - r)
      ⟨hy.1.1.1, htime.1.le, htime.2.le.trans ha.2.le⟩ z
      ⟨hz.1, ha.1.le.trans hz.2.1, hz.2.2⟩ (hgy.trans hzy.symm) with heq | heq | heq
    · have he := congrArg Prod.snd heq
      dsimp at he
      linarith [htime.2, hz.2.1]
    · exact htime.1.ne' heq.1
    · have he : y.2 - r = 1 := heq.1
      linarith [htime.2, ha.2]

theorem IsCylindricalDiagram.seam_subset_closure_sides_of_rotation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E × ℝ → F} {P : Set E} {S J : Set F}
    (hf : IsCylindricalDiagram f P S) (hg : IsCylindricalDiagram g P S)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (hrot : ∀ z, g z =
      if z.2 ≤ 1 - r then f (z.1, z.2 + r) else f (z.1, z.2 + r - 1))
    {c d : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1)
    (hgerms : ∀ x ∈ P, f (x, r) ∈ J →
      (x, r) ∈ closure (((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | y.2 < r}) ∧
        (x, r) ∈ closure (((P ×ˢ Icc c d) ∩ f ⁻¹' J) ∩ {y | r < y.2}))
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    J ∩ g '' (P ×ˢ ({1} : Set ℝ)) ⊆ closure (J ∩ g '' (P ×ˢ Ioo a 1)) ∧
      J ∩ g '' (P ×ˢ ({1} : Set ℝ)) ⊆ closure (J \ g '' (P ×ˢ Icc a 1)) := by
  have hall (y : F) (hy : y ∈ J ∩ g '' (P ×ˢ ({1} : Set ℝ))) :
      y ∈ closure (J ∩ g '' (P ×ˢ Ioo a 1)) ∧
        y ∈ closure (J \ g '' (P ×ˢ Icc a 1)) := by
    obtain ⟨hyJ, ⟨⟨x, t⟩, ⟨hxP, ht⟩, hxy⟩⟩ := hy
    have ht' : t = 1 := ht
    subst t
    have hgr : g (x, 1) = f (x, r) := by
      rw [hrot, ite_eq_right (by change ¬(1 : ℝ) ≤ 1 - r; linarith [hr.1])]
      congr 1
      ext
      · rfl
      · dsimp
        ring
    rw [hgr] at hxy
    have hxJ : f (x, r) ∈ J := hxy.symm ▸ hyJ
    obtain ⟨hlo, hhi⟩ := hgerms x hxP hxJ
    exact hxy ▸ hf.mem_closure_sides_of_seam_rotation hg hr hrot hc hd hxP hlo hhi ha
  exact ⟨fun y hy => (hall y hy).1, fun y hy => (hall y hy).2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
