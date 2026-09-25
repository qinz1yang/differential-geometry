import DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianBigonLift
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCylindricalDiagram.exists_upper_returning_arc_in_strip
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {f : E × ℝ → F} {P B : Set E} {S : Set F}
    (hf : IsCylindricalDiagram f P S) (hP : IsPolyhedron P) (hBP : B ⊆ P)
    (e : S ≃ₜ (P × loopCircle))
    (he : ∀ (x : P) (t : Icc (0 : ℝ) 1), (e.symm (x, (t : ℝ)) : F) = f (x, t))
    {β : ℝ → F} (hβ : IsPLHomeomorphOn β (Icc 0 1) (β '' Icc 0 1))
    (hβside : β '' Icc 0 1 ⊆ f '' (B ×ˢ Icc 0 1)) {g : F → ℝ}
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ht : β t ∈ S,
      (e ⟨β t, ht⟩).2 = (g (β t) : loopCircle))
    {m : ℤ} (hzero : g (β 0) = m) (hone : g (β 1) = m)
    (hopen : ∀ t ∈ Ioo (0 : ℝ) 1, g (β t) < m) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, (m : ℝ) - δ ≤ g (β t) ∧ g (β t) ≤ m) :
    ∃ (a : ℝ) (γ : ℝ → E × ℝ), 0 < a ∧ a < 1 ∧
      IsPLHomeomorphOn γ (Icc 0 1) (γ '' Icc 0 1) ∧
      γ '' Icc 0 1 ⊆ B ×ˢ Ioc a 1 ∧
      (γ '' Icc 0 1) ∩ (B ×ˢ ({1} : Set ℝ)) = {γ 0, γ 1} ∧
      (∀ t ∈ Icc (0 : ℝ) 1, f (γ t) = β t) ∧
      f '' (γ '' Icc 0 1) = β '' Icc 0 1 := by
  classical
  let a : ℝ := (1 - δ) / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hgap : a < 1 - δ := by dsimp [a]; linarith
  have hstrip := hf.isPLHomeomorphOn_strip hP ha.le le_rfl (Or.inl ha)
  have hβstrip : β '' Icc 0 1 ⊆ f '' (P ×ˢ Icc a 1) := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨⟨x, u⟩, ⟨hxB, hu⟩, hxu⟩ := hβside ⟨t, ht, rfl⟩
    have hys : β t ∈ S := hf.image_eq ▸ ⟨(x, u), ⟨hBP hxB, hu⟩, hxu⟩
    let v : ℝ := g (β t) - m + 1
    have hv : v ∈ Icc a 1 := by
      obtain ⟨hl, hu⟩ := hbound t ht
      dsimp [v]
      exact ⟨by linarith, by linarith⟩
    have hm : ((m : ℝ) : loopCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
      exact ⟨m, by simp only [zsmul_eq_mul, mul_one]⟩
    have hvcoe : (v : loopCircle) = (g (β t) : loopCircle) := by
      change ((g (β t) - (m : ℝ) + 1 : ℝ) : loopCircle) = _
      rw [AddCircle.coe_add, AddCircle.coe_sub, hm, AddCircle.coe_period, sub_zero, add_zero]
    have hxu' : e.symm (⟨x, hBP hxB⟩, (u : loopCircle)) = (⟨β t, hys⟩ : S) := by
      apply Subtype.ext
      exact (he ⟨x, hBP hxB⟩ ⟨u, hu⟩).trans hxu
    have hucoe : (u : loopCircle) = (g (β t) : loopCircle) := by
      rw [← hlift t ht hys, ← hxu', e.apply_symm_apply]
    have hxv := he ⟨x, hBP hxB⟩ ⟨v, ha.le.trans hv.1, hv.2⟩
    change (e.symm (⟨x, hBP hxB⟩, (v : loopCircle)) : F) = f (x, v) at hxv
    rw [hvcoe, ← hucoe, hxu'] at hxv
    exact ⟨(x, v), ⟨hBP hxB, hv⟩, hxv.symm⟩
  let γ : ℝ → E × ℝ := Function.invFunOn f (P ×ˢ Icc a 1) ∘ β
  have hγ := hβ.trans (hstrip.symm.restrict
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn hβ).isPolyhedron hβstrip)
  have hγimage : Function.invFunOn f (P ×ˢ Icc a 1) '' (β '' Icc 0 1) =
      γ '' Icc 0 1 := image_image _ _ _
  rw [hγimage] at hγ
  have hγmap (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f (γ t) = β t :=
    hstrip.bijOn.invOn_invFunOn.2 (hβstrip ⟨t, ht, rfl⟩)
  have hγcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (γ t).1 ∈ B ∧ (γ t).2 = g (β t) - m + 1 := by
    obtain ⟨⟨x, u⟩, ⟨hxB, hu⟩, hxu⟩ := hβside ⟨t, ht, rfl⟩
    have hγP := hstrip.symm.bijOn.mapsTo (hβstrip ⟨t, ht, rfl⟩)
    have hys : β t ∈ S := hf.image_eq ▸ ⟨(x, u), ⟨hBP hxB, hu⟩, hxu⟩
    have hγe := he ⟨(γ t).1, hγP.1⟩
      ⟨(γ t).2, ha.le.trans hγP.2.1, hγP.2.2⟩
    have hxe := he ⟨x, hBP hxB⟩ ⟨u, hu⟩
    have hex : (e ⟨β t, hys⟩).1 = ⟨x, hBP hxB⟩ := by
      have hh : e.symm (⟨x, hBP hxB⟩, (u : loopCircle)) = (⟨β t, hys⟩ : S) :=
        Subtype.ext (hxe.trans hxu)
      rw [← hh, e.apply_symm_apply]
    have heγ : e.symm (⟨(γ t).1, hγP.1⟩, ((γ t).2 : loopCircle)) =
        (⟨β t, hys⟩ : S) := Subtype.ext (hγe.trans (hγmap t ht))
    have hfst : (γ t).1 = x := by
      rw [← heγ, e.apply_symm_apply] at hex
      exact congrArg Subtype.val hex
    refine ⟨hfst ▸ hxB, ?_⟩
    have hcoe : ((γ t).2 : loopCircle) = (g (β t) : loopCircle) := by
      rw [← hlift t ht hys, ← heγ, e.apply_symm_apply]
    have hm : ((m : ℝ) : loopCircle) = 0 := by
      apply (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr
      exact ⟨m, by simp only [zsmul_eq_mul, mul_one]⟩
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ioc
      (p := (1 : ℝ)) (a := 0) ⟨ha.trans_le hγP.2.1, by simpa using hγP.2.2⟩
      (show g (β t) - m + 1 ∈ Ioc (0 : ℝ) (0 + 1) from by
        obtain ⟨hl, hu⟩ := hbound t ht
        constructor <;> linarith)).mp
    rw [AddCircle.coe_add, AddCircle.coe_sub, hm, AddCircle.coe_period,
      sub_zero, add_zero]
    exact hcoe
  have hγside : γ '' Icc 0 1 ⊆ B ×ˢ Ioc a 1 := by
    rintro z ⟨t, ht, rfl⟩
    obtain ⟨hB, hheight⟩ := hγcoord t ht
    obtain ⟨hl, hu⟩ := hbound t ht
    exact ⟨hB, by rw [hheight]; linarith, by rw [hheight]; linarith⟩
  refine ⟨a, γ, ha, ha1, hγ, hγside, ?_, hγmap, ?_⟩
  · ext z
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, -, htop⟩
      rcases ht.1.eq_or_lt with ht0 | ht0
      · exact Or.inl (congrArg γ ht0.symm)
      · rcases ht.2.eq_or_lt with ht1 | ht1
        · exact Or.inr (congrArg γ ht1)
        · have hc := (hγcoord t ht).2
          have ho := hopen t ⟨ht0, ht1⟩
          have : (γ t).2 = 1 := htop
          linarith
    · rintro (rfl | rfl)
      · refine ⟨⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩,
          (hγcoord 0 ⟨le_rfl, zero_le_one⟩).1, ?_⟩
        rw [(hγcoord 0 ⟨le_rfl, zero_le_one⟩).2, hzero, sub_self, zero_add]
        rfl
      · refine ⟨⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩,
          (hγcoord 1 ⟨zero_le_one, le_rfl⟩).1, ?_⟩
        rw [(hγcoord 1 ⟨zero_le_one, le_rfl⟩).2, hone, sub_self, zero_add]
        rfl
  · rw [image_image]
    exact image_congr fun t ht => hγmap t ht

end DifferentialGeometry.Topology.PiecewiseLinear
