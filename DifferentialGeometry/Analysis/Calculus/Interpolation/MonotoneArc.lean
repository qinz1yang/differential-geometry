import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
import Mathlib.Algebra.AddConstMap.Basic
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.OrderClosed
import DifferentialGeometry.Topology.LoopSpace.PeriodicExtension

noncomputable section

open Set
open scoped NNReal

namespace CircleDeg1Lift

private theorem exists_monotone_affine_patch
    (f : CircleDeg1Lift) (hf : Continuous f) {a b : ℝ} (hab : a < b) :
    ∃ h : ℝ → ℝ, Continuous h ∧ Monotone h ∧
      (∀ x ≤ b, h x = f a + ((f b - f a) / (b - a)) * (x - a)) ∧
      (∀ x, b ≤ x → h x = f x) ∧ h a = f a ∧
      (∀ K : ℝ≥0, LipschitzWith K f → LipschitzWith K h) := by
  let s := (f b - f a) / (b - a)
  let L := fun x : ℝ => f a + s * (x - a)
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr (f.monotone hab.le)) (sub_pos.mpr hab).le
  have hLa : L a = f a := by simp [L]
  have hLb : L b = f b := by
    dsimp only [L, s]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne')]
    ring
  have hLm : Monotone L := fun x y hxy => by
    dsimp only [L]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (sub_le_sub_right hxy a) hs) _
  let h := fun x : ℝ => if x ≤ b then L x else f x
  have hhc : Continuous h := by
    apply Continuous.if_le (by dsimp [L]; fun_prop) hf continuous_id continuous_const
    intro x hx
    change x = b at hx
    subst x
    exact hLb
  have hleft (x : ℝ) (hx : x ≤ b) : h x = L x := ite_eq_left hx
  have hright (x : ℝ) (hx : b ≤ x) : h x = f x := by
    rcases hx.eq_or_lt with rfl | hx
    · simp only [h, le_refl, ↓reduceIte, hLb]
    · exact ite_eq_right hx.not_ge
  have hhm : Monotone h := by
    intro x y hxy
    by_cases hy : y ≤ b
    · rw [hleft y hy, hleft x (hxy.trans hy)]
      exact hLm hxy
    · by_cases hx : x ≤ b
      · rw [hleft x hx, hright y (le_of_not_ge hy)]
        exact (hLm hx).trans (hLb ▸ f.monotone (le_of_not_ge hy))
      · rw [hright x (le_of_not_ge hx), hright y (le_of_not_ge hy)]
        exact f.monotone hxy
  refine ⟨h, hhc, hhm, hleft, hright, (hleft a hab.le).trans hLa, ?_⟩
  intro K hK
  have hfdiff {x y : ℝ} (hxy : x ≤ y) : f y - f x ≤ (K : ℝ) * (y - x) := by
    have h := hK.dist_le_mul y x
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (f.monotone hxy)),
      abs_of_nonneg (sub_nonneg.mpr hxy)] using h
  have hsK : s ≤ K := (div_le_iff₀ (sub_pos.mpr hab)).mpr (hfdiff hab.le)
  have hLdiff {x y : ℝ} (hxy : x ≤ y) : L y - L x ≤ (K : ℝ) * (y - x) := by
    calc
      L y - L x = s * (y - x) := by dsimp only [L]; ring
      _ ≤ (K : ℝ) * (y - x) := mul_le_mul_of_nonneg_right hsK (sub_nonneg.mpr hxy)
  have hhdiff {x y : ℝ} (hxy : x ≤ y) : h y - h x ≤ (K : ℝ) * (y - x) := by
    by_cases hy : y ≤ b
    · rw [hleft y hy, hleft x (hxy.trans hy)]
      exact hLdiff hxy
    · by_cases hx : x ≤ b
      · rw [hright y (le_of_not_ge hy), hleft x hx]
        have h₁ := hLdiff hx
        rw [hLb] at h₁
        have h₂ := hfdiff (le_of_not_ge hy)
        linarith
      · rw [hright x (le_of_not_ge hx), hright y (le_of_not_ge hy)]
        exact hfdiff hxy
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hhm hxy)), neg_sub] using hhdiff hxy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (hhm hyx))] using hhdiff hyx

private theorem exists_continuous_periodic_extension
    {h : ℝ → ℝ} (hc : Continuous h) (hm : Monotone h) (a : ℝ)
    (hp : h (a + 1) = h a + 1) :
    ∃ g : CircleDeg1Lift, Continuous g ∧ EqOn g h (Icc a (a + 1)) ∧
      (∀ K : ℝ≥0, LipschitzWith K h → LipschitzWith K g) := by
  obtain ⟨G, hGc, hGcc⟩ := AddConstMap.exists_continuous_extension_Icc a hc.continuousOn hp
  have hGp (x : ℝ) : G (x + 1) = G x + 1 := G.map_add_const' x
  have hGm : Monotone G := (AddConstMapClass.monotone_iff_Icc (f := G)
    (by norm_num : (0 : ℝ) < 1) a).mpr (by
      intro x hx y hy hxy
      rw [hGcc hx, hGcc hy]
      exact hm hxy)
  let g : CircleDeg1Lift := ⟨⟨G, hGm⟩, hGp⟩
  refine ⟨g, hGc, hGcc, ?_⟩
  intro K hK
  let H : AddConstMap ℝ ℝ 1 ((K : ℝ) - 1) :=
    ⟨fun x => (K : ℝ) * x - G x, fun x => by rw [hGp]; ring⟩
  have hHm : Monotone H := (AddConstMapClass.monotone_iff_Icc (f := H)
    (by norm_num : (0 : ℝ) < 1) a).mpr (by
      intro x hx y hy hxy
      change (K : ℝ) * x - G x ≤ (K : ℝ) * y - G y
      rw [hGcc hx, hGcc hy]
      have h := hK.dist_le_mul y x
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hm hxy)),
        abs_of_nonneg (sub_nonneg.mpr hxy)] at h
      linarith)
  have hgd {x y : ℝ} (hxy : x ≤ y) : g y - g x ≤ (K : ℝ) * (y - x) := by
    have h := hHm hxy
    change (K : ℝ) * x - G x ≤ (K : ℝ) * y - G y at h
    change G y - G x ≤ (K : ℝ) * (y - x)
    linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rcases le_total x y with hxy | hyx
  · simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (g.monotone hxy)), neg_sub] using hgd hxy
  · simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (g.monotone hyx))] using hgd hyx

theorem exists_continuous_affine_interpolation
    (f : CircleDeg1Lift) (hf : Continuous f) {a b : ℝ} (hab : a < b) (hba : b < a + 1) :
    ∃ g : CircleDeg1Lift, Continuous g ∧
      EqOn g f (⋃ k : ℤ, Ioo (a + k) (b + k))ᶜ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, g (a + t * (b - a)) = (1 - t) * f a + t * f b) ∧
      LipschitzOnWith (Real.nnabs ((f b - f a) / (b - a))) g (Icc a b) ∧
      (∀ K : ℝ≥0, LipschitzWith K f → LipschitzWith K g) := by
  obtain ⟨h, hc, hm, hleft, hright, ha, hLip⟩ := exists_monotone_affine_patch f hf hab
  have hp : h (a + 1) = h a + 1 := by rw [hright _ hba.le, f.map_add_one, ha]
  obtain ⟨g, hgc, hgh, hgLip⟩ := exists_continuous_periodic_extension hc hm a hp
  have hformula {x : ℝ} (hx : x ∈ Icc a b) :
      g x = f a + ((f b - f a) / (b - a)) * (x - a) := by
    rw [hgh ⟨hx.1, hx.2.trans hba.le⟩, hleft x hx.2]
  refine ⟨g, hgc, ?_, ?_, ?_, fun K hK => hgLip K (hLip K hK)⟩
  · intro x hx
    obtain ⟨k, hk, _⟩ := existsUnique_sub_zsmul_mem_Ico (by norm_num : (0 : ℝ) < 1) x a
    have hk' : x - (k : ℝ) ∈ Ico a (a + 1) := by simpa only [zsmul_eq_mul, mul_one] using hk
    have hnot : x - (k : ℝ) ∉ Ioo a b := by
      intro hxk
      apply hx
      exact mem_iUnion.mpr ⟨k, by constructor <;> linarith [hxk.1, hxk.2]⟩
    have heq : h (x - (k : ℝ)) = f (x - (k : ℝ)) := by
      by_cases hxb : b ≤ x - (k : ℝ)
      · exact hright _ hxb
      · have hxa : x - (k : ℝ) = a := by
          by_contra hne
          exact hnot ⟨lt_of_le_of_ne hk'.1 (Ne.symm hne), lt_of_not_ge hxb⟩
        rw [hxa, ha]
    have hbase := (hgh (Ico_subset_Icc_self hk')).trans heq
    rw [g.map_sub_int, f.map_sub_int] at hbase
    linarith
  · intro t ht
    have hx : a + t * (b - a) ∈ Icc a b := by
      constructor <;> nlinarith [ht.1, ht.2]
    rw [hformula hx]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [hformula hx, hformula hy, Real.dist_eq, Real.dist_eq]
    have heq : f a + ((f b - f a) / (b - a)) * (x - a) -
        (f a + ((f b - f a) / (b - a)) * (y - a)) =
        ((f b - f a) / (b - a)) * (x - y) := by ring
    rw [heq, abs_mul]
    rfl

end CircleDeg1Lift

end
