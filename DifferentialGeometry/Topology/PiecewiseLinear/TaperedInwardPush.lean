/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section CollarZero

variable {E : Type*}

theorem collarOutwardMap_eq_self_of_eq_zero {g : E → ℝ} (a : ℝ) {x : E × ℝ} (hg : g x.1 = 0)
    (hx : 0 ≤ x.2) : collarOutwardMap g a x = x := by
  refine Prod.ext rfl ?_
  change max 0 (min x.2 (max (x.2 - g x.1) (2 * x.2 - a))) = x.2
  rw [hg, sub_zero, min_eq_left (le_max_left _ _), max_eq_right hx]

end CollarZero

section Bottom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {B W : Set E} {ρ : E × ℝ → E}

theorem IsPLHomeomorphOn.mem_bottom_iff_snd_eq_zero
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hbottom : ∀ x ∈ B, ρ (x, 0) = x)
    {z : E × ℝ} (hz : z ∈ B ×ˢ Icc (0 : ℝ) 1) : ρ z ∈ B ↔ z.2 = 0 := by
  constructor
  · intro hB
    have heq : z = (ρ z, 0) :=
      hρ.bijOn.injOn hz ⟨hB, le_rfl, zero_le_one⟩ (hbottom _ hB).symm
    exact congrArg Prod.snd heq
  · intro hzero
    have heq : z = (z.1, 0) := Prod.ext rfl hzero
    rw [heq, hbottom _ hz.1]
    exact hz.1
end Bottom

section Taper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B W R : Set E} {ρ : E × ℝ → E}

theorem IsPLHomeomorphOn.exists_pos_forall_le_of_disjoint
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hBR : Disjoint B R) (hbottom : ∀ x ∈ B, ρ (x, 0) = x) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → a ≤ t := by
  classical
  let U := B ×ˢ Icc (0 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hleft : LeftInvOn τ ρ U := hρ.bijOn.invOn_invFunOn.1
  have hright : RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hheight : ∀ x ∈ W ∩ R, 0 < (τ x).2 := by
    intro x hx
    have hne : (τ x).2 ≠ 0 := by
      intro hzero
      have hxB : x ∈ B := by
        rw [← hright hx.1]
        exact (hρ.mem_bottom_iff_snd_eq_zero hbottom (hτ hx.1)).mpr hzero
      exact Set.disjoint_left.mp hBR hxB hx.2
    exact lt_of_le_of_ne (hτ hx.1).2.1 hne.symm
  obtain ⟨r, hr, hrheight⟩ : ∃ r : ℝ, 0 < r ∧ ∀ x ∈ W ∩ R, r ≤ (τ x).2 := by
    by_cases hne : (W ∩ R).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (hW.isCompact.inter_right hR.isClosed).exists_isMinOn hne
        (hρ.isPiecewiseAffineOn_invFunOn.continuousOn.snd.mono inter_subset_left)
      exact ⟨(τ x).2, hheight x hx, fun y hy => hmin hy⟩
    · exact ⟨1, zero_lt_one, fun x hx => False.elim (hne ⟨x, hx⟩)⟩
  refine ⟨min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_⟩
  intro y hy t ht hmem
  have hzU : ((y, t) : E × ℝ) ∈ U := ⟨hy, ht⟩
  have hxW : ρ (y, t) ∈ W := hρ.bijOn.mapsTo hzU
  have hle := hrheight (ρ (y, t)) ⟨hxW, hmem⟩
  rw [hleft hzU] at hle
  exact (min_le_left _ _).trans hle

theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_of_taper
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ} (hgpl : IsPiecewiseAffineOn g univ)
    (hgpos : ∀ y : E, 0 ≤ g y) {a : ℝ} (ha : 0 < a) (haone : a ≤ 1)
    (hseam : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ InjOn f (W ∪ R) ∧
      MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∈ B → x ∈ B ∧ g x = 0) ∧
      EqOn f id R ∧ (∀ y ∈ B, g y = 0 → ∀ t ∈ Icc (0 : ℝ) 1, f (ρ (y, t)) = ρ (y, t)) ∧
      (∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
        f (ρ (y, t)) = ρ (y, s) ∧ t ≤ s ∧ s ≤ t + g y) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ MapsTo f' (W ∪ R) (W ∪ R) ∧ EqOn f' id R ∧
      LeftInvOn f' f (W ∪ R) := by
  classical
  let U := B ×ˢ Icc (0 : ℝ) 1
  let τ := Function.invFunOn ρ U
  have hτ : MapsTo τ W U := hρ.symm.bijOn.mapsTo
  have hleft : LeftInvOn τ ρ U := hρ.bijOn.invOn_invFunOn.1
  have hright : RightInvOn τ ρ W := hρ.bijOn.invOn_invFunOn.2
  have hBW : B ⊆ W := fun x hx =>
    hbottom x hx ▸ hρ.bijOn.mapsTo ⟨hx, le_rfl, zero_le_one⟩
  set H := collarInwardMap g a with hHdef
  set H' := collarOutwardMap g a
  have hHfst : ∀ z : E × ℝ, (H z).1 = z.1 := by
    intro z
    simp only [hHdef, collarInwardMap_fst]
  have hHU : MapsTo H U U := collarInwardMap_mapsTo_prod_Icc g haone B
  have hH'U : MapsTo H' U U := collarOutwardMap_mapsTo_prod_Icc g a B
  set Q : E → E := ρ ∘ H ∘ τ
  set Q' : E → E := ρ ∘ H' ∘ τ
  have hQW : MapsTo Q W W := hρ.bijOn.mapsTo.comp (hHU.comp hτ)
  have hQ'W : MapsTo Q' W W := hρ.bijOn.mapsTo.comp (hH'U.comp hτ)
  have hQpl : IsPiecewiseAffineOn Q W := by
    have hHτ : IsPiecewiseAffineOn (H ∘ τ) W := by
      have hcomp := (isPiecewiseAffineOn_collarInwardMap hgpl a).comp
        hρ.isPiecewiseAffineOn_invFunOn
      simpa only [preimage_univ, inter_univ] using hcomp
    have hcomp := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hHU.comp hτ)
    rwa [hinter] at hcomp
  have hQ'pl : IsPiecewiseAffineOn Q' W := by
    have hHτ : IsPiecewiseAffineOn (H' ∘ τ) W := by
      have hcomp := (isPiecewiseAffineOn_collarOutwardMap hgpl a).comp
        hρ.isPiecewiseAffineOn_invFunOn
      simpa only [preimage_univ, inter_univ] using hcomp
    have hcomp := hρ.isPiecewiseAffineOn.comp hHτ
    have hinter : W ∩ (H' ∘ τ) ⁻¹' U = W := inter_eq_left.mpr (hH'U.comp hτ)
    rwa [hinter] at hcomp
  have hQinj : InjOn Q W := by
    intro x hx y hy hxy
    apply hρ.symm.bijOn.injOn hx hy
    exact collarInwardMap_injective g a
      (hρ.bijOn.injOn (hHU (hτ hx)) (hHU (hτ hy)) hxy)
  have hQzero : ∀ x ∈ W, g (τ x).1 = 0 → Q x = x := by
    intro x hx hg0
    change ρ (collarInwardMap g a (τ x)) = x
    rw [collarInwardMap_eq_self_of_eq_zero a hg0]
    exact hright hx
  have hQ'zero : ∀ x ∈ W, g (τ x).1 = 0 → Q' x = x := by
    intro x hx hg0
    change ρ (collarOutwardMap g a (τ x)) = x
    rw [collarOutwardMap_eq_self_of_eq_zero a hg0 (hτ hx).2.1]
    exact hright hx
  have hQfixed : ∀ x ∈ W, a ≤ (τ x).2 → Q x = x := by
    intro x hx ht
    change ρ (collarInwardMap g a (τ x)) = x
    rw [collarInwardMap_eq_self_of_le g ht]
    exact hright hx
  have hQ'fixed : ∀ x ∈ W, a ≤ (τ x).2 → Q' x = x := by
    intro x hx ht
    change ρ (collarOutwardMap g a (τ x)) = x
    rw [collarOutwardMap_eq_self_of_le g ht (hτ hx).2.1]
    exact hright hx
  have hseamW : ∀ x ∈ W ∩ R, g (τ x).1 = 0 ∨ a ≤ (τ x).2 := by
    intro x hx
    have hz := hτ hx.1
    have hmem : ρ ((τ x).1, (τ x).2) ∈ R := by
      change ρ (τ x) ∈ R
      rw [hright hx.1]
      exact hx.2
    exact hseam _ hz.1 _ hz.2 hmem
  have hQR : EqOn Q id (W ∩ R) := by
    intro x hx
    rcases hseamW x hx with h0 | hle
    · exact hQzero x hx.1 h0
    · exact hQfixed x hx.1 hle
  have hQ'R : EqOn Q' id (W ∩ R) := by
    intro x hx
    rcases hseamW x hx with h0 | hle
    · exact hQ'zero x hx.1 h0
    · exact hQ'fixed x hx.1 hle
  have hQpreR : ∀ x ∈ W, Q x ∈ R → Q x = x := by
    intro x hx hRmem
    have heq : τ (Q x) = H (τ x) := hleft (hHU (hτ hx))
    rcases hseamW (Q x) ⟨hQW hx, hRmem⟩ with h0 | hhigh
    · rw [heq, hHfst (τ x)] at h0
      exact hQzero x hx h0
    · rw [heq] at hhigh
      refine hQfixed x hx ?_
      by_contra hlt
      exact (not_lt_of_ge hhigh) (collarInwardMap_snd_lt_of_lt g (lt_of_not_ge hlt))
  have hQnotB : ∀ x ∈ W, Q x ∈ B → x ∈ B ∧ g x = 0 := by
    intro x hx hmem
    have hz : (H (τ x)).2 = 0 :=
      (hρ.mem_bottom_iff_snd_eq_zero hbottom (hHU (hτ hx))).mp hmem
    obtain ⟨ht, hgz⟩ :=
      (collarInwardMap_snd_eq_zero_iff ha (hgpos (τ x).1) (hτ hx).2.1).mp hz
    have hxB : x ∈ B := by
      rw [← hright hx]
      exact (hρ.mem_bottom_iff_snd_eq_zero hbottom (hτ hx)).mpr ht
    have hx1 : (τ x).1 = x := by
      have h0 := hbottom (τ x).1 (hτ hx).1
      have h1 : ((τ x).1, (0 : ℝ)) = τ x := Prod.ext rfl ht.symm
      rw [h1, hright hx] at h0
      exact h0.symm
    exact ⟨hxB, by rw [← hx1]; exact hgz⟩
  have hQfix0 : ∀ y ∈ B, g y = 0 → ∀ t ∈ Icc (0 : ℝ) 1, Q (ρ (y, t)) = ρ (y, t) := by
    intro y hy hg0 t ht
    have hzU : ((y, t) : E × ℝ) ∈ U := ⟨hy, ht⟩
    refine hQzero (ρ (y, t)) (hρ.bijOn.mapsTo hzU) ?_
    rw [hleft hzU]
    exact hg0
  have hQfiber : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ∃ s ∈ Icc (0 : ℝ) 1,
      Q (ρ (y, t)) = ρ (y, s) ∧ t ≤ s ∧ s ≤ t + g y := by
    intro y hy t ht
    have hzU : (y, t) ∈ U := ⟨hy, ht⟩
    refine ⟨(H (y, t)).2, (hHU hzU).2, ?_, le_collarInwardMap_snd g a (y, t), ?_⟩
    · change ρ (H (τ (ρ (y, t)))) = ρ (y, (H (y, t)).2)
      rw [hleft hzU]
      exact congrArg ρ (Prod.ext (hHfst (y, t)) rfl)
    · change max t (min (t + g y) ((t + a) / 2)) ≤ t + g y
      exact max_le (by linarith [hgpos y]) (min_le_left _ _)
  have hQQ' : ∀ x ∈ W, Q' (Q x) = x := by
    intro x hx
    have heq : τ (Q x) = H (τ x) := hleft (hHU (hτ hx))
    change ρ (collarOutwardMap g a (τ (Q x))) = x
    rw [heq,
      collarOutwardMap_collarInwardMap g a (x := τ x) (hgpos (τ x).1) (hτ hx).2.1]
    exact hright hx
  let f := W.piecewise Q id
  let f' := W.piecewise Q' id
  have hfW : EqOn f Q W := W.piecewise_eqOn Q id
  have hf'W : EqOn f' Q' W := W.piecewise_eqOn Q' id
  have hfR : EqOn f id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hfW hxW]
      exact hQR ⟨hxW, hx⟩
    · exact piecewise_eq_of_notMem W Q id hxW
  have hf'R : EqOn f' id R := by
    intro x hx
    by_cases hxW : x ∈ W
    · rw [hf'W hxW]
      exact hQ'R ⟨hxW, hx⟩
    · exact piecewise_eq_of_notMem W Q' id hxW
  have hfpl : IsPiecewiseAffineOn f (W ∪ R) :=
    hQpl.piecewise_of_isClosed hR.isPLHomeomorphOn_id.isPiecewiseAffineOn
      hW.isClosed hR.isClosed hQR
  have hf'pl : IsPiecewiseAffineOn f' (W ∪ R) :=
    hQ'pl.piecewise_of_isClosed hR.isPLHomeomorphOn_id.isPiecewiseAffineOn
      hW.isClosed hR.isClosed hQ'R
  have hfinj : InjOn f (W ∪ R) := by
    intro x hx y hy hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hfW hx, hfW hy] at hxy
      exact hQinj hx hy hxy
    · rw [hfW hx, hfR hy] at hxy
      exact (hQpreR x hx (hxy.symm ▸ hy)).symm.trans hxy
    · rw [hfR hx, hfW hy] at hxy
      exact hxy.trans (hQpreR y hy (hxy ▸ hx))
    · simpa only [hfR hx, hfR hy, id_eq] using hxy
  have hfmap : MapsTo f (W ∪ R) (W ∪ R) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hfW hx]
      exact Or.inl (hQW hx)
    · rw [hfR hx]
      exact Or.inr hx
  have hf'map : MapsTo f' (W ∪ R) (W ∪ R) := by
    intro x hx
    rcases hx with hx | hx
    · rw [hf'W hx]
      exact Or.inl (hQ'W hx)
    · rw [hf'R hx]
      exact Or.inr hx
  refine ⟨f, f', hfpl, hfinj, hfmap, ?_, hfR, ?_, ?_, hf'pl, hf'map, hf'R, ?_⟩
  · intro x hx hmem
    by_cases hxW : x ∈ W
    · rw [hfW hxW] at hmem
      exact hQnotB x hxW hmem
    · rcases hx with hx | hx
      · exact absurd hx hxW
      · rw [hfR hx] at hmem
        simp only [id_eq] at hmem
        exact absurd (hBW hmem) hxW
  · intro y hy hg0 t ht
    have hxW : ρ (y, t) ∈ W := hρ.bijOn.mapsTo ⟨hy, ht⟩
    rw [hfW hxW]
    exact hQfix0 y hy hg0 t ht
  · intro y hy t ht
    have hxW : ρ (y, t) ∈ W := hρ.bijOn.mapsTo ⟨hy, ht⟩
    obtain ⟨s, hs, hQeq, hts, hsle⟩ := hQfiber y hy t ht
    refine ⟨s, hs, ?_, hts, hsle⟩
    rw [hfW hxW]
    exact hQeq
  · intro x hx
    rcases hx with hx | hx
    · rw [hfW hx, hf'W (hQW hx)]
      exact hQQ' x hx
    · by_cases hxW : x ∈ W
      · rw [hfW hxW, hf'W (hQW hxW)]
        exact hQQ' x hxW
      · have hfix : f x = x := hfR hx
        rw [hfix]
        exact hf'R hx

theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hBc : IsCompact B) (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ}
    (hgpl : IsPiecewiseAffineOn g univ) (hgpos : ∀ y : E, 0 ≤ g y) {a : ℝ} (ha : 0 < a)
    (haone : a ≤ 1) (hseam : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t)
    {Z : Type*} [MetricSpace Z] {h : E → Z} (hh : ContinuousOn h W) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ InjOn f (W ∪ R) ∧
      MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∈ B → x ∈ B ∧ g x = 0) ∧
      EqOn f id R ∧ (∀ y ∈ B, g y = 0 → ∀ t ∈ Icc (0 : ℝ) 1, f (ρ (y, t)) = ρ (y, t)) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ MapsTo f' (W ∪ R) (W ∪ R) ∧ EqOn f' id R ∧
      LeftInvOn f' f (W ∪ R) ∧ ∀ x ∈ W ∪ R, dist (h (f x)) (h x) < ε := by
  classical
  let U := B ×ˢ Icc (0 : ℝ) 1
  have hUc : IsCompact U := hBc.prod isCompact_Icc
  have hhρ : ContinuousOn (fun z => h (ρ z)) U :=
    hh.comp hρ.isPiecewiseAffineOn.continuousOn hρ.bijOn.mapsTo
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hUc.uniformContinuousOn_of_continuous hhρ) ε hε
  have hhalf : (0 : ℝ) < δ / 2 := by linarith
  have hzero : ∀ y : E, min (g y) (δ / 2) = 0 ↔ g y = 0 := by
    intro y
    constructor
    · intro hmin
      rcases min_cases (g y) (δ / 2) with ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at hmin
        exact hmin
      · rw [heq] at hmin
        exact absurd hmin hhalf.ne'
    · intro hgy
      rw [hgy, min_eq_left hhalf.le]
  have hscalepos : ∀ y : E, 0 ≤ min (g y) (δ / 2) := fun y => le_min (hgpos y) hhalf.le
  have hscalepl : IsPiecewiseAffineOn (fun y : E => min (g y) (δ / 2)) univ :=
    hgpl.min (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (δ / 2)) isOpen_univ)
  have hseam' : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R →
      min (g y) (δ / 2) = 0 ∨ a ≤ t := by
    intro y hy t ht hmem
    rcases hseam y hy t ht hmem with h0 | hle
    · exact Or.inl ((hzero y).mpr h0)
    · exact Or.inr hle
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hfR, hfix0, hfiber, hf'pl, hf'map, hf'R, hinv⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn_of_taper hW hR hbottom hscalepl hscalepos
      ha haone hseam'
  refine ⟨f, f', hfpl, hfinj, hfmap, ?_, hfR, ?_, hf'pl, hf'map, hf'R, hinv, ?_⟩
  · intro x hx hmem
    obtain ⟨hxB, hminz⟩ := hfB x hx hmem
    exact ⟨hxB, (hzero x).mp hminz⟩
  · intro y hy hg0 t ht
    exact hfix0 y hy ((hzero y).mpr hg0) t ht
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨z, hzU, rfl⟩ := hρ.bijOn.surjOn hx
      obtain ⟨y, t⟩ := z
      obtain ⟨s, hs, hfeq, hts, hsle⟩ := hfiber y hzU.1 t hzU.2
      have hdist : dist ((y, s) : E × ℝ) (y, t) < δ := by
        rw [Prod.dist_eq]
        refine max_lt (by simpa using hδ) ?_
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]
        calc s - t ≤ min (g y) (δ / 2) := by linarith
          _ ≤ δ / 2 := min_le_right _ _
          _ < δ := by linarith
      rw [hfeq]
      exact hclose (y, s) ⟨hzU.1, hs⟩ (y, t) hzU hdist
    · rw [hfR hx]
      simpa using hε

theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_of_disjoint
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hBR : Disjoint B R) (hBc : IsCompact B) (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {Z : Type*}
    [MetricSpace Z] {h : E → Z} (hh : ContinuousOn h W) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ InjOn f (W ∪ R) ∧
      MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∉ B) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ MapsTo f' (W ∪ R) (W ∪ R) ∧
      LeftInvOn f' f (W ∪ R) ∧ ∀ x ∈ W ∪ R, dist (h (f x)) (h x) < ε := by
  obtain ⟨a, ha, haone, hheight⟩ := hρ.exists_pos_forall_le_of_disjoint hW hR hBR hbottom
  have hgpl : IsPiecewiseAffineOn (fun _ : E => (1 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (1 : ℝ)) isOpen_univ
  have hseam : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → (1 : ℝ) = 0 ∨ a ≤ t :=
    fun y hy t ht hmem => Or.inr (hheight y hy t ht hmem)
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, -, -, hf'pl, hf'map, -, hinv, hdist⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt hW hR hBc hbottom hgpl
      (fun _ => zero_le_one) ha haone hseam hh hε
  refine ⟨f, f', hfpl, hfinj, hfmap, fun x hx hmem => ?_, hf'pl, hf'map, hinv, hdist⟩
  exact one_ne_zero (hfB x hx hmem).2

end Taper

end DifferentialGeometry.Topology.PiecewiseLinear
