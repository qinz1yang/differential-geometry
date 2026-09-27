/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.CrosscutExtension
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.Homeomorph.ClosedPasting
import DifferentialGeometry.External.Schoenflies.BoundaryContinuity2

open Set Metric Schoenflies

namespace DifferentialGeometry.Topology.PlanarJordan

def planeRect (a b c d : ℝ) : Set Plane := {x | a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d}

def planeOpenRect (a b c d : ℝ) : Set Plane := {x | a < x 0 ∧ x 0 < b ∧ c < x 1 ∧ x 1 < d}

noncomputable def planeScale (s t : ℝ) (hs : s ≠ 0) (ht : t ≠ 0) : Plane ≃L[ℝ] Plane :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => Plane.mk (s * x 0) (t * x 1)
      invFun := fun y => Plane.mk (y 0 / s) (y 1 / t)
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [mul_add]
      map_smul' := fun r x => by
        ext i
        fin_cases i <;> simp <;> ring
      left_inv := fun x => by
        ext i
        fin_cases i <;> simp [hs, ht]
      right_inv := fun y => by
        ext i
        fin_cases i <;> simp [hs, ht, mul_div_cancel₀] }

theorem planeScale_apply {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (x : Plane) :
    planeScale s t hs ht x = Plane.mk (s * x 0) (t * x 1) := rfl

theorem planeScale_symm_apply {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) (y : Plane) :
    (planeScale s t hs ht).symm y = Plane.mk (y 0 / s) (y 1 / t) := rfl

noncomputable def planeRectMap {a b c d : ℝ} (hab : a < b) (hcd : c < d) : Plane ≃ₜ Plane :=
  (planeScale ((b - a) / 2) ((d - c) / 2) (by linarith) (by linarith)).toHomeomorph.trans
    (Homeomorph.addLeft (Plane.mk ((a + b) / 2) ((c + d) / 2)))

theorem planeRectMap_symm_apply_zero {a b c d : ℝ} (hab : a < b) (hcd : c < d) (y : Plane) :
    (planeRectMap hab hcd).symm y 0 = (y 0 - (a + b) / 2) / ((b - a) / 2) := by
  change ((-(Plane.mk ((a + b) / 2) ((c + d) / 2)) + y) 0) / ((b - a) / 2) = _
  simp
  ring

theorem planeRectMap_symm_apply_one {a b c d : ℝ} (hab : a < b) (hcd : c < d) (y : Plane) :
    (planeRectMap hab hcd).symm y 1 = (y 1 - (c + d) / 2) / ((d - c) / 2) := by
  change ((-(Plane.mk ((a + b) / 2) ((c + d) / 2)) + y) 1) / ((d - c) / 2) = _
  simp
  ring

theorem planeRectMap_image_closedSquare {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    planeRectMap hab hcd '' Plane.closedSquare 0 1 = planeRect a b c d := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simp only [mem_preimage, Plane.closedSquare_eq_inter, mem_inter_iff, mem_ofPred_eq,
    planeRectMap_symm_apply_zero, planeRectMap_symm_apply_one, planeRect,
    PiLp.zero_apply, zero_sub, zero_add]
  have h1 : 0 < (b - a) / 2 := by linarith
  have h2 : 0 < (d - c) / 2 := by linarith
  rw [le_div_iff₀ h1, div_le_iff₀ h1, le_div_iff₀ h2, div_le_iff₀ h2]
  constructor
  · rintro ⟨⟨p1, p2⟩, p3, p4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨p1, p2, p3, p4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem planeRectMap_image_openSquare {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    planeRectMap hab hcd '' Plane.openSquare 0 1 = planeOpenRect a b c d := by
  rw [Homeomorph.image_eq_preimage_symm]
  ext y
  simp only [mem_preimage, Plane.openSquare_eq_inter, mem_inter_iff, mem_ofPred_eq,
    planeRectMap_symm_apply_zero, planeRectMap_symm_apply_one, planeOpenRect,
    PiLp.zero_apply, zero_sub, zero_add]
  have h1 : 0 < (b - a) / 2 := by linarith
  have h2 : 0 < (d - c) / 2 := by linarith
  rw [lt_div_iff₀ h1, div_lt_iff₀ h1, lt_div_iff₀ h2, div_lt_iff₀ h2]
  constructor
  · rintro ⟨⟨p1, p2⟩, p3, p4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨p1, p2, p3, p4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem isCompact_planeRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsCompact (planeRect a b c d) := by
  rw [← planeRectMap_image_closedSquare hab hcd]
  exact (isCompact_closedSquare 0 1).image (planeRectMap hab hcd).continuous

theorem isJordanCurve_frontier_planeRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsJordanCurve (frontier (planeRect a b c d)) := by
  rw [← planeRectMap_image_closedSquare hab hcd, ← Homeomorph.image_frontier]
  exact isJordanCurve_image _ (isJordanCurve_frontier_closedSquare 0 one_pos)

theorem interior_planeRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    interior (planeRect a b c d) = planeOpenRect a b c d := by
  rw [← planeRectMap_image_closedSquare hab hcd, ← Homeomorph.image_interior,
    interior_closedSquare_zero_one, planeRectMap_image_openSquare]

theorem inside_frontier_planeRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    inside (frontier (planeRect a b c d)) = planeOpenRect a b c d := by
  have hne : (interior (planeRect a b c d)).Nonempty := by
    rw [interior_planeRect hab hcd]
    refine ⟨Plane.mk ((a + b) / 2) ((c + d) / 2), ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [← interior_eq_inside_frontier_of_isCompact (isCompact_planeRect hab hcd)
    (isJordanCurve_frontier_planeRect hab hcd) hne, interior_planeRect hab hcd]

theorem isClosed_planeRect (a b c d : ℝ) : IsClosed (planeRect a b c d) := by
  have h0 := Plane.continuous_coord 0
  have h1 := Plane.continuous_coord 1
  exact (isClosed_le continuous_const h0).inter ((isClosed_le h0 continuous_const).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const)))

theorem mem_frontier_planeRect {a b c d : ℝ} (hab : a < b) (hcd : c < d) {x : Plane} :
    x ∈ frontier (planeRect a b c d) ↔
      x ∈ planeRect a b c d ∧ (x 0 = a ∨ x 0 = b ∨ x 1 = c ∨ x 1 = d) := by
  rw [(isClosed_planeRect a b c d).frontier_eq, interior_planeRect hab hcd]
  simp only [mem_sdiff, planeRect, planeOpenRect, mem_ofPred_eq, not_and_or, not_lt]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4⟩, h⟩
    refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl (le_antisymm h h1)
    · exact Or.inr (Or.inl (le_antisymm h2 h))
    · exact Or.inr (Or.inr (Or.inl (le_antisymm h h3)))
    · exact Or.inr (Or.inr (Or.inr (le_antisymm h4 h)))
  · rintro ⟨⟨h1, h2, h3, h4⟩, h⟩
    refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inl h.le
    · exact Or.inr (Or.inl h.ge)
    · exact Or.inr (Or.inr (Or.inl h.le))
    · exact Or.inr (Or.inr (Or.inr h.ge))

theorem mem_segment_horizontal {a b y : ℝ} (hab : a ≤ b) {x : Plane} :
    x ∈ segment ℝ (Plane.mk a y) (Plane.mk b y) ↔ a ≤ x 0 ∧ x 0 ≤ b ∧ x 1 = y := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    obtain rfl : s = 1 - t := by linarith
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    refine ⟨by nlinarith [mul_nonneg ht (sub_nonneg.mpr hab)],
      by nlinarith [mul_nonneg hs (sub_nonneg.mpr hab)], by ring⟩
  · rintro ⟨h1, h2, h3⟩
    rcases eq_or_lt_of_le hab with heq | hlt
    · refine ⟨1, 0, zero_le_one, le_rfl, by ring, ?_⟩
      ext i
      fin_cases i
      · simp
        linarith
      · simp [h3]
    · set t := (x 0 - a) / (b - a) with htdef
      have hba : 0 < b - a := sub_pos.mpr hlt
      refine ⟨1 - t, t, ?_, div_nonneg (by linarith) hba.le, by ring, ?_⟩
      · rw [sub_nonneg, htdef, div_le_one hba]
        linarith
      · ext i
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
            Matrix.cons_val_zero]
          rw [htdef]
          field_simp
          ring
        · simp [h3]
          ring

theorem mem_openSegment_horizontal {a b y : ℝ} (hab : a < b) {x : Plane} :
    x ∈ openSegment ℝ (Plane.mk a y) (Plane.mk b y) ↔ a < x 0 ∧ x 0 < b ∧ x 1 = y := by
  constructor
  · rintro ⟨s, t, hs, ht, hst, rfl⟩
    obtain rfl : s = 1 - t := by linarith
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    refine ⟨by nlinarith [mul_pos ht (sub_pos.mpr hab)],
      by nlinarith [mul_pos hs (sub_pos.mpr hab)], by ring⟩
  · rintro ⟨h1, h2, h3⟩
    set t := (x 0 - a) / (b - a) with htdef
    have hba : 0 < b - a := sub_pos.mpr hab
    refine ⟨1 - t, t, ?_, div_pos (by linarith) hba, by ring, ?_⟩
    · rw [sub_pos, htdef, div_lt_one hba]
      linarith
    · ext i
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
          Matrix.cons_val_zero]
        rw [htdef]
        field_simp
        ring
      · simp [h3]
        ring

theorem mem_segment_vertical {a y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) {x : Plane}
    (hx : x ∈ segment ℝ (Plane.mk a y₁) (Plane.mk a y₂)) :
    x 0 = a ∧ y₁ ≤ x 1 ∧ x 1 ≤ y₂ := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  obtain rfl : s = 1 - t := by linarith
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  refine ⟨by ring, by nlinarith [mul_nonneg ht (sub_nonneg.mpr hy)],
    by nlinarith [mul_nonneg hs (sub_nonneg.mpr hy)]⟩

theorem image_planeRect_eq_closure_inside (h : Plane ≃ₜ Plane) {a b c d : ℝ} (hab : a < b)
    (hcd : c < d) :
    h '' planeRect a b c d = closure (inside (h '' frontier (planeRect a b c d))) := by
  have hne : (interior (planeRect a b c d)).Nonempty := by
    rw [interior_planeRect hab hcd]
    refine ⟨Plane.mk ((a + b) / 2) ((c + d) / 2), ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [← image_inside, ← Homeomorph.image_closure, closure_inside_frontier_eq_of_isCompact
    (isCompact_planeRect hab hcd) (isJordanCurve_frontier_planeRect hab hcd) hne]

theorem exists_homeomorph_eqOn_strip {α β δ W η : ℝ} (hη : 0 < η) (hαβ : α + 4 * η < β)
    (hδ : 0 < δ) (hδW : δ < W) (F : Plane ≃ₜ Plane)
    (hFid : ∀ x ∈ planeRect α β (-δ) δ, (x 0 ≤ α + η ∨ β - η ≤ x 0) → F x = x)
    (hFQ : ∀ x ∈ planeRect α β (-δ) δ, α < x 0 → x 0 < β →
      F x ∈ planeOpenRect α β (-W) W)
    (hFcol : ∀ x ∈ planeRect α β (-δ) δ, α + η < x 0 → x 0 < β - η → α + η / 2 < F x 0) :
    ∃ H : Plane ≃ₜ Plane, EqOn H F (planeRect α β (-δ) δ) ∧
      EqOn H id (planeOpenRect α β (-W) W)ᶜ := by
  classical
  have hab : α < β := by linarith
  have hW : -W < W := by linarith
  have hδ' : -δ < δ := by linarith
  have hWδ : -W < δ := by linarith
  have hQJ := isJordanCurve_frontier_planeRect hab hW
  have hLJ := isJordanCurve_frontier_planeRect hab hWδ
  have hQin := inside_frontier_planeRect hab hW
  have hLin := inside_frontier_planeRect hab hWδ
  set pL : Plane := Plane.mk α δ with hpL
  set pR : Plane := Plane.mk β δ with hpR
  set qL : Plane := Plane.mk α (-δ) with hqL
  set qR : Plane := Plane.mk β (-δ) with hqR
  have hTmem : ∀ x, x ∈ segment ℝ pL pR ↔ α ≤ x 0 ∧ x 0 ≤ β ∧ x 1 = δ :=
    fun _ => mem_segment_horizontal hab.le
  have hBmem : ∀ x, x ∈ segment ℝ qL qR ↔ α ≤ x 0 ∧ x 0 ≤ β ∧ x 1 = -δ :=
    fun _ => mem_segment_horizontal hab.le
  have hTK : ∀ x ∈ segment ℝ pL pR, x ∈ planeRect α β (-δ) δ := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := (hTmem x).mp hx
    exact ⟨h1, h2, by linarith, h3.le⟩
  have hBK : ∀ x ∈ segment ℝ qL qR, x ∈ planeRect α β (-δ) δ := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := (hBmem x).mp hx
    exact ⟨h1, h2, h3.ge, by linarith⟩
  have hpL0 : pL 0 = α := by simp [hpL]
  have hpR0 : pR 0 = β := by simp [hpR]
  have hqL0 : qL 0 = α := by simp [hqL]
  have hqR0 : qR 0 = β := by simp [hqR]
  have hFpL : F pL = pL :=
    hFid pL (hTK pL (left_mem_segment ℝ pL pR)) (Or.inl (by rw [hpL0]; linarith))
  have hFpR : F pR = pR :=
    hFid pR (hTK pR (right_mem_segment ℝ pL pR)) (Or.inr (by rw [hpR0]; linarith))
  have hFqL : F qL = qL :=
    hFid qL (hBK qL (left_mem_segment ℝ qL qR)) (Or.inl (by rw [hqL0]; linarith))
  have hFqR : F qR = qR :=
    hFid qR (hBK qR (right_mem_segment ℝ qL qR)) (Or.inr (by rw [hqR0]; linarith))
  have hpq : pL ≠ pR := fun h => by
    have := congrArg (fun x : Plane => x 0) h
    simp only [hpL0, hpR0] at this
    linarith
  have hqq : qL ≠ qR := fun h => by
    have := congrArg (fun x : Plane => x 0) h
    simp only [hqL0, hqR0] at this
    linarith
  have hT : IsArcBetween (segment ℝ pL pR) pL pR := isArcBetween_segment hpq
  have hB : IsArcBetween (segment ℝ qL qR) qL qR := isArcBetween_segment hqq
  have hFT : IsArcBetween (F '' segment ℝ pL pR) pL pR := by
    have := isArcBetween_image F hT
    rwa [hFpL, hFpR] at this
  have hfrQ : ∀ x : Plane, x ∈ frontier (planeRect α β (-W) W) ↔ x ∈ planeRect α β (-W) W ∧
      (x 0 = α ∨ x 0 = β ∨ x 1 = -W ∨ x 1 = W) := fun _ => mem_frontier_planeRect hab hW
  have hfrL : ∀ x : Plane, x ∈ frontier (planeRect α β (-W) δ) ↔ x ∈ planeRect α β (-W) δ ∧
      (x 0 = α ∨ x 0 = β ∨ x 1 = -W ∨ x 1 = δ) := fun _ => mem_frontier_planeRect hab hWδ
  have hpL1 : pL 1 = δ := by simp [hpL]
  have hpR1 : pR 1 = δ := by simp [hpR]
  have hqL1 : qL 1 = -δ := by simp [hqL]
  have hqR1 : qR 1 = -δ := by simp [hqR]
  have hpLQ : pL ∈ frontier (planeRect α β (-W) W) := by
    rw [hfrQ]
    refine ⟨⟨by rw [hpL0], by rw [hpL0]; linarith, by rw [hpL1]; linarith,
      by rw [hpL1]; linarith⟩, Or.inl hpL0⟩
  have hpRQ : pR ∈ frontier (planeRect α β (-W) W) := by
    rw [hfrQ]
    refine ⟨⟨by rw [hpR0]; linarith, by rw [hpR0], by rw [hpR1]; linarith,
      by rw [hpR1]; linarith⟩, Or.inr (Or.inl hpR0)⟩
  have hqLL : qL ∈ frontier (planeRect α β (-W) δ) := by
    rw [hfrL]
    refine ⟨⟨by rw [hqL0], by rw [hqL0]; linarith, by rw [hqL1]; linarith,
      by rw [hqL1]; linarith⟩, Or.inl hqL0⟩
  have hqRL : qR ∈ frontier (planeRect α β (-W) δ) := by
    rw [hfrL]
    refine ⟨⟨by rw [hqR0]; linarith, by rw [hqR0], by rw [hqR1]; linarith,
      by rw [hqR1]; linarith⟩, Or.inr (Or.inl hqR0)⟩
  have hext : ∀ x y : Plane, x 0 = y 0 → x 1 = y 1 → x = y := by
    intro x y h0 h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
  have hTend : ∀ x ∈ segment ℝ pL pR, x ≠ pL → x ≠ pR → α < x 0 ∧ x 0 < β := by
    intro x hx h1 h2
    obtain ⟨a1, a2, a3⟩ := (hTmem x).mp hx
    refine ⟨lt_of_le_of_ne a1 fun h => h1 (hext _ _ (by rw [hpL0, h]) (by rw [hpL1, a3])),
      lt_of_le_of_ne a2 fun h => h2 (hext _ _ (by rw [hpR0, h]) (by rw [hpR1, a3]))⟩
  have hBend : ∀ x ∈ segment ℝ qL qR, x ≠ qL → x ≠ qR → α < x 0 ∧ x 0 < β := by
    intro x hx h1 h2
    obtain ⟨a1, a2, a3⟩ := (hBmem x).mp hx
    refine ⟨lt_of_le_of_ne a1 fun h => h1 (hext _ _ (by rw [hqL0, h]) (by rw [hqL1, a3])),
      lt_of_le_of_ne a2 fun h => h2 (hext _ _ (by rw [hqR0, h]) (by rw [hqR1, a3]))⟩
  have hTC : segment ℝ pL pR \ {pL, pR} ⊆ inside (frontier (planeRect α β (-W) W)) := by
    rintro x ⟨hx, hne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    obtain ⟨h1, h2⟩ := hTend x hx hne.1 hne.2
    have h3 := ((hTmem x).mp hx).2.2
    rw [hQin]
    exact ⟨h1, h2, by linarith, by linarith⟩
  have hFTC : F '' segment ℝ pL pR \ {pL, pR} ⊆ inside (frontier (planeRect α β (-W) W)) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    have hx1 : x ≠ pL := fun h => hne.1 (by rw [h, hFpL])
    have hx2 : x ≠ pR := fun h => hne.2 (by rw [h, hFpR])
    obtain ⟨h1, h2⟩ := hTend x hx hx1 hx2
    rw [hQin]
    exact hFQ x (hTK x hx) h1 h2
  let f₁ : ArcHomeo (segment ℝ pL pR) (F '' segment ℝ pL pR) pL pR pL pR :=
    { toFun := F
      invFun := F.symm
      continuousOn_toFun := F.continuous.continuousOn
      continuousOn_invFun := F.symm.continuous.continuousOn
      leftInvOn := fun x _ => F.symm_apply_apply x
      rightInvOn := fun y _ => F.apply_symm_apply y
      image_eq := rfl
      map_left := hFpL
      map_right := hFpR }
  obtain ⟨E₁, hE₁T, hE₁fix, -⟩ := exists_homeomorph_extending_crosscut hQJ hT hFT hpLQ hpRQ
    hTC hFTC f₁
  rw [hQin] at hE₁fix
  have hE₁T' : ∀ x ∈ segment ℝ pL pR, E₁ x = F x := fun x hx => hE₁T hx
  have hE₁fr : ∀ x ∈ frontier (planeRect α β (-W) δ), x ∉ segment ℝ pL pR → E₁ x = x ∧
      (x 0 = α ∨ x 0 = β ∨ x 1 = -W) := by
    intro x hx hxT
    obtain ⟨⟨h1, h2, h3, h4⟩, h⟩ := (hfrL x).mp hx
    have hside : x 0 = α ∨ x 0 = β ∨ x 1 = -W := by
      rcases h with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact (hxT ((hTmem x).mpr ⟨h1, h2, h⟩)).elim
    refine ⟨hE₁fix fun hx' => ?_, hside⟩
    obtain ⟨g1, g2, g3, g4⟩ := hx'
    rcases hside with h | h | h
    · linarith
    · linarith
    · linarith
  have hE₁Q : ∀ x ∈ planeRect α β (-W) W, E₁ x ∈ planeRect α β (-W) W := by
    intro x hx
    by_contra hn
    have hy : E₁ (E₁ x) = E₁ x :=
      hE₁fix fun h => hn ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩
    have heq := E₁.injective hy
    rw [heq] at hn
    exact hn hx
  set J := E₁ '' frontier (planeRect α β (-W) δ) with hJdef
  have hJJ : IsJordanCurve J := isJordanCurve_image E₁ hLJ
  have hsep := jordan_curve_theorem hJJ
  have hinJ : inside J = E₁ '' planeOpenRect α β (-W) δ := by
    rw [hJdef, ← image_inside, hLin]
  have hinQ : ∀ x ∈ inside J, x ∈ planeRect α β (-W) W := by
    intro x hx
    rw [hinJ] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact hE₁Q w ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, by linarith [hw.2.2.2]⟩
  have hconn : ∀ S : Set Plane, IsPreconnected S → S ⊆ Jᶜ → (S ∩ inside J).Nonempty →
      S ⊆ inside J := by
    intro S hS hSJ hne
    refine hS.subset_left_of_subset_union hsep.isOpen_inside hsep.isOpen_outside
      disjoint_inside_outside ?_ hne
    rw [inside_union_outside]
    exact hSJ
  have hcoord : ∀ (x y : Plane) (i : Fin 2), |x i - y i| ≤ dist x y := by
    intro x y i
    have := PiLp.dist_apply_le x y i
    rwa [Real.dist_eq] at this
  set z : Plane := Plane.mk (α + η / 4) (-W) with hz
  have hz0 : z 0 = α + η / 4 := by simp [hz]
  have hz1 : z 1 = -W := by simp [hz]
  have hTcl : IsClosed (F '' segment ℝ pL pR) :=
    ((Schoenflies.isCompact_segment pL pR).image F.continuous).isClosed
  have hzT : z ∉ F '' segment ℝ pL pR := by
    rintro ⟨w, hw, hwz⟩
    by_cases h1 : w = pL
    · rw [h1, hFpL] at hwz
      have := congrArg (fun x : Plane => x 1) hwz
      simp only [hpL1, hz1] at this
      linarith
    by_cases h2 : w = pR
    · rw [h2, hFpR] at hwz
      have := congrArg (fun x : Plane => x 1) hwz
      simp only [hpR1, hz1] at this
      linarith
    obtain ⟨a1, a2⟩ := hTend w hw h1 h2
    have := (hFQ w (hTK w hw) a1 a2).2.2.1
    rw [hwz, hz1] at this
    exact lt_irrefl _ this
  obtain ⟨r₀, hr₀, hr₀sub⟩ := Metric.isOpen_iff.mp hTcl.isOpen_compl z hzT
  set r := min r₀ (min (η / 8) (W - δ)) with hrdef
  have hr : 0 < r := lt_min hr₀ (lt_min (by linarith) (by linarith))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrη : r ≤ η / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrW : r ≤ W - δ := (min_le_right _ _).trans (min_le_right _ _)
  have hball0 : ∀ x ∈ ball z r, α < x 0 ∧ x 0 < α + η / 2 := by
    intro x hx
    have h := (hcoord x z 0).trans_lt (mem_ball.mp hx)
    rw [hz0, abs_lt] at h
    constructor <;> linarith [h.1, h.2]
  have hJball : ∀ x ∈ ball z r, x ∈ J → x 1 = -W := by
    rintro x hxb ⟨w, hw, rfl⟩
    by_cases hwT : w ∈ segment ℝ pL pR
    · exact (hr₀sub (ball_subset_ball hrr₀ hxb) ⟨w, hwT, (hE₁T' w hwT).symm⟩).elim
    · obtain ⟨hfix, hside⟩ := hE₁fr w hw hwT
      rw [hfix] at hxb ⊢
      obtain ⟨b1, b2⟩ := hball0 w hxb
      rcases hside with h | h | h
      · linarith
      · linarith
      · exact h
  have hlow : ∀ x ∈ ball z r, x 1 < -W → x ∉ inside J := fun x _ hx hin => by
    have := (hinQ x hin).2.2.1
    linarith
  have hline : ∀ x ∈ ball z r, x 1 = -W → x ∈ J := by
    intro x hxb hx1
    obtain ⟨b1, b2⟩ := hball0 x hxb
    have hxL : x ∈ frontier (planeRect α β (-W) δ) :=
      (hfrL x).mpr ⟨⟨b1.le, by linarith, hx1.ge, by linarith⟩, Or.inr (Or.inr (Or.inl hx1))⟩
    have hxT : x ∉ segment ℝ pL pR := fun h => by
      have := ((hTmem x).mp h).2.2
      linarith
    exact ⟨x, hxL, (hE₁fr x hxL hxT).1⟩
  have hzJ : z ∈ J := hline z (mem_ball_self hr) hz1
  obtain ⟨y, hyb, hyin⟩ : (ball z r ∩ inside J).Nonempty := by
    have hzfr : z ∈ frontier (inside J) := by rw [hsep.frontier_inside]; exact hzJ
    exact mem_closure_iff.mp (frontier_subset_closure hzfr) (ball z r) isOpen_ball
      (mem_ball_self hr)
  have hy1 : -W < y 1 := by
    rcases lt_trichotomy (y 1) (-W) with h | h | h
    · exact (hlow y hyb h hyin).elim
    · exact (hyin.1 (hline y hyb h)).elim
    · exact h
  have hUin : ball z r ∩ {x : Plane | -W < x 1} ⊆ inside J := by
    refine hconn _ ((convex_ball z r).inter (Plane.convex_coord_gt 1 (-W))).isPreconnected
      ?_ ⟨y, ⟨hyb, hy1⟩, hyin⟩
    intro x hx hxJ
    have h1 := hJball x hx.1 hxJ
    have h2 : -W < x 1 := hx.2
    linarith
  set q₃ : Plane := Plane.mk (α + η / 4) (-W + r / 2) with hq₃
  have hq₃0 : q₃ 0 = α + η / 4 := by simp [hq₃]
  have hq₃1 : q₃ 1 = -W + r / 2 := by simp [hq₃]
  have hq₃in : q₃ ∈ inside J := by
    refine hUin ⟨?_, ?_⟩
    · rw [mem_ball, EuclideanSpace.dist_eq, Fin.sum_univ_two, Real.dist_eq, Real.dist_eq,
        hq₃0, hz0, hq₃1, hz1, sub_self, abs_zero]
      rw [show -W + r / 2 - -W = r / 2 by ring, abs_of_pos (by linarith),
        show (0 : ℝ) ^ 2 + (r / 2) ^ 2 = (r / 2) ^ 2 by ring, Real.sqrt_sq (by linarith)]
      linarith
    · change -W < q₃ 1
      rw [hq₃1]
      linarith
  set q' : Plane := Plane.mk (α + η / 4) (-δ) with hq'
  have hq'0 : q' 0 = α + η / 4 := by simp [hq']
  have hq'1 : q' 1 = -δ := by simp [hq']
  have hr2 : -W + r / 2 ≤ -δ := by linarith
  have hSin : segment ℝ q₃ q' ⊆ inside J := by
    refine hconn _ (convex_segment q₃ q').isPreconnected ?_
      ⟨q₃, left_mem_segment ℝ q₃ q', hq₃in⟩
    intro x hx hxJ
    have hx' : x ∈ segment ℝ (Plane.mk (α + η / 4) (-W + r / 2))
        (Plane.mk (α + η / 4) (-δ)) := hx
    obtain ⟨x0, x1a, x1b⟩ := mem_segment_vertical hr2 hx'
    obtain ⟨w, hw, hwx⟩ := hxJ
    by_cases hwT : w ∈ segment ℝ pL pR
    · rw [hE₁T' w hwT] at hwx
      obtain ⟨a1, a2, a3⟩ := (hTmem w).mp hwT
      by_cases hmid : α + η < w 0 ∧ w 0 < β - η
      · have := hFcol w (hTK w hwT) hmid.1 hmid.2
        rw [hwx, x0] at this
        linarith
      · have hFw : F w = w := hFid w (hTK w hwT) (by
          by_contra hc
          push Not at hc
          exact hmid ⟨hc.1, hc.2⟩)
        rw [hFw] at hwx
        rw [← hwx] at x1b
        linarith
    · obtain ⟨hfix, hside⟩ := hE₁fr w hw hwT
      rw [hfix] at hwx
      rw [← hwx] at x0 x1a
      rcases hside with h | h | h
      · linarith
      · linarith
      · linarith
  have hq'in : q' ∈ inside J := hSin (right_mem_segment ℝ q₃ q')
  have hq'B : q' ∈ openSegment ℝ qL qR :=
    (mem_openSegment_horizontal hab).mpr ⟨by rw [hq'0]; linarith, by rw [hq'0]; linarith, hq'1⟩
  have hFq' : F q' = q' := hFid q' ⟨by rw [hq'0]; linarith, by rw [hq'0]; linarith,
    by rw [hq'1], by rw [hq'1]; linarith⟩ (Or.inl (by rw [hq'0]; linarith))
  have hB'J : F '' openSegment ℝ qL qR ⊆ inside J := by
    refine hconn _ ((convex_openSegment qL qR).isPreconnected.image F F.continuous.continuousOn)
      ?_ ⟨q', ⟨q', hq'B, hFq'⟩, hq'in⟩
    rintro _ ⟨x, hx, rfl⟩ ⟨w, hw, hwe⟩
    obtain ⟨a1, a2, a3⟩ := (mem_openSegment_horizontal hab).mp hx
    by_cases hwT : w ∈ segment ℝ pL pR
    · rw [hE₁T' w hwT] at hwe
      have hwx := F.injective hwe
      rw [hwx] at hwT
      have := ((hTmem x).mp hwT).2.2
      linarith
    · obtain ⟨hfix, hside⟩ := hE₁fr w hw hwT
      rw [hfix] at hwe
      have hin := hFQ x (hBK x (openSegment_subset_segment ℝ qL qR hx)) a1 a2
      rw [← hwe] at hin
      rcases hside with h | h | h
      · linarith [hin.1]
      · linarith [hin.2.1]
      · linarith [hin.2.2.1]
  let G : Plane ≃ₜ Plane := F.trans E₁.symm
  have hGapp : ∀ x, G x = E₁.symm (F x) := fun _ => rfl
  have hE₁qL : E₁ qL = qL := hE₁fix fun h => by linarith [h.1, hqL0]
  have hE₁qR : E₁ qR = qR := hE₁fix fun h => by linarith [h.2.1, hqR0]
  have hGqL : G qL = qL := by rw [hGapp, hFqL, E₁.symm_apply_eq, hE₁qL]
  have hGqR : G qR = qR := by rw [hGapp, hFqR, E₁.symm_apply_eq, hE₁qR]
  have hGB : IsArcBetween (G '' segment ℝ qL qR) qL qR := by
    have := isArcBetween_image G hB
    rwa [hGqL, hGqR] at this
  have hBC : segment ℝ qL qR \ {qL, qR} ⊆ inside (frontier (planeRect α β (-W) δ)) := by
    rintro x ⟨hx, hne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    obtain ⟨h1, h2⟩ := hBend x hx hne.1 hne.2
    have h3 := ((hBmem x).mp hx).2.2
    rw [hLin]
    exact ⟨h1, h2, by linarith, by linarith⟩
  have hGBC : G '' segment ℝ qL qR \ {qL, qR} ⊆ inside (frontier (planeRect α β (-W) δ)) := by
    rintro _ ⟨⟨x, hx, rfl⟩, hne⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
    have hx1 : x ≠ qL := fun h => hne.1 (by rw [h, hGqL])
    have hx2 : x ≠ qR := fun h => hne.2 (by rw [h, hGqR])
    obtain ⟨h1, h2⟩ := hBend x hx hx1 hx2
    have hxo : x ∈ openSegment ℝ qL qR :=
      (mem_openSegment_horizontal hab).mpr ⟨h1, h2, ((hBmem x).mp hx).2.2⟩
    have hFxin : F x ∈ inside J := hB'J ⟨x, hxo, rfl⟩
    rw [hinJ] at hFxin
    obtain ⟨w, hw, hwe⟩ := hFxin
    rw [hLin, hGapp, ← hwe, E₁.symm_apply_apply]
    exact hw
  let f₂ : ArcHomeo (segment ℝ qL qR) (G '' segment ℝ qL qR) qL qR qL qR :=
    { toFun := G
      invFun := G.symm
      continuousOn_toFun := G.continuous.continuousOn
      continuousOn_invFun := G.symm.continuous.continuousOn
      leftInvOn := fun x _ => G.symm_apply_apply x
      rightInvOn := fun y _ => G.apply_symm_apply y
      image_eq := rfl
      map_left := hGqL
      map_right := hGqR }
  obtain ⟨D₀, hD₀B, hD₀fix, -⟩ := exists_homeomorph_extending_crosscut hLJ hB hGB hqLL hqRL
    hBC hGBC f₂
  rw [hLin] at hD₀fix
  have hfront : EqOn G D₀ (frontier (planeRect α β (-δ) δ)) := by
    intro x hx
    obtain ⟨⟨h1, h2, h3, h4⟩, h⟩ := (mem_frontier_planeRect hab hδ').mp hx
    rcases h with h | h | h | h
    · have hFx := hFid x ⟨h1, h2, h3, h4⟩ (Or.inl (by rw [h]; linarith))
      have hEx : E₁ x = x := hE₁fix fun hh => by linarith [hh.1]
      have hDx : D₀ x = x := hD₀fix fun hh => by linarith [hh.1]
      rw [hGapp, hFx, hDx, E₁.symm_apply_eq, hEx]
    · have hFx := hFid x ⟨h1, h2, h3, h4⟩ (Or.inr (by rw [h]; linarith))
      have hEx : E₁ x = x := hE₁fix fun hh => by linarith [hh.2.1]
      have hDx : D₀ x = x := hD₀fix fun hh => by linarith [hh.2.1]
      rw [hGapp, hFx, hDx, E₁.symm_apply_eq, hEx]
    · exact (hD₀B ((hBmem x).mpr ⟨h1, h2, h⟩)).symm
    · have hxT := (hTmem x).mpr ⟨h1, h2, h⟩
      have hDx : D₀ x = x := hD₀fix fun hh => by linarith [hh.2.2.2]
      rw [hGapp, hDx, E₁.symm_apply_eq, hE₁T' x hxT]
  have himage : G '' planeRect α β (-δ) δ = D₀ '' planeRect α β (-δ) δ := by
    rw [image_planeRect_eq_closure_inside G hab hδ', image_planeRect_eq_closure_inside D₀ hab hδ',
      hfront.image_eq]
  obtain ⟨D, hDG, hDD₀⟩ :=
    Homeomorph.exists_pasting_of_image_eq G D₀ (isClosed_planeRect α β (-δ) δ) himage hfront
  refine ⟨D.trans E₁, fun x hx => ?_, fun x hx => ?_⟩
  · change E₁ (D x) = F x
    rw [hDG hx, hGapp, E₁.apply_symm_apply]
  · change E₁ (D x) = x
    have hxK : x ∉ interior (planeRect α β (-δ) δ) := by
      rw [interior_planeRect hab hδ']
      intro hh
      exact hx ⟨hh.1, hh.2.1, by linarith [hh.2.2.1], by linarith [hh.2.2.2]⟩
    have hxL : x ∉ planeOpenRect α β (-W) δ := fun hh =>
      hx ⟨hh.1, hh.2.1, hh.2.2.1, by linarith [hh.2.2.2]⟩
    rw [hDD₀ hxK, hD₀fix hxL]
    exact hE₁fix hx

end DifferentialGeometry.Topology.PlanarJordan
