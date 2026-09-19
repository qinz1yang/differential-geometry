/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

/-!
# Compactly supported wedge pushes in a slab
-/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

noncomputable section

def slabWedgeCore (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  min p.1 (c - p.1) - |p.2.1| - |p.2.2|

def slabWedgeHat (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  max 0 (slabWedgeCore c p) / 4

def slabWedgeSupport (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Icc 0 c ×ˢ (Icc (-c) c ×ˢ Icc (-c) c)

def wedgeSlab (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ c}

def wedgeSlabInterior (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 < p.1 ∧ p.1 < c}

def wedgeSlabBoundary (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p.1 = 0 ∨ p.1 = c}

def positiveSlabFold (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p ∈ wedgeSlab c ∧
    ((p.2.2 = 0 ∧ 0 ≤ p.2.1) ∨ (p.2.1 = 0 ∧ 0 ≤ p.2.2))}

def negativeSlabFold (c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | p ∈ wedgeSlab c ∧
    ((p.2.2 = 0 ∧ p.2.1 ≤ 0) ∨ (p.2.1 = 0 ∧ p.2.2 ≤ 0))}

def positiveWedgeDisplacement (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (0, slabWedgeHat c p, slabWedgeHat c p)

def negativeWedgeDisplacement (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (0, -slabWedgeHat c p, -slabWedgeHat c p)

def positiveWedgePush (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  p + positiveWedgeDisplacement c p

def negativeWedgePush (c : ℝ) (p : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  p + negativeWedgeDisplacement c p

theorem slabWedgeHat_nonneg (c : ℝ) (p : ℝ × ℝ × ℝ) : 0 ≤ slabWedgeHat c p := by
  rw [slabWedgeHat]
  exact div_nonneg (le_max_left _ _) (by norm_num)

theorem slabWedgeHat_eq_zero_of_left_face {c : ℝ} {p : ℝ × ℝ × ℝ} (hp : p.1 = 0) :
    slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    rw [slabWedgeCore, hp]
    simp only [sub_zero]
    calc
      min 0 c - |p.2.1| - |p.2.2| ≤ min 0 c := by
        nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
      _ ≤ 0 := min_le_left _ _
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

theorem slabWedgeHat_eq_zero_of_right_face {c : ℝ} {p : ℝ × ℝ × ℝ} (hp : p.1 = c) :
    slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    rw [slabWedgeCore, hp]
    simp only [sub_self]
    calc
      min c 0 - |p.2.1| - |p.2.2| ≤ min c 0 := by
        nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
      _ ≤ 0 := min_le_right _ _
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

theorem slabWedgeHat_axis (c x : ℝ) (hx : x ∈ Icc (0 : ℝ) c) :
    slabWedgeHat c (x, 0, 0) = min x (c - x) / 4 := by
  rw [slabWedgeHat, slabWedgeCore]
  simp only [abs_zero, sub_zero]
  rw [max_eq_right]
  exact le_min hx.1 (sub_nonneg.mpr hx.2)

theorem slabWedgeHat_axis_eq_zero_iff {c x : ℝ} (hx : x ∈ Icc (0 : ℝ) c) :
    slabWedgeHat c (x, 0, 0) = 0 ↔ x = 0 ∨ x = c := by
  rw [slabWedgeHat_axis c x hx]
  have hc : 0 ≤ c := hx.1.trans hx.2
  constructor
  · intro h
    have hmin : min x (c - x) = 0 := by linarith
    rcases le_total x (c - x) with hle | hle
    · exact Or.inl (by rwa [min_eq_left hle] at hmin)
    · right
      have : c - x = 0 := by rwa [min_eq_right hle] at hmin
      linarith
  · rintro (rfl | rfl)
    · simp [hc]
    · simp [hc]

theorem slabWedgeHat_pos_on_axis {c x : ℝ} (hx0 : 0 < x) (hxc : x < c) :
    0 < slabWedgeHat c (x, 0, 0) := by
  rw [slabWedgeHat_axis c x ⟨hx0.le, hxc.le⟩]
  exact div_pos (lt_min hx0 (sub_pos.mpr hxc)) (by norm_num)

theorem isCompact_slabWedgeSupport (c : ℝ) : IsCompact (slabWedgeSupport c) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem slabWedgeHat_eq_zero_of_notMem_support {c : ℝ} {p : ℝ × ℝ × ℝ}
    (hp : p ∉ slabWedgeSupport c) : slabWedgeHat c p = 0 := by
  have hcore : slabWedgeCore c p ≤ 0 := by
    by_contra h
    have hpos : 0 < slabWedgeCore c p := lt_of_not_ge h
    have hx0 : 0 ≤ p.1 := by
      by_contra hx
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
    have hxc : p.1 ≤ c := by
      by_contra hx
      have hmin := min_le_right p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1, abs_nonneg p.2.2]
    have hy : |p.2.1| ≤ c := by
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.2]
    have hz : |p.2.2| ≤ c := by
      have hmin := min_le_left p.1 (c - p.1)
      rw [slabWedgeCore] at hpos
      nlinarith [abs_nonneg p.2.1]
    exact hp ⟨⟨hx0, hxc⟩, abs_le.mp hy, abs_le.mp hz⟩
  rw [slabWedgeHat, max_eq_left hcore, zero_div]

theorem slabWedgeHat_eqOn_zero_compl_support (c : ℝ) :
    EqOn (slabWedgeHat c) (fun _ => 0) (slabWedgeSupport c)ᶜ :=
  fun _ hp => slabWedgeHat_eq_zero_of_notMem_support hp

theorem support_slabWedgeHat_subset (c : ℝ) :
    Function.support (slabWedgeHat c) ⊆ slabWedgeSupport c := by
  intro p hp
  by_contra hmem
  exact hp (slabWedgeHat_eq_zero_of_notMem_support hmem)

theorem hasCompactSupport_slabWedgeHat (c : ℝ) : HasCompactSupport (slabWedgeHat c) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_slabWedgeSupport c)
    (support_slabWedgeHat_subset c)

private noncomputable def quarterAffineMap : ℝ →ᵃ[ℝ] ℝ :=
  ((4 : ℝ)⁻¹ • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap

private theorem quarterAffineMap_apply (x : ℝ) : quarterAffineMap x = x / 4 := by
  change (4 : ℝ)⁻¹ • x = x / 4
  simp only [smul_eq_mul]
  ring

theorem isPiecewiseAffineOn_slabWedgeCore (c : ℝ) :
    IsPiecewiseAffineOn (slabWedgeCore c) univ := by
  have hid : IsPiecewiseAffineOn (id : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ) univ :=
    isPiecewiseAffineOn_id isOpen_univ
  have hx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.1) univ :=
    hid.affine_comp (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hy : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.1) univ :=
    hid.affine_comp ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hz : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => p.2.2) univ :=
    hid.affine_comp ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).toAffineMap
  have hconst : ∀ r : ℝ, IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => r) univ := fun r =>
    hid.affine_comp (AffineMap.const ℝ (ℝ × ℝ × ℝ) r)
  have hcx : IsPiecewiseAffineOn (fun p : ℝ × ℝ × ℝ => c - p.1) univ := by
    have h := (hconst c).add (hx.affine_comp (-AffineMap.id ℝ ℝ))
    refine h.congr fun p _ => ?_
    change c - p.1 = c + -p.1
    rw [sub_eq_add_neg]
  have hcore := ((hx.min hcx).add (hy.abs.affine_comp (-AffineMap.id ℝ ℝ))).add
    (hz.abs.affine_comp (-AffineMap.id ℝ ℝ))
  refine hcore.congr fun p _ => ?_
  change slabWedgeCore c p = min p.1 (c - p.1) + -|p.2.1| + -|p.2.2|
  simp only [slabWedgeCore, sub_eq_add_neg]

theorem isPiecewiseAffineOn_slabWedgeHat (c : ℝ) :
    IsPiecewiseAffineOn (slabWedgeHat c) univ := by
  have hconst : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  have h := (hconst.max (isPiecewiseAffineOn_slabWedgeCore c)).affine_comp quarterAffineMap
  refine h.congr fun p _ => ?_
  change slabWedgeHat c p = quarterAffineMap (max 0 (slabWedgeCore c p))
  rw [quarterAffineMap_apply]
  rfl

theorem lipschitzWith_slabWedgeCore (c : ℝ) : LipschitzWith 3 (slabWedgeCore c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hx : |p.1 - q.1| ≤ dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have hy : |p.2.1 - q.2.1| ≤ dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hz : |p.2.2 - q.2.2| ≤ dist p q := by
    simp only [Prod.dist_eq, Real.dist_eq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hmin : |min p.1 (c - p.1) - min q.1 (c - q.1)| ≤ dist p q := by
    calc
      |min p.1 (c - p.1) - min q.1 (c - q.1)| ≤
          max |p.1 - q.1| |(c - p.1) - (c - q.1)| := abs_min_sub_min_le_max _ _ _ _
      _ = |p.1 - q.1| := by
        rw [show (c - p.1) - (c - q.1) = -(p.1 - q.1) by ring, abs_neg, max_self]
      _ ≤ dist p q := hx
  have habsy : abs (|p.2.1| - |q.2.1|) ≤ dist p q :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans hy
  have habsz : abs (|p.2.2| - |q.2.2|) ≤ dist p q :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans hz
  rw [Real.dist_eq]
  change |slabWedgeCore c p - slabWedgeCore c q| ≤ (3 : ℝ) * dist p q
  calc
    |slabWedgeCore c p - slabWedgeCore c q| ≤
        |min p.1 (c - p.1) - min q.1 (c - q.1)| +
          abs (|p.2.1| - |q.2.1|) + abs (|p.2.2| - |q.2.2|) := by
      rw [slabWedgeCore, slabWedgeCore]
      have h₁ := abs_sub (min p.1 (c - p.1) - min q.1 (c - q.1))
        ((|p.2.1| - |q.2.1|) + (|p.2.2| - |q.2.2|))
      have h₂ := abs_add_le (|p.2.1| - |q.2.1|) (|p.2.2| - |q.2.2|)
      rw [show min p.1 (c - p.1) - |p.2.1| - |p.2.2| -
          (min q.1 (c - q.1) - |q.2.1| - |q.2.2|) =
            (min p.1 (c - p.1) - min q.1 (c - q.1)) -
              ((|p.2.1| - |q.2.1|) + (|p.2.2| - |q.2.2|)) by ring]
      linarith
    _ ≤ dist p q + dist p q + dist p q := by linarith
    _ = (3 : ℝ) * dist p q := by ring

theorem lipschitzWith_slabWedgeHat (c : ℝ) : LipschitzWith (3 / 4) (slabWedgeHat c) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hcore := (lipschitzWith_slabWedgeCore c).dist_le_mul p q
  have hmax : |max 0 (slabWedgeCore c p) - max 0 (slabWedgeCore c q)| ≤
      |slabWedgeCore c p - slabWedgeCore c q| := by
    calc
      |max 0 (slabWedgeCore c p) - max 0 (slabWedgeCore c q)| ≤
          max |(0 : ℝ) - 0| |slabWedgeCore c p - slabWedgeCore c q| :=
        abs_max_sub_max_le_max _ _ _ _
      _ = |slabWedgeCore c p - slabWedgeCore c q| := by simp
  rw [Real.dist_eq]
  change |slabWedgeHat c p - slabWedgeHat c q| ≤ ((3 / 4 : NNReal) : ℝ) * dist p q
  rw [show slabWedgeHat c p - slabWedgeHat c q =
      (max 0 (slabWedgeCore c p) - max 0 (slabWedgeCore c q)) / 4 by
        rw [slabWedgeHat, slabWedgeHat]; ring, abs_div]
  rw [Real.dist_eq] at hcore
  norm_num at hcore ⊢
  nlinarith

theorem isPiecewiseAffineOn_positiveWedgeDisplacement (c : ℝ) :
    IsPiecewiseAffineOn (positiveWedgeDisplacement c) univ := by
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  exact (hzero.prod_mk ((isPiecewiseAffineOn_slabWedgeHat c).prod_mk
    (isPiecewiseAffineOn_slabWedgeHat c))).congr fun _ _ => rfl

theorem isPiecewiseAffineOn_negativeWedgeDisplacement (c : ℝ) :
    IsPiecewiseAffineOn (negativeWedgeDisplacement c) univ := by
  have hhat := (isPiecewiseAffineOn_slabWedgeHat c).affine_comp (-AffineMap.id ℝ ℝ)
  have hzero : IsPiecewiseAffineOn (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) univ :=
    isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ℝ × ℝ × ℝ) 0) isOpen_univ
  exact (hzero.prod_mk (hhat.prod_mk hhat)).congr fun _ _ => rfl

theorem lipschitzWith_positiveWedgeDisplacement (c : ℝ) :
    LipschitzWith (3 / 4) (positiveWedgeDisplacement c) := by
  change LipschitzWith (3 / 4) (fun p : ℝ × ℝ × ℝ =>
    (0, slabWedgeHat c p, slabWedgeHat c p))
  have hzero : LipschitzWith 0 (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) := LipschitzWith.const 0
  simpa only [max_self,
    max_eq_right (show (0 : NNReal) ≤ 3 / 4 by positivity)] using
    hzero.prodMk ((lipschitzWith_slabWedgeHat c).prodMk (lipschitzWith_slabWedgeHat c))

theorem lipschitzWith_negativeWedgeDisplacement (c : ℝ) :
    LipschitzWith (3 / 4) (negativeWedgeDisplacement c) := by
  change LipschitzWith (3 / 4) (fun p : ℝ × ℝ × ℝ =>
    (0, -slabWedgeHat c p, -slabWedgeHat c p))
  have hneg : LipschitzWith (3 / 4) (fun p => -slabWedgeHat c p) :=
    (lipschitzWith_slabWedgeHat c).neg
  have hzero : LipschitzWith 0 (fun _ : ℝ × ℝ × ℝ => (0 : ℝ)) := LipschitzWith.const 0
  simpa only [negativeWedgeDisplacement, max_self,
    max_eq_right (show (0 : NNReal) ≤ 3 / 4 by positivity)] using hzero.prodMk (hneg.prodMk hneg)

theorem isPLHomeomorphOn_positiveWedgePush (c : ℝ) :
    IsPLHomeomorphOn (positiveWedgePush c) univ univ := by
  change IsPLHomeomorphOn (fun p => p + positiveWedgeDisplacement c p) univ univ
  exact isPLHomeomorphOn_id_add_of_lipschitz
    (isPiecewiseAffineOn_positiveWedgeDisplacement c)
    (lipschitzWith_positiveWedgeDisplacement c) (by norm_num : (3 / 4 : NNReal) < 1)

theorem isPLHomeomorphOn_negativeWedgePush (c : ℝ) :
    IsPLHomeomorphOn (negativeWedgePush c) univ univ := by
  change IsPLHomeomorphOn (fun p => p + negativeWedgeDisplacement c p) univ univ
  exact isPLHomeomorphOn_id_add_of_lipschitz
    (isPiecewiseAffineOn_negativeWedgeDisplacement c)
    (lipschitzWith_negativeWedgeDisplacement c) (by norm_num : (3 / 4 : NNReal) < 1)

noncomputable def positiveWedgePushHomeomorph (c : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_positiveWedgePush c).homeomorph.trans (Homeomorph.Set.univ _))

noncomputable def negativeWedgePushHomeomorph (c : ℝ) :
    (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
  (Homeomorph.Set.univ _).symm.trans
    ((isPLHomeomorphOn_negativeWedgePush c).homeomorph.trans (Homeomorph.Set.univ _))

@[simp]
theorem positiveWedgePushHomeomorph_apply (c : ℝ) (p : ℝ × ℝ × ℝ) :
    positiveWedgePushHomeomorph c p = positiveWedgePush c p := rfl

@[simp]
theorem negativeWedgePushHomeomorph_apply (c : ℝ) (p : ℝ × ℝ × ℝ) :
    negativeWedgePushHomeomorph c p = negativeWedgePush c p := rfl

theorem eqOn_positiveWedgePush_id_compl_support (c : ℝ) :
    EqOn (positiveWedgePush c) id (slabWedgeSupport c)ᶜ := by
  intro p hp
  rw [positiveWedgePush, positiveWedgeDisplacement,
    slabWedgeHat_eq_zero_of_notMem_support hp]
  simp

theorem eqOn_negativeWedgePush_id_compl_support (c : ℝ) :
    EqOn (negativeWedgePush c) id (slabWedgeSupport c)ᶜ := by
  intro p hp
  rw [negativeWedgePush, negativeWedgeDisplacement,
    slabWedgeHat_eq_zero_of_notMem_support hp]
  simp

theorem eqOn_positiveWedgePush_id_slabBoundary (c : ℝ) :
    EqOn (positiveWedgePush c) id (wedgeSlabBoundary c) := by
  intro p hp
  rcases hp with hp | hp
  · rw [positiveWedgePush, positiveWedgeDisplacement, slabWedgeHat_eq_zero_of_left_face hp]
    simp
  · rw [positiveWedgePush, positiveWedgeDisplacement, slabWedgeHat_eq_zero_of_right_face hp]
    simp

theorem eqOn_negativeWedgePush_id_slabBoundary (c : ℝ) :
    EqOn (negativeWedgePush c) id (wedgeSlabBoundary c) := by
  intro p hp
  rcases hp with hp | hp
  · rw [negativeWedgePush, negativeWedgeDisplacement, slabWedgeHat_eq_zero_of_left_face hp]
    simp
  · rw [negativeWedgePush, negativeWedgeDisplacement, slabWedgeHat_eq_zero_of_right_face hp]
    simp

@[simp]
theorem positiveWedgePush_fst (c : ℝ) (p : ℝ × ℝ × ℝ) :
    (positiveWedgePush c p).1 = p.1 := by
  simp [positiveWedgePush, positiveWedgeDisplacement]

@[simp]
theorem negativeWedgePush_fst (c : ℝ) (p : ℝ × ℝ × ℝ) :
    (negativeWedgePush c p).1 = p.1 := by
  simp [negativeWedgePush, negativeWedgeDisplacement]

theorem mapsTo_positiveWedgePush_wedgeSlab (c : ℝ) :
    MapsTo (positiveWedgePush c) (wedgeSlab c) (wedgeSlab c) :=
  fun _ hp => by
    change 0 ≤ _ ∧ _ ≤ c at hp ⊢
    simpa only [positiveWedgePush_fst] using hp

theorem mapsTo_negativeWedgePush_wedgeSlab (c : ℝ) :
    MapsTo (negativeWedgePush c) (wedgeSlab c) (wedgeSlab c) :=
  fun _ hp => by
    change 0 ≤ _ ∧ _ ≤ c at hp ⊢
    simpa only [negativeWedgePush_fst] using hp

theorem mapsTo_positiveWedgePush_wedgeSlabInterior (c : ℝ) :
    MapsTo (positiveWedgePush c) (wedgeSlabInterior c) (wedgeSlabInterior c) :=
  fun _ hp => by
    change 0 < _ ∧ _ < c at hp ⊢
    simpa only [positiveWedgePush_fst] using hp

theorem mapsTo_negativeWedgePush_wedgeSlabInterior (c : ℝ) :
    MapsTo (negativeWedgePush c) (wedgeSlabInterior c) (wedgeSlabInterior c) :=
  fun _ hp => by
    change 0 < _ ∧ _ < c at hp ⊢
    simpa only [negativeWedgePush_fst] using hp

theorem not_disjoint_image_positive_negative_slabFold_of_fix_left_endpoint {c : ℝ} (hc : 0 ≤ c)
    {f g : (ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ)}
    (hf : f (0, 0, 0) = (0, 0, 0)) (hg : g (0, 0, 0) = (0, 0, 0)) :
    ¬Disjoint (f '' positiveSlabFold c) (g '' negativeSlabFold c) := by
  rw [Set.not_disjoint_iff]
  refine ⟨(0, 0, 0), ⟨0, ?_, hf⟩, ⟨0, ?_, hg⟩⟩
  · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
  · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩

theorem image_positiveSlabFold_inter_image_negativeSlabFold {c : ℝ} (hc : 0 ≤ c) :
    positiveWedgePush c '' positiveSlabFold c ∩ negativeWedgePush c '' negativeSlabFold c =
      {(0, 0, 0), (c, 0, 0)} := by
  ext w
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
    have hpnonneg : 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
      rcases hp.2 with h | h
      · exact ⟨h.2, h.1.symm.le⟩
      · exact ⟨h.1.symm.le, h.2⟩
    have hqnonpos : q.2.1 ≤ 0 ∧ q.2.2 ≤ 0 := by
      rcases hq.2 with h | h
      · exact ⟨h.2, h.1.le⟩
      · exact ⟨h.1.le, h.2⟩
    rcases hpnonneg with ⟨hpy0, hpz0⟩
    rcases hqnonpos with ⟨hqy0, hqz0⟩
    have hpHat := slabWedgeHat_nonneg c p
    have hqHat := slabWedgeHat_nonneg c q
    have hy := congrArg (fun z : ℝ × ℝ × ℝ => z.2.1) hqp
    have hz := congrArg (fun z : ℝ × ℝ × ℝ => z.2.2) hqp
    change q.2.1 - slabWedgeHat c q = p.2.1 + slabWedgeHat c p at hy
    change q.2.2 - slabWedgeHat c q = p.2.2 + slabWedgeHat c p at hz
    have hpy : p.2.1 = 0 := by linarith
    have hpz : p.2.2 = 0 := by linarith
    have hpHat0 : slabWedgeHat c p = 0 := by linarith
    have haxis : slabWedgeHat c (p.1, 0, 0) = 0 := by
      rw [show (p.1, 0, 0) = p by
        exact Prod.ext rfl (Prod.ext hpy.symm hpz.symm)]
      exact hpHat0
    have hx : p.1 = 0 ∨ p.1 = c :=
      (slabWedgeHat_axis_eq_zero_iff hp.1).mp haxis
    rcases hx with hx | hx
    · left
      apply Prod.ext
      · simpa only [positiveWedgePush_fst] using hx
      · apply Prod.ext <;> simp [positiveWedgePush, positiveWedgeDisplacement, hpy, hpz, hpHat0]
    · right
      apply Prod.ext
      · simpa only [positiveWedgePush_fst] using hx
      · apply Prod.ext <;> simp [positiveWedgePush, positiveWedgeDisplacement, hpy, hpz, hpHat0]
  · intro hw
    rcases hw with rfl | hw
    · refine ⟨⟨(0, 0, 0), ?_, ?_⟩, ⟨(0, 0, 0), ?_, ?_⟩⟩
      · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_positiveWedgePush_id_slabBoundary c (Or.inl rfl)]
        rfl
      · exact ⟨⟨le_rfl, hc⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_negativeWedgePush_id_slabBoundary c (Or.inl rfl)]
        rfl
    · have hwc : w = (c, 0, 0) := by simpa using hw
      subst w
      refine ⟨⟨(c, 0, 0), ?_, ?_⟩, ⟨(c, 0, 0), ?_, ?_⟩⟩
      · exact ⟨⟨hc, le_rfl⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_positiveWedgePush_id_slabBoundary c (Or.inr rfl)]
        rfl
      · exact ⟨⟨hc, le_rfl⟩, Or.inl ⟨rfl, le_rfl⟩⟩
      · rw [eqOn_negativeWedgePush_id_slabBoundary c (Or.inr rfl)]
        rfl

theorem disjoint_positive_negative_wedge_push_on_slabInterior {c : ℝ} :
    Disjoint (positiveWedgePush c '' (positiveSlabFold c ∩ wedgeSlabInterior c))
      (negativeWedgePush c '' (negativeSlabFold c ∩ wedgeSlabInterior c)) := by
  rw [Set.disjoint_left]
  rintro w ⟨p, ⟨hp, hpopen⟩, rfl⟩ ⟨q, ⟨hq, hqopen⟩, hqp⟩
  have hw : positiveWedgePush c p ∈
      positiveWedgePush c '' positiveSlabFold c ∩ negativeWedgePush c '' negativeSlabFold c :=
    ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqp⟩⟩
  have hc : 0 ≤ c := le_trans hpopen.1.le hpopen.2.le
  rw [image_positiveSlabFold_inter_image_negativeSlabFold hc] at hw
  rcases hw with hw | hw
  · have := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hw
    simp only [positiveWedgePush_fst] at this
    linarith [hpopen.1]
  · have hw' : positiveWedgePush c p = (c, 0, 0) := by simpa using hw
    have := congrArg (fun z : ℝ × ℝ × ℝ => z.1) hw'
    simp only [positiveWedgePush_fst] at this
    linarith [hpopen.2]

end

end DifferentialGeometry.Topology.PiecewiseLinear
