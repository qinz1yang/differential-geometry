/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Deformation

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.AxisGeometry

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary
open HyperbolicConvexity AsymptoticRays ElementaryGroups BoundaryStabilizer
open FixedLocusGeometry LorentzExtremal

variable {n : ℕ}

def axisPlane (ξ η : BoundaryH n) : Submodule ℝ (LorVec n) :=
  Submodule.span ℝ {ξ.val, η.val}

def axis (ξ η : BoundaryH n) : Set (HUpper n) :=
  {x | x.val ∈ axisPlane ξ η}

theorem left_mem_axisPlane (ξ η : BoundaryH n) : ξ.val ∈ axisPlane ξ η :=
  Submodule.subset_span (by simp)

theorem right_mem_axisPlane (ξ η : BoundaryH n) : η.val ∈ axisPlane ξ η :=
  Submodule.subset_span (by simp)

theorem axisPlane_comm (ξ η : BoundaryH n) : axisPlane ξ η = axisPlane η ξ := by
  simp only [axisPlane, pair_comm]

theorem axis_comm (ξ η : BoundaryH n) : axis ξ η = axis η ξ := by
  simp only [axis, axisPlane_comm ξ η]

theorem boundaryPairPoint_mem_axis (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    boundaryPairPoint ξ η hne ∈ axis ξ η :=
  (axisPlane ξ η).smul_mem _
    ((axisPlane ξ η).add_mem (left_mem_axisPlane ξ η) (right_mem_axisPlane ξ η))

theorem orthogonal_axisPlane {ξ η : BoundaryH n} {v : LorVec n}
    (hξ : lorB v ξ.val = 0) (hη : lorB v η.val = 0) :
    ∀ w ∈ axisPlane ξ η, lorB v w = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem z hz =>
    rcases hz with hz | hz
    · simpa only [hz] using hξ
    · simpa only [Set.mem_singleton_iff.mp hz] using hη
  | zero => simp only [lorB, sdot, tc, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero]
  | add a b _ _ ha hb => rw [lorB_add_right, ha, hb, add_zero]
  | smul c a _ ha => rw [lorB_smul_right, ha, mul_zero]

def planeProject (ξ η : BoundaryH n) (v : LorVec n) : LorVec n :=
  (lorB v η.val / lorB ξ.val η.val) • ξ.val +
    (lorB v ξ.val / lorB ξ.val η.val) • η.val

theorem planeProject_mem (ξ η : BoundaryH n) (v : LorVec n) :
    planeProject ξ η v ∈ axisPlane ξ η :=
  (axisPlane ξ η).add_mem
    ((axisPlane ξ η).smul_mem _ (left_mem_axisPlane ξ η))
    ((axisPlane ξ η).smul_mem _ (right_mem_axisPlane ξ η))

theorem planeProject_pair_left (ξ η : BoundaryH n) (hne : ξ ≠ η) (v : LorVec n) :
    lorB (planeProject ξ η v) ξ.val = lorB v ξ.val := by
  have hb : lorB ξ.val η.val ≠ 0 := (lorB_boundary_neg_of_ne hne).ne
  simp only [planeProject, lorB_add_left, lorB_smul_left, ξ.is_null,
    lorB_comm η.val ξ.val, mul_zero, zero_add]
  exact div_mul_cancel₀ _ hb

theorem planeProject_pair_right (ξ η : BoundaryH n) (hne : ξ ≠ η) (v : LorVec n) :
    lorB (planeProject ξ η v) η.val = lorB v η.val := by
  have hb : lorB ξ.val η.val ≠ 0 := (lorB_boundary_neg_of_ne hne).ne
  simp only [planeProject, lorB_add_left, lorB_smul_left, η.is_null,
    mul_zero, add_zero]
  exact div_mul_cancel₀ _ hb

theorem normal_orthogonal (ξ η : BoundaryH n) (hne : ξ ≠ η) (v : LorVec n) :
    ∀ w ∈ axisPlane ξ η, lorB (v - planeProject ξ η v) w = 0 := by
  apply orthogonal_axisPlane
  · rw [lorB_sub_left, planeProject_pair_left ξ η hne, sub_self]
  · rw [lorB_sub_left, planeProject_pair_right ξ η hne, sub_self]

theorem planeProject_future (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    0 < tc (planeProject ξ η x.val) := by
  have hb := lorB_boundary_neg_of_ne hne
  have hξ := Busemann.lorB_upper_boundary_neg x ξ
  have hη := Busemann.lorB_upper_boundary_neg x η
  rw [planeProject, tc_add, tc_smul, tc_smul, ξ.tc_eq, η.tc_eq, mul_one, mul_one]
  exact add_pos (div_pos_of_neg_of_neg hη hb) (div_pos_of_neg_of_neg hξ hb)

theorem normal_norm_eq (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    lorB (x.val - planeProject ξ η x.val) (x.val - planeProject ξ η x.val) =
      -lorB (planeProject ξ η x.val) (planeProject ξ η x.val) - 1 := by
  have horth := normal_orthogonal ξ η hne x.val _ (planeProject_mem ξ η x.val)
  rw [lorB_sub_left] at horth
  rw [lorB_sub_left, lorB_sub_right, lorB_sub_right,
    lorB_comm (planeProject ξ η x.val) x.val, x.is_unit]
  linarith

theorem one_le_neg_planeProject_norm (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (x : HUpper n) :
    1 ≤ -lorB (planeProject ξ η x.val) (planeProject ξ η x.val) := by
  have horth := normal_orthogonal ξ η hne x.val _
    (boundaryPairPoint_mem_axis ξ η hne)
  have hpos := lorB_self_nonneg_of_orth (boundaryPairPoint ξ η hne).is_unit horth
  rw [normal_norm_eq ξ η hne x] at hpos
  linarith

def axisRadius (ξ η : BoundaryH n) (x : HUpper n) : ℝ :=
  Real.sqrt (-lorB (planeProject ξ η x.val) (planeProject ξ η x.val))

theorem one_le_axisRadius (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    1 ≤ axisRadius ξ η x := by
  have h := Real.sqrt_le_sqrt (one_le_neg_planeProject_norm ξ η hne x)
  simpa only [Real.sqrt_one, axisRadius] using h

theorem axisRadius_pos (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    0 < axisRadius ξ η x := zero_lt_one.trans_le (one_le_axisRadius ξ η hne x)

theorem axisRadius_sq (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    axisRadius ξ η x ^ 2 =
      -lorB (planeProject ξ η x.val) (planeProject ξ η x.val) :=
  Real.sq_sqrt (zero_le_one.trans (one_le_neg_planeProject_norm ξ η hne x))

def axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) : HUpper n where
  val := (axisRadius ξ η x)⁻¹ • planeProject ξ η x.val
  is_unit := by
    rw [lorB_smul_left, lorB_smul_right,
      show lorB (planeProject ξ η x.val) (planeProject ξ η x.val) =
        -(axisRadius ξ η x ^ 2) by linarith [axisRadius_sq ξ η hne x]]
    field_simp [(axisRadius_pos ξ η hne x).ne']
  future := by
    rw [tc_smul]
    exact mul_pos (inv_pos.mpr (axisRadius_pos ξ η hne x)) (planeProject_future ξ η hne x)

theorem axisFoot_mem (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    axisFoot ξ η hne x ∈ axis ξ η :=
  (axisPlane ξ η).smul_mem _ (planeProject_mem ξ η x.val)

theorem cosh_dist_axis (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (x a : HUpper n) (ha : a ∈ axis ξ η) :
    Real.cosh (dist x a) =
      axisRadius ξ η x * Real.cosh (dist (axisFoot ξ η hne x) a) := by
  have horth := normal_orthogonal ξ η hne x.val a.val ha
  rw [lorB_sub_left] at horth
  rw [cosh_dist, cosh_dist]
  change -lorB x.val a.val =
    axisRadius ξ η x * -lorB ((axisRadius ξ η x)⁻¹ • planeProject ξ η x.val) a.val
  rw [lorB_smul_left]
  field_simp [(axisRadius_pos ξ η hne x).ne']
  linarith

theorem cosh_dist_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) (x : HUpper n) :
    Real.cosh (dist x (axisFoot ξ η hne x)) = axisRadius ξ η x := by
  simpa only [dist_self, Real.cosh_zero, mul_one] using
    cosh_dist_axis ξ η hne x _ (axisFoot_mem ξ η hne x)

theorem dist_axisFoot_le (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (x a : HUpper n) (ha : a ∈ axis ξ η) :
    dist x (axisFoot ξ η hne x) ≤ dist x a := by
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_dist_axisFoot, cosh_dist_axis ξ η hne x a ha]
  exact le_mul_of_one_le_right (axisRadius_pos ξ η hne x).le (Real.one_le_cosh _)

theorem eq_axisFoot_of_dist_le (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (x a : HUpper n) (ha : a ∈ axis ξ η)
    (hd : dist x a ≤ dist x (axisFoot ξ η hne x)) :
    a = axisFoot ξ η hne x := by
  have hcosh := Real.cosh_strictMonoOn.monotoneOn dist_nonneg dist_nonneg hd
  rw [cosh_dist_axis ξ η hne x a ha, cosh_dist_axisFoot] at hcosh
  have hle : Real.cosh (dist (axisFoot ξ η hne x) a) ≤ 1 := by
    nlinarith [axisRadius_pos ξ η hne x]
  have hdist : dist (axisFoot ξ η hne x) a ≤ 0 :=
    (Real.cosh_strictMonoOn.le_iff_le dist_nonneg (by norm_num : (0 : ℝ) ∈ Ici 0)).mp
      (by simpa only [Real.cosh_zero] using hle)
  exact (dist_eq_zero.mp (le_antisymm hdist dist_nonneg)).symm

theorem axisFoot_eq_self (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {x : HUpper n} (hx : x ∈ axis ξ η) : axisFoot ξ η hne x = x :=
  (eq_axisFoot_of_dist_le ξ η hne x x hx (by rw [dist_self]; exact dist_nonneg)).symm

theorem continuous_planeProject (ξ η : BoundaryH n) :
    Continuous (planeProject ξ η) := by
  have hξ : Continuous (fun v : LorVec n => lorB v ξ.val) := by
    exact (HyperbolicGeometry.continuous_neg_lorB_right ξ.val).neg.congr
      (fun v => neg_neg (lorB v ξ.val))
  have hη : Continuous (fun v : LorVec n => lorB v η.val) := by
    exact (HyperbolicGeometry.continuous_neg_lorB_right η.val).neg.congr
      (fun v => neg_neg (lorB v η.val))
  exact ((hη.div_const _).smul continuous_const).add
    ((hξ.div_const _).smul continuous_const)

theorem continuous_axisRadius (ξ η : BoundaryH n) : Continuous (axisRadius ξ η) :=
  Real.continuous_sqrt.comp
    ((HyperbolicGeometry.continuous_lorB_self.comp
      ((continuous_planeProject ξ η).comp continuous_val)).neg)

theorem continuous_axisFoot (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    Continuous (axisFoot ξ η hne) := by
  apply StratumDeformation.continuous_of_val
  exact ((continuous_axisRadius ξ η).inv₀ (fun x => (axisRadius_pos ξ η hne x).ne')).smul
    ((continuous_planeProject ξ η).comp continuous_val)

theorem isClosed_axis (ξ η : BoundaryH n) : IsClosed (axis ξ η) :=
  (axisPlane ξ η).closed_of_finiteDimensional.preimage continuous_val

theorem planeProject_eq_radius_smul_foot (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (x : HUpper n) :
    planeProject ξ η x.val = axisRadius ξ η x • (axisFoot ξ η hne x).val := by
  change _ = axisRadius ξ η x • ((axisRadius ξ η x)⁻¹ • planeProject ξ η x.val)
  rw [smul_smul, mul_inv_cancel₀ (axisRadius_pos ξ η hne x).ne', one_smul]

theorem cosh_dist_decomposition (ξ η : BoundaryH n) (hne : ξ ≠ η) (x y : HUpper n) :
    Real.cosh (dist x y) =
      axisRadius ξ η x * axisRadius ξ η y *
        Real.cosh (dist (axisFoot ξ η hne x) (axisFoot ξ η hne y)) -
      lorB (x.val - planeProject ξ η x.val) (y.val - planeProject ξ η y.val) := by
  have hx := normal_orthogonal ξ η hne x.val _ (planeProject_mem ξ η y.val)
  have hy := normal_orthogonal ξ η hne y.val _ (planeProject_mem ξ η x.val)
  rw [lorB_sub_left] at hx hy
  rw [lorB_comm y.val (planeProject ξ η x.val),
    lorB_comm (planeProject ξ η y.val) (planeProject ξ η x.val)] at hy
  have he : lorB (planeProject ξ η x.val) (planeProject ξ η y.val) =
      axisRadius ξ η x * axisRadius ξ η y *
        lorB (axisFoot ξ η hne x).val (axisFoot ξ η hne y).val := by
    rw [planeProject_eq_radius_smul_foot ξ η hne x,
      planeProject_eq_radius_smul_foot ξ η hne y, lorB_smul_left, lorB_smul_right, mul_assoc]
  rw [cosh_dist, cosh_dist, lorB_sub_left, lorB_sub_right, lorB_sub_right]
  nlinarith [he]

theorem normal_pair_le (ξ η : BoundaryH n) (hne : ξ ≠ η) (x y : HUpper n) :
    lorB (x.val - planeProject ξ η x.val) (y.val - planeProject ξ η y.val) ≤
      axisRadius ξ η x * axisRadius ξ η y - 1 := by
  have hx := normal_orthogonal ξ η hne x.val _ (boundaryPairPoint_mem_axis ξ η hne)
  have hy := normal_orthogonal ξ η hne y.val _ (boundaryPairPoint_mem_axis ξ η hne)
  have hcs := lorB_sq_le_of_orth (boundaryPairPoint ξ η hne).is_unit hx hy
  rw [normal_norm_eq ξ η hne x, normal_norm_eq ξ η hne y,
    ← axisRadius_sq ξ η hne x, ← axisRadius_sq ξ η hne y] at hcs
  have hR := one_le_axisRadius ξ η hne x
  have hS := one_le_axisRadius ξ η hne y
  have hprod : 1 ≤ axisRadius ξ η x * axisRadius ξ η y := by nlinarith
  have hsq : (axisRadius ξ η x ^ 2 - 1) * (axisRadius ξ η y ^ 2 - 1) ≤
      (axisRadius ξ η x * axisRadius ξ η y - 1) ^ 2 := by
    nlinarith [sq_nonneg (axisRadius ξ η x - axisRadius ξ η y)]
  nlinarith

theorem dist_axisFoot_le_dist (ξ η : BoundaryH n) (hne : ξ ≠ η) (x y : HUpper n) :
    dist (axisFoot ξ η hne x) (axisFoot ξ η hne y) ≤ dist x y := by
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  rw [cosh_dist_decomposition ξ η hne x y]
  have hnormal := normal_pair_le ξ η hne x y
  have hR := one_le_axisRadius ξ η hne x
  have hS := one_le_axisRadius ξ η hne y
  have hprod : 0 ≤ axisRadius ξ η x * axisRadius ξ η y - 1 := by nlinarith
  have hcosh : 0 ≤ Real.cosh (dist (axisFoot ξ η hne x) (axisFoot ξ η hne y)) - 1 :=
    sub_nonneg.mpr (Real.one_le_cosh _)
  nlinarith [mul_nonneg hprod hcosh]

theorem boundary_pair_cases (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) :
    ((poBoundaryMulAction hn).smul g ξ = ξ ∧ (poBoundaryMulAction hn).smul g η = η) ∨
    ((poBoundaryMulAction hn).smul g ξ = η ∧ (poBoundaryMulAction hn).smul g η = ξ) := by
  let := poBoundaryMulAction hn
  have hinj : g • ξ ≠ g • η := fun h => hne ((MulAction.toPerm g).injective h)
  rcases hpair with ⟨hξ | hξ, hη | hη⟩
  · exact (hinj (hξ.trans hη.symm)).elim
  · exact Or.inl ⟨hξ, hη⟩
  · exact Or.inr ⟨hξ, hη⟩
  · exact (hinj (hξ.trans hη.symm)).elim

theorem boundary_pair_inv (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) :
    (poBoundaryMulAction hn).smul g⁻¹ ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g⁻¹ η ∈ ({ξ, η} : Set (BoundaryH n)) := by
  let := poBoundaryMulAction hn
  rcases boundary_pair_cases hn g ξ η hne hpair with ⟨hξ, hη⟩ | ⟨hξ, hη⟩
  · exact ⟨Or.inl (boundary_inv_fixed hn g ξ hξ), Or.inr (boundary_inv_fixed hn g η hη)⟩
  · have hξ' : g⁻¹ • ξ = η := by
      change g • η = ξ at hη
      rw [← hη, inv_smul_smul]
    have hη' : g⁻¹ • η = ξ := by
      change g • ξ = η at hξ
      rw [← hξ, inv_smul_smul]
    exact ⟨Or.inr hξ', Or.inl hη'⟩

theorem smul_mem_axis (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    {x : HUpper n} (hx : x ∈ axis ξ η) :
    (poMulAction hn).smul g x ∈ axis ξ η := by
  let := poBoundaryMulAction hn
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center (LorGrp n)) g
  have hb (ζ : BoundaryH n)
      (hζ : (poBoundaryMulAction hn).smul (QuotientGroup.mk' _ A) ζ ∈
        ({ξ, η} : Set (BoundaryH n))) :
      matOf A *ᵥ ζ.val ∈ axisPlane ξ η := by
    have hvec : matOf A *ᵥ ζ.val = tc (matOf A *ᵥ ζ.val) • (A • ζ).val := by
      change _ = tc (matOf A *ᵥ ζ.val) • ((tc (matOf A *ᵥ ζ.val))⁻¹ • (matOf A *ᵥ ζ.val))
      rw [smul_smul, mul_inv_cancel₀ (tc_matOf_mulVec_ne_zero A ζ), one_smul]
    change A • ζ ∈ ({ξ, η} : Set (BoundaryH n)) at hζ
    rw [hvec]
    apply (axisPlane ξ η).smul_mem
    rcases hζ with hζ | hζ
    · rw [hζ]; exact left_mem_axisPlane ξ η
    · rw [hζ]; exact right_mem_axisPlane ξ η
  have hlift : ∀ v ∈ axisPlane ξ η, matOf A *ᵥ v ∈ axisPlane ξ η := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with hv | hv
      · rw [hv]; exact hb ξ hpair.1
      · rw [Set.mem_singleton_iff.mp hv]; exact hb η hpair.2
    | zero => rw [Matrix.mulVec_zero]; exact (axisPlane ξ η).zero_mem
    | add v w _ _ hv hw =>
      rw [Matrix.mulVec_add]; exact (axisPlane ξ η).add_mem hv hw
    | smul c v _ hv =>
      rw [Matrix.mulVec_smul]; exact (axisPlane ξ η).smul_mem c hv
  change upperize (matOf A *ᵥ x.val) ∈ axisPlane ξ η
  unfold upperize
  split_ifs
  · exact hlift x.val hx
  · exact (axisPlane ξ η).neg_mem (hlift x.val hx)

theorem image_axis (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) :
    (fun x : HUpper n => (poMulAction hn).smul g x) '' axis ξ η = axis ξ η := by
  let := poMulAction hn
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact smul_mem_axis hn g ξ η hpair hx
  · intro x hx
    exact ⟨g⁻¹ • x, smul_mem_axis hn g⁻¹ ξ η (boundary_pair_inv hn g ξ η hne hpair) hx,
      smul_inv_smul g x⟩

theorem axisFoot_smul (hn : 1 ≤ n) (g : PO n 1) (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (x : HUpper n) :
    axisFoot ξ η hne ((poMulAction hn).smul g x) =
      (poMulAction hn).smul g (axisFoot ξ η hne x) := by
  let := poMulAction hn
  apply Eq.symm
  apply eq_axisFoot_of_dist_le ξ η hne (g • x) (g • axisFoot ξ η hne x)
    (smul_mem_axis hn g ξ η hpair (axisFoot_mem ξ η hne x))
  have h := dist_axisFoot_le ξ η hne x (g⁻¹ • axisFoot ξ η hne (g • x))
    (smul_mem_axis hn g⁻¹ ξ η (boundary_pair_inv hn g ξ η hne hpair)
      (axisFoot_mem ξ η hne (g • x)))
  rw [po_dist_smul hn]
  calc
    dist x (axisFoot ξ η hne x) ≤ dist x (g⁻¹ • axisFoot ξ η hne (g • x)) := h
    _ = dist (g • x) (axisFoot ξ η hne (g • x)) := by
      rw [← po_dist_smul hn g, smul_inv_smul]

theorem displacement_axisFoot_le (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n))) (x : HUpper n) :
    dist ((poMulAction hn).smul g (axisFoot ξ η hne x)) (axisFoot ξ η hne x) ≤
      dist ((poMulAction hn).smul g x) x := by
  rw [← axisFoot_smul hn g ξ η hne hpair x]
  exact dist_axisFoot_le_dist ξ η hne _ x

theorem rayTo_mem_axis (ξ η : BoundaryH n) (hne : ξ ≠ η) (t : ℝ) :
    rayTo (boundaryPairPoint ξ η hne) ξ t ∈ axis ξ η := by
  change (rayTo (boundaryPairPoint ξ η hne) ξ t).val ∈ axisPlane ξ η
  rw [rayTo_boundaryPairPoint_val]
  exact (axisPlane ξ η).smul_mem _
    ((axisPlane ξ η).add_mem
      ((axisPlane ξ η).smul_mem _ (left_mem_axisPlane ξ η))
      ((axisPlane ξ η).smul_mem _ (right_mem_axisPlane ξ η)))

theorem planeProject_eq_self (ξ η : BoundaryH n) (hne : ξ ≠ η)
    {x : HUpper n} (hx : x ∈ axis ξ η) : planeProject ξ η x.val = x.val := by
  have hf := axisFoot_eq_self ξ η hne hx
  have hR : axisRadius ξ η x = 1 := by
    rw [← cosh_dist_axisFoot ξ η hne x, hf, dist_self, Real.cosh_zero]
  rw [planeProject_eq_radius_smul_foot ξ η hne x, hf, hR, one_smul]

theorem axis_eq_range_rayTo (ξ η : BoundaryH n) (hne : ξ ≠ η) :
    axis ξ η = range (rayTo (boundaryPairPoint ξ η hne) ξ) := by
  apply Subset.antisymm
  · intro x hx
    let b := lorB ξ.val η.val
    let a := lorB x.val η.val / b
    let c := lorB x.val ξ.val / b
    let s := Real.sqrt (-2 * b)
    have hb : b < 0 := lorB_boundary_neg_of_ne hne
    have ha : 0 < a := div_pos_of_neg_of_neg (Busemann.lorB_upper_boundary_neg x η) hb
    have hc : 0 < c := div_pos_of_neg_of_neg (Busemann.lorB_upper_boundary_neg x ξ) hb
    have hs : 0 < s := Real.sqrt_pos.mpr (by dsimp [b] at *; linarith)
    have hs2 : s ^ 2 = -2 * b := Real.sq_sqrt (by linarith)
    have hxval : x.val = a • ξ.val + c • η.val := (planeProject_eq_self ξ η hne hx).symm
    have hunit := x.is_unit
    rw [hxval] at hunit
    simp only [lorB_add_left, lorB_add_right, lorB_smul_left, lorB_smul_right,
      ξ.is_null, η.is_null, lorB_comm η.val ξ.val] at hunit
    have hac : (a * s) * (c * s) = 1 := by
      change a * (a * 0 + c * b) + c * (a * b + c * 0) = -1 at hunit
      nlinarith
    have hexp : Real.exp (Real.log (a * s)) = a * s := Real.exp_log (mul_pos ha hs)
    have hexpn : Real.exp (-Real.log (a * s)) = c * s := by
      rw [Real.exp_neg, hexp]
      exact inv_eq_of_mul_eq_one_left (by simpa only [mul_comm] using hac)
    refine ⟨Real.log (a * s), HUpper.ext ?_⟩
    rw [rayTo_boundaryPairPoint_val, hexp, hexpn]
    change s⁻¹ • ((a * s) • ξ.val + (c * s) • η.val) = x.val
    rw [hxval, smul_add, smul_smul, smul_smul]
    have hsa : s⁻¹ * (a * s) = a := by field_simp
    have hsc : s⁻¹ * (c * s) = c := by field_simp
    rw [hsa, hsc]
  · rintro _ ⟨t, rfl⟩
    exact rayTo_mem_axis ξ η hne t

theorem cosh_dist_normal_geod (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (y : HUpper n) (hpy : axisFoot ξ η hne y ≠ y)
    (a : HUpper n) (ha : a ∈ axis ξ η) (t : ℝ) :
    Real.cosh (dist (geodFromTo (axisFoot ξ η hne y) y hpy t) a) =
      Real.cosh t * Real.cosh (dist (axisFoot ξ η hne y) a) := by
  have hr : axisRadius ξ η y = Real.cosh (dist (axisFoot ξ η hne y) y) := by
    rw [dist_comm, cosh_dist_axisFoot]
  have hax : Real.cosh (dist a y) =
      Real.cosh (dist (axisFoot ξ η hne y) y) *
        Real.cosh (dist a (axisFoot ξ η hne y)) := by
    rw [dist_comm a y, cosh_dist_axis ξ η hne y a ha, hr,
      dist_comm a (axisFoot ξ η hne y)]
  rw [dist_comm, cosh_dist_geodFromTo hpy, hax,
    dist_comm a (axisFoot ξ η hne y)]
  ring

theorem cosh_displacement_normal_geod (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hpy : axisFoot ξ η hne y ≠ y) (t : ℝ) :
    Real.cosh (dist ((poMulAction hn).smul g
      (geodFromTo (axisFoot ξ η hne y) y hpy t))
        (geodFromTo (axisFoot ξ η hne y) y hpy t)) =
      Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y)) (axisFoot ξ η hne y)) +
        (Real.sinh t / Real.sinh (dist (axisFoot ξ η hne y) y)) ^ 2 *
          (Real.cosh (dist ((poMulAction hn).smul g y) y) -
            Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y))
              (axisFoot ξ η hne y))) := by
  let := poMulAction hn
  let p := axisFoot ξ η hne y
  let q := geodFromTo p y hpy
  let A := Real.cosh (dist (g • p) p)
  have hs : Real.sinh (dist p y) ≠ 0 := (Real.sinh_pos_iff.mpr (dist_pos.mpr hpy)).ne'
  have hgp : g • p ∈ axis ξ η := smul_mem_axis hn g ξ η hpair (axisFoot_mem ξ η hne y)
  have higp : g⁻¹ • p ∈ axis ξ η :=
    smul_mem_axis hn g⁻¹ ξ η (boundary_pair_inv hn g ξ η hne hpair) (axisFoot_mem ξ η hne y)
  have hmove (a : HUpper n) : dist (g • q t) a = dist (g⁻¹ • a) (q t) := by
    calc
      dist (g • q t) a = dist (g • q t) (g • (g⁻¹ • a)) := by rw [smul_inv_smul]
      _ = dist (g⁻¹ • a) (q t) := by rw [po_dist_smul hn, dist_comm]
  have hinvp : dist p (g⁻¹ • p) = dist (g • p) p := by
    rw [← po_dist_smul hn g, smul_inv_smul]
  have hnear : Real.cosh (dist (g • q t) p) = Real.cosh t * A := by
    rw [hmove, dist_comm]
    exact (cosh_dist_normal_geod ξ η hne y hpy _ higp t).trans
      (by change Real.cosh t * Real.cosh (dist p (g⁻¹ • p)) = _; rw [hinvp])
  have hstart : Real.cosh (dist (g⁻¹ • y) p) = Real.cosh (dist p y) * A := by
    have he : dist (g⁻¹ • y) p = dist y (g • p) := by
      rw [← po_dist_smul hn g, smul_inv_smul]
    rw [he, cosh_dist_axis ξ η hne y _ hgp, dist_comm p (g • p)]
    rw [← cosh_dist_axisFoot ξ η hne y, dist_comm y p]
  have hinvy : dist (g⁻¹ • y) y = dist (g • y) y := by
    rw [← po_dist_smul hn g, smul_inv_smul, dist_comm]
  have hcross : Real.cosh (dist (g • q t) y) =
      Real.cosh t * (Real.cosh (dist p y) * A) +
        Real.sinh t * ((Real.cosh (dist (g • y) y) -
          Real.cosh (dist p y) ^ 2 * A) / Real.sinh (dist p y)) := by
    rw [hmove, cosh_dist_geodFromTo hpy, hstart, hinvy, pow_two, mul_assoc]
  have he := cosh_dist_geodFromTo hpy (g • q t) t
  change Real.cosh (dist (g • q t) (q t)) =
    Real.cosh t * Real.cosh (dist (g • q t) p) +
      Real.sinh t * ((Real.cosh (dist (g • q t) y) -
        Real.cosh (dist p y) * Real.cosh (dist (g • q t) p)) /
          Real.sinh (dist p y)) at he
  rw [hnear, hcross] at he
  change Real.cosh (dist (g • q t) (q t)) =
    A + (Real.sinh t / Real.sinh (dist p y)) ^ 2 *
      (Real.cosh (dist (g • y) y) - A)
  rw [he]
  field_simp
  linear_combination A * (Real.sinh (dist p y)) ^ 2 * Real.cosh_sq_sub_sinh_sq t -
    A * (Real.sinh t) ^ 2 * Real.cosh_sq_sub_sinh_sq (dist p y)

theorem displacement_le_normal_geod (hn : 1 ≤ n) (g : PO n 1)
    (ξ η : BoundaryH n) (hne : ξ ≠ η)
    (hpair : (poBoundaryMulAction hn).smul g ξ ∈ ({ξ, η} : Set (BoundaryH n)) ∧
      (poBoundaryMulAction hn).smul g η ∈ ({ξ, η} : Set (BoundaryH n)))
    (y : HUpper n) (hpy : axisFoot ξ η hne y ≠ y)
    {t : ℝ} (ht : dist (axisFoot ξ η hne y) y ≤ t) :
    dist ((poMulAction hn).smul g y) y ≤
      dist ((poMulAction hn).smul g (geodFromTo (axisFoot ξ η hne y) y hpy t))
        (geodFromTo (axisFoot ξ η hne y) y hpy t) := by
  have he := cosh_displacement_normal_geod hn g ξ η hne hpair y hpy t
  have hs : 0 < Real.sinh (dist (axisFoot ξ η hne y) y) :=
    Real.sinh_pos_iff.mpr (dist_pos.mpr hpy)
  have hratio : 1 ≤ Real.sinh t / Real.sinh (dist (axisFoot ξ η hne y) y) :=
    (one_le_div hs).mpr (Real.sinh_le_sinh.mpr ht)
  have hsq : 1 ≤ (Real.sinh t / Real.sinh (dist (axisFoot ξ η hne y) y)) ^ 2 := by
    nlinarith
  have hproj := Real.cosh_strictMonoOn.monotoneOn dist_nonneg dist_nonneg
    (displacement_axisFoot_le hn g ξ η hne hpair y)
  have hnonneg : 0 ≤ Real.cosh (dist ((poMulAction hn).smul g y) y) -
      Real.cosh (dist ((poMulAction hn).smul g (axisFoot ξ η hne y)) (axisFoot ξ η hne y)) :=
    sub_nonneg.mpr hproj
  have hmul := mul_le_mul_of_nonneg_right hsq hnonneg
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  linarith

end DifferentialGeometry.AxisGeometry
