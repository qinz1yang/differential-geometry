import DifferentialGeometry.Topology.Homotopy.SquareBoundary
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open scoped unitInterval
namespace DifferentialGeometry.Topology

private def squareLo (t : unitInterval) : ℝ := max (2 * (t : ℝ) - 1) 0
private def squareHi (t : unitInterval) : ℝ := min (2 * (t : ℝ)) 1

private theorem squareLo_nonneg (t : unitInterval) : 0 ≤ squareLo t := le_max_right _ _
private theorem squareHi_le_one (t : unitInterval) : squareHi t ≤ 1 := min_le_right _ _
private theorem squareLo_le_hi (t : unitInterval) : squareLo t ≤ squareHi t := by
  dsimp [squareLo, squareHi]
  exact max_le (le_min (by linarith) (by linarith [t.property.2]))
    (le_min (by linarith [t.property.1]) zero_le_one)
private theorem squareLo_add_hi (t : unitInterval) : squareLo t + squareHi t = 2 * (t : ℝ) := by
  dsimp [squareLo, squareHi]
  by_cases h : 2 * (t : ℝ) ≤ 1
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

private def squareDiagonalParam : C(unitInterval × unitInterval, unitInterval × unitInterval) where
  toFun p :=
    (⟨squareLo p.2 + (squareHi p.2 - squareLo p.2) * (p.1 : ℝ), by
      constructor
      · nlinarith [squareLo_nonneg p.2, squareLo_le_hi p.2, p.1.property.1]
      · nlinarith [squareLo_le_hi p.2, squareHi_le_one p.2, p.1.property.2]⟩,
    ⟨squareHi p.2 - (squareHi p.2 - squareLo p.2) * (p.1 : ℝ), by
      constructor
      · nlinarith [squareLo_nonneg p.2, squareLo_le_hi p.2, p.1.property.2]
      · nlinarith [squareLo_le_hi p.2, squareHi_le_one p.2, p.1.property.1]⟩)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;>
      dsimp [squareLo, squareHi] <;> fun_prop

private theorem squareDiagonalParam_sum (p : unitInterval × unitInterval) :
    ((squareDiagonalParam p).1 : ℝ) + ((squareDiagonalParam p).2 : ℝ) = 2 * (p.2 : ℝ) := by
  change squareLo p.2 + (squareHi p.2 - squareLo p.2) * (p.1 : ℝ) +
      (squareHi p.2 - (squareHi p.2 - squareLo p.2) * (p.1 : ℝ)) = _
  linarith [squareLo_add_hi p.2]

private theorem squareDiagonalParam_surjective : Function.Surjective squareDiagonalParam := by
  rintro ⟨x, y⟩
  let t : unitInterval := ⟨((x : ℝ) + (y : ℝ)) / 2,
    by constructor <;> linarith [x.property.1, x.property.2, y.property.1, y.property.2]⟩
  have ht : 2 * (t : ℝ) = (x : ℝ) + (y : ℝ) := by dsimp [t]; ring
  have hl : squareLo t ≤ (x : ℝ) := by
    dsimp [squareLo]
    rw [ht]
    exact max_le (by linarith [y.property.2]) x.property.1
  have hu : (x : ℝ) ≤ squareHi t := by
    dsimp [squareHi]
    rw [ht]
    exact le_min (by linarith [y.property.1]) x.property.2
  let d := squareHi t - squareLo t
  have hd : 0 ≤ d := sub_nonneg.mpr (squareLo_le_hi t)
  let r : unitInterval := ⟨((x : ℝ) - squareLo t) / d,
    unitInterval.div_mem (sub_nonneg.mpr hl) hd (by dsimp [d]; linarith)⟩
  have he : d * (r : ℝ) = (x : ℝ) - squareLo t := by
    by_cases hd0 : d = 0
    · have hx : (x : ℝ) - squareLo t = 0 := by dsimp [d] at hd0; linarith
      simp [r, hx]
    · exact mul_div_cancel₀ _ hd0
  refine ⟨(r, t), Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)⟩
  · change squareLo t + d * (r : ℝ) = (x : ℝ)
    rw [he]
    ring
  · change squareHi t - d * (r : ℝ) = (y : ℝ)
    rw [he]
    linarith [squareLo_add_hi t]

private theorem squareDiagonalParam_width_zero (t : unitInterval)
    (h : squareHi t - squareLo t = 0) : t = 0 ∨ t = 1 := by
  by_cases ht : 2 * (t : ℝ) ≤ 1
  · left
    apply Subtype.ext
    change (t : ℝ) = 0
    simp only [squareLo, squareHi, min_eq_left ht, max_eq_right (by linarith : 2 * (t : ℝ) - 1 ≤ 0)] at h
    linarith
  · right
    apply Subtype.ext
    change (t : ℝ) = 1
    simp only [squareLo, squareHi, min_eq_right (le_of_not_ge ht), max_eq_left (by linarith : 0 ≤ 2 * (t : ℝ) - 1)] at h
    linarith

private theorem squareDiagonalParam_factorsThrough {X : Type*} [TopologicalSpace X]
    {a b : X} {p q : Path a b} (H : p.Homotopy q) :
    Function.FactorsThrough H.toContinuousMap squareDiagonalParam := by
  rintro ⟨r, t⟩ ⟨s, u⟩ h
  have he := congrArg (fun z : unitInterval × unitInterval => (z.1 : ℝ) + (z.2 : ℝ)) h
  rw [squareDiagonalParam_sum, squareDiagonalParam_sum] at he
  have htu : t = u := Subtype.ext (by linarith)
  subst u
  by_cases hw : squareHi t - squareLo t = 0
  · rcases squareDiagonalParam_width_zero t hw with rfl | rfl <;> simp
  · have he := congrArg (fun z : unitInterval × unitInterval => (z.1 : ℝ)) h
    change squareLo t + (squareHi t - squareLo t) * (r : ℝ) =
      squareLo t + (squareHi t - squareLo t) * (s : ℝ) at he
    have hrs : r = s := Subtype.ext (mul_left_cancel₀ hw (add_left_cancel he))
    subst s
    rfl

private def squareHomotopyDesc {X : Type*} [TopologicalSpace X]
    {a b : X} {p q : Path a b} (H : p.Homotopy q) : C(unitInterval × unitInterval, X) :=
  (Topology.IsQuotientMap.of_surjective_continuous squareDiagonalParam_surjective
    squareDiagonalParam.continuous).lift H.toContinuousMap (squareDiagonalParam_factorsThrough H)

private theorem squareHomotopyDesc_apply {X : Type*} [TopologicalSpace X]
    {a b : X} {p q : Path a b} (H : p.Homotopy q) (v : unitInterval × unitInterval) :
    squareHomotopyDesc H (squareDiagonalParam v) = H v := by
  exact congrArg (fun f => f v)
    ((Topology.IsQuotientMap.of_surjective_continuous squareDiagonalParam_surjective
      squareDiagonalParam.continuous).lift_comp H.toContinuousMap (squareDiagonalParam_factorsThrough H))

private def intervalLeftHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

private def intervalRightHalf (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.property.1, t.property.2]⟩

private theorem squareDiagonalParam_zero_leftHalf (t : unitInterval) :
    squareDiagonalParam (0, intervalLeftHalf t) = (0, t) := by
  have hlo : squareLo (intervalLeftHalf t) = 0 := by
    dsimp [squareLo, intervalLeftHalf]
    rw [max_eq_right (by linarith [t.property.2])]
  have hhi : squareHi (intervalLeftHalf t) = (t : ℝ) := by
    dsimp [squareHi, intervalLeftHalf]
    rw [min_eq_left (by linarith [t.property.2])]
    ring
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [squareDiagonalParam, hlo, hhi]

private theorem squareDiagonalParam_one_leftHalf (t : unitInterval) :
    squareDiagonalParam (1, intervalLeftHalf t) = (t, 0) := by
  have hlo : squareLo (intervalLeftHalf t) = 0 := by
    dsimp [squareLo, intervalLeftHalf]
    rw [max_eq_right (by linarith [t.property.2])]
  have hhi : squareHi (intervalLeftHalf t) = (t : ℝ) := by
    dsimp [squareHi, intervalLeftHalf]
    rw [min_eq_left (by linarith [t.property.2])]
    ring
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [squareDiagonalParam, hlo, hhi]

private theorem squareDiagonalParam_zero_rightHalf (t : unitInterval) :
    squareDiagonalParam (0, intervalRightHalf t) = (t, 1) := by
  have hlo : squareLo (intervalRightHalf t) = (t : ℝ) := by
    dsimp [squareLo, intervalRightHalf]
    rw [max_eq_left (by linarith [t.property.1])]
    ring
  have hhi : squareHi (intervalRightHalf t) = 1 := by
    dsimp [squareHi, intervalRightHalf]
    rw [min_eq_right (by linarith [t.property.1])]
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [squareDiagonalParam, hlo, hhi]

private theorem squareDiagonalParam_one_rightHalf (t : unitInterval) :
    squareDiagonalParam (1, intervalRightHalf t) = (1, t) := by
  have hlo : squareLo (intervalRightHalf t) = (t : ℝ) := by
    dsimp [squareLo, intervalRightHalf]
    rw [max_eq_left (by linarith [t.property.1])]
    ring
  have hhi : squareHi (intervalRightHalf t) = 1 := by
    dsimp [squareHi, intervalRightHalf]
    rw [min_eq_right (by linarith [t.property.1])]
  apply Prod.ext <;> apply Subtype.ext <;>
    simp [squareDiagonalParam, hlo, hhi]

private theorem path_trans_intervalLeftHalf {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (intervalLeftHalf t) = p t := by
  rw [← Path.extend_apply, Path.extend_trans_of_le_half p q
    (show (intervalLeftHalf t : ℝ) ≤ 1 / 2 by dsimp [intervalLeftHalf]; linarith [t.property.2])]
  have he : 2 * (intervalLeftHalf t : ℝ) = (t : ℝ) := by dsimp [intervalLeftHalf]; ring
  rw [he, Path.extend_apply]

private theorem path_trans_intervalRightHalf {X : Type*} [TopologicalSpace X]
    {a b c : X} (p : Path a b) (q : Path b c) (t : unitInterval) :
    (p.trans q) (intervalRightHalf t) = q t := by
  rw [← Path.extend_apply, Path.extend_trans_of_half_le p q
    (show 1 / 2 ≤ (intervalRightHalf t : ℝ) by dsimp [intervalRightHalf]; linarith [t.property.1])]
  have he : 2 * (intervalRightHalf t : ℝ) - 1 = (t : ℝ) := by dsimp [intervalRightHalf]; ring
  rw [he, Path.extend_apply]

theorem exists_square_of_boundary_homotopic {X : Type*} [TopologicalSpace X]
    {a b c d : X} (bottom : Path a b) (top : Path c d)
    (left : Path a c) (right : Path b d)
    (h : (bottom.trans right).Homotopic (left.trans top)) :
    ∃ F : C(unitInterval × unitInterval, X),
      (∀ s, F (0, s) = bottom s) ∧ (∀ s, F (1, s) = top s) ∧
      (∀ t, F (t, 0) = left t) ∧ (∀ t, F (t, 1) = right t) := by
  obtain ⟨H⟩ := h
  refine ⟨squareHomotopyDesc H, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [← squareDiagonalParam_zero_leftHalf s, squareHomotopyDesc_apply, H.apply_zero]
    exact path_trans_intervalLeftHalf bottom right s
  · intro s
    rw [← squareDiagonalParam_one_rightHalf s, squareHomotopyDesc_apply, H.apply_one]
    exact path_trans_intervalRightHalf left top s
  · intro t
    rw [← squareDiagonalParam_one_leftHalf t, squareHomotopyDesc_apply, H.apply_one]
    exact path_trans_intervalLeftHalf left top t
  · intro t
    rw [← squareDiagonalParam_zero_rightHalf t, squareHomotopyDesc_apply, H.apply_zero]
    exact path_trans_intervalRightHalf bottom right t

theorem square_boundary_homotopic_iff {X : Type*} [TopologicalSpace X]
    {a b c d : X} (bottom : Path a b) (top : Path c d)
    (left : Path a c) (right : Path b d) :
    (bottom.trans right).Homotopic (left.trans top) ↔
      ∃ F : C(unitInterval × unitInterval, X),
        (∀ s, F (0, s) = bottom s) ∧ (∀ s, F (1, s) = top s) ∧
        (∀ t, F (t, 0) = left t) ∧ (∀ t, F (t, 1) = right t) := by
  constructor
  · exact exists_square_of_boundary_homotopic bottom top left right
  · rintro ⟨F, hbottom, htop, hleft, hright⟩
    exact square_boundary_homotopic bottom top left right F hbottom htop hleft hright

end DifferentialGeometry.Topology
