import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import DifferentialGeometry.Analysis.Calculus.Interpolation.FiniteClosedCover

set_option autoImplicit false

noncomputable section

open Set
open MeasureTheory
open scoped NNReal

namespace DifferentialGeometry.Topology.Planar.SlitRegluing

/-- The closed square on which the finite slit construction acts. -/
def square : Set ℂ := {z | |z.re| ≤ 1 ∧ |z.im| ≤ 1}

/-- The three open source triangles in the positive quadrant. -/
def baseCell : Fin 3 → Set ℂ
  | 0 => {z | 0 < z.im ∧ z.im < z.re ∧ z.re < 1}
  | 1 => {z | 0 < z.re ∧ z.re < z.im ∧ 2 * z.im < 1 + z.re}
  | 2 => {z | 0 < z.re ∧ 1 + z.re < 2 * z.im ∧ z.im < 1}

/-- The corresponding closed source triangles. -/
def baseClosedCell : Fin 3 → Set ℂ
  | 0 => {z | 0 ≤ z.im ∧ z.im ≤ z.re ∧ z.re ≤ 1}
  | 1 => {z | 0 ≤ z.re ∧ z.re ≤ z.im ∧ 2 * z.im ≤ 1 + z.re}
  | 2 => {z | 0 ≤ z.re ∧ 1 + z.re ≤ 2 * z.im ∧ z.im ≤ 1}

/-- The three affine formulas before reflection in the coordinate axes. -/
def baseBranch : Fin 3 → ℂ → ℂ
  | 0, z => ⟨(1 + z.re) / 2, z.im⟩
  | 1, z => ⟨1 / 2 + 3 * z.re / 2 - z.im, z.re⟩
  | 2, z => ⟨z.re, 2 * z.im - 1⟩

/-- The global affine inverses of the three branch formulas. -/
def baseBranchInv : Fin 3 → ℂ → ℂ
  | 0, z => ⟨2 * z.re - 1, z.im⟩
  | 1, z => ⟨z.im, 1 / 2 + 3 * z.im / 2 - z.re⟩
  | 2, z => ⟨z.re, (1 + z.im) / 2⟩

/-- The open target triangles of the three affine branches. -/
def baseTargetCell : Fin 3 → Set ℂ
  | 0 => {z | 0 < z.im ∧ z.im < 2 * z.re - 1 ∧ z.re < 1}
  | 1 => {z | 0 < z.im ∧ z.im < z.re ∧ 2 * z.re < 1 + z.im}
  | 2 => {z | 0 < z.re ∧ z.re < z.im ∧ z.im < 1}

/-- The closed target triangles of the three affine branches. -/
def baseClosedTargetCell : Fin 3 → Set ℂ
  | 0 => {z | 0 ≤ z.im ∧ z.im ≤ 2 * z.re - 1 ∧ z.re ≤ 1}
  | 1 => {z | 0 ≤ z.im ∧ z.im ≤ z.re ∧ 2 * z.re ≤ 1 + z.im}
  | 2 => {z | 0 ≤ z.re ∧ z.re ≤ z.im ∧ z.im ≤ 1}

theorem baseBranchInv_baseBranch (i : Fin 3) (z : ℂ) :
    baseBranchInv i (baseBranch i z) = z := by
  fin_cases i <;> apply Complex.ext <;> simp [baseBranch, baseBranchInv]; ring

theorem baseBranch_baseBranchInv (i : Fin 3) (z : ℂ) :
    baseBranch i (baseBranchInv i z) = z := by
  fin_cases i <;> apply Complex.ext <;> simp [baseBranch, baseBranchInv]; ring

theorem baseBranch_mem_target_iff (i : Fin 3) (z : ℂ) :
    baseBranch i z ∈ baseTargetCell i ↔ z ∈ baseCell i := by
  fin_cases i <;> dsimp [baseBranch, baseTargetCell, baseCell] <;>
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

theorem baseBranch_mem_closedTarget_iff (i : Fin 3) (z : ℂ) :
    baseBranch i z ∈ baseClosedTargetCell i ↔ z ∈ baseClosedCell i := by
  fin_cases i <;> dsimp [baseBranch, baseClosedTargetCell, baseClosedCell] <;>
    constructor <;> rintro ⟨h₁, h₂, h₃⟩ <;> constructor <;> try linarith
  all_goals constructor <;> linarith

theorem baseBranch_image_cell (i : Fin 3) :
    baseBranch i '' baseCell i = baseTargetCell i := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (baseBranch_mem_target_iff i w).mpr hw
  · intro hz
    refine ⟨baseBranchInv i z, ?_, baseBranch_baseBranchInv i z⟩
    exact (baseBranch_mem_target_iff i (baseBranchInv i z)).mp
      (by simpa only [baseBranch_baseBranchInv] using hz)

theorem baseBranch_image_closedCell (i : Fin 3) :
    baseBranch i '' baseClosedCell i = baseClosedTargetCell i := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (baseBranch_mem_closedTarget_iff i w).mpr hw
  · intro hz
    refine ⟨baseBranchInv i z, ?_, baseBranch_baseBranchInv i z⟩
    exact (baseBranch_mem_closedTarget_iff i (baseBranchInv i z)).mp
      (by simpa only [baseBranch_baseBranchInv] using hz)

theorem baseCell_subset_closedCell (i : Fin 3) : baseCell i ⊆ baseClosedCell i := by
  intro z hz
  fin_cases i <;> exact ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

theorem baseClosedCell_bounds (i : Fin 3) {z : ℂ} (hz : z ∈ baseClosedCell i) :
    0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 := by
  fin_cases i <;> dsimp [baseClosedCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem baseClosedTargetCell_bounds (i : Fin 3) {z : ℂ}
    (hz : z ∈ baseClosedTargetCell i) :
    0 ≤ z.re ∧ z.re ≤ 1 ∧ 0 ≤ z.im ∧ z.im ≤ 1 := by
  fin_cases i <;> dsimp [baseClosedTargetCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_mem_baseClosedCell {z : ℂ}
    (hx : 0 ≤ z.re) (hx' : z.re ≤ 1) (hy : 0 ≤ z.im) (hy' : z.im ≤ 1) :
    ∃ i, z ∈ baseClosedCell i := by
  by_cases h₀ : z.im ≤ z.re
  · exact ⟨0, hy, h₀, hx'⟩
  · by_cases h₁ : 2 * z.im ≤ 1 + z.re
    · exact ⟨1, hx, le_of_not_ge h₀, h₁⟩
    · exact ⟨2, hx, le_of_not_ge h₁, hy'⟩

theorem exists_mem_baseClosedTargetCell {z : ℂ}
    (hx : 0 ≤ z.re) (hx' : z.re ≤ 1) (hy : 0 ≤ z.im) (hy' : z.im ≤ 1) :
    ∃ i, z ∈ baseClosedTargetCell i := by
  by_cases h₂ : z.re ≤ z.im
  · exact ⟨2, hx, h₂, hy'⟩
  · by_cases h₀ : z.im ≤ 2 * z.re - 1
    · exact ⟨0, hy, h₀, hx'⟩
    · exact ⟨1, hy, le_of_not_ge h₂, by linarith⟩

theorem baseCell_pairwiseDisjoint : Pairwise (fun i j => Disjoint (baseCell i) (baseCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals dsimp [baseCell] at hi hj
  all_goals rcases hi with ⟨h₁, h₂, h₃⟩; rcases hj with ⟨h₄, h₅, h₆⟩; linarith

theorem baseTargetCell_pairwiseDisjoint : Pairwise (fun i j => Disjoint (baseTargetCell i) (baseTargetCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals dsimp [baseTargetCell] at hi hj
  all_goals rcases hi with ⟨h₁, h₂, h₃⟩; rcases hj with ⟨h₄, h₅, h₆⟩; linarith

theorem baseBranch_eq_on_interface01 {z : ℂ} (h : z.im = z.re) :
    baseBranch 0 z = baseBranch 1 z := by
  apply Complex.ext <;> simp [baseBranch, h]; ring

theorem baseBranch_eq_on_interface12 {z : ℂ} (h : 2 * z.im = 1 + z.re) :
    baseBranch 1 z = baseBranch 2 z := by
  apply Complex.ext <;> dsimp [baseBranch] <;> linarith

theorem baseBranch_eq_self_on_outer (i : Fin 3) {z : ℂ}
    (hz : z ∈ baseClosedCell i) (houter : z.re = 1 ∨ z.im = 1) :
    baseBranch i z = z := by
  fin_cases i <;> dsimp [baseClosedCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals rcases houter with h | h <;> apply Complex.ext <;> dsimp [baseBranch] <;> linarith

private def coordinateLinear (a b c d : ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := ⟨a * z.re + b * z.im, c * z.re + d * z.im⟩
  map_add' z w := by
    apply Complex.ext <;> simp <;> ring
  map_smul' r z := by
    apply Complex.ext <;> simp <;> ring

private def coordinateAffine (a b c d u v : ℝ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := ⟨a * z.re + b * z.im + u, c * z.re + d * z.im + v⟩
  linear := coordinateLinear a b c d
  map_vadd' z w := by
    apply Complex.ext <;> simp [coordinateLinear] <;> ring

/-- The bundled affine maps underlying the base formulas. -/
def baseAffine : Fin 3 → ℂ →ᵃ[ℝ] ℂ
  | 0 => coordinateAffine (1 / 2) 0 0 1 (1 / 2) 0
  | 1 => coordinateAffine (3 / 2) (-1) 1 0 (1 / 2) 0
  | 2 => coordinateAffine 1 0 0 2 0 (-1)

theorem baseAffine_apply (i : Fin 3) (z : ℂ) : baseAffine i z = baseBranch i z := by
  fin_cases i <;> apply Complex.ext <;> simp [baseAffine, coordinateAffine, baseBranch] <;> ring

private theorem coordinateLinear_det (a b c d : ℝ) :
    LinearMap.det (coordinateLinear a b c d) = a * d - b * c := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  have hmatrix : LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      (coordinateLinear a b c d) = !![a, b; c, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, coordinateLinear]
  rw [hmatrix, Matrix.det_fin_two_of]

theorem baseAffine_det (i : Fin 3) :
    LinearMap.det (baseAffine i).linear = ![(1 / 2 : ℝ), 1, 2] i := by
  fin_cases i <;> norm_num [baseAffine, coordinateAffine, coordinateLinear_det]

/-- Simultaneous input and output reflections produce all twelve branches. -/
def reflect (s : Bool × Bool) (z : ℂ) : ℂ :=
  ⟨if s.1 then -z.re else z.re, if s.2 then -z.im else z.im⟩

theorem reflect_reflect (s : Bool × Bool) (z : ℂ) : reflect s (reflect s z) = z := by
  rcases s with ⟨sx, sy⟩
  cases sx <;> cases sy <;> apply Complex.ext <;> simp [reflect]

private def reflectAffine (s : Bool × Bool) : ℂ →ᵃ[ℝ] ℂ :=
  coordinateAffine (if s.1 then -1 else 1) 0 0 (if s.2 then -1 else 1) 0 0

private theorem reflectAffine_apply (s : Bool × Bool) (z : ℂ) :
    reflectAffine s z = reflect s z := by
  rcases s with ⟨sx, sy⟩
  cases sx <;> cases sy <;> apply Complex.ext <;> simp [reflectAffine, coordinateAffine, reflect]

/-- The twelve open triangles of the slit construction. -/
def sourceCell (s : Bool × Bool) (i : Fin 3) : Set ℂ := reflect s ⁻¹' baseCell i

/-- The twelve closed triangles used for composed-map pasting. -/
def sourceClosedCell (s : Bool × Bool) (i : Fin 3) : Set ℂ :=
  reflect s ⁻¹' baseClosedCell i

/-- The twelve open image triangles. -/
def targetCell (s : Bool × Bool) (i : Fin 3) : Set ℂ := reflect s ⁻¹' baseTargetCell i

/-- The twelve closed image triangles. -/
def targetClosedCell (s : Bool × Bool) (i : Fin 3) : Set ℂ :=
  reflect s ⁻¹' baseClosedTargetCell i

/-- Each branch is defined on the whole plane, independently of its cell. -/
def branch (s : Bool × Bool) (i : Fin 3) (z : ℂ) : ℂ :=
  reflect s (baseBranch i (reflect s z))

/-- The explicit global inverse of each affine branch. -/
def branchInv (s : Bool × Bool) (i : Fin 3) (z : ℂ) : ℂ :=
  reflect s (baseBranchInv i (reflect s z))

/-- The real affine structure of each of the twelve formulas. -/
def branchAffine (s : Bool × Bool) (i : Fin 3) : ℂ →ᵃ[ℝ] ℂ :=
  (reflectAffine s).comp ((baseAffine i).comp (reflectAffine s))

theorem branchAffine_apply (s : Bool × Bool) (i : Fin 3) (z : ℂ) :
    branchAffine s i z = branch s i z := by
  simp only [branchAffine, AffineMap.comp_apply, reflectAffine_apply, baseAffine_apply, branch]

theorem branchInv_branch (s : Bool × Bool) (i : Fin 3) (z : ℂ) :
    branchInv s i (branch s i z) = z := by
  simp only [branchInv, branch, reflect_reflect, baseBranchInv_baseBranch]

theorem branch_branchInv (s : Bool × Bool) (i : Fin 3) (z : ℂ) :
    branch s i (branchInv s i z) = z := by
  simp only [branchInv, branch, reflect_reflect, baseBranch_baseBranchInv]

theorem branch_det (s : Bool × Bool) (i : Fin 3) :
    LinearMap.det (branchAffine s i).linear = ![(1 / 2 : ℝ), 1, 2] i := by
  change LinearMap.det ((reflectAffine s).linear.comp
    ((baseAffine i).linear.comp (reflectAffine s).linear)) = _
  rw [LinearMap.det_comp, LinearMap.det_comp, baseAffine_det]
  rcases s with ⟨sx, sy⟩
  cases sx <;> cases sy <;> simp [reflectAffine, coordinateAffine, coordinateLinear_det]

theorem branch_det_pos (s : Bool × Bool) (i : Fin 3) :
    0 < LinearMap.det (branchAffine s i).linear := by
  rw [branch_det]
  fin_cases i <;> norm_num

theorem branch_lipschitz (s : Bool × Bool) (i : Fin 3) :
    ∃ K : ℝ≥0, LipschitzWith K (branch s i) := by
  obtain ⟨K, hK⟩ := (branchAffine s i).lipschitzWith_of_finiteDimensional
  have hfun : (branchAffine s i : ℂ → ℂ) = branch s i := funext (branchAffine_apply s i)
  exact ⟨K, hfun ▸ hK⟩

theorem branch_antilipschitz (s : Bool × Bool) (i : Fin 3) :
    ∃ K : ℝ≥0, AntilipschitzWith K (branch s i) := by
  have hinj : Function.Injective (branchAffine s i) := by
    intro z w h
    simpa only [branchAffine_apply, branchInv_branch] using congrArg (branchInv s i) h
  obtain ⟨K, hK⟩ := AffineMap.antilipschitzWith_of_finiteDimensional hinj
  have hfun : (branchAffine s i : ℂ → ℂ) = branch s i := funext (branchAffine_apply s i)
  exact ⟨K, hfun ▸ hK⟩

theorem branchInv_lipschitz (s : Bool × Bool) (i : Fin 3) :
    ∃ K : ℝ≥0, LipschitzWith K (branchInv s i) := by
  obtain ⟨K, hK⟩ := branch_antilipschitz s i
  refine ⟨K, LipschitzWith.of_dist_le_mul fun z w => ?_⟩
  simpa only [branch_branchInv] using hK.le_mul_dist (branchInv s i z) (branchInv s i w)

theorem branch_mem_target_iff (s : Bool × Bool) (i : Fin 3) (z : ℂ) :
    branch s i z ∈ targetCell s i ↔ z ∈ sourceCell s i := by
  simp only [targetCell, sourceCell, Set.mem_preimage, branch, reflect_reflect,
    baseBranch_mem_target_iff]

theorem branch_mem_closedTarget_iff (s : Bool × Bool) (i : Fin 3) (z : ℂ) :
    branch s i z ∈ targetClosedCell s i ↔ z ∈ sourceClosedCell s i := by
  simp only [targetClosedCell, sourceClosedCell, Set.mem_preimage, branch, reflect_reflect,
    baseBranch_mem_closedTarget_iff]

theorem branch_image_cell (s : Bool × Bool) (i : Fin 3) :
    branch s i '' sourceCell s i = targetCell s i := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (branch_mem_target_iff s i w).mpr hw
  · intro hz
    refine ⟨branchInv s i z, ?_, branch_branchInv s i z⟩
    exact (branch_mem_target_iff s i (branchInv s i z)).mp
      (by simpa only [branch_branchInv] using hz)

theorem branch_image_closedCell (s : Bool × Bool) (i : Fin 3) :
    branch s i '' sourceClosedCell s i = targetClosedCell s i := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (branch_mem_closedTarget_iff s i w).mpr hw
  · intro hz
    refine ⟨branchInv s i z, ?_, branch_branchInv s i z⟩
    exact (branch_mem_closedTarget_iff s i (branchInv s i z)).mp
      (by simpa only [branch_branchInv] using hz)

theorem baseBranch_eq_of_mem_closedCells (i j : Fin 3) {z : ℂ}
    (hi : z ∈ baseClosedCell i) (hj : z ∈ baseClosedCell j) :
    baseBranch i z = baseBranch j z := by
  fin_cases i <;> fin_cases j <;> dsimp [baseClosedCell] at hi hj
  all_goals rcases hi with ⟨h₁, h₂, h₃⟩; rcases hj with ⟨h₄, h₅, h₆⟩
  all_goals apply Complex.ext <;> dsimp [baseBranch] <;> linarith

/-- The positive-quadrant representative, with either sign allowed on an axis. -/
def quadrant (z : ℂ) : Bool × Bool :=
  (if z.re < 0 then true else false, if z.im < 0 then true else false)

theorem reflect_quadrant (z : ℂ) : reflect (quadrant z) z = ⟨|z.re|, |z.im|⟩ := by
  apply Complex.ext
  · by_cases h : z.re < 0
    · simp [reflect, quadrant, h, abs_of_neg h]
    · simp [reflect, quadrant, h, abs_of_nonneg (le_of_not_gt h)]
  · by_cases h : z.im < 0
    · simp [reflect, quadrant, h, abs_of_neg h]
    · simp [reflect, quadrant, h, abs_of_nonneg (le_of_not_gt h)]

private theorem reflect_eq_abs (s : Bool × Bool) {z : ℂ}
    (hz : 0 ≤ (reflect s z).re ∧ 0 ≤ (reflect s z).im) :
    reflect s z = ⟨|z.re|, |z.im|⟩ := by
  rcases s with ⟨sx, sy⟩
  cases sx <;> cases sy <;> apply Complex.ext <;> dsimp [reflect] at hz ⊢
  all_goals first
    | exact (abs_of_nonneg (by linarith [hz.1, hz.2])).symm
    | exact (abs_of_nonpos (by linarith [hz.1, hz.2])).symm

/-- A deterministic choice on shared base edges. -/
def baseIndex (z : ℂ) : Fin 3 :=
  if z.im ≤ z.re then 0 else if 2 * z.im ≤ 1 + z.re then 1 else 2

theorem mem_baseClosedCell_baseIndex {z : ℂ}
    (hx : 0 ≤ z.re) (hx' : z.re ≤ 1) (hy : 0 ≤ z.im) (hy' : z.im ≤ 1) :
    z ∈ baseClosedCell (baseIndex z) := by
  unfold baseIndex
  split_ifs with h₀ h₁
  · exact ⟨hy, h₀, hx'⟩
  · exact ⟨hx, le_of_not_ge h₀, h₁⟩
  · exact ⟨hx, le_of_not_ge h₁, hy'⟩

/-- The single-valued slit map. It is the identity outside the square.
Continuity is asserted only after composition with a map identifying the slit traces. -/
def slitMap (z : ℂ) : ℂ := by
  classical
  exact if z ∈ square then branch (quadrant z) (baseIndex (reflect (quadrant z) z)) z else z

theorem slitMap_eq_self_of_notMem {z : ℂ} (hz : z ∉ square) : slitMap z = z := by
  simp only [slitMap, ite_eq_right hz]

theorem sourceClosedCell_subset_square (s : Bool × Bool) (i : Fin 3) :
    sourceClosedCell s i ⊆ square := by
  intro z hz
  obtain ⟨hx, hx', hy, hy'⟩ := baseClosedCell_bounds i hz
  have heq := reflect_eq_abs s ⟨hx, hy⟩
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  exact ⟨by simpa only [hr] using hx',
    by simpa only [hi] using hy'⟩

theorem mem_chosen_closedCell {z : ℂ} (hz : z ∈ square) :
    z ∈ sourceClosedCell (quadrant z) (baseIndex (reflect (quadrant z) z)) := by
  apply mem_baseClosedCell_baseIndex
  · rw [reflect_quadrant]; exact abs_nonneg _
  · rw [reflect_quadrant]; exact hz.1
  · rw [reflect_quadrant]; exact abs_nonneg _
  · rw [reflect_quadrant]; exact hz.2

theorem exists_mem_sourceClosedCell {z : ℂ} (hz : z ∈ square) :
    ∃ s i, z ∈ sourceClosedCell s i :=
  ⟨quadrant z, baseIndex (reflect (quadrant z) z), mem_chosen_closedCell hz⟩

private theorem baseBranch_im_eq_zero (i : Fin 3) {z : ℂ}
    (hz : z ∈ baseClosedCell i) (hy : z.im = 0) : (baseBranch i z).im = 0 := by
  fin_cases i <;> dsimp [baseClosedCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals dsimp [baseBranch]; linarith

private theorem baseBranch_at_re_zero (i : Fin 3) {z : ℂ}
    (hz : z ∈ baseClosedCell i) (hx : z.re = 0) :
    (baseBranch i z).re = 0 ∨
      ((baseBranch i z).im = 0 ∧ 0 ≤ (baseBranch i z).re ∧ (baseBranch i z).re ≤ 1 / 2) := by
  fin_cases i <;> dsimp [baseClosedCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  · right
    dsimp [baseBranch]
    exact ⟨by linarith, by linarith, by linarith⟩
  · right
    dsimp [baseBranch]
    exact ⟨hx, by linarith, by linarith⟩
  · exact Or.inl hx

private theorem sign_eq_or_zero (s t : Bool) (r : ℝ)
    (hs : 0 ≤ if s then -r else r) (ht : 0 ≤ if t then -r else r) :
    s = t ∨ r = 0 := by
  cases s <;> cases t <;> simp_all <;> linarith

private theorem comp_reflect_eq {M : Type*} (f : ℂ → M)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ))
    (s t : Bool × Bool) (z v : ℂ)
    (hs : 0 ≤ (reflect s z).re ∧ 0 ≤ (reflect s z).im)
    (ht : 0 ≤ (reflect t z).re ∧ 0 ≤ (reflect t z).im)
    (hx : z.re = 0 → v.re = 0 ∨ (v.im = 0 ∧ 0 ≤ v.re ∧ v.re ≤ 1 / 2))
    (hy : z.im = 0 → v.im = 0) :
    f (reflect s v) = f (reflect t v) := by
  have hre := sign_eq_or_zero s.1 t.1 z.re hs.1 ht.1
  have him := sign_eq_or_zero s.2 t.2 z.im hs.2 ht.2
  have himeq : (reflect s v).im = (reflect t v).im := by
    rcases him with h | h
    · simp [reflect, h]
    · simp [reflect, hy h]
  rcases hre with h | h
  · apply congrArg f
    exact Complex.ext (by simp [reflect, h]) himeq
  · rcases hx h with hv | ⟨hv, hv₀, hv₁⟩
    · apply congrArg f
      exact Complex.ext (by simp [reflect, hv]) himeq
    · have hpos : (⟨v.re, 0⟩ : ℂ) = (v.re : ℂ) := rfl
      have hneg : (⟨-v.re, 0⟩ : ℂ) = -(v.re : ℂ) := by
        apply Complex.ext <;> simp
      have hp : f (⟨v.re, 0⟩ : ℂ) = f ⟨-v.re, 0⟩ := by
        rw [hpos, hneg]
        exact hpair v.re ⟨hv₀, hv₁⟩
      rcases s with ⟨sx, sy⟩
      rcases t with ⟨tx, ty⟩
      cases sx <;> cases tx <;> simp [reflect, hv, hp]

/-- On closed-cell overlaps, only the composed map has matching values. -/
theorem comp_branch_eq_of_mem_closedCells {M : Type*} (f : ℂ → M)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ))
    (s t : Bool × Bool) (i j : Fin 3) {z : ℂ}
    (hi : z ∈ sourceClosedCell s i) (hj : z ∈ sourceClosedCell t j) :
    f (branch s i z) = f (branch t j z) := by
  have hsi := baseClosedCell_bounds i hi
  have htj := baseClosedCell_bounds j hj
  have hs : 0 ≤ (reflect s z).re ∧ 0 ≤ (reflect s z).im := ⟨hsi.1, hsi.2.2.1⟩
  have ht : 0 ≤ (reflect t z).re ∧ 0 ≤ (reflect t z).im := ⟨htj.1, htj.2.2.1⟩
  have heq : reflect t z = reflect s z := (reflect_eq_abs t ht).trans (reflect_eq_abs s hs).symm
  have hj' : reflect s z ∈ baseClosedCell j := by
    change reflect t z ∈ baseClosedCell j at hj
    rwa [heq] at hj
  have hbranch := baseBranch_eq_of_mem_closedCells i j hi hj'
  unfold branch
  rw [heq, ← hbranch]
  apply comp_reflect_eq f hpair s t z (baseBranch i (reflect s z)) hs ht
  · intro hx
    exact baseBranch_at_re_zero i hi (by simp [reflect, hx])
  · intro hy
    exact baseBranch_im_eq_zero i hi (by simp [reflect, hy])

theorem comp_slitMap_eqOn_closedCell {M : Type*} (f : ℂ → M)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ))
    (s : Bool × Bool) (i : Fin 3) :
    EqOn (f ∘ slitMap) (f ∘ branch s i) (sourceClosedCell s i) := by
  intro z hz
  have hzs := sourceClosedCell_subset_square s i hz
  simp only [Function.comp_apply, slitMap, ite_eq_left hzs]
  exact comp_branch_eq_of_mem_closedCells f hpair _ s _ i (mem_chosen_closedCell hzs) hz

theorem branch_mem_square (s : Bool × Bool) (i : Fin 3) {z : ℂ}
    (hz : z ∈ sourceClosedCell s i) : branch s i z ∈ square := by
  have ht := (branch_mem_closedTarget_iff s i z).mpr hz
  obtain ⟨hx, hx', hy, hy'⟩ := baseClosedTargetCell_bounds i ht
  have heq := reflect_eq_abs s ⟨hx, hy⟩
  have hr := congrArg Complex.re heq
  have hi := congrArg Complex.im heq
  exact ⟨by simpa only [hr] using hx',
    by simpa only [hi] using hy'⟩

theorem slitMap_mem_square {z : ℂ} (hz : z ∈ square) : slitMap z ∈ square := by
  simp only [slitMap, ite_eq_left hz]
  exact branch_mem_square _ _ (mem_chosen_closedCell hz)

theorem branch_eq_self_on_outer (s : Bool × Bool) (i : Fin 3) {z : ℂ}
    (hz : z ∈ sourceClosedCell s i) (houter : |z.re| = 1 ∨ |z.im| = 1) :
    branch s i z = z := by
  have hb := baseClosedCell_bounds i hz
  have heq := reflect_eq_abs s ⟨hb.1, hb.2.2.1⟩
  have ho : (reflect s z).re = 1 ∨ (reflect s z).im = 1 := by
    simpa only [heq] using houter
  simp only [branch, baseBranch_eq_self_on_outer i hz ho, reflect_reflect]

theorem slitMap_eq_self_on_outer {z : ℂ} (houter : |z.re| = 1 ∨ |z.im| = 1) :
    slitMap z = z := by
  by_cases hz : z ∈ square
  · simp only [slitMap, ite_eq_left hz]
    exact branch_eq_self_on_outer _ _ (mem_chosen_closedCell hz) houter
  · exact slitMap_eq_self_of_notMem hz

theorem exists_mem_targetClosedCell {z : ℂ} (hz : z ∈ square) :
    ∃ s i, z ∈ targetClosedCell s i := by
  obtain ⟨i, hi⟩ := exists_mem_baseClosedTargetCell
    (z := reflect (quadrant z) z)
    (by rw [reflect_quadrant]; exact abs_nonneg _)
    (by rw [reflect_quadrant]; exact hz.1)
    (by rw [reflect_quadrant]; exact abs_nonneg _)
    (by rw [reflect_quadrant]; exact hz.2)
  exact ⟨quadrant z, i, hi⟩

/-- The slit can omit one trace as a point-set map, but the composed image is exact. -/
theorem comp_slitMap_image_square {M : Type*} (f : ℂ → M)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ)) :
    (f ∘ slitMap) '' square = f '' square := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨slitMap z, slitMap_mem_square hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨s, i, hi⟩ := exists_mem_targetClosedCell hz
    have hmem : branchInv s i z ∈ sourceClosedCell s i :=
      (branch_mem_closedTarget_iff s i (branchInv s i z)).mp
        (by simpa only [branch_branchInv] using hi)
    refine ⟨branchInv s i z, sourceClosedCell_subset_square s i hmem, ?_⟩
    have heq := comp_slitMap_eqOn_closedCell f hpair s i hmem
    simpa only [Function.comp_apply, branch_branchInv] using heq

theorem range_comp_slitMap {M : Type*} (f : ℂ → M)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ)) :
    Set.range (f ∘ slitMap) = Set.range f := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨slitMap z, rfl⟩
  · rintro _ ⟨z, rfl⟩
    by_cases hz : z ∈ square
    · have hm : f z ∈ (f ∘ slitMap) '' square :=
        (comp_slitMap_image_square f hpair).symm ▸ (mem_image_of_mem f hz)
      exact Set.image_subset_range _ _ hm
    · exact ⟨z, by simp only [Function.comp_apply, slitMap_eq_self_of_notMem hz]⟩

theorem baseCell_pos (i : Fin 3) {z : ℂ} (hz : z ∈ baseCell i) :
    0 < z.re ∧ 0 < z.im := by
  fin_cases i <;> dsimp [baseCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals exact ⟨by linarith, by linarith⟩

theorem baseTargetCell_pos (i : Fin 3) {z : ℂ} (hz : z ∈ baseTargetCell i) :
    0 < z.re ∧ 0 < z.im := by
  fin_cases i <;> dsimp [baseTargetCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  all_goals exact ⟨by linarith, by linarith⟩

private theorem quadrant_eq_of_reflect_pos (s : Bool × Bool) {z : ℂ}
    (hz : 0 < (reflect s z).re ∧ 0 < (reflect s z).im) : quadrant z = s := by
  have hq : 0 ≤ (reflect (quadrant z) z).re ∧ 0 ≤ (reflect (quadrant z) z).im := by
    rw [reflect_quadrant]
    exact ⟨abs_nonneg _, abs_nonneg _⟩
  apply Prod.ext
  · rcases sign_eq_or_zero (quadrant z).1 s.1 z.re hq.1 hz.1.le with h | h
    · exact h
    · have : 0 < (0 : ℝ) := by simpa [reflect, h] using hz.1
      exact this.false.elim
  · rcases sign_eq_or_zero (quadrant z).2 s.2 z.im hq.2 hz.2.le with h | h
    · exact h
    · have : 0 < (0 : ℝ) := by simpa [reflect, h] using hz.2
      exact this.false.elim

theorem sourceCell_subset_closedCell (s : Bool × Bool) (i : Fin 3) :
    sourceCell s i ⊆ sourceClosedCell s i := fun _ hz => baseCell_subset_closedCell i hz

theorem baseIndex_eq_of_mem_cell (i : Fin 3) {z : ℂ} (hz : z ∈ baseCell i) :
    baseIndex z = i := by
  fin_cases i <;> dsimp [baseCell] at hz <;> rcases hz with ⟨h₁, h₂, h₃⟩
  · simp only [baseIndex, ite_eq_left h₂.le]
    rfl
  · simp only [baseIndex, ite_eq_right (not_le_of_gt h₂), ite_eq_left h₃.le]
    rfl
  · have hxy : z.re < z.im := by linarith
    simp only [baseIndex, ite_eq_right (not_le_of_gt hxy), ite_eq_right (not_le_of_gt h₂)]
    rfl

/-- The raw map agrees with its affine formula on each open cell. -/
theorem slitMap_eqOn_cell (s : Bool × Bool) (i : Fin 3) :
    EqOn slitMap (branch s i) (sourceCell s i) := by
  intro z hz
  have hzs := sourceClosedCell_subset_square s i (sourceCell_subset_closedCell s i hz)
  have hq := quadrant_eq_of_reflect_pos s (baseCell_pos i hz)
  simp only [slitMap, ite_eq_left hzs, hq, baseIndex_eq_of_mem_cell i hz]

theorem sourceCell_pairwiseDisjoint :
    Pairwise (fun p q : (Bool × Bool) × Fin 3 =>
      Disjoint (sourceCell p.1 p.2) (sourceCell q.1 q.2)) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ hne
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hs := quadrant_eq_of_reflect_pos s (baseCell_pos i hi)
  have ht := quadrant_eq_of_reflect_pos t (baseCell_pos j hj)
  have hst : s = t := hs.symm.trans ht
  have hij : i ≠ j := fun h => hne (Prod.ext hst h)
  have hj' : z ∈ sourceCell s j := hst.symm ▸ hj
  exact Set.disjoint_left.mp (baseCell_pairwiseDisjoint hij) hi hj'

theorem targetCell_pairwiseDisjoint :
    Pairwise (fun p q : (Bool × Bool) × Fin 3 =>
      Disjoint (targetCell p.1 p.2) (targetCell q.1 q.2)) := by
  rintro ⟨s, i⟩ ⟨t, j⟩ hne
  apply Set.disjoint_left.mpr
  intro z hi hj
  have hs := quadrant_eq_of_reflect_pos s (baseTargetCell_pos i hi)
  have ht := quadrant_eq_of_reflect_pos t (baseTargetCell_pos j hj)
  have hst : s = t := hs.symm.trans ht
  have hij : i ≠ j := fun h => hne (Prod.ext hst h)
  have hj' : z ∈ targetCell s j := hst.symm ▸ hj
  exact Set.disjoint_left.mp (baseTargetCell_pairwiseDisjoint hij) hi hj'

theorem baseCell_isOpen (i : Fin 3) : IsOpen (baseCell i) := by
  fin_cases i
  · exact (isOpen_lt continuous_const Complex.continuous_im).inter
      ((isOpen_lt Complex.continuous_im Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const))
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re Complex.continuous_im).inter
        (isOpen_lt (Complex.continuous_im.const_mul 2) (continuous_const.add Complex.continuous_re)))
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt (continuous_const.add Complex.continuous_re) (Complex.continuous_im.const_mul 2)).inter
        (isOpen_lt Complex.continuous_im continuous_const))

theorem baseClosedCell_isClosed (i : Fin 3) : IsClosed (baseClosedCell i) := by
  fin_cases i
  · exact (isClosed_le continuous_const Complex.continuous_im).inter
      ((isClosed_le Complex.continuous_im Complex.continuous_re).inter
        (isClosed_le Complex.continuous_re continuous_const))
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re Complex.continuous_im).inter
        (isClosed_le (Complex.continuous_im.const_mul 2) (continuous_const.add Complex.continuous_re)))
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le (continuous_const.add Complex.continuous_re) (Complex.continuous_im.const_mul 2)).inter
        (isClosed_le Complex.continuous_im continuous_const))

private theorem continuous_reflect (s : Bool × Bool) : Continuous (reflect s) := by
  have hfun : (reflectAffine s : ℂ → ℂ) = reflect s := funext (reflectAffine_apply s)
  exact hfun ▸ (reflectAffine s).continuous_of_finiteDimensional

theorem sourceCell_isOpen (s : Bool × Bool) (i : Fin 3) : IsOpen (sourceCell s i) :=
  (baseCell_isOpen i).preimage (continuous_reflect s)

theorem sourceClosedCell_isClosed (s : Bool × Bool) (i : Fin 3) :
    IsClosed (sourceClosedCell s i) :=
  (baseClosedCell_isClosed i).preimage (continuous_reflect s)

theorem targetCell_isOpen (s : Bool × Bool) (i : Fin 3) : IsOpen (targetCell s i) := by
  rw [← branch_image_cell]
  have heq : branch s i '' sourceCell s i =
      branchInv s i ⁻¹' sourceCell s i := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [Set.mem_preimage, branchInv_branch] using hw
    · intro hz
      exact ⟨branchInv s i z, hz, branch_branchInv s i z⟩
  rw [heq]
  obtain ⟨K, hK⟩ := branchInv_lipschitz s i
  exact (sourceCell_isOpen s i).preimage hK.continuous

/-- The finitely many affine lines containing all source-cell edges. -/
def sourceEdgeLines : Set ℂ :=
  {z | ∃ s : Bool × Bool, (reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
    (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
    (reflect s z).re = (reflect s z).im ∨
    2 * (reflect s z).im = 1 + (reflect s z).re}

/-- The finitely many affine lines containing all image-cell edges. -/
def targetEdgeLines : Set ℂ :=
  {z | ∃ s : Bool × Bool, (reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
    (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
    (reflect s z).re = (reflect s z).im ∨
    2 * (reflect s z).re = 1 + (reflect s z).im}

theorem exists_mem_sourceCell_of_not_mem_edgeLines {z : ℂ}
    (hz : z ∈ square) (hne : z ∉ sourceEdgeLines) : ∃ s i, z ∈ sourceCell s i := by
  obtain ⟨s, i, hi⟩ := exists_mem_sourceClosedCell hz
  have hn : ¬((reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
      (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
      (reflect s z).re = (reflect s z).im ∨
      2 * (reflect s z).im = 1 + (reflect s z).re) := fun h => hne ⟨s, h⟩
  simp only [not_or] at hn
  refine ⟨s, i, ?_⟩
  change reflect s z ∈ baseCell i
  change reflect s z ∈ baseClosedCell i at hi
  fin_cases i <;> dsimp [baseClosedCell, baseCell] at hi ⊢
  all_goals rcases hi with ⟨h₁, h₂, h₃⟩
  all_goals rcases hn with ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩
  all_goals constructor <;> try (by_contra h; simp only [not_lt] at h; first
    | exact n₁ (by linarith) | exact n₂ (by linarith))
  all_goals constructor <;> (by_contra h; simp only [not_lt] at h; first
    | exact n₃ (by linarith) | exact n₄ (by linarith) | exact n₅ (by linarith)
    | exact n₆ (by linarith))

theorem exists_mem_targetCell_of_not_mem_edgeLines {z : ℂ}
    (hz : z ∈ square) (hne : z ∉ targetEdgeLines) : ∃ s i, z ∈ targetCell s i := by
  obtain ⟨s, i, hi⟩ := exists_mem_targetClosedCell hz
  have hn : ¬((reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
      (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
      (reflect s z).re = (reflect s z).im ∨
      2 * (reflect s z).re = 1 + (reflect s z).im) := fun h => hne ⟨s, h⟩
  simp only [not_or] at hn
  refine ⟨s, i, ?_⟩
  change reflect s z ∈ baseTargetCell i
  change reflect s z ∈ baseClosedTargetCell i at hi
  fin_cases i <;> dsimp [baseClosedTargetCell, baseTargetCell] at hi ⊢
  all_goals rcases hi with ⟨h₁, h₂, h₃⟩
  all_goals rcases hn with ⟨n₁, n₂, n₃, n₄, n₅, n₆⟩
  all_goals constructor <;> try (by_contra h; simp only [not_lt] at h; first
    | exact n₁ (by linarith) | exact n₂ (by linarith))
  all_goals constructor <;> (by_contra h; simp only [not_lt] at h; first
    | exact n₃ (by linarith) | exact n₄ (by linarith) | exact n₅ (by linarith)
    | exact n₆ (by linarith))

theorem iUnion_sourceClosedCell :
    (⋃ p : (Bool × Bool) × Fin 3, sourceClosedCell p.1 p.2) = square := by
  apply Set.Subset.antisymm
  · exact iUnion_subset fun p => sourceClosedCell_subset_square p.1 p.2
  · intro z hz
    obtain ⟨s, i, hi⟩ := exists_mem_sourceClosedCell hz
    exact mem_iUnion.mpr ⟨(s, i), hi⟩

theorem convex_square : Convex ℝ square := by
  have heq : square = Complex.reLm ⁻¹' Icc (-1 : ℝ) 1 ∩
      Complex.imLm ⁻¹' Icc (-1 : ℝ) 1 := by
    ext z
    change (|z.re| ≤ 1 ∧ |z.im| ≤ 1) ↔
      ((-1 ≤ z.re ∧ z.re ≤ 1) ∧ (-1 ≤ z.im ∧ z.im ≤ 1))
    simp only [abs_le]
  rw [heq]
  exact ((convex_Icc (-1 : ℝ) 1).linear_preimage Complex.reLm).inter
    ((convex_Icc (-1 : ℝ) 1).linear_preimage Complex.imLm)

/-- Local metric bounds on the original square suffice for the composed surgery. -/
theorem lipschitzOnWith_comp_slitMap {M : Type*} [PseudoEMetricSpace M]
    {f : ℂ → M} {K : ℝ≥0} (hf : LipschitzOnWith K f square)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (f ∘ slitMap) square := by
  classical
  choose B hB using fun p : (Bool × Bool) × Fin 3 => branch_lipschitz p.1 p.2
  refine ⟨Finset.univ.sup (fun p => K * B p), ?_⟩
  apply DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover convex_square
    (fun p : (Bool × Bool) × Fin 3 => sourceClosedCell p.1 p.2)
    (fun p => (sourceClosedCell_isClosed p.1 p.2).preimage continuous_subtype_val)
    (fun z hz => ?_) (fun p => K * B p) (fun p => ?_)
  · obtain ⟨s, i, hi⟩ := exists_mem_sourceClosedCell hz
    exact ⟨(s, i), hi⟩
  · have hl : LipschitzOnWith (K * B p) (f ∘ branch p.1 p.2)
        (square ∩ sourceClosedCell p.1 p.2) :=
      hf.comp (hB p).lipschitzOnWith (fun z hz => branch_mem_square p.1 p.2 hz.2)
    intro z hz w hw
    have hez := comp_slitMap_eqOn_closedCell f hpair p.1 p.2 hz.2
    have hew := comp_slitMap_eqOn_closedCell f hpair p.1 p.2 hw.2
    rw [hez, hew]
    exact hl hz hw

theorem continuousOn_comp_slitMap {M : Type*} [TopologicalSpace M]
    {f : ℂ → M} (hf : ContinuousOn f square)
    (hpair : ∀ r ∈ Icc (0 : ℝ) (1 / 2), f (r : ℂ) = f (-r : ℂ)) :
    ContinuousOn (f ∘ slitMap) square := by
  rw [← iUnion_sourceClosedCell]
  apply (locallyFinite_of_finite (fun p : (Bool × Bool) × Fin 3 =>
    sourceClosedCell p.1 p.2)).continuousOn_iUnion
    (fun p => sourceClosedCell_isClosed p.1 p.2)
  intro p
  obtain ⟨K, hK⟩ := branch_lipschitz p.1 p.2
  have hc : ContinuousOn (f ∘ branch p.1 p.2) (sourceClosedCell p.1 p.2) :=
    hf.comp hK.continuous.continuousOn (fun z hz => branch_mem_square p.1 p.2 hz)
  exact hc.congr (comp_slitMap_eqOn_closedCell f hpair p.1 p.2)

/-- The positive and negative traces of the chosen model seam point. -/
theorem branch_seam_values :
    branch (false, false) 1 (Complex.I / 4) = (1 / 4 : ℂ) ∧
    branch (true, false) 1 (Complex.I / 4) = (-1 / 4 : ℂ) := by
  constructor <;> apply Complex.ext <;> norm_num [branch, reflect, baseBranch]

theorem slitMap_eq_branch_near_seam_pos {z : ℂ}
    (hx : 0 < z.re) (hx' : z.re < 1 / 8)
    (hy : 1 / 8 < z.im) (hy' : z.im < 3 / 8) :
    slitMap z = branch (false, false) 1 z := by
  apply slitMap_eqOn_cell (false, false) 1
  change 0 < z.re ∧ z.re < z.im ∧ 2 * z.im < 1 + z.re
  exact ⟨hx, by linarith, by linarith⟩

theorem slitMap_eq_branch_near_seam_neg {z : ℂ}
    (hx : -1 / 8 < z.re) (hx' : z.re < 0)
    (hy : 1 / 8 < z.im) (hy' : z.im < 3 / 8) :
    slitMap z = branch (true, false) 1 z := by
  apply slitMap_eqOn_cell (true, false) 1
  change 0 < -z.re ∧ -z.re < z.im ∧ 2 * z.im < 1 + -z.re
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem volume_reflected_linear_fiber (s : Bool × Bool) (a b c : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) :
    volume {z : ℂ | a * (reflect s z).re + b * (reflect s z).im = c} = 0 := by
  let l : ℂ →ₗ[ℝ] ℝ := a • Complex.reLm + b • Complex.imLm
  let A : AffineSubspace ℝ ℂ :=
    ({c} : AffineSubspace ℝ ℝ).comap (l.toAffineMap.comp (reflectAffine s))
  have hmem (z : ℂ) : z ∈ A ↔ a * (reflect s z).re + b * (reflect s z).im = c := by
    simp [A, l, reflectAffine_apply]
  have hne : A ≠ ⊤ := by
    intro htop
    have hall (z : ℂ) : a * z.re + b * z.im = c := by
      have hm : reflect s z ∈ A := by rw [htop]; trivial
      simpa only [reflect_reflect] using (hmem (reflect s z)).mp hm
    have h₀ := hall 0
    have h₁ := hall 1
    have hI := hall Complex.I
    norm_num at h₀ h₁ hI
    rcases hab with ha | hb
    · exact ha (by linarith)
    · exact hb (by linarith)
  have hset : (A : Set ℂ) = {z | a * (reflect s z).re + b * (reflect s z).im = c} :=
    Set.ext hmem
  rw [← hset]
  exact MeasureTheory.Measure.addHaar_affineSubspace volume A hne

private theorem volume_reflected_coordinate_edges (s : Bool × Bool) :
    volume {z : ℂ | (reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
      (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
      (reflect s z).re = (reflect s z).im} = 0 := by
  have hr₀ := volume_reflected_linear_fiber s 1 0 0 (Or.inl one_ne_zero)
  have hi₀ := volume_reflected_linear_fiber s 0 1 0 (Or.inr one_ne_zero)
  have hr₁ := volume_reflected_linear_fiber s 1 0 1 (Or.inl one_ne_zero)
  have hi₁ := volume_reflected_linear_fiber s 0 1 1 (Or.inr one_ne_zero)
  have hd := volume_reflected_linear_fiber s 1 (-1) 0 (Or.inl one_ne_zero)
  simp only [one_mul, zero_mul, add_zero, zero_add, neg_one_mul,
    ← sub_eq_add_neg, sub_eq_zero] at hr₀ hi₀ hr₁ hi₁ hd
  simpa only [Set.ofPred_or] using
    measure_union_null hr₀ (measure_union_null hi₀ (measure_union_null hr₁
      (measure_union_null hi₁ hd)))

theorem volume_sourceEdgeLines : volume sourceEdgeLines = 0 := by
  have hset : sourceEdgeLines = ⋃ s : Bool × Bool,
      {z : ℂ | (reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
        (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
        (reflect s z).re = (reflect s z).im ∨
        2 * (reflect s z).im = 1 + (reflect s z).re} := by
    ext z
    simp only [sourceEdgeLines, mem_ofPred_eq, mem_iUnion]
  rw [hset]
  apply measure_iUnion_null
  intro s
  have hlast : volume {z : ℂ | 2 * (reflect s z).im = 1 + (reflect s z).re} = 0 := by
    have heq : {z : ℂ | 2 * (reflect s z).im = 1 + (reflect s z).re} =
        {z : ℂ | (-1) * (reflect s z).re + 2 * (reflect s z).im = 1} := by
      ext z
      constructor <;> intro h <;> dsimp at h ⊢ <;> linarith
    rw [heq]
    exact volume_reflected_linear_fiber s (-1) 2 1 (Or.inl (by norm_num))
  simpa only [Set.ofPred_or, union_assoc] using
    measure_union_null (volume_reflected_coordinate_edges s) hlast

theorem volume_targetEdgeLines : volume targetEdgeLines = 0 := by
  have hset : targetEdgeLines = ⋃ s : Bool × Bool,
      {z : ℂ | (reflect s z).re = 0 ∨ (reflect s z).im = 0 ∨
        (reflect s z).re = 1 ∨ (reflect s z).im = 1 ∨
        (reflect s z).re = (reflect s z).im ∨
        2 * (reflect s z).re = 1 + (reflect s z).im} := by
    ext z
    simp only [targetEdgeLines, mem_ofPred_eq, mem_iUnion]
  rw [hset]
  apply measure_iUnion_null
  intro s
  have hlast : volume {z : ℂ | 2 * (reflect s z).re = 1 + (reflect s z).im} = 0 := by
    have heq : {z : ℂ | 2 * (reflect s z).re = 1 + (reflect s z).im} =
        {z : ℂ | 2 * (reflect s z).re + (-1) * (reflect s z).im = 1} := by
      ext z
      constructor <;> intro h <;> dsimp at h ⊢ <;> linarith
    rw [heq]
    exact volume_reflected_linear_fiber s 2 (-1) 1 (Or.inl (by norm_num))
  simpa only [Set.ofPred_or, union_assoc] using
    measure_union_null (volume_reflected_coordinate_edges s) hlast

theorem sourceCell_ae_cover :
    ∀ᵐ z : ℂ, z ∈ square ↔ ∃ s i, z ∈ sourceCell s i := by
  have hn : ∀ᵐ z : ℂ, z ∉ sourceEdgeLines := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_sourceEdgeLines
  filter_upwards [hn] with z hz
  constructor
  · exact fun h => exists_mem_sourceCell_of_not_mem_edgeLines h hz
  · rintro ⟨s, i, hi⟩
    exact sourceClosedCell_subset_square s i (sourceCell_subset_closedCell s i hi)

theorem targetCell_ae_cover :
    ∀ᵐ z : ℂ, z ∈ square ↔ ∃ s i, z ∈ targetCell s i := by
  have hn : ∀ᵐ z : ℂ, z ∉ targetEdgeLines := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_targetEdgeLines
  filter_upwards [hn] with z hz
  constructor
  · exact fun h => exists_mem_targetCell_of_not_mem_edgeLines h hz
  · rintro ⟨s, i, hi⟩
    rw [← branch_image_cell] at hi
    obtain ⟨w, hw, rfl⟩ := hi
    exact branch_mem_square s i (sourceCell_subset_closedCell s i hw)

/-- The square transported by the literal dilation used in a small source patch. -/
def scaledSquare (r : ℝ) : Set ℂ := {z | z / (r : ℂ) ∈ square}

/-- The actual scaled slit formula, with no change of the original target map. -/
def scaledSlitMap (r : ℝ) (z : ℂ) : ℂ := (r : ℂ) * slitMap (z / (r : ℂ))

/-- The corresponding globally defined scaled affine branch. -/
def scaledBranch (r : ℝ) (s : Bool × Bool) (i : Fin 3) (z : ℂ) : ℂ :=
  (r : ℂ) * branch s i (z / (r : ℂ))

private theorem mul_div_real (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    (r : ℂ) * (z / (r : ℂ)) = z := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hc]

private theorem scaled_paired_values {M : Type*} {f : ℂ → M} {r : ℝ} (hr : 0 < r)
    (hpair : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-t : ℂ)) :
    ∀ t ∈ Icc (0 : ℝ) (1 / 2),
      f ((r : ℂ) * (t : ℂ)) = f ((r : ℂ) * (-t : ℂ)) := by
  intro t ht
  have hrt : r * t ∈ Icc (0 : ℝ) (r / 2) :=
    ⟨mul_nonneg hr.le ht.1, by nlinarith [ht.2]⟩
  simpa only [Complex.ofReal_mul, mul_neg] using hpair (r * t) hrt

theorem scaledSlitMap_eq_self_of_notMem {r : ℝ} (hr : r ≠ 0) {z : ℂ}
    (hz : z ∉ scaledSquare r) : scaledSlitMap r z = z := by
  rw [scaledSlitMap, slitMap_eq_self_of_notMem hz]
  exact mul_div_real r hr z

theorem scaledSlitMap_eq_self_on_outer {r : ℝ} (hr : 0 < r) {z : ℂ}
    (houter : |z.re| = r ∨ |z.im| = r) : scaledSlitMap r z = z := by
  have hdiv : |(z / (r : ℂ)).re| = 1 ∨ |(z / (r : ℂ)).im| = 1 := by
    rcases houter with h | h
    · left
      simp [Complex.div_ofReal_re, abs_div, abs_of_pos hr, h, hr.ne']
    · right
      simp [Complex.div_ofReal_im, abs_div, abs_of_pos hr, h, hr.ne']
  rw [scaledSlitMap, slitMap_eq_self_on_outer hdiv]
  exact mul_div_real r hr.ne' z

theorem scaledSlitMap_mem_scaledSquare {r : ℝ} (hr : r ≠ 0) {z : ℂ}
    (hz : z ∈ scaledSquare r) : scaledSlitMap r z ∈ scaledSquare r := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  change (r : ℂ) * slitMap (z / (r : ℂ)) / (r : ℂ) ∈ square
  rw [mul_div_cancel_left₀ _ hc]
  exact slitMap_mem_square hz

theorem scaledSlitMap_eq_scaledBranch {r : ℝ} (s : Bool × Bool) (i : Fin 3) {z : ℂ}
    (hz : z / (r : ℂ) ∈ sourceCell s i) :
    scaledSlitMap r z = scaledBranch r s i z :=
  congrArg (fun w : ℂ => (r : ℂ) * w) (slitMap_eqOn_cell s i hz)

theorem comp_scaledSlitMap_eq_scaledBranch {M : Type*} {f : ℂ → M} {r : ℝ}
    (hr : 0 < r) (hpair : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-t : ℂ))
    (s : Bool × Bool) (i : Fin 3) {z : ℂ}
    (hz : z / (r : ℂ) ∈ sourceClosedCell s i) :
    f (scaledSlitMap r z) = f (scaledBranch r s i z) :=
  comp_slitMap_eqOn_closedCell (fun w => f ((r : ℂ) * w))
    (scaled_paired_values hr hpair) s i hz

private theorem lipschitz_mul_complex (c : ℂ) :
    LipschitzWith ‖c‖₊ (fun z : ℂ => c * z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp [dist_eq_norm, ← mul_sub]

private theorem lipschitz_div_complex (c : ℂ) :
    LipschitzWith ‖c⁻¹‖₊ (fun z : ℂ => z / c) := by
  have hfun : (fun z : ℂ => c⁻¹ * z) = (fun z : ℂ => z / c) := by
    funext z
    rw [div_eq_mul_inv, mul_comm]
  exact hfun ▸ lipschitz_mul_complex c⁻¹

theorem lipschitzOnWith_comp_scaledSlitMap {M : Type*} [PseudoEMetricSpace M]
    {f : ℂ → M} {K : ℝ≥0} {r : ℝ} (hr : 0 < r)
    (hf : LipschitzOnWith K f (scaledSquare r))
    (hpair : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-t : ℂ)) :
    ∃ L : ℝ≥0, LipschitzOnWith L (f ∘ scaledSlitMap r) (scaledSquare r) := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hg : LipschitzOnWith (K * ‖(r : ℂ)‖₊) (fun w => f ((r : ℂ) * w)) square :=
    hf.comp (lipschitz_mul_complex (r : ℂ)).lipschitzOnWith
      (fun w hw => by simpa only [scaledSquare, mem_ofPred_eq, mul_div_cancel_left₀ _ hc] using hw)
  obtain ⟨L, hL⟩ := lipschitzOnWith_comp_slitMap hg (scaled_paired_values hr hpair)
  refine ⟨L * ‖((r : ℂ)⁻¹)‖₊, ?_⟩
  exact hL.comp (lipschitz_div_complex (r : ℂ)).lipschitzOnWith (fun _ hz => hz)

theorem continuousOn_comp_scaledSlitMap {M : Type*} [TopologicalSpace M]
    {f : ℂ → M} {r : ℝ} (hr : 0 < r) (hf : ContinuousOn f (scaledSquare r))
    (hpair : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-t : ℂ)) :
    ContinuousOn (f ∘ scaledSlitMap r) (scaledSquare r) := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hg : ContinuousOn (fun w => f ((r : ℂ) * w)) square :=
    hf.comp (continuous_const.mul continuous_id).continuousOn
      (fun w hw => by simpa only [scaledSquare, mem_ofPred_eq, mul_div_cancel_left₀ _ hc] using hw)
  exact (continuousOn_comp_slitMap hg (scaled_paired_values hr hpair)).comp
    (continuous_id.div_const (r : ℂ)).continuousOn (fun _ hz => hz)

theorem scaledBranch_seam_values {r : ℝ} (hr : r ≠ 0) :
    scaledBranch r (false, false) 1 ((r : ℂ) * (Complex.I / 4)) = (r : ℂ) / 4 ∧
    scaledBranch r (true, false) 1 ((r : ℂ) * (Complex.I / 4)) = -(r : ℂ) / 4 := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  simp only [scaledBranch, mul_div_cancel_left₀ _ hc,
    branch_seam_values.1, branch_seam_values.2]
  constructor <;> ring

theorem comp_scaledSlitMap_image_scaledSquare {M : Type*} {f : ℂ → M} {r : ℝ}
    (hr : 0 < r) (hpair : ∀ t ∈ Icc (0 : ℝ) (r / 2), f (t : ℂ) = f (-t : ℂ)) :
    (f ∘ scaledSlitMap r) '' scaledSquare r = f '' scaledSquare r := by
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨scaledSlitMap r z, scaledSlitMap_mem_scaledSquare hr.ne' hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hm : f z ∈ (fun w : ℂ => f ((r : ℂ) * w)) '' square :=
      ⟨z / (r : ℂ), hz, congrArg f (mul_div_real r hr.ne' z)⟩
    rw [← comp_slitMap_image_square (fun w : ℂ => f ((r : ℂ) * w))
      (scaled_paired_values hr hpair)] at hm
    obtain ⟨w, hw, heq⟩ := hm
    refine ⟨(r : ℂ) * w, ?_, ?_⟩
    · simpa only [scaledSquare, mem_ofPred_eq, mul_div_cancel_left₀ _ hc] using hw
    · simpa only [Function.comp_apply, scaledSlitMap, mul_div_cancel_left₀ _ hc] using heq

end DifferentialGeometry.Topology.Planar.SlitRegluing
