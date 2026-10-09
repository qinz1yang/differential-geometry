import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclid
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldBridge

/-!
# Profile and bridges of the flat compact fold

Lane CF, tier 2, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §3). The three moduli are linear in the canonical
distances `canon j = ‖z - vⱼ‖ - radⱼ` with slope `profileSlope = 2/5`:
`modOne = 3/2 + κ canon₁` (the circle about `+3/2`, image of `v₁`), `modTwo = 3/2 + κ canon₂`
(about `-3/2`, image of `v₂`) and `modThree = 3 - κ canon₃` (about `0`, the outer cone `v₃`). On
the triangle `|canon j| < 1` (`canon_mem`), so `modOne, modTwo ∈ (11/10, 19/10)` and
`modThree ∈ (13/5, 17/5)`.

The bridges are A4's `twoCircle` with the cofactor obtained from the segment identities of
`CompactFoldEuclid`: `bridgeOne` (wall `1`, circles `|u| = modThree`, `|u - 3/2| = modOne`),
`bridgeZero` (wall `0`, `|u| = modThree`, `|u + 3/2| = modTwo`) and `bridgeTwo` (wall `2`,
`|u - 3/2| = modOne`, `|u + 3/2| = modTwo`). On the open domains `domOne`, `domZero`, `domTwo`
(the cofactor denominators are positive and `‖z‖ < 2`), which contain the triangle minus the two
vertices of the wall, each bridge is smooth, lies on its two circles, and has the sign of the side
function of its wall as the sign of its imaginary part. Each bridge satisfies the wall identity
`bridge ∘ refl = conj ∘ bridge` everywhere. On the triangle `Re bridgeOne > 0`,
`Re bridgeZero < 0`, `‖bridgeTwo‖ < 3/2` and `‖bridgeOne‖, ‖bridgeZero‖ > 5/2`.
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace EuclidShape

variable (σ : EuclidShape)

def profileSlope : ℝ := 2 / 5

def modOne (z : ℂ) : ℝ := 3 / 2 + profileSlope * σ.canon 0 z

def modTwo (z : ℂ) : ℝ := 3 / 2 + profileSlope * σ.canon 1 z

def modThree (z : ℂ) : ℝ := 3 - profileSlope * σ.canon 2 z

def cofBridgeOne (z : ℂ) : ℝ :=
  ((σ.modThree z + σ.modOne z) ^ 2 - 9 / 4) * (3 / 2 + σ.modThree z - σ.modOne z) *
    (profileSlope * σ.cofOneThree z)

def cofBridgeZero (z : ℂ) : ℝ :=
  ((σ.modThree z + σ.modTwo z) ^ 2 - 9 / 4) * (3 / 2 + σ.modThree z - σ.modTwo z) *
    (profileSlope * σ.cofZeroThree z)

def cofBridgeTwo (z : ℂ) : ℝ :=
  (σ.modOne z + σ.modTwo z + 3) * (9 - (σ.modOne z - σ.modTwo z) ^ 2) *
    (profileSlope * σ.cofOneTwo z)

def bridgeOne (z : ℂ) : ℂ :=
  twoCircle 0 (3 / 2) (σ.modThree z) (σ.modOne z) (σ.wallSide 1 z) (σ.cofBridgeOne z)

def bridgeZero (z : ℂ) : ℂ :=
  twoCircle 0 (-(3 / 2)) (σ.modThree z) (σ.modTwo z) (σ.wallSide 0 z) (σ.cofBridgeZero z)

def bridgeTwo (z : ℂ) : ℂ :=
  twoCircle (3 / 2) (-(3 / 2)) (σ.modOne z) (σ.modTwo z) (σ.wallSide 2 z) (σ.cofBridgeTwo z)

def domOne : Set ℂ :=
  {z | 0 < ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re ∧
    0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re) ∧ ‖z‖ < 2}

def domZero : Set ℂ :=
  {z | 0 < ‖z‖ + z.re ∧ 0 < ‖z - σ.vertexTwo‖ + (Real.sin σ.θ₁ - z.re) ∧ ‖z‖ < 2}

def domTwo : Set ℂ :=
  {z | 0 < ‖z - σ.vertexTwo‖ + (σ.rotTwo z).re ∧
    0 < ‖z - σ.vertexOne‖ + (Real.sin σ.θ₃ - (σ.rotTwo z).re) ∧ ‖z‖ < 2}

theorem continuous_rotTwo : Continuous σ.rotTwo := by
  unfold rotTwo
  fun_prop

theorem isOpen_domOne : IsOpen σ.domOne := by
  have h1 : Continuous fun z : ℂ => ‖z‖ + (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by fun_prop
  have h2 : Continuous fun z : ℂ =>
      ‖z - σ.vertexOne‖ + (Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re) := by fun_prop
  have h3 : Continuous fun z : ℂ => ‖z‖ := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    (isOpen_lt h3 continuous_const))

theorem isOpen_domZero : IsOpen σ.domZero := by
  have h1 : Continuous fun z : ℂ => ‖z‖ + z.re := by fun_prop
  have h2 : Continuous fun z : ℂ => ‖z - σ.vertexTwo‖ + (Real.sin σ.θ₁ - z.re) := by fun_prop
  have h3 : Continuous fun z : ℂ => ‖z‖ := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    (isOpen_lt h3 continuous_const))

theorem isOpen_domTwo : IsOpen σ.domTwo := by
  have h := σ.continuous_rotTwo
  have h1 : Continuous fun z : ℂ => ‖z - σ.vertexTwo‖ + (σ.rotTwo z).re := by fun_prop
  have h2 : Continuous fun z : ℂ => ‖z - σ.vertexOne‖ + (Real.sin σ.θ₃ - (σ.rotTwo z).re) := by
    fun_prop
  have h3 : Continuous fun z : ℂ => ‖z‖ := by fun_prop
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    (isOpen_lt h3 continuous_const))

theorem norm_lt_two_of_mem {z : ℂ} (hz : z ∈ σ.triangle) : ‖z‖ < 2 := by
  linarith [σ.norm_le_one_of_mem hz]

theorem triangle_subset_domOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) : z ∈ σ.domOne :=
  ⟨σ.cof_pos_one_three_left hz h0, σ.cof_pos_one_three_right hz h1, σ.norm_lt_two_of_mem hz⟩

theorem triangle_subset_domZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h2 : z ≠ σ.vertexTwo) : z ∈ σ.domZero :=
  ⟨σ.cof_pos_zero_three_left hz h0, σ.cof_pos_zero_three_right hz h2, σ.norm_lt_two_of_mem hz⟩

theorem triangle_subset_domTwo {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : z ∈ σ.domTwo :=
  ⟨σ.cof_pos_one_two_left hz h2, σ.cof_pos_one_two_right hz h1, σ.norm_lt_two_of_mem hz⟩

theorem cofOneThree_pos {z : ℂ} (hz : z ∈ σ.domOne) : 0 < σ.cofOneThree z := by
  have := hz.1
  have := hz.2.1
  unfold cofOneThree
  positivity

theorem cofZeroThree_pos {z : ℂ} (hz : z ∈ σ.domZero) : 0 < σ.cofZeroThree z := by
  have := hz.1
  have := hz.2.1
  unfold cofZeroThree
  positivity

theorem cofOneTwo_pos {z : ℂ} (hz : z ∈ σ.domTwo) : 0 < σ.cofOneTwo z := by
  have := hz.1
  have := hz.2.1
  unfold cofOneTwo
  positivity

theorem rad_le_one_aux {a b c : ℝ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : 0 < c) :
    (a + b - c) / 2 < 1 := by linarith

theorem radOne_lt_one : σ.radOne < 1 :=
  rad_le_one_aux (Real.sin_le_one _) (Real.sin_le_one _) σ.sin_θ₁_pos

theorem radTwo_lt_one : σ.radTwo < 1 :=
  rad_le_one_aux (Real.sin_le_one _) (Real.sin_le_one _) σ.sin_θ₂_pos

theorem radThree_lt_one : σ.radThree < 1 :=
  rad_le_one_aux (Real.sin_le_one _) (Real.sin_le_one _) σ.sin_θ₃_pos

theorem canon_ge (j : Fin 3) (z : ℂ) : -1 < σ.canon j z := by
  fin_cases j
  · change -1 < ‖z - σ.vertexOne‖ - σ.radOne
    linarith [norm_nonneg (z - σ.vertexOne), σ.radOne_lt_one]
  · change -1 < ‖z - σ.vertexTwo‖ - σ.radTwo
    linarith [norm_nonneg (z - σ.vertexTwo), σ.radTwo_lt_one]
  · change -1 < ‖z‖ - σ.radThree
    linarith [norm_nonneg z, σ.radThree_lt_one]

theorem canon_lt_of_mem (j : Fin 3) {z : ℂ} (hz : z ∈ σ.triangle) : σ.canon j z < 1 := by
  fin_cases j
  · change ‖z - σ.vertexOne‖ - σ.radOne < 1
    linarith [σ.norm_sub_vertexOne_le hz, σ.radOne_pos]
  · change ‖z - σ.vertexTwo‖ - σ.radTwo < 1
    linarith [σ.norm_sub_vertexTwo_le hz, σ.radTwo_pos]
  · change ‖z‖ - σ.radThree < 1
    linarith [σ.norm_le_one_of_mem hz, σ.radThree_pos]

theorem canon_le_of_norm (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 2) : σ.canon j z < 3 := by
  have h1 : ‖σ.vertexOne‖ ≤ 1 := by rw [norm_vertexOne]; exact Real.sin_le_one _
  have h2 : ‖σ.vertexTwo‖ ≤ 1 := by rw [norm_vertexTwo]; exact Real.sin_le_one _
  fin_cases j
  · change ‖z - σ.vertexOne‖ - σ.radOne < 3
    linarith [norm_sub_le z σ.vertexOne, σ.radOne_pos]
  · change ‖z - σ.vertexTwo‖ - σ.radTwo < 3
    linarith [norm_sub_le z σ.vertexTwo, σ.radTwo_pos]
  · change ‖z‖ - σ.radThree < 3
    linarith [σ.radThree_pos]

theorem canon_two_sub_canon_zero_le (z : ℂ) : σ.canon 2 z - σ.canon 0 z ≤ 2 := by
  change ‖z‖ - σ.radThree - (‖z - σ.vertexOne‖ - σ.radOne) ≤ 2
  have h := norm_le_norm_add_norm_sub' z σ.vertexOne
  have h1 : ‖σ.vertexOne‖ ≤ 1 := by rw [norm_vertexOne]; exact Real.sin_le_one _
  have := σ.radOne_lt_one
  have := σ.radThree_pos
  have h3 : ‖z‖ ≤ ‖σ.vertexOne‖ + ‖z - σ.vertexOne‖ := by
    have := norm_add_le σ.vertexOne (z - σ.vertexOne)
    rwa [add_sub_cancel] at this
  linarith

theorem canon_two_sub_canon_one_le (z : ℂ) : σ.canon 2 z - σ.canon 1 z ≤ 2 := by
  change ‖z‖ - σ.radThree - (‖z - σ.vertexTwo‖ - σ.radTwo) ≤ 2
  have h1 : ‖σ.vertexTwo‖ ≤ 1 := by rw [norm_vertexTwo]; exact Real.sin_le_one _
  have := σ.radTwo_lt_one
  have := σ.radThree_pos
  have h3 : ‖z‖ ≤ ‖σ.vertexTwo‖ + ‖z - σ.vertexTwo‖ := by
    have := norm_add_le σ.vertexTwo (z - σ.vertexTwo)
    rwa [add_sub_cancel] at this
  linarith

theorem abs_canon_zero_sub_canon_one_le (z : ℂ) : |σ.canon 0 z - σ.canon 1 z| ≤ 2 := by
  change |‖z - σ.vertexOne‖ - σ.radOne - (‖z - σ.vertexTwo‖ - σ.radTwo)| ≤ 2
  have h := abs_norm_sub_norm_le (z - σ.vertexOne) (z - σ.vertexTwo)
  have e : z - σ.vertexOne - (z - σ.vertexTwo) = σ.vertexTwo - σ.vertexOne := by ring
  have hn : ‖σ.vertexTwo - σ.vertexOne‖ = Real.sin σ.θ₃ := by
    rw [← norm_neg, neg_sub, norm_vertexOne_sub_vertexTwo]
  rw [e, hn] at h
  have := Real.sin_le_one σ.θ₃
  have := σ.radOne_lt_one
  have := σ.radTwo_lt_one
  have := σ.radOne_pos
  have := σ.radTwo_pos
  rw [abs_le] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem cofBridgeOne_pos {z : ℂ} (hz : z ∈ σ.domOne) : 0 < σ.cofBridgeOne z := by
  have hc := σ.cofOneThree_pos hz
  have h0 := σ.canon_le_of_norm 0 hz.2.2
  have h2 := σ.canon_le_of_norm 2 hz.2.2
  have g0 := σ.canon_ge 0 z
  have g2 := σ.canon_ge 2 z
  have hd := σ.canon_two_sub_canon_zero_le z
  have e1 : 3 / 2 < σ.modThree z + σ.modOne z := by
    unfold modThree modOne profileSlope
    linarith
  have e2 : 0 < 3 / 2 + σ.modThree z - σ.modOne z := by
    unfold modThree modOne profileSlope
    linarith
  have e3 : 0 < (σ.modThree z + σ.modOne z) ^ 2 - 9 / 4 := by nlinarith
  unfold cofBridgeOne profileSlope
  positivity

theorem cofBridgeZero_pos {z : ℂ} (hz : z ∈ σ.domZero) : 0 < σ.cofBridgeZero z := by
  have hc := σ.cofZeroThree_pos hz
  have h1 := σ.canon_le_of_norm 1 hz.2.2
  have h2 := σ.canon_le_of_norm 2 hz.2.2
  have g1 := σ.canon_ge 1 z
  have g2 := σ.canon_ge 2 z
  have hd := σ.canon_two_sub_canon_one_le z
  have e1 : 3 / 2 < σ.modThree z + σ.modTwo z := by
    unfold modThree modTwo profileSlope
    linarith
  have e2 : 0 < 3 / 2 + σ.modThree z - σ.modTwo z := by
    unfold modThree modTwo profileSlope
    linarith
  have e3 : 0 < (σ.modThree z + σ.modTwo z) ^ 2 - 9 / 4 := by nlinarith
  unfold cofBridgeZero profileSlope
  positivity

theorem cofBridgeTwo_pos {z : ℂ} (hz : z ∈ σ.domTwo) : 0 < σ.cofBridgeTwo z := by
  have hc := σ.cofOneTwo_pos hz
  have g0 := σ.canon_ge 0 z
  have g1 := σ.canon_ge 1 z
  have hd := σ.abs_canon_zero_sub_canon_one_le z
  rw [abs_le] at hd
  have e1 : 0 < σ.modOne z + σ.modTwo z + 3 := by
    unfold modOne modTwo profileSlope
    linarith
  have e2 : 0 < 9 - (σ.modOne z - σ.modTwo z) ^ 2 := by
    have : σ.modOne z - σ.modTwo z = profileSlope * (σ.canon 0 z - σ.canon 1 z) := by
      unfold modOne modTwo
      ring
    rw [this]
    unfold profileSlope
    nlinarith [hd.1, hd.2]
  unfold cofBridgeTwo profileSlope
  positivity

theorem heron_bridgeOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ((σ.modThree z + σ.modOne z) ^ 2 - (3 / 2 - 0) ^ 2) *
        ((3 / 2 - 0) ^ 2 - (σ.modThree z - σ.modOne z) ^ 2) =
      σ.wallSide 1 z ^ 2 * σ.cofBridgeOne z := by
  have h := σ.canon_add_canon_one_three hz.1 hz.2.1
  have e : 3 / 2 - σ.modThree z + σ.modOne z = profileSlope * (σ.canon 0 z + σ.canon 2 z) := by
    unfold modThree modOne
    ring
  rw [h] at e
  unfold cofBridgeOne
  have : (3 / 2 - 0 : ℝ) ^ 2 - (σ.modThree z - σ.modOne z) ^ 2 =
      (3 / 2 - σ.modThree z + σ.modOne z) * (3 / 2 + σ.modThree z - σ.modOne z) := by ring
  rw [this, e]
  ring

theorem heron_bridgeZero {z : ℂ} (hz : z ∈ σ.domZero) :
    ((σ.modThree z + σ.modTwo z) ^ 2 - (-(3 / 2) - 0) ^ 2) *
        ((-(3 / 2) - 0) ^ 2 - (σ.modThree z - σ.modTwo z) ^ 2) =
      σ.wallSide 0 z ^ 2 * σ.cofBridgeZero z := by
  have h := σ.canon_add_canon_zero_three hz.1 hz.2.1
  have e : 3 / 2 - σ.modThree z + σ.modTwo z = profileSlope * (σ.canon 1 z + σ.canon 2 z) := by
    unfold modThree modTwo
    ring
  rw [h] at e
  unfold cofBridgeZero
  have : (-(3 / 2) - 0 : ℝ) ^ 2 - (σ.modThree z - σ.modTwo z) ^ 2 =
      (3 / 2 - σ.modThree z + σ.modTwo z) * (3 / 2 + σ.modThree z - σ.modTwo z) := by ring
  rw [show (-(3 / 2) - 0 : ℝ) ^ 2 = (3 / 2) ^ 2 by ring] at this ⊢
  rw [this, e]
  ring

theorem heron_bridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ((σ.modOne z + σ.modTwo z) ^ 2 - (-(3 / 2) - 3 / 2) ^ 2) *
        ((-(3 / 2) - 3 / 2) ^ 2 - (σ.modOne z - σ.modTwo z) ^ 2) =
      σ.wallSide 2 z ^ 2 * σ.cofBridgeTwo z := by
  have h := σ.canon_add_canon_one_two hz.1 hz.2.1
  have e : σ.modOne z + σ.modTwo z - 3 = profileSlope * (σ.canon 0 z + σ.canon 1 z) := by
    unfold modOne modTwo
    ring
  rw [h] at e
  unfold cofBridgeTwo
  have : (σ.modOne z + σ.modTwo z) ^ 2 - (-(3 / 2) - 3 / 2 : ℝ) ^ 2 =
      (σ.modOne z + σ.modTwo z - 3) * (σ.modOne z + σ.modTwo z + 3) := by ring
  rw [this, e]
  ring


theorem exp_neg_mul_vertexOne :
    exp (-((σ.θ₃ : ℂ) * I)) * σ.vertexOne = (Real.sin σ.θ₂ : ℂ) := by
  rw [vertexOne, mul_left_comm, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

theorem ne_zero_of_mem_domOne {z : ℂ} (hz : z ∈ σ.domOne) : z ≠ 0 := by
  rintro rfl
  have := hz.1
  simp at this

theorem ne_vertexOne_of_mem_domOne {z : ℂ} (hz : z ∈ σ.domOne) : z ≠ σ.vertexOne := by
  rintro rfl
  have := hz.2.1
  rw [sub_self, norm_zero, zero_add, σ.exp_neg_mul_vertexOne, ofReal_re, sub_self] at this
  exact lt_irrefl _ this

theorem ne_zero_of_mem_domZero {z : ℂ} (hz : z ∈ σ.domZero) : z ≠ 0 := by
  rintro rfl
  have := hz.1
  simp at this

theorem ne_vertexTwo_of_mem_domZero {z : ℂ} (hz : z ∈ σ.domZero) : z ≠ σ.vertexTwo := by
  rintro rfl
  have := hz.2.1
  rw [sub_self, norm_zero, zero_add, vertexTwo, ofReal_re, sub_self] at this
  exact lt_irrefl _ this

theorem ne_vertexTwo_of_mem_domTwo {z : ℂ} (hz : z ∈ σ.domTwo) : z ≠ σ.vertexTwo := by
  rintro rfl
  have := hz.1
  rw [sub_self, norm_zero, zero_add, rotTwo_vertexTwo, zero_re] at this
  exact lt_irrefl _ this

theorem ne_vertexOne_of_mem_domTwo {z : ℂ} (hz : z ∈ σ.domTwo) : z ≠ σ.vertexOne := by
  rintro rfl
  have := hz.2.1
  rw [sub_self, norm_zero, zero_add, rotTwo_vertexOne, ofReal_re, sub_self] at this
  exact lt_irrefl _ this

theorem modOne_pos (z : ℂ) : 0 < σ.modOne z := by
  have := σ.canon_ge 0 z
  unfold modOne profileSlope
  linarith

theorem modTwo_pos (z : ℂ) : 0 < σ.modTwo z := by
  have := σ.canon_ge 1 z
  unfold modTwo profileSlope
  linarith

theorem modThree_pos {z : ℂ} (hz : ‖z‖ < 2) : 0 < σ.modThree z := by
  have := σ.canon_le_of_norm 2 hz
  unfold modThree profileSlope
  linarith

theorem norm_bridgeOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ‖σ.bridgeOne z‖ = σ.modThree z ∧ ‖σ.bridgeOne z - 3 / 2‖ = σ.modOne z := by
  have hab : (0 : ℝ) ≠ 3 / 2 := by norm_num
  have hP := (σ.cofBridgeOne_pos hz).le
  have hH := σ.heron_bridgeOne hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP (σ.modThree_pos hz.2.2).le hH
    simpa [bridgeOne] using h
  · have h := norm_twoCircle_sub_right hab hP (σ.modOne_pos z).le hH
    rw [bridgeOne]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h
    exact h

theorem norm_bridgeZero {z : ℂ} (hz : z ∈ σ.domZero) :
    ‖σ.bridgeZero z‖ = σ.modThree z ∧ ‖σ.bridgeZero z + 3 / 2‖ = σ.modTwo z := by
  have hab : (0 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (σ.cofBridgeZero_pos hz).le
  have hH := σ.heron_bridgeZero hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP (σ.modThree_pos hz.2.2).le hH
    simpa [bridgeZero] using h
  · have h := norm_twoCircle_sub_right hab hP (σ.modTwo_pos z).le hH
    rw [bridgeZero]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h
    exact h

theorem norm_bridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ‖σ.bridgeTwo z - 3 / 2‖ = σ.modOne z ∧ ‖σ.bridgeTwo z + 3 / 2‖ = σ.modTwo z := by
  have hab : (3 / 2 : ℝ) ≠ -(3 / 2) := by norm_num
  have hP := (σ.cofBridgeTwo_pos hz).le
  have hH := σ.heron_bridgeTwo hz
  constructor
  · have h := norm_twoCircle_sub_left hab hP (σ.modOne_pos z).le hH
    rw [bridgeTwo]
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring] at h
    exact h
  · have h := norm_twoCircle_sub_right hab hP (σ.modTwo_pos z).le hH
    rw [bridgeTwo]
    rw [show ((-(3 / 2) : ℝ) : ℂ) = -(3 / 2) by push_cast; ring, sub_neg_eq_add] at h
    exact h

theorem im_bridgeOne_pos {z : ℂ} (hz : z ∈ σ.domOne) (hw : 0 < σ.wallSide 1 z) :
    0 < (σ.bridgeOne z).im :=
  twoCircle_im_pos (by norm_num) hw (σ.cofBridgeOne_pos hz)

theorem im_bridgeZero_pos {z : ℂ} (hz : z ∈ σ.domZero) (hw : 0 < σ.wallSide 0 z) :
    0 < (σ.bridgeZero z).im :=
  twoCircle_im_pos (by norm_num) hw (σ.cofBridgeZero_pos hz)

theorem im_bridgeTwo_pos {z : ℂ} (hz : z ∈ σ.domTwo) (hw : 0 < σ.wallSide 2 z) :
    0 < (σ.bridgeTwo z).im :=
  twoCircle_im_pos (by norm_num) hw (σ.cofBridgeTwo_pos hz)

theorem im_bridgeOne_eq_zero {z : ℂ} (hw : σ.wallSide 1 z = 0) : (σ.bridgeOne z).im = 0 := by
  rw [bridgeOne, hw, twoCircle_im_eq_zero]

theorem im_bridgeZero_eq_zero {z : ℂ} (hw : σ.wallSide 0 z = 0) : (σ.bridgeZero z).im = 0 := by
  rw [bridgeZero, hw, twoCircle_im_eq_zero]

theorem im_bridgeTwo_eq_zero {z : ℂ} (hw : σ.wallSide 2 z = 0) : (σ.bridgeTwo z).im = 0 := by
  rw [bridgeTwo, hw, twoCircle_im_eq_zero]

theorem canon_zero_refl (i : Fin 3) (z : ℂ) (h : σ.wallSide i σ.vertexOne = 0) :
    σ.canon 0 (σ.refl i z) = σ.canon 0 z := by
  change ‖σ.refl i z - σ.vertexOne‖ - σ.radOne = ‖z - σ.vertexOne‖ - σ.radOne
  rw [σ.norm_refl_sub i z _ h]

theorem canon_one_refl (i : Fin 3) (z : ℂ) (h : σ.wallSide i σ.vertexTwo = 0) :
    σ.canon 1 (σ.refl i z) = σ.canon 1 z := by
  change ‖σ.refl i z - σ.vertexTwo‖ - σ.radTwo = ‖z - σ.vertexTwo‖ - σ.radTwo
  rw [σ.norm_refl_sub i z _ h]

theorem canon_two_refl (i : Fin 3) (z : ℂ) (h : σ.wallSide i 0 = 0) :
    σ.canon 2 (σ.refl i z) = σ.canon 2 z := by
  change ‖σ.refl i z‖ - σ.radThree = ‖z‖ - σ.radThree
  have h' := σ.norm_refl_sub i z _ h
  rw [sub_zero, sub_zero] at h'
  rw [h']

theorem bridgeOne_refl_one (z : ℂ) : σ.bridgeOne (σ.refl 1 z) = conj (σ.bridgeOne z) := by
  have h0 : σ.canon 0 (σ.refl 1 z) = σ.canon 0 z := σ.canon_zero_refl 1 z σ.wallSide_one_vertexOne
  have h2 : σ.canon 2 (σ.refl 1 z) = σ.canon 2 z := σ.canon_two_refl 1 z σ.wallSide_one_zero
  have hn : ‖σ.refl 1 z‖ = ‖z‖ := by
    have := σ.norm_refl_sub 1 z 0 σ.wallSide_one_zero
    simpa using this
  have hn1 : ‖σ.refl 1 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 1 z _ σ.wallSide_one_vertexOne
  have hre : (exp (-((σ.θ₃ : ℂ) * I)) * σ.refl 1 z).re = (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
    change (exp (-((σ.θ₃ : ℂ) * I)) * (exp (2 * (σ.θ₃ : ℂ) * I) * conj z)).re = _
    have e : exp (-((σ.θ₃ : ℂ) * I)) * exp (2 * (σ.θ₃ : ℂ) * I) =
        conj (exp (-((σ.θ₃ : ℂ) * I))) := by
      rw [← Complex.exp_add, ← Complex.exp_conj]
      congr 1
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [← mul_assoc, e, ← map_mul, Complex.conj_re]
  have hc : σ.cofOneThree (σ.refl 1 z) = σ.cofOneThree z := by
    rw [cofOneThree, cofOneThree, hn, hn1, hre]
  have hb : σ.cofBridgeOne (σ.refl 1 z) = σ.cofBridgeOne z := by
    rw [cofBridgeOne, cofBridgeOne, modThree, modThree, modOne, modOne, h0, h2, hc]
  rw [bridgeOne, bridgeOne, modThree, modThree, modOne, modOne, h0, h2, hb, wallSide_refl,
    twoCircle_neg]

theorem bridgeZero_refl_zero (z : ℂ) : σ.bridgeZero (σ.refl 0 z) = conj (σ.bridgeZero z) := by
  have h1 : σ.canon 1 (σ.refl 0 z) = σ.canon 1 z := σ.canon_one_refl 0 z σ.wallSide_zero_vertexTwo
  have h2 : σ.canon 2 (σ.refl 0 z) = σ.canon 2 z := σ.canon_two_refl 0 z σ.wallSide_zero_zero
  have hn : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z
  have hn2 : ‖σ.refl 0 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 0 z _ σ.wallSide_zero_vertexTwo
  have hre : (σ.refl 0 z).re = z.re := Complex.conj_re z
  have hc : σ.cofZeroThree (σ.refl 0 z) = σ.cofZeroThree z := by
    rw [cofZeroThree, cofZeroThree, hn, hn2, hre]
  have hb : σ.cofBridgeZero (σ.refl 0 z) = σ.cofBridgeZero z := by
    rw [cofBridgeZero, cofBridgeZero, modThree, modThree, modTwo, modTwo, h1, h2, hc]
  rw [bridgeZero, bridgeZero, modThree, modThree, modTwo, modTwo, h1, h2, hb, wallSide_refl,
    twoCircle_neg]

theorem bridgeTwo_refl_two (z : ℂ) : σ.bridgeTwo (σ.refl 2 z) = conj (σ.bridgeTwo z) := by
  have h0 : σ.canon 0 (σ.refl 2 z) = σ.canon 0 z := σ.canon_zero_refl 2 z σ.wallSide_two_vertexOne
  have h1 : σ.canon 1 (σ.refl 2 z) = σ.canon 1 z := σ.canon_one_refl 2 z σ.wallSide_two_vertexTwo
  have hn1 : ‖σ.refl 2 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexOne
  have hn2 : ‖σ.refl 2 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexTwo
  have hre : (σ.rotTwo (σ.refl 2 z)).re = (σ.rotTwo z).re := by
    rw [rotTwo_refl_two, Complex.conj_re]
  have hc : σ.cofOneTwo (σ.refl 2 z) = σ.cofOneTwo z := by
    rw [cofOneTwo, cofOneTwo, hn1, hn2, hre]
  have hb : σ.cofBridgeTwo (σ.refl 2 z) = σ.cofBridgeTwo z := by
    rw [cofBridgeTwo, cofBridgeTwo, modOne, modOne, modTwo, modTwo, h0, h1, hc]
  rw [bridgeTwo, bridgeTwo, modOne, modOne, modTwo, modTwo, h0, h1, hb, wallSide_refl,
    twoCircle_neg]


theorem contDiff_re_aux : ContDiff ℝ ∞ (fun z : ℂ => z.re) := reCLM.contDiff

theorem contDiff_im_aux : ContDiff ℝ ∞ (fun z : ℂ => z.im) := imCLM.contDiff

theorem contDiff_mul_aux (c : ℂ) : ContDiff ℝ ∞ (fun z : ℂ => c * z) :=
  contDiff_const.mul contDiff_id

theorem contDiff_rotTwo : ContDiff ℝ ∞ σ.rotTwo := by
  have h : σ.rotTwo = fun z => -(exp ((σ.θ₂ : ℂ) * I) * (z - σ.vertexTwo)) := rfl
  rw [h]
  exact ((contDiff_mul_aux _).comp (contDiff_id.sub contDiff_const)).neg

theorem contDiff_wallSide (i : Fin 3) : ContDiff ℝ ∞ (σ.wallSide i) := by
  fin_cases i
  · exact contDiff_im_aux
  · have h : σ.wallSide 1 = fun z => Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im :=
      funext σ.wallSide_one_apply
    change ContDiff ℝ ∞ (σ.wallSide 1)
    rw [h]
    exact (contDiff_const.mul contDiff_re_aux).sub (contDiff_const.mul contDiff_im_aux)
  · change ContDiff ℝ ∞ (fun z => (σ.rotTwo z).im)
    exact contDiff_im_aux.comp σ.contDiff_rotTwo

theorem contDiffAt_canon_zero {z : ℂ} (h : z ≠ σ.vertexOne) :
    ContDiffAt ℝ ∞ (σ.canon 0) z := by
  change ContDiffAt ℝ ∞ (fun u => ‖u - σ.vertexOne‖ - σ.radOne) z
  exact ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h)).sub contDiffAt_const

theorem contDiffAt_canon_one {z : ℂ} (h : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ (σ.canon 1) z := by
  change ContDiffAt ℝ ∞ (fun u => ‖u - σ.vertexTwo‖ - σ.radTwo) z
  exact ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h)).sub contDiffAt_const

theorem contDiffAt_canon_two {z : ℂ} (h : z ≠ 0) : ContDiffAt ℝ ∞ (σ.canon 2) z := by
  change ContDiffAt ℝ ∞ (fun u => ‖u‖ - σ.radThree) z
  exact (contDiffAt_norm ℝ h).sub contDiffAt_const

theorem contDiffAt_cofOneThree {z : ℂ} (hz : z ∈ σ.domOne) :
    ContDiffAt ℝ ∞ σ.cofOneThree z := by
  have h0 := σ.ne_zero_of_mem_domOne hz
  have h1 := σ.ne_vertexOne_of_mem_domOne hz
  have hr : ContDiffAt ℝ ∞ (fun u : ℂ => (exp (-((σ.θ₃ : ℂ) * I)) * u).re) z :=
    (contDiff_re_aux.comp (contDiff_mul_aux _)).contDiffAt
  have hn0 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ h0
  have hn1 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u - σ.vertexOne‖) z :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h1)
  exact (contDiffAt_const.div (hn0.add hr) hz.1.ne').add
    (contDiffAt_const.div (hn1.add (contDiffAt_const.sub hr)) hz.2.1.ne')

theorem contDiffAt_cofZeroThree {z : ℂ} (hz : z ∈ σ.domZero) :
    ContDiffAt ℝ ∞ σ.cofZeroThree z := by
  have h0 := σ.ne_zero_of_mem_domZero hz
  have h2 := σ.ne_vertexTwo_of_mem_domZero hz
  have hr : ContDiffAt ℝ ∞ (fun u : ℂ => u.re) z := contDiff_re_aux.contDiffAt
  have hn0 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ h0
  have hn2 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u - σ.vertexTwo‖) z :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h2)
  exact (contDiffAt_const.div (hn0.add hr) hz.1.ne').add
    (contDiffAt_const.div (hn2.add (contDiffAt_const.sub hr)) hz.2.1.ne')

theorem contDiffAt_cofOneTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContDiffAt ℝ ∞ σ.cofOneTwo z := by
  have h1 := σ.ne_vertexOne_of_mem_domTwo hz
  have h2 := σ.ne_vertexTwo_of_mem_domTwo hz
  have hr : ContDiffAt ℝ ∞ (fun u : ℂ => (σ.rotTwo u).re) z :=
    (contDiff_re_aux.comp σ.contDiff_rotTwo).contDiffAt
  have hn1 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u - σ.vertexOne‖) z :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h1)
  have hn2 : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u - σ.vertexTwo‖) z :=
    (contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 h2)
  exact (contDiffAt_const.div (hn2.add hr) hz.1.ne').add
    (contDiffAt_const.div (hn1.add (contDiffAt_const.sub hr)) hz.2.1.ne')

theorem contDiffAt_bridgeOne {z : ℂ} (hz : z ∈ σ.domOne) : ContDiffAt ℝ ∞ σ.bridgeOne z := by
  have h0 := σ.contDiffAt_canon_zero (σ.ne_vertexOne_of_mem_domOne hz)
  have h2 := σ.contDiffAt_canon_two (σ.ne_zero_of_mem_domOne hz)
  have hA : ContDiffAt ℝ ∞ σ.modThree z := contDiffAt_const.sub (contDiffAt_const.mul h2)
  have hB : ContDiffAt ℝ ∞ σ.modOne z := contDiffAt_const.add (contDiffAt_const.mul h0)
  have hP : ContDiffAt ℝ ∞ σ.cofBridgeOne z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul (σ.contDiffAt_cofOneThree hz))
  exact contDiffAt_twoCircle hA hB (σ.contDiff_wallSide 1).contDiffAt hP
    (σ.cofBridgeOne_pos hz) (by norm_num)

theorem contDiffAt_bridgeZero {z : ℂ} (hz : z ∈ σ.domZero) :
    ContDiffAt ℝ ∞ σ.bridgeZero z := by
  have h1 := σ.contDiffAt_canon_one (σ.ne_vertexTwo_of_mem_domZero hz)
  have h2 := σ.contDiffAt_canon_two (σ.ne_zero_of_mem_domZero hz)
  have hA : ContDiffAt ℝ ∞ σ.modThree z := contDiffAt_const.sub (contDiffAt_const.mul h2)
  have hB : ContDiffAt ℝ ∞ σ.modTwo z := contDiffAt_const.add (contDiffAt_const.mul h1)
  have hP : ContDiffAt ℝ ∞ σ.cofBridgeZero z :=
    ((((hA.add hB).pow 2).sub contDiffAt_const).mul ((contDiffAt_const.add hA).sub hB)).mul
      (contDiffAt_const.mul (σ.contDiffAt_cofZeroThree hz))
  exact contDiffAt_twoCircle hA hB (σ.contDiff_wallSide 0).contDiffAt hP
    (σ.cofBridgeZero_pos hz) (by norm_num)

theorem contDiffAt_bridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) : ContDiffAt ℝ ∞ σ.bridgeTwo z := by
  have h0 := σ.contDiffAt_canon_zero (σ.ne_vertexOne_of_mem_domTwo hz)
  have h1 := σ.contDiffAt_canon_one (σ.ne_vertexTwo_of_mem_domTwo hz)
  have hA : ContDiffAt ℝ ∞ σ.modOne z := contDiffAt_const.add (contDiffAt_const.mul h0)
  have hB : ContDiffAt ℝ ∞ σ.modTwo z := contDiffAt_const.add (contDiffAt_const.mul h1)
  have hP : ContDiffAt ℝ ∞ σ.cofBridgeTwo z :=
    (((hA.add hB).add contDiffAt_const).mul (contDiffAt_const.sub ((hA.sub hB).pow 2))).mul
      (contDiffAt_const.mul (σ.contDiffAt_cofOneTwo hz))
  exact contDiffAt_twoCircle hA hB (σ.contDiff_wallSide 2).contDiffAt hP
    (σ.cofBridgeTwo_pos hz) (by norm_num)

theorem modOne_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    11 / 10 < σ.modOne z ∧ σ.modOne z < 19 / 10 := by
  have h1 := σ.canon_ge 0 z
  have h2 := σ.canon_lt_of_mem 0 hz
  unfold modOne profileSlope
  constructor <;> linarith

theorem modTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    11 / 10 < σ.modTwo z ∧ σ.modTwo z < 19 / 10 := by
  have h1 := σ.canon_ge 1 z
  have h2 := σ.canon_lt_of_mem 1 hz
  unfold modTwo profileSlope
  constructor <;> linarith

theorem modThree_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    13 / 5 < σ.modThree z ∧ σ.modThree z < 17 / 5 := by
  have h1 := σ.canon_ge 2 z
  have h2 := σ.canon_lt_of_mem 2 hz
  unfold modThree profileSlope
  constructor <;> linarith

theorem re_bridgeOne_pos {z : ℂ} (hz : z ∈ σ.triangle) : 0 < (σ.bridgeOne z).re := by
  have hA := σ.modThree_mem hz
  have hB := σ.modOne_mem hz
  rw [bridgeOne, twoCircle_re]
  have : 0 < σ.modThree z ^ 2 - σ.modOne z ^ 2 + (3 / 2 - 0) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < 2 * (3 / 2 - 0) := by norm_num
  have := div_pos this h2
  linarith

theorem re_bridgeZero_neg {z : ℂ} (hz : z ∈ σ.triangle) : (σ.bridgeZero z).re < 0 := by
  have hA := σ.modThree_mem hz
  have hB := σ.modTwo_mem hz
  rw [bridgeZero, twoCircle_re]
  have : 0 < σ.modThree z ^ 2 - σ.modTwo z ^ 2 + (-(3 / 2) - 0) ^ 2 := by nlinarith
  have h2 : 2 * (-(3 / 2) - 0 : ℝ) < 0 := by norm_num
  have := div_neg_of_pos_of_neg this h2
  linarith

theorem norm_bridgeOne_gt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    5 / 2 < ‖σ.bridgeOne z‖ := by
  rw [(σ.norm_bridgeOne (σ.triangle_subset_domOne hz h0 h1)).1]
  linarith [(σ.modThree_mem hz).1]

theorem norm_bridgeZero_gt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (h2 : z ≠ σ.vertexTwo) : 5 / 2 < ‖σ.bridgeZero z‖ := by
  rw [(σ.norm_bridgeZero (σ.triangle_subset_domZero hz h0 h2)).1]
  linarith [(σ.modThree_mem hz).1]

theorem norm_bridgeTwo_lt {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : ‖σ.bridgeTwo z‖ < 3 / 2 := by
  obtain ⟨e1, e2⟩ := σ.norm_bridgeTwo (σ.triangle_subset_domTwo hz h1 h2)
  have hA := σ.modOne_mem hz
  have hB := σ.modTwo_mem hz
  have q1 := normSq_eq_sq_norm (σ.bridgeTwo z - 3 / 2)
  have q2 := normSq_eq_sq_norm (σ.bridgeTwo z + 3 / 2)
  have q := normSq_eq_sq_norm (σ.bridgeTwo z)
  rw [e1] at q1
  rw [e2] at q2
  simp only [sub_re, add_re, sub_im, add_im, div_ofNat_re, div_ofNat_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_div, sub_zero, add_zero] at q1 q2
  have hsq : ‖σ.bridgeTwo z‖ ^ 2 < (3 / 2) ^ 2 := by nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (by norm_num) hsq

end EuclidShape

end GC.Seifert
