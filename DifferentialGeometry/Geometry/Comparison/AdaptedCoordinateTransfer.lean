import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Transfer of the adapted-coordinate clauses (LC68, LC72: kernels)

Blueprint `master207A.tex`, LC68 (`lem:collapse-adapted-radial-stability`, lines 23988–24071)
and LC72 (`lem:collapse-calibrated-gradient-transfer`, lines 24242–24316). KL Definition 4.21 in
rank one has three clauses for a function `φ` on `B(q,1)` and a splitting coordinate `Φ`:
`(1 + γ)`-Lipschitz; image within `γ` of `(-1, 1)` in both directions (infimum distances); and
for every tested pair `(x, y)` and every unit minimizing direction `w`, the derivative test
`|Dφ_x(w) - (Φ y - Φ x)/d(x,y)| < γ`. No definition of adaptedness is introduced here: the
clauses are written out.

* `lipschitz_clause_of_perturbation`, `image_clauses_of_perturbation`,
  `derivative_clause_of_perturbation`: if `ψ - φ` is `h`-Lipschitz on the ball, values differ by at
  most `h`, derivatives differ by at most `h` along the tested direction, and `γ + h ≤ ζ`, then the
  three clauses pass from `φ` at quality `γ` to `ψ` at quality `ζ` (LC68's argument; the far-point
  domain `B(q, ζ⁻¹) ⊆ B(q, γ⁻¹)` is `ball_inv_subset_of_le`).
* `norm_add_unit_sq_le` and `norm_sub_le_of_calibrated_directions`: the inner-product core of
  LC72: if `‖F‖ ≤ 1 + e` and `⟪F, v⟫ ≤ -1 + e` for a unit `v`, then `‖F + v‖² ≤ 4e + e²`; two such
  vectors with errors `γ, ε` differ by at most `A(γ, ε) = √(4γ + γ²) + √(4ε + ε²)`.

The Riemannian bindings (gradient of a smooth function, the direction of a minimizing segment
to `p`, integration from `q` along minimizing segments) are not part of these kernels.
-/

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison

/-- LC68, Lipschitz clause. -/
theorem lipschitz_clause_of_perturbation {X : Type*} [PseudoMetricSpace X] {B : Set X}
    {φ ψ : X → ℝ} {γ h ζ : ℝ} (hζ : γ + h ≤ ζ)
    (hφ : ∀ x ∈ B, ∀ y ∈ B, |φ x - φ y| ≤ (1 + γ) * dist x y)
    (hdiff : ∀ x ∈ B, ∀ y ∈ B, |(ψ x - φ x) - (ψ y - φ y)| ≤ h * dist x y) :
    ∀ x ∈ B, ∀ y ∈ B, |ψ x - ψ y| ≤ (1 + ζ) * dist x y := by
  intro x hx y hy
  have h1 := hφ x hx y hy
  have h2 := hdiff x hx y hy
  have h3 : ψ x - ψ y = (φ x - φ y) + ((ψ x - φ x) - (ψ y - φ y)) := by ring
  rw [h3]
  calc |(φ x - φ y) + ((ψ x - φ x) - (ψ y - φ y))|
      ≤ |φ x - φ y| + |(ψ x - φ x) - (ψ y - φ y)| := abs_add_le _ _
    _ ≤ (1 + γ) * dist x y + h * dist x y := add_le_add h1 h2
    _ ≤ (1 + ζ) * dist x y := by nlinarith [dist_nonneg (x := x) (y := y)]

/-- LC68, image clauses (infimum distances, no nearest points or closed images assumed). -/
theorem image_clauses_of_perturbation {X : Type*} {B : Set X} {φ ψ : X → ℝ} {γ h ζ : ℝ}
    (hζ : γ + h ≤ ζ) (hh : 0 ≤ h) (hval : ∀ x ∈ B, |ψ x - φ x| ≤ h)
    (hφ1 : ∀ x ∈ B, infDist (φ x) (Ioo (-1 : ℝ) 1) ≤ γ)
    (hφ2 : ∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (φ '' B) ≤ γ) :
    (∀ x ∈ B, infDist (ψ x) (Ioo (-1 : ℝ) 1) ≤ ζ) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 1, infDist t (ψ '' B) ≤ ζ := by
  constructor
  · intro x hx
    have h1 := infDist_le_infDist_add_dist (x := ψ x) (y := φ x) (s := Ioo (-1 : ℝ) 1)
    rw [Real.dist_eq] at h1
    linarith [hφ1 x hx, hval x hx]
  · intro t ht
    rcases B.eq_empty_or_nonempty with hB | hB
    · simp only [hB, image_empty, infDist_empty]
      linarith [hφ2 t ht, infDist_nonneg (x := t) (s := φ '' B)]
    · have hne : (φ '' B).Nonempty := hB.image φ
      have key : infDist t (ψ '' B) ≤ infDist t (φ '' B) + h := by
        apply le_of_forall_gt
        intro r hr
        obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ :=
          (infDist_lt_iff hne).mp (show infDist t (φ '' B) < r - h by linarith)
        have h2 := infDist_le_dist_of_mem (x := t) (mem_image_of_mem ψ hx)
        have h3 : dist t (ψ x) ≤ dist t (φ x) + h := by
          have := dist_triangle t (φ x) (ψ x)
          rw [Real.dist_eq (φ x) (ψ x), abs_sub_comm] at this
          linarith [hval x hx]
        linarith
      linarith [hφ2 t ht]

/-- LC68 / LC72, derivative clause for one tested direction. -/
theorem derivative_clause_of_perturbation {a b s γ h ζ : ℝ} (hζ : γ + h ≤ ζ)
    (ha : |a - s| < γ) (hab : |b - a| ≤ h) : |b - s| < ζ := by
  have := abs_sub_le b a s
  linarith

/-- The far-point test domain shrinks with the quality. -/
theorem ball_inv_subset_of_le {X : Type*} [PseudoMetricSpace X] (q : X) {γ ζ : ℝ}
    (hγ : 0 < γ) (hγζ : γ ≤ ζ) : ball q ζ⁻¹ ⊆ ball q γ⁻¹ :=
  ball_subset_ball (inv_anti₀ hγ hγζ)

/-- LC72, inner-product core: a vector of norm at most `1 + e` whose inner product with a unit
vector `v` is at most `-1 + e` lies within `√(4e + e²)` of `-v`. -/
theorem norm_add_unit_sq_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {F v : V} {e : ℝ} (hF : ‖F‖ ≤ 1 + e) (hv : ‖v‖ = 1)
    (hFv : inner ℝ F v ≤ -1 + e) : ‖F + v‖ ^ 2 ≤ 4 * e + e ^ 2 := by
  rw [norm_add_sq_real, hv]
  have hF2 : ‖F‖ ^ 2 ≤ (1 + e) ^ 2 := pow_le_pow_left₀ (norm_nonneg F) hF 2
  nlinarith

/-- LC72: two calibrated vectors are within `A(γ, ε) = √(4γ + γ²) + √(4ε + ε²)`. -/
theorem norm_sub_le_of_calibrated_directions {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {F G v : V} {γ ε : ℝ} (hv : ‖v‖ = 1)
    (hF : ‖F‖ ≤ 1 + γ) (hFv : inner ℝ F v ≤ -1 + γ)
    (hG : ‖G‖ ≤ 1 + ε) (hGv : inner ℝ G v ≤ -1 + ε) :
    ‖F - G‖ ≤ sqrt (4 * γ + γ ^ 2) + sqrt (4 * ε + ε ^ 2) := by
  have h1 : ‖F + v‖ ≤ sqrt (4 * γ + γ ^ 2) :=
    le_sqrt_of_sq_le (norm_add_unit_sq_le hF hv hFv)
  have h2 : ‖G + v‖ ≤ sqrt (4 * ε + ε ^ 2) :=
    le_sqrt_of_sq_le (norm_add_unit_sq_le hG hv hGv)
  calc ‖F - G‖ = ‖(F + v) - (G + v)‖ := by congr 1; abel
    _ ≤ ‖F + v‖ + ‖G + v‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- LC72: the error `A(γ, ε)` dominates `ε`, so the transferred function is
`(1 + γ + A)`-Lipschitz whenever it is `(1 + ε)`-Lipschitz. -/
theorem le_sqrt_four_mul_add_sq {ε : ℝ} (hε : 0 ≤ ε) : ε ≤ sqrt (4 * ε + ε ^ 2) :=
  le_sqrt_of_sq_le (by nlinarith)

/-- LC72: along a minimizing segment from `x` to `p`, the centered radial function
`u = d(p, ·) - d(p, q)` decreases by exactly the traversed length. -/
theorem radial_decrease_along_segment {X : Type*} [PseudoMetricSpace X] {p q x y : X}
    (hy : dist x y + dist y p = dist x p) :
    (dist p y - dist p q) - (dist p x - dist p q) = -dist x y := by
  rw [dist_comm p y, dist_comm p x, ← hy]
  ring

end DifferentialGeometry.Geometry.Comparison
