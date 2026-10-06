import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# From a Kleiner-Lott approximation to the additive-distortion map `π` of the rank kernels
(review 75, section C.1 / C.3-C.5, S-X144b group G7)

The rank-exactness kernels of S-X144 take a map `π : B(p, 6) → ℝ`, `ℝ²` or the half plane `H`
with `|d(x, y) − |π x − π y|| ≤ ε_m`. This file produces `π` from a Kleiner-Lott approximation
`f : KleinerLottApprox p (a, z) δ` into an `L²` product `A ×₂ Z` whose second factor `Z` is a
thin factor of diameter `≤ D` (`A = ℝ`, `ℝ²` or the closed upper half plane):

* `π = fst ∘ f`, `π p = a`;
* `−δ ≤ d(x, y) − d_A(π x, π y) ≤ δ + D` for `x, y ∈ B(p, δ⁻¹)`
  (`kl_projection_distortion_SMR`), hence `ε_m = f(δ, D) = δ + D`
  (`kl_projection_abs_SMR`); without a thin factor (`A` is the whole target) `ε_m = δ`
  (`kl_distortion_SMR`);
* the numerical bound `ε_m = δ + D ≤ 1/100` holds as soon as `δ ≤ δ₀ = 1/200` and `D ≤ 1/200`
  (`add_le_hundredth_SMR`); with no thin factor `δ ≤ 1/100` suffices; `B(p, 6) ⊆ B(p, δ⁻¹)`
  follows (`six_le_inv_of_add_le_SMR`);
* the three shapes in exactly the hypothesis form of the kernels: `exists_line_projection_SMR`
  (`π : X → ℝ`), `exists_plane_projection_SMR` (`π : X → ℝ²`), `exists_halfplane_projection_SMR`
  (`π : X → ℝ²` with `0 ≤ π x 1` everywhere and `π p = a`, so `π p = (0, h)` when
  `a = (0, h)`).

Difference to the review text of C.3 (`π : B(p, 6) → ℝ²`, `ε_m` as a free parameter): here `π` is
a total map `X → A` (the kernels use total maps with the distortion hypothesis on `B(p, 6)` only),
and `ε_m` is `δ + D`, where `δ` is the tolerance of the actual product approximation and `D` a
bound for the distances of its second factor; the distortion is one-sided in the factor, namely
`−δ ≤ d − d_A ≤ δ + D`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

section Projection

variable {X : Type*} [MetricSpace X] {A Z : Type*} [MetricSpace A] [MetricSpace Z]
  {p : X} {a : A} {z : Z} {δ D : ℝ}

/-- **The projection of a product approximation.** `f : KleinerLottApprox p (a, z) δ` into `A ×₂ Z`
where all distances in `Z` are `≤ D`: the first coordinate `π = fst ∘ f` has
`π p = a` and `−δ ≤ d(x, y) − d(π x, π y) ≤ δ + D` on `B(p, δ⁻¹)`. -/
theorem kl_projection_distortion_SMR (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) :
    ∃ π : X → A, π p = a ∧ ∀ x ∈ Metric.ball p δ⁻¹, ∀ y ∈ Metric.ball p δ⁻¹,
      -δ ≤ dist x y - dist (π x) (π y) ∧ dist x y - dist (π x) (π y) ≤ δ + D := by
  refine ⟨fun x => (f.toFun x).fst, ?_, fun x hx y hy => ?_⟩
  · change (f.toFun p).fst = a
    rw [f.basepoint]
    rfl
  · have hdist := f.distortion x hx y hy
    rw [abs_le] at hdist
    have hsq := WithLp.prod_dist_sq_eq_add_sq (f.toFun x) (f.toFun y)
    have hzz := hZ (f.toFun x).snd (f.toFun y).snd
    have ha := dist_nonneg (x := (f.toFun x).fst) (y := (f.toFun y).fst)
    have hb := dist_nonneg (x := (f.toFun x).snd) (y := (f.toFun y).snd)
    have hd := dist_nonneg (x := f.toFun x) (y := f.toFun y)
    have hle : dist (f.toFun x).fst (f.toFun y).fst ≤ dist (f.toFun x) (f.toFun y) := by
      nlinarith
    have hge : dist (f.toFun x) (f.toFun y) ≤
        dist (f.toFun x).fst (f.toFun y).fst + dist (f.toFun x).snd (f.toFun y).snd := by
      nlinarith [mul_nonneg ha hb]
    constructor
    · change -δ ≤ dist x y - dist (f.toFun x).fst (f.toFun y).fst
      linarith [hdist.1, hdist.2]
    · change dist x y - dist (f.toFun x).fst (f.toFun y).fst ≤ δ + D
      linarith [hdist.1, hdist.2]

/-- The absolute form: `|d(x, y) − d(π x, π y)| ≤ δ + D` on `B(p, δ⁻¹)`; this is the additive
distortion `ε_m = δ + D` required by the kernels. -/
theorem kl_projection_abs_SMR (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) :
    ∃ π : X → A, π p = a ∧ ∀ x ∈ Metric.ball p δ⁻¹, ∀ y ∈ Metric.ball p δ⁻¹,
      |dist x y - dist (π x) (π y)| ≤ δ + D := by
  obtain ⟨π, hp, h⟩ := kl_projection_distortion_SMR f hZ
  have hD : 0 ≤ D := le_trans dist_nonneg (hZ z z)
  refine ⟨π, hp, fun x hx y hy => ?_⟩
  obtain ⟨h1, h2⟩ := h x hx y hy
  rw [abs_le]
  constructor <;> linarith

/-- Without a thin factor (the target is `A` itself): `π = f` has `ε_m = δ`. -/
theorem kl_distortion_SMR {Y : Type*} [MetricSpace Y] {q : Y} (f : KleinerLottApprox p q δ) :
    ∃ π : X → Y, π p = q ∧ ∀ x ∈ Metric.ball p δ⁻¹, ∀ y ∈ Metric.ball p δ⁻¹,
      |dist x y - dist (π x) (π y)| ≤ δ :=
  ⟨f.toFun, f.basepoint, fun x hx y hy => by
    rw [abs_sub_comm]
    exact f.distortion x hx y hy⟩

end Projection

section Numbers

/-- **The numerical bound.** `ε_m = δ + D ≤ 1/100` for `δ ≤ δ₀ = 1/200` and `D ≤ 1/200`. -/
theorem add_le_hundredth_SMR {δ D : ℝ} (hδ : δ ≤ 1 / 200) (hD : D ≤ 1 / 200) :
    δ + D ≤ 1 / 100 := by
  linarith

/-- `B(p, 6) ⊆ B(p, δ⁻¹)` from `δ + D ≤ 1/100`, `0 < δ`, `0 ≤ D`: the radius `6` of the kernels
lies inside the radius `δ⁻¹ ≥ 100` of the approximation. -/
theorem six_le_inv_of_add_le_SMR {δ D : ℝ} (hδ : 0 < δ) (hD : 0 ≤ D) (h : δ + D ≤ 1 / 100) :
    (6 : ℝ) ≤ δ⁻¹ := by
  rw [← one_div, le_div_iff₀ hδ]
  linarith

end Numbers

section Shapes

variable {X : Type*} [MetricSpace X] {Z : Type*} [MetricSpace Z] {p : X} {z : Z} {δ D : ℝ}

/-- The ball restriction used by all three shapes. -/
theorem ball_six_subset_SMR {Y : Type*} [MetricSpace Y] {q : Y} (f : KleinerLottApprox p q δ)
    (hD : 0 ≤ D) (hε : δ + D ≤ 1 / 100) : Metric.ball p 6 ⊆ Metric.ball p δ⁻¹ :=
  Metric.ball_subset_ball (six_le_inv_of_add_le_SMR f.error_pos hD hε)

/-- **The line shape** (`A = ℝ`): the hypotheses of `not_two_of_line_ball_SMR` /
`not_three_of_line_ball_SMR` with `ε_m = δ + D ≤ 1/100`. -/
theorem exists_line_projection_SMR {a : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) :
    ∃ π : X → ℝ, π p = a ∧ ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6,
      |(dist x y - |π x - π y|)| ≤ δ + D := by
  obtain ⟨π, hp, h⟩ := kl_projection_abs_SMR f hZ
  have hs := ball_six_subset_SMR f (le_trans dist_nonneg (hZ z z)) hε
  exact ⟨π, hp, fun x hx y hy => by
    have := h x (hs hx) y (hs hy)
    rwa [Real.dist_eq] at this⟩

/-- **The plane shape** (`A = ℝ²`): the hypotheses of the planar kernel with `ε_m = δ + D`. -/
theorem exists_plane_projection_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) :
    ∃ π : X → EuclideanSpace ℝ (Fin 2), π p = a ∧ ∀ x ∈ Metric.ball p 6,
      ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ δ + D := by
  obtain ⟨π, hp, h⟩ := kl_projection_abs_SMR f hZ
  have hs := ball_six_subset_SMR f (le_trans dist_nonneg (hZ z z)) hε
  exact ⟨π, hp, fun x hx y hy => by
    have := h x (hs hx) y (hs hy)
    rwa [dist_eq_norm] at this⟩

/-- **The half-plane shape** (`A = H`, the closed upper half plane): the hypotheses of the pointed
half-plane kernel with `ε_m = δ + D`: `0 ≤ π x 1` for all `x` and `π p = a` (so `π p = (0, h)` when
`a = (0, h)`). -/
theorem exists_halfplane_projection_SMR {a : {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) :
    ∃ π : X → EuclideanSpace ℝ (Fin 2), (∀ x, 0 ≤ π x 1) ∧ π p = a.1 ∧
      ∀ x ∈ Metric.ball p 6, ∀ y ∈ Metric.ball p 6, |(dist x y - ‖π x - π y‖)| ≤ δ + D := by
  obtain ⟨π, hp, h⟩ := kl_projection_abs_SMR f hZ
  have hs := ball_six_subset_SMR f (le_trans dist_nonneg (hZ z z)) hε
  exact ⟨fun x => (π x).1, fun x => (π x).2, congrArg Subtype.val hp, fun x hx y hy => by
    have := h x (hs hx) y (hs hy)
    rwa [Subtype.dist_eq, dist_eq_norm] at this⟩

/-- The thin-factor hypothesis in the diameter form of `EdgeFamily.covers_nonslim`:
`diam Z ≤ D` for a bounded `Z` gives `dist z₁ z₂ ≤ D`. -/
theorem dist_le_of_diam_le_SMR (hb : Bornology.IsBounded (Set.univ : Set Z))
    (hdiam : Metric.diam (Set.univ : Set Z) ≤ D) (z₁ z₂ : Z) : dist z₁ z₂ ≤ D :=
  le_trans (Metric.dist_le_diam_of_mem hb (Set.mem_univ _) (Set.mem_univ _)) hdiam

end Shapes

end GC.MetricGeometry
