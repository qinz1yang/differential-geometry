import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxDistortion
import DifferentialGeometry.Geometry.Collapse.MetricRank.RankAdaptersBinding

/-!
# Thin product approximations feed the rank kernels and adapters (review 75, section C, S-X144b
group G7, wiring)

`ApproxDistortion` turns a Kleiner-Lott approximation `f : KleinerLottApprox p (a, z) δ` into a
product `A ×₂ Z` with a thin factor (`dist z₁ z₂ ≤ D`, `δ + D ≤ 1/100`) into the map `π` of the
kernels. This file composes that with the kernels (`¬ HasEuclideanSplitting`, any metric space
`X`) and with the rank adapters of `RankAdaptersBinding` (the scaled space
`(M, m.rescale (ρ p)⁻¹)`, where `f` is a Kleiner-Lott approximation at the rescaled metric):

* thin line `ℝ ×₂ Z`      : no splitting of rank `n ≥ 2`; rank `= 1` (with the one-splitting `h1`);
* thin half plane `H ×₂ Z` at `(0, h)`, `0 ≤ h ≤ 1/20` : no splitting of rank `n ≥ 2`; rank `≤ 1`,
  `= 1` with `h1`;
* thin plane `ℝ² ×₂ Z`    : no splitting of rank `n ≥ 3`; rank `≤ 2`, `= 2` with `h2`.

The tolerances of the kernels (`β ≤ 3/20`) are independent of the tolerance `δ` of the thin
product approximation.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v w

section KernelLevel

variable {X : Type u} [MetricSpace X] {Z : Type w} [MetricSpace Z] {p : X} {z : Z} {δ D β : ℝ}

/-- A thin line product approximation excludes every splitting of rank `n ≥ 2`. -/
theorem not_hasEuclideanSplitting_ge_two_of_thin_line_SMR {a : ℝ}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) (hβ : β ≤ 3 / 20) {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasEuclideanSplitting.{u, v} p n β := by
  obtain ⟨π, -, h⟩ := exists_line_projection_SMR f hZ hε
  exact not_hasEuclideanSplitting_ge_two_of_line_ball_SMR hβ hε π h hn

/-- A thin plane product approximation excludes every splitting of rank `n ≥ 3`. -/
theorem not_hasEuclideanSplitting_ge_three_of_thin_plane_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) (hβ : β ≤ 3 / 20) {n : ℕ} (hn : 3 ≤ n) :
    ¬ HasEuclideanSplitting.{u, v} p n β := by
  obtain ⟨π, -, h⟩ := exists_plane_projection_SMR f hZ hε
  exact not_hasEuclideanSplitting_ge_three_of_planar_ball_SMR hβ hε π h hn

/-- A thin half-plane product approximation at a point `(0, h)` with `0 ≤ h ≤ 1/20` excludes every
splitting of rank `n ≥ 2`. -/
theorem not_hasEuclideanSplitting_ge_two_of_thin_halfplane_SMR {h : ℝ}
    {a : {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D)
    (hε : δ + D ≤ 1 / 100) (hβ : β ≤ 3 / 20) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (ha0 : a.1 0 = 0) (ha1 : a.1 1 = h) {n : ℕ} (hn : 2 ≤ n) :
    ¬ HasEuclideanSplitting.{u, v} p n β := by
  obtain ⟨π, hH, hp, h'⟩ := exists_halfplane_projection_SMR f hZ hε
  exact not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR hβ hε π h'
    (fun x _ => hH x) hh0 hh1 (by rw [hp]; exact ha0) (by rw [hp]; exact ha1) hn

end KernelLevel

section RankLevel

variable {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
  {Z : Type w} [MetricSpace Z] {z : Z} {δ D : ℝ}

/-- **Thin line gives rank one.** `f` is a Kleiner-Lott approximation at the rescaled metric of
`p`; `h1` is the one-splitting of the fixture. -/
theorem scaledSplittingRank_eq_one_of_thin_line_SMR {a : ℝ}
    (f : @KleinerLottApprox M (WithLp 2 (ℝ × Z)) (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (h1 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1))
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, v} ρ hρ β p = 1 := by
  obtain ⟨π, -, h⟩ := @exists_line_projection_SMR M
    (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) Z _ p z δ D a f hZ hε
  exact scaledSplittingRank_eq_one_of_line_ball_SMR h1 hβ₂ hβ₃ hε π
    (fun x y hx hy => h x hx y hy)

/-- **Thin half plane gives rank at most one** at a point `(0, h)`, `0 ≤ h ≤ 1/20`. -/
theorem scaledSplittingRank_le_one_of_thin_halfplane_SMR {h : ℝ}
    {a : {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}}
    (f : @KleinerLottApprox M (WithLp 2 ({v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1} × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (ha0 : a.1 0 = 0) (ha1 : a.1 1 = h) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 1 := by
  obtain ⟨π, hH, hp, h'⟩ := @exists_halfplane_projection_SMR M
    (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) Z _ p z δ D a f hZ hε
  exact scaledSplittingRank_le_one_of_halfplane_boundary_SMR hβ₂ hβ₃ hε π
    (fun x y hx hy => h' x hx y hy) (fun x _ => hH x) hh0 hh1 (by rw [hp]; exact ha0)
    (by rw [hp]; exact ha1)

/-- **Thin half plane gives rank one** (the edge point) with the one-splitting `h1`. -/
theorem scaledSplittingRank_eq_one_of_thin_halfplane_SMR {h : ℝ}
    {a : {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}}
    (f : @KleinerLottApprox M (WithLp 2 ({v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1} × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (h1 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1))
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (ha0 : a.1 0 = 0) (ha1 : a.1 1 = h) :
    scaledSplittingRank.{u, v} ρ hρ β p = 1 := by
  obtain ⟨π, hH, hp, h'⟩ := @exists_halfplane_projection_SMR M
    (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) Z _ p z δ D a f hZ hε
  exact scaledSplittingRank_eq_one_of_halfplane_boundary_SMR h1 hβ₂ hβ₃ hε π
    (fun x y hx hy => h' x hx y hy) (fun x _ => hH x) hh0 hh1 (by rw [hp]; exact ha0)
    (by rw [hp]; exact ha1)

/-- **Thin plane gives rank at most two.** -/
theorem scaledSplittingRank_le_two_of_thin_plane_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : @KleinerLottApprox M (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100) (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 2 := by
  obtain ⟨π, -, h⟩ := @exists_plane_projection_SMR M
    (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) Z _ p z δ D a f hZ hε
  exact scaledSplittingRank_le_two_of_planar_ball_SMR hβ₃ hε π (fun x y hx hy => h x hx y hy)

/-- **Thin plane gives rank two** with the two-splitting `h2`. -/
theorem scaledSplittingRank_eq_two_of_thin_plane_SMR {a : EuclideanSpace ℝ (Fin 2)}
    (f : @KleinerLottApprox M (WithLp 2 (EuclideanSpace ℝ (Fin 2) × Z))
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (h2 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (hβ₃ : β 3 ≤ 3 / 20) :
    scaledSplittingRank.{u, v} ρ hρ β p = 2 := by
  obtain ⟨π, -, h⟩ := @exists_plane_projection_SMR M
    (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) Z _ p z δ D a f hZ hε
  exact scaledSplittingRank_eq_two_of_planar_ball_SMR h2 hβ₃ hε π
    (fun x y hx hy => h x hx y hy)

end RankLevel

end GC.MetricGeometry
