import DifferentialGeometry.Geometry.Collapse.MetricRank.RankAdapters
import DifferentialGeometry.Geometry.Collapse.MetricRank.LineBallExclusion
import DifferentialGeometry.Geometry.Collapse.MetricRank.HalfPlaneBinding
import DifferentialGeometry.Geometry.Collapse.MetricRank.PlanarBallExclusion

/-!
# Rank adapters fed by the metric kernels (review 75, section C, S-X144b group G6)

The kernels of S-X144 exclude splittings of a metric space `X` at a point `p` from the existence of
an additive-distortion map `π` on `B(p, 6)`. Here `X` is the scaled metric space
`(M, m.rescale (ρ p)⁻¹)` of the rank interface, whose distance is `(ρ p)⁻¹ * dist`; its ball of
radius `6` is `{x | (ρ p)⁻¹ * dist x p < 6}`. The hypotheses on `π` are therefore written with
`(ρ p)⁻¹ * dist …` and are the kernel hypotheses verbatim (they unify by `rfl`).

Each adapter below feeds the kernel conclusions `¬ HasEuclideanSplitting` at `β 2` and `β 3`
SEPARATELY into the interface lemmas of `RankAdapters`; the existence side `h1` / `h2` is an
explicit input:

* line ball (`π : M → ℝ`)           : rank `= 1` (`β 2 ≤ 3/20`, `β 3 ≤ 3/20`, `ε_m ≤ 1/100`);
* pointed half plane (`π : M → ℝ²`) : rank `≤ 1`, and `= 1` with `h1` (`‖π p‖ ≤ 1/20`);
* planar ball (`π : M → ℝ²`)        : rank `≤ 2`, and `= 2` with `h2` (`β 3 ≤ 3/20`).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

section Binding

variable {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
  {εm : ℝ}

/-- **Line ball gives rank one.** The two exclusions are the `n = 2` (at `β 2`) and `n = 3`
(at `β 3`) applications of the line kernel; `h1` is the one-splitting of the fixture. -/
theorem scaledSplittingRank_eq_one_of_line_ball_SMR
    (h1 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1))
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : M → ℝ)
    (hπ : ∀ x y : M, (ρ p)⁻¹ * dist x p < 6 → (ρ p)⁻¹ * dist y p < 6 →
      |((ρ p)⁻¹ * dist x y - |π x - π y|)| ≤ εm) :
    scaledSplittingRank.{u, v} ρ hρ β p = 1 :=
  scaledSplittingRank_eq_one_SMR h1
    (@not_two_of_line_ball_SMR.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 2) εm
      hβ₂ hεm π fun x hx y hy => hπ x y hx hy)
    (@not_three_of_line_ball_SMR.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 3) εm
      hβ₃ hεm π fun x hx y hy => hπ x y hx hy)

/-- **Pointed half plane gives rank at most one.** `π : M → ℝ²` maps `B(p, 6)` into the upper
half plane `0 ≤ π x 1` and sends `p` to `(0, h)`, `0 ≤ h ≤ 1/20`; the half-plane kernel excludes
every `n ≥ 2`, used at `n = 2` (at `β 2`) and `n = 3` (at `β 3`). -/
theorem scaledSplittingRank_le_one_of_halfplane_boundary_SMR {h : ℝ}
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) (hεm : εm ≤ 1 / 100)
    (π : M → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x y : M, (ρ p)⁻¹ * dist x p < 6 → (ρ p)⁻¹ * dist y p < 6 →
      |(ρ p)⁻¹ * dist x y - ‖π x - π y‖| ≤ εm)
    (hH : ∀ x : M, (ρ p)⁻¹ * dist x p < 6 → 0 ≤ π x 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (hp0 : π p 0 = 0) (hp1 : π p 1 = h) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 1 :=
  scaledSplittingRank_le_one_SMR
    (@not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 2) εm h hβ₂ hεm π
      (fun x hx y hy => hπ x y hx hy) (fun x hx => hH x hx) hh0 hh1 hp0 hp1 2 le_rfl)
    (@not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 3) εm h hβ₃ hεm π
      (fun x hx y hy => hπ x y hx hy) (fun x hx => hH x hx) hh0 hh1 hp0 hp1 3 (by norm_num))

/-- **Pointed half plane gives rank one** (the edge point): the previous adapter together with the
one-splitting `h1` of the fixture. -/
theorem scaledSplittingRank_eq_one_of_halfplane_boundary_SMR {h : ℝ}
    (h1 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1))
    (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20) (hεm : εm ≤ 1 / 100)
    (π : M → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x y : M, (ρ p)⁻¹ * dist x p < 6 → (ρ p)⁻¹ * dist y p < 6 →
      |(ρ p)⁻¹ * dist x y - ‖π x - π y‖| ≤ εm)
    (hH : ∀ x : M, (ρ p)⁻¹ * dist x p < 6 → 0 ≤ π x 1) (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20)
    (hp0 : π p 0 = 0) (hp1 : π p 1 = h) :
    scaledSplittingRank.{u, v} ρ hρ β p = 1 :=
  scaledSplittingRank_eq_one_SMR h1
    (@not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 2) εm h hβ₂ hεm π
      (fun x hx y hy => hπ x y hx hy) (fun x hx => hH x hx) hh0 hh1 hp0 hp1 2 le_rfl)
    (@not_hasEuclideanSplitting_ge_two_at_halfplane_boundary_SMR.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 3) εm h hβ₃ hεm π
      (fun x hx y hy => hπ x y hx hy) (fun x hx => hH x hx) hh0 hh1 hp0 hp1 3 (by norm_num))

/-- **Planar ball gives rank at most two** (no three-splitting at `β 3 ≤ 3/20`). -/
theorem scaledSplittingRank_le_two_of_planar_ball_SMR
    (hβ₃ : β 3 ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : M → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x y : M, (ρ p)⁻¹ * dist x p < 6 → (ρ p)⁻¹ * dist y p < 6 →
      |(ρ p)⁻¹ * dist x y - ‖π x - π y‖| ≤ εm) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 2 :=
  scaledSplittingRank_le_two_SMR
    (@not_three_of_planar_ball_SMR.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 3) εm
      hβ₃ hεm π fun x hx y hy => hπ x y hx hy)

/-- **Planar ball gives rank two**: the three-splitting exclusion of the planar kernel together
with the two-splitting `h2` of the fixture. -/
theorem scaledSplittingRank_eq_two_of_planar_ball_SMR
    (h2 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (hβ₃ : β 3 ≤ 3 / 20) (hεm : εm ≤ 1 / 100) (π : M → EuclideanSpace ℝ (Fin 2))
    (hπ : ∀ x y : M, (ρ p)⁻¹ * dist x p < 6 → (ρ p)⁻¹ * dist y p < 6 →
      |(ρ p)⁻¹ * dist x y - ‖π x - π y‖| ≤ εm) :
    scaledSplittingRank.{u, v} ρ hρ β p = 2 :=
  scaledSplittingRank_eq_two_SMR h2
    (@not_three_of_planar_ball_SMR.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p (β 3) εm
      hβ₃ hεm π fun x hx y hy => hπ x y hx hy)

end Binding

end GC.MetricGeometry
