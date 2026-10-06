import DifferentialGeometry.Geometry.Collapse.MetricRank.HalfPlaneNested
import DifferentialGeometry.Geometry.Collapse.MetricRank.SplittingOfThinProduct
import DifferentialGeometry.Geometry.Collapse.MetricRank.ApproxRankWiring

/-!
# The thin half plane has rank exactly one (S-X144c, group G11)

A Kleiner-Lott approximation of `p` into the product `H ×₂ Z` of the closed upper half plane with
a thin factor (`dist ≤ D`, `δ + D ≤ 1/100`) at a base point `(a, z)` with `a = (0, h)`,
`0 ≤ h ≤ 1/20`:

* `exists_splitting_of_thin_halfplane_SMR` : it is a one-splitting at every tolerance `β` with
  `2 δ ≤ β < 1`, with the factor `[0, ∞) ×₂ Z` of `HasEuclideanSplitting` (the nested isometry
  `halfPlaneNestedIso_SMR`, translation of `ℝ¹`, relaxation of G9);
* `scaledSplittingRank_eq_one_of_thin_halfplane_only_SMR` : `scaledSplittingRank = 1` at the
  rescaled metric, from the thin approximation and the register alone (the exclusion of ranks 2
  and 3 is the half-plane kernel of `ApproxRankWiring`, the existence of the one-splitting the
  previous item; ApproxRankWiring has the same statement with an explicit `h1`).

Universes: the factor of the splitting is `WithLp 2 ([0, ∞) ×₂ Z) : Type w`, so the rank is
`scaledSplittingRank.{u, w}` for `Z : Type w`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u w

local notation "HP" => {v : EuclideanSpace ℝ (Fin 2) // 0 ≤ v 1}
local notation "HR" => {t : ℝ // 0 ≤ t}

section Splitting

variable {X : Type u} [MetricSpace X] {p : X} {δ β : ℝ} {Z : Type w} [MetricSpace Z] {z : Z}

/-- **Thin half plane: a one-splitting.** An approximation `p ↦ (a, z)` into `H ×₂ Z` at
tolerance `δ` is a one-splitting at every tolerance `β` with `2 δ ≤ β < 1`, for every base point
`a` of the half plane (the factor of the splitting is `[0, ∞) ×₂ Z`). -/
theorem exists_splitting_of_thin_halfplane_SMR {a : HP}
    (f : KleinerLottApprox p (WithLp.toLp 2 (a, z)) δ) (hβ : 2 * δ ≤ β) (hβ1 : β < 1) :
    HasEuclideanSplitting.{u, w} p 1 β := by
  have h : HasEuclideanSplitting.{u, w} p 1 δ :=
    ⟨WithLp 2 (HR × Z), inferInstance, WithLp.toLp 2 ((⟨a.1 1, a.2⟩ : HR), z),
      ⟨f.transportTo_SMR (halfPlaneNestedIso_SMR a) (halfPlaneNestedIso_apply_base_SMR a z)⟩⟩
  exact h.relax_SMR hβ hβ1

end Splitting

section RankLevel

variable {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
  {Z : Type w} [MetricSpace Z] {z : Z} {δ D : ℝ}

/-- **Thin half plane at an edge point: rank exactly one, no `h1`.** `f` is a Kleiner-Lott
approximation of the rescaled metric into `H ×₂ Z` at a base point `a = (0, h)` with
`0 ≤ h ≤ 1/20`; the tolerance of the one-splitting is `2 δ ≤ β 1 < 1`. -/
theorem scaledSplittingRank_eq_one_of_thin_halfplane_only_SMR {h : ℝ} {a : HP}
    (f : @KleinerLottApprox M (WithLp 2 (HP × Z)) (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₁ : 2 * δ ≤ β 1) (hβ₁1 : β 1 < 1) (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20) (ha0 : a.1 0 = 0) (ha1 : a.1 1 = h) :
    scaledSplittingRank.{u, w} ρ hρ β p = 1 :=
  scaledSplittingRank_eq_one_of_thin_halfplane_SMR f hZ hε
    (@exists_splitting_of_thin_halfplane_SMR M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p δ
      (β 1) Z _ z a f hβ₁ hβ₁1) hβ₂ hβ₃ hh0 hh1 ha0 ha1

/-- **Thin half plane, rank exactly one, register form**: `1/50 ≤ β 1 < 1`. -/
theorem scaledSplittingRank_eq_one_of_thin_halfplane_only_of_hundredth_SMR {h : ℝ} {a : HP}
    (f : @KleinerLottApprox M (WithLp 2 (HP × Z)) (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) _ p
      (WithLp.toLp 2 (a, z)) δ)
    (hZ : ∀ z₁ z₂ : Z, dist z₁ z₂ ≤ D) (hε : δ + D ≤ 1 / 100)
    (hβ₁ : 1 / 50 ≤ β 1) (hβ₁1 : β 1 < 1) (hβ₂ : β 2 ≤ 3 / 20) (hβ₃ : β 3 ≤ 3 / 20)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1 / 20) (ha0 : a.1 0 = 0) (ha1 : a.1 1 = h) :
    scaledSplittingRank.{u, w} ρ hρ β p = 1 := by
  have hD : 0 ≤ D := le_trans dist_nonneg (hZ z z)
  exact scaledSplittingRank_eq_one_of_thin_halfplane_only_SMR f hZ hε (by linarith) hβ₁1 hβ₂ hβ₃
    hh0 hh1 ha0 ha1

end RankLevel

end GC.MetricGeometry
