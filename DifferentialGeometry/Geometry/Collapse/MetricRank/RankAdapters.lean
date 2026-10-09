import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# Rank adapters through `scaledSplittingRank_eq_iff` (review 75, section C.1, S-X144b group G6)

Disposition D75-9 fixes the rank interface: the scaled rank at `p` equals `k` iff `k ≤ 3`, a
`k`-splitting exists at the tolerance `β k` (when `k ≠ 0`), and for every `j` with `k < j ≤ 3`
there is NO `j`-splitting at the tolerance `β j`, all at the rescaled metric
`m.rescale (ρ p)⁻¹`. The two tolerances `β 2`, `β 3` are different numbers, so no monotonicity
across tolerances is used and there is NO generic "excluding `k + 1` suffices" lemma here:
every adapter names its exclusions separately (`not_two`, `not_three`) and takes the
existence side (`h1`, `h2`) as an explicit input, to be supplied by the fixture.

* `scaledSplittingRank_eq_one_SMR` : `h1`, `not_two`, `not_three` give rank `1`;
* `scaledSplittingRank_le_one_SMR` : `not_two`, `not_three` give rank `≤ 1` (no existence side);
* `scaledSplittingRank_eq_two_SMR` : `h2`, `not_three` give rank `2`;
* `scaledSplittingRank_le_two_SMR` : `not_three` gives rank `≤ 2`.

The exclusions are supplied by the metric kernels of the lane S-X144 (line, half plane, plane) in
`RankAdaptersBinding`.
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

variable {M : Type u} [m : MetricSpace M] {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}

/-- **Rank one.** A one-splitting at `β 1`, and separately no two-splitting at `β 2` and no
three-splitting at `β 3` (all at the rescaled metric of `p`), give scaled rank exactly `1`. -/
theorem scaledSplittingRank_eq_one_SMR
    (h1 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 1 (β 1))
    (not_two : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (not_three : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 3 (β 3)) :
    scaledSplittingRank.{u, v} ρ hρ β p = 1 := by
  refine scaledSplittingRank_eq_iff.{u, v}.mpr ⟨by norm_num, fun _ => h1, fun j hj hj3 => ?_⟩
  obtain rfl | rfl : j = 2 ∨ j = 3 := by omega
  · exact not_two
  · exact not_three

/-- **Rank at most one.** No two-splitting at `β 2` and no three-splitting at `β 3` (at the
rescaled metric of `p`) give scaled rank `≤ 1`; rank `0` is not excluded. -/
theorem scaledSplittingRank_le_one_SMR
    (not_two : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (not_three : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 3 (β 3)) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 1 := by
  have hle := scaledSplittingRank_le.{u, v} ρ hρ β p
  have hk := (scaledSplittingRank_eq_iff.{u, v} (ρ := ρ) (hρ := hρ) (β := β) (p := p)
    (k := scaledSplittingRank.{u, v} ρ hρ β p)).mp rfl
  by_contra hgt
  obtain h2 | h3 : scaledSplittingRank.{u, v} ρ hρ β p = 2 ∨
      scaledSplittingRank.{u, v} ρ hρ β p = 3 := by omega
  · have hs := hk.2.1 (by omega)
    rw [h2] at hs
    exact not_two hs
  · have hs := hk.2.1 (by omega)
    rw [h3] at hs
    exact not_three hs

/-- **Rank two.** A two-splitting at `β 2` and no three-splitting at `β 3` (at the rescaled
metric of `p`) give scaled rank exactly `2`. -/
theorem scaledSplittingRank_eq_two_SMR
    (h2 : @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (not_three : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 3 (β 3)) :
    scaledSplittingRank.{u, v} ρ hρ β p = 2 := by
  refine scaledSplittingRank_eq_iff.{u, v}.mpr ⟨by norm_num, fun _ => h2, fun j hj hj3 => ?_⟩
  obtain rfl : j = 3 := by omega
  exact not_three

/-- **Rank at most two.** No three-splitting at `β 3` (at the rescaled metric of `p`) gives scaled
rank `≤ 2`. -/
theorem scaledSplittingRank_le_two_SMR
    (not_three : ¬ @HasEuclideanSplitting.{u, v} M
      (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 3 (β 3)) :
    scaledSplittingRank.{u, v} ρ hρ β p ≤ 2 := by
  have hle := scaledSplittingRank_le.{u, v} ρ hρ β p
  have hk := (scaledSplittingRank_eq_iff.{u, v} (ρ := ρ) (hρ := hρ) (β := β) (p := p)
    (k := scaledSplittingRank.{u, v} ρ hρ β p)).mp rfl
  by_contra hgt
  have h3 : scaledSplittingRank.{u, v} ρ hρ β p = 3 := by omega
  have hs := hk.2.1 (by omega)
  rw [h3] at hs
  exact not_three hs

end GC.MetricGeometry
