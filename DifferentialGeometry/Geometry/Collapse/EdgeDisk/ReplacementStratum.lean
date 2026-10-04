import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# FDC01 kernel: the selected edge centre is one-stratum, and the replacement arithmetic

Frozen blueprint master207B, lemma `lem:fibration-actual-replacement-edge-chart` (FDC01, lines
7157–7244).

* `scaledSplittingRank_eq_one_of_exclusions`: "EGP01 excludes a two-splitting at `p_i`, and LC18
  excludes the three-stratum. The exhaustive LC16 stratification therefore makes `p_i` a one-stratum
  point", once the zero stratum is excluded. Stated for the actual LC16 strata
  (`GC.MetricGeometry.scaledSplittingStratum`).
* `edgeReplacement_coordinate_lt`: the (Repl) arithmetic. From `|η_j(q')| < .8Δ`,
  `|η_i(q) - η_i(q')| < .01Δ`, EGP02–04's comparison
  `|η_j(q) - η_j(q')| ≤ (|η_i(q) - η_i(q')| + 2θ)/.99` with `θ < 1/100`, and (AE)'s
  `|u - η_j(q)| ≤ 5c₃/4`, for `Δ > 100`: `|η_j(q)| < 2Δ` and the normalized vector `|u| < 3Δ`; also
  the radius step `(.7Δ + 1.01) < .72Δ`.
The binding (EGP01, LC18 at `p_i`, LPA05/ZSP02 for the zero exclusion, LFR32/LFR44 for `q'` and
`p_j`) is not in the tree.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

open GC.MetricGeometry

universe u v

/-- **FDC01, stratum step.** A point of nonzero scaled splitting rank with neither a two- nor a
three-splitting lies in the one-stratum. -/
theorem scaledSplittingRank_eq_one_of_exclusions {M : Type u} [m : MetricSpace M]
    {ρ : M → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {p : M}
    (h0 : scaledSplittingRank.{u, v} ρ hρ β p ≠ 0)
    (h2 : ¬ @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 2 (β 2))
    (h3 : ¬ @HasEuclideanSplitting.{u, v} M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρ p))) p 3 (β 3)) :
    p ∈ scaledSplittingStratum.{u, v} ρ hρ β 1 := by
  have hle := scaledSplittingRank_le.{u, v} ρ hρ β p
  have hspl := (scaledSplittingRank_eq_iff.{u, v}.mp rfl).2.1 h0
  change scaledSplittingRank.{u, v} ρ hρ β p = 1
  generalize hk : scaledSplittingRank.{u, v} ρ hρ β p = k at hle hspl h0
  interval_cases k
  · exact absurd rfl h0
  · rfl
  · exact absurd hspl h2
  · exact absurd hspl h3

/-- **FDC01, (Repl) arithmetic.** -/
theorem edgeReplacement_coordinate_lt {a a' b b' w θ c₃ Δ : ℝ} (hΔ : 100 < Δ) (hθ : θ < 1 / 100)
    (hc₃ : c₃ < 1 / 100000) (ha' : |a'| < 4 / 5 * Δ) (hb : |b - b'| < 1 / 100 * Δ)
    (hcmp : |a - a'| ≤ (|b - b'| + 2 * θ) / (99 / 100)) (hw : |w - a| ≤ 5 * c₃ / 4) :
    |a - a'| < 4 / 100 * Δ ∧ |a| < 2 * Δ ∧ |w| < 3 * Δ ∧ 7 / 10 * Δ + 101 / 100 < 72 / 100 * Δ := by
  have h1 : |a - a'| < 4 / 100 * Δ := by
    have h2 : (|b - b'| + 2 * θ) / (99 / 100) < 4 / 100 * Δ := by
      rw [div_lt_iff₀ (by norm_num)]
      linarith
    linarith
  have h3 : |a| < 2 * Δ := by
    have := abs_sub_abs_le_abs_sub a a'
    linarith
  have h4 : |w| < 3 * Δ := by
    have := abs_sub_abs_le_abs_sub w a
    linarith
  exact ⟨h1, h3, h4, by linarith⟩

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
