/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TaperedInwardPush

/-!
# The tapered inward push fixing a prescribed polyhedron

`TaperedInwardPush.lean` pushes a collar off its bottom `B` by a nonnegative piecewise affine
height `g`, and leaves the complementary polyhedron `R` pointwise fixed.  A stagewise
construction needs one more set left fixed: the compact region already moved inward by the
earlier stages, which lies in the collar and must not be touched again.

Enlarging the fixed set is a condition on the thinness parameter alone.  The seam condition

    ∀ y ∈ B, ∀ t ∈ Icc 0 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t

is stable under replacing `R` by `R ∪ D` for a polyhedron `D` disjoint from the collar bottom,
at the smaller level `min a c` where `c` is the level produced for `D` by
`IsPLHomeomorphOn.exists_pos_forall_le_of_disjoint`.  Nothing else about `D` is used: it need
not meet the collar, and it need not be connected.

If moreover `D ⊆ W ∪ R`, then `W ∪ (R ∪ D) = W ∪ R`, so the enlargement costs nothing at all —
every clause of the tapered push stays on the same set `W ∪ R`, and the conclusion simply gains
`EqOn f id D` and `EqOn f' id D`.  This is why the fixed region of a stage is routed through
the `R` slot rather than being read off from the thinness level: the delivered push exposes no
clause about the collar coordinate of an arbitrary point.

## Main results

* `IsPLHomeomorphOn.exists_pos_forall_le_seam_union`: the seam condition for `R ∪ D`.
* `IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt`: the
  tapered push at a prescribed tolerance, fixing `D` pointwise together with `R`.

Taking `D = ∅` returns `IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt`
unchanged, since `Disjoint B ∅` and `∅ ⊆ W ∪ R` always hold and `EqOn f id ∅` is vacuous; the
intended instance is a compact polyhedral neighbourhood of the image of an earlier stage, which
is disjoint from the bottom because that image has already been pushed into the interior.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Fixing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B W R D : Set E} {ρ : E × ℝ → E}

/-- **The seam condition survives adjoining a polyhedron disjoint from the collar bottom.**

The collar meets `D` only above the positive level supplied by
`IsPLHomeomorphOn.exists_pos_forall_le_of_disjoint`, so the two alternatives of the seam
condition for `R` remain the two alternatives for `R ∪ D` once the thinness level is lowered to
the minimum of the two levels.  The height `g` enters only through the hypothesis; it is not
constrained, and in particular it may vanish. -/
theorem IsPLHomeomorphOn.exists_pos_forall_le_seam_union
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hD : IsPolyhedron D)
    (hBD : Disjoint B D) (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ} {a : ℝ} (ha : 0 < a)
    (haone : a ≤ 1)
    (hseam : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 ∧
      ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R ∪ D → g y = 0 ∨ b ≤ t := by
  obtain ⟨c, hc, -, hcle⟩ := hρ.exists_pos_forall_le_of_disjoint hW hD hBD hbottom
  refine ⟨min a c, lt_min ha hc, (min_le_left _ _).trans haone, ?_⟩
  intro y hy t ht hmem
  rcases hmem with hmem | hmem
  · rcases hseam y hy t ht hmem with h0 | hle
    · exact Or.inl h0
    · exact Or.inr ((min_le_left _ _).trans hle)
  · exact Or.inr ((min_le_right _ _).trans (hcle y hy t ht hmem))

/-- **The tapered inward push at a prescribed tolerance, fixing a prescribed polyhedron.**

The hypotheses are those of
`IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt` together with a
polyhedron `D` inside `W ∪ R` which misses the collar bottom, and the conclusion is the same
one with the two extra clauses `EqOn f id D` and `EqOn f' id D`.

The proof runs the tapered push at the polyhedron `R ∪ D` and at the thinness level of
`IsPLHomeomorphOn.exists_pos_forall_le_seam_union`.  Because `D ⊆ W ∪ R`, the set carrying the
conclusion does not change, so no clause has to be restricted afterwards: restriction would not
be available, since piecewise affinity on a set does not pass to an arbitrary subset. -/
theorem IsPLHomeomorphOn.exists_piecewiseAffineOn_inward_leftInvOn_taper_fixing_dist_lt
    (hρ : IsPLHomeomorphOn ρ (B ×ˢ Icc (0 : ℝ) 1) W) (hW : IsPolyhedron W) (hR : IsPolyhedron R)
    (hD : IsPolyhedron D) (hBD : Disjoint B D) (hDWR : D ⊆ W ∪ R) (hBc : IsCompact B)
    (hbottom : ∀ x ∈ B, ρ (x, 0) = x) {g : E → ℝ} (hgpl : IsPiecewiseAffineOn g univ)
    (hgpos : ∀ y : E, 0 ≤ g y) {a : ℝ} (ha : 0 < a) (haone : a ≤ 1)
    (hseam : ∀ y ∈ B, ∀ t ∈ Icc (0 : ℝ) 1, ρ (y, t) ∈ R → g y = 0 ∨ a ≤ t)
    {Z : Type*} [MetricSpace Z] {h : E → Z} (hh : ContinuousOn h W) {ε : ℝ} (hε : 0 < ε) :
    ∃ f f' : E → E, IsPiecewiseAffineOn f (W ∪ R) ∧ InjOn f (W ∪ R) ∧
      MapsTo f (W ∪ R) (W ∪ R) ∧ (∀ x ∈ W ∪ R, f x ∈ B → x ∈ B ∧ g x = 0) ∧
      EqOn f id R ∧ EqOn f id D ∧
      (∀ y ∈ B, g y = 0 → ∀ t ∈ Icc (0 : ℝ) 1, f (ρ (y, t)) = ρ (y, t)) ∧
      IsPiecewiseAffineOn f' (W ∪ R) ∧ MapsTo f' (W ∪ R) (W ∪ R) ∧ EqOn f' id R ∧
      EqOn f' id D ∧ LeftInvOn f' f (W ∪ R) ∧ ∀ x ∈ W ∪ R, dist (h (f x)) (h x) < ε := by
  obtain ⟨b, hb, hbone, hbseam⟩ :=
    hρ.exists_pos_forall_le_seam_union hW hD hBD hbottom ha haone hseam
  have hunion : W ∪ (R ∪ D) = W ∪ R := by
    rw [← union_assoc]
    exact union_eq_left.mpr hDWR
  obtain ⟨f, f', hfpl, hfinj, hfmap, hfB, hfRD, hfix0, hf'pl, hf'map, hf'RD, hinv, hdist⟩ :=
    hρ.exists_piecewiseAffineOn_inward_leftInvOn_taper_dist_lt hW (hR.union hD) hBc hbottom
      hgpl hgpos hb hbone hbseam hh hε
  rw [hunion] at hfpl hfinj hfmap hfB hf'pl hf'map hinv hdist
  exact ⟨f, f', hfpl, hfinj, hfmap, hfB, fun x hx => hfRD (mem_union_left D hx),
    fun x hx => hfRD (mem_union_right R hx), hfix0, hf'pl, hf'map,
    fun x hx => hf'RD (mem_union_left D hx), fun x hx => hf'RD (mem_union_right R hx),
    hinv, hdist⟩

end Fixing

end DifferentialGeometry.Topology.PiecewiseLinear
