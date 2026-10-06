import DifferentialGeometry.Geometry.Metric.Approximation.SplittingRank

/-!
# Relaxing the tolerance of a Kleiner-Lott approximation (S-X144c, group G9)

A `KleinerLottApprox p q δ` is an approximation at the *fixed* base points `p ↦ q` (the field
`basepoint : toFun p = q`), on the ball `B(p, δ⁻¹)`, with additive distortion `δ` and
coverage `δ` up to `δ⁻¹ − δ`. Passing to a larger tolerance `β` shrinks the ball to
`B(p, β⁻¹)`, so distortion is inherited, but the coverage of the points `y` with
`d(y, q) < β⁻¹ − β` must produce a preimage inside the *smaller* ball. The radial control
`|d(f x, q) − d(x, p)| ≤ δ` (`KleinerLottApprox.radial_error`) gives it exactly when
`2 δ ≤ β`:

* `KleinerLottApprox.relax_SMR` : `KleinerLottApprox p q δ → 2 δ ≤ β → β < 1 →
  KleinerLottApprox p q β` — the best constant of the argument. The two errors that add up are
  the coverage error `δ (+ ε)` and the radial error `δ`; the slack `ε` comes from the strictness
  of `d(y, q) < β⁻¹ − β` (the `infDist` form of the coverage, not the `< 2 δ` form of
  `coverage_witness`, is used);
* `KleinerLottApprox.relax_three_SMR` : the same with `3 δ ≤ β`, the constant of
  `KleinerLottApprox.toClosedBall` (a corollary);
* `HasEuclideanSplitting.relax_SMR` : tolerance monotonicity of `HasEuclideanSplitting`
  (`HasEuclideanSplitting p k δ → 2 δ ≤ β → β < 1 → HasEuclideanSplitting p k β`), which is the
  tool that replaces the explicit splitting hypotheses `h1`, `h2` of the rank adapters.

Base points: the base point is part of the data of the structure, so the relaxed approximation
has the *same* `p ↦ q` and the same map `toFun`; a change of the base point is a separate
operation (`KleinerLottApprox.transport_SMR` in `SplittingOfThinProduct` moves `q` along an
isometry of the target).
-/

set_option autoImplicit false

namespace GC.MetricGeometry

universe u v

section Relax

variable {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] {p : X} {q : Y} {δ β : ℝ}

/-- **Tolerance relaxation.** A Kleiner-Lott `δ`-approximation at `p ↦ q` is a Kleiner-Lott
`β`-approximation with the same map and base points as soon as `2 δ ≤ β < 1`. -/
def KleinerLottApprox.relax_SMR (f : KleinerLottApprox p q δ) (hβ : 2 * δ ≤ β)
    (hβ1 : β < 1) : KleinerLottApprox p q β where
  error_pos := by linarith [f.error_pos]
  error_lt_one := hβ1
  toFun := f.toFun
  basepoint := f.basepoint
  distortion x hx x' hx' := by
    have hδβ : δ ≤ β := by linarith [f.error_pos]
    have hsub : Metric.ball p β⁻¹ ⊆ Metric.ball p δ⁻¹ :=
      Metric.ball_subset_ball (inv_anti₀ f.error_pos hδβ)
    exact (f.distortion x (hsub hx) x' (hsub hx')).trans hδβ
  coverage y hy := by
    have hδβ : δ ≤ β := by linarith [f.error_pos]
    have hinv : β⁻¹ ≤ δ⁻¹ := inv_anti₀ f.error_pos hδβ
    have hsub : Metric.ball p β⁻¹ ⊆ Metric.ball p δ⁻¹ := Metric.ball_subset_ball hinv
    have hy' : dist y q < δ⁻¹ - δ := by linarith
    set s : ℝ := β⁻¹ - β - dist y q with hs
    have hspos : 0 < s := by rw [hs]; linarith
    set ε : ℝ := min (s / 2) δ with hε
    have hε1 : ε ≤ s / 2 := min_le_left _ _
    have hε2 : ε ≤ δ := min_le_right _ _
    have hεpos : 0 < ε := lt_min (by linarith) f.error_pos
    have hlt : Metric.infDist y (f.toFun '' Metric.ball p δ⁻¹) < δ + ε :=
      lt_of_le_of_lt (f.coverage y hy') (by linarith)
    obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := (Metric.infDist_lt_iff f.image_nonempty).mp hlt
    have hrad := (abs_le.mp (f.radial_error x hx)).1
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxball : x ∈ Metric.ball p β⁻¹ := by
      rw [Metric.mem_ball]
      linarith
    have hmem : f.toFun x ∈ f.toFun '' Metric.ball p β⁻¹ := ⟨x, hxball, rfl⟩
    exact (Metric.infDist_le_dist_of_mem hmem).trans (by linarith)

/-- The relaxation with the constant `3 δ ≤ β` of `KleinerLottApprox.toClosedBall`. -/
def KleinerLottApprox.relax_three_SMR (f : KleinerLottApprox p q δ) (hβ : 3 * δ ≤ β)
    (hβ1 : β < 1) : KleinerLottApprox p q β :=
  f.relax_SMR (by linarith [f.error_pos]) hβ1

end Relax

section Splitting

variable {X : Type u} [MetricSpace X] {p : X} {k : ℕ} {δ β : ℝ}

/-- **Tolerance monotonicity of `HasEuclideanSplitting`**: a `k`-splitting at tolerance `δ` is
a `k`-splitting at every tolerance `β` with `2 δ ≤ β < 1` (same factor, same base point). -/
theorem HasEuclideanSplitting.relax_SMR (h : HasEuclideanSplitting.{u, v} p k δ)
    (hβ : 2 * δ ≤ β) (hβ1 : β < 1) : HasEuclideanSplitting.{u, v} p k β := by
  obtain ⟨Y, mY, q, ⟨f⟩⟩ := h
  exact ⟨Y, mY, q, ⟨f.relax_SMR hβ hβ1⟩⟩

/-- The same with `3 δ ≤ β`. -/
theorem HasEuclideanSplitting.relax_three_SMR (h : HasEuclideanSplitting.{u, v} p k δ)
    (hβ : 3 * δ ≤ β) (hβ1 : β < 1) : HasEuclideanSplitting.{u, v} p k β := by
  obtain ⟨Y, mY, q, ⟨f⟩⟩ := h
  exact ⟨Y, mY, q, ⟨f.relax_three_SMR hβ hβ1⟩⟩

end Splitting

end GC.MetricGeometry
