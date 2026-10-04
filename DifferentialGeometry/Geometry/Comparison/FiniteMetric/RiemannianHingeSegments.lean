import DifferentialGeometry.Geometry.Comparison.FiniteMetric.RiemannianHinge
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.HopfRinow

/-!
# CM5.b with segment input (LFR21 G3 hinge part)

For a complete finite-regularity metric `g : C^{r+1}` (`2 ≤ r`) with `sec_g ≥ 0`, whose length
distance is the ambient distance (`hnorm`):

* `comparisonAngle_le_arccos_of_segments_finite`: two unit-speed metric segments `c₁ : [0, a] → M`,
  `c₂ : [0, b] → M` from `o` are radial geodesics `t ↦ exp_o (t u)`, `t ↦ exp_o (t v)` with
  `|u| = |v| = 1` (CM2.a, `exists_expMap_eq_of_segment`), and
  `comparisonAngle a b d(c₁ a, c₂ b) ≤ arccos g_o(u, v)` (CM5.b);
* `comparisonAngle_le_arccos_of_points_finite`: the same for three points `o, y, z`, with the
  minimizing radial geodesics of CM2.b (`exists_unit_segment_expMap`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.FiniteComparison

open DifferentialGeometry.Geometry.Comparison.Toponogov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **CM5.b, segment input** (LFR21 G3 hinge part): two unit-speed metric segments from `o` are
radial geodesics with unit initial directions `u, v`, and the Euclidean comparison angle of their
endpoints is at most the Riemannian angle `arccos g_o(u, v)`. -/
theorem comparisonAngle_le_arccos_of_segments_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {o : M} {c₁ c₂ : ℝ → M} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc₁0 : c₁ 0 = o) (hc₂0 : c₂ 0 = o)
    (hc₁ : ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a, dist (c₁ s) (c₁ t) = |s - t|)
    (hc₂ : ∀ s ∈ Icc 0 b, ∀ t ∈ Icc 0 b, dist (c₂ s) (c₂ t) = |s - t|) :
    ∃ u v : E, g.inner o u u = 1 ∧ g.inner o v v = 1 ∧
      (∀ t ∈ Icc 0 a, c₁ t = g.expMap (⟨o, t • u⟩ : TangentBundle I M)) ∧
      (∀ t ∈ Icc 0 b, c₂ t = g.expMap (⟨o, t • v⟩ : TangentBundle I M)) ∧
      comparisonAngle a b (dist (c₁ a) (c₂ b)) ≤ Real.arccos (g.inner o u v) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨u, hu, hcu⟩ := Bundle.ContMDiffRiemannianMetric.exists_expMap_eq_of_segment g hr hnorm hc₁
  obtain ⟨v, hv, hcv⟩ := Bundle.ContMDiffRiemannianMetric.exists_expMap_eq_of_segment g hr hnorm hc₂
  subst hc₁0
  have hA : c₁ a = g.expMap (⟨c₁ 0, a • u⟩ : TangentBundle I M) := (hcu a ⟨ha.le, le_rfl⟩).2
  have hB : c₂ b = g.expMap (⟨c₁ 0, b • v⟩ : TangentBundle I M) := by
    rw [← hc₂0]
    exact (hcv b ⟨hb.le, le_rfl⟩).2
  have hv' : g.inner (c₁ 0) v v = 1 := by
    rw [← hc₂0]
    exact hv
  have hminA : dist (c₁ 0) (g.expMap (⟨c₁ 0, a • u⟩ : TangentBundle I M)) = a := by
    rw [← hA, hc₁ 0 ⟨le_rfl, ha.le⟩ a ⟨ha.le, le_rfl⟩, zero_sub, abs_neg, abs_of_pos ha]
  have hminB : dist (c₁ 0) (g.expMap (⟨c₁ 0, b • v⟩ : TangentBundle I M)) = b := by
    rw [← hB, ← hc₂0, hc₂ 0 ⟨le_rfl, hb.le⟩ b ⟨hb.le, le_rfl⟩, zero_sub, abs_neg, abs_of_pos hb]
  refine ⟨u, v, hu, hv', fun t ht => (hcu t ht).2, fun t ht => ?_, ?_⟩
  · rw [← hc₂0]
    exact (hcv t ht).2
  · rw [hA, hB]
    exact comparisonAngle_le_arccos_inner_finite g hr1 hnorm _ u v ha hb hu hv' hminA hminB hsec

/-- **CM5.b for three points**: from `o` to `y ≠ o` and `z ≠ o` run minimizing radial geodesics
with unit initial directions `u, v`, and the Euclidean comparison angle of the triangle at `o` is at
most `arccos g_o(u, v)`. -/
theorem comparisonAngle_le_arccos_of_points_finite
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hsec : ∀ y : M, ∀ w₁ w₂ : TangentSpace I y, 0 ≤ g.sectionalCurvature y w₁ w₂)
    {o y z : M} (hy : y ≠ o) (hz : z ≠ o) :
    ∃ u v : E, g.inner o u u = 1 ∧ g.inner o v v = 1 ∧
      g.expMap (⟨o, dist o y • u⟩ : TangentBundle I M) = y ∧
      g.expMap (⟨o, dist o z • v⟩ : TangentBundle I M) = z ∧
      comparisonAngle (dist o y) (dist o z) (dist y z) ≤ Real.arccos (g.inner o u v) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  obtain ⟨u, hu, -, hyu⟩ := Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm o y
  obtain ⟨v, hv, -, hzv⟩ := Bundle.ContMDiffRiemannianMetric.exists_unit_segment_expMap g hr hnorm o z
  have hminA : dist o (g.expMap (⟨o, dist o y • u⟩ : TangentBundle I M)) = dist o y := by
    rw [hyu]
  have hminB : dist o (g.expMap (⟨o, dist o z • v⟩ : TangentBundle I M)) = dist o z := by
    rw [hzv]
  have h := comparisonAngle_le_arccos_inner_finite g hr1 hnorm o u v (dist_pos.mpr hy.symm)
    (dist_pos.mpr hz.symm) hu hv hminA hminB hsec
  rw [hyu, hzv] at h
  exact ⟨u, v, hu, hv, hyu, hzv, h⟩

end DifferentialGeometry.Geometry.FiniteComparison
