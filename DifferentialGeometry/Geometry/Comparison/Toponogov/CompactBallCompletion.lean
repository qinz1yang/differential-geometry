import DifferentialGeometry.Geometry.Comparison.DistanceHessianLocal

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M] in
private theorem edist_le_two_radius (g : SmoothRiemannianMetric I M) {o x y : M}
    {R : ℝ} (hR : 0 ≤ R)
    (hx : riemannianEDistOf g o x ≤ ENNReal.ofReal R)
    (hy : riemannianEDistOf g o y ≤ ENNReal.ofReal R) :
    riemannianEDistOf g x y ≤ ENNReal.ofReal (2 * R) := by
  calc
    _ ≤ riemannianEDistOf g x o + riemannianEDistOf g o y := riemannianEDistOf_triangle g x o y
    _ ≤ ENNReal.ofReal R + ENNReal.ofReal R := by
      rw [riemannianEDistOf_comm g x o]
      exact add_le_add hx hy
    _ = ENNReal.ofReal (2 * R) := by rw [← ENNReal.ofReal_add hR hR]; congr 1; ring

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem exists_complete_metric_preserving_closedBall_distances_and_lenses
    (g : SmoothRiemannianMetric I M) (o : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact {z : M | riemannianEDistOf g o z ≤ ENNReal.ofReal (4 * R)}) :
    ∃ (g' : SmoothRiemannianMetric I M) (W : Set M),
      RiemannianMetricComplete g' ∧ IsOpen W ∧
      {z : M | riemannianEDistOf g o z ≤ ENNReal.ofReal (4 * R)} ⊆ W ∧
      (∀ z ∈ W, g'.inner z = g.inner z) ∧
      (∀ (z : M) (v : TangentSpace I z), g.inner z v v ≤ g'.inner z v v) ∧
      ∀ x : M, riemannianEDistOf g o x ≤ ENNReal.ofReal R →
        ∀ y : M, riemannianEDistOf g o y ≤ ENNReal.ofReal R →
          riemannianEDistOf g' x y = riemannianEDistOf g x y ∧
          ∀ z : M,
            riemannianEDistOf g' x z + riemannianEDistOf g' z y = riemannianEDistOf g' x y →
            riemannianEDistOf g x z + riemannianEDistOf g z y = riemannianEDistOf g x y ∧
              z ∈ W := by
  obtain ⟨g', W, hcomplete, hW, hballW, heq, hle⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact (I := I) g hcompact
  refine ⟨g', W, hcomplete, hW, hballW, heq, hle, ?_⟩
  intro x hx y hy
  have hxy := edist_le_two_radius g hR.le hx hy
  have hpatch : {z : M | riemannianEDistOf g x z ≤ ENNReal.ofReal (3 * R)} ⊆ W := by
    intro z hz
    apply hballW
    calc
      _ ≤ riemannianEDistOf g o x + riemannianEDistOf g x z := riemannianEDistOf_triangle g o x z
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal (3 * R) := add_le_add hx hz
      _ = ENNReal.ofReal (4 * R) := by
        rw [← ENNReal.ofReal_add hR.le (by positivity)]; congr 1; ring
  have hxy3 : riemannianEDistOf g x y < ENNReal.ofReal (3 * R) :=
    hxy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith))
  have hd : riemannianEDistOf g' x y = riemannianEDistOf g x y :=
    riemannianEDistOf_eq_of_eqOn_ball g g' hpatch heq hle hxy3
  refine ⟨hd, ?_⟩
  intro z hz
  have hsum := (add_le_add (edistOf_mono g g' hle x z)
    (edistOf_mono g g' hle z y)).trans_eq (hz.trans hd)
  have hz4 : riemannianEDistOf g o z ≤ ENNReal.ofReal (4 * R) := by
    have hxz : riemannianEDistOf g x z ≤ ENNReal.ofReal (2 * R) :=
      (le_add_right le_rfl).trans (hsum.trans hxy)
    calc
      _ ≤ riemannianEDistOf g o x + riemannianEDistOf g x z := riemannianEDistOf_triangle g o x z
      _ ≤ ENNReal.ofReal R + ENNReal.ofReal (2 * R) := add_le_add hx hxz
      _ = ENNReal.ofReal (3 * R) := by
        rw [← ENNReal.ofReal_add hR.le (by positivity)]; congr 1; ring
      _ ≤ ENNReal.ofReal (4 * R) := ENNReal.ofReal_le_ofReal (by linarith)
  exact ⟨le_antisymm hsum (riemannianEDistOf_triangle g x z y), hballW hz4⟩

end DifferentialGeometry
