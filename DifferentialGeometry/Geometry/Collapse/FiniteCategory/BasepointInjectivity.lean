import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Bounds.VolumeInjectivity
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# LFR08 for complete smooth manifolds carrying their Riemannian distance

Blueprint 207A, LFR08 (`lem:collapse-local-injectivity-from-basepoint`, A:25380–25411): a basepoint
volume lower bound `Vol B(p,r) ≥ v` and `|Rm| ≤ A` on `B(p, 2S + r + 2)` give one injectivity
radius lower bound `ι(n, r, v, S, A) > 0` on `B(p, S)`.

The row is the ported theorem
`DifferentialGeometry.CheegerGromovCompactness.exists_uniform_injRadius_of_base_volume`
(`Pointed/Bounds/VolumeInjectivity.lean`, verbatim from the team branch). This file binds it to
the aligned block used by W3-F1 and the local-collapse rows: a manifold `M` whose metric-space
distance is the Riemannian distance of `g` (`hmetric`), balls are metric balls and the volume is
`ballVolume`. The constant `ι` is chosen before the manifold, so it is common to every member of a
sequence with these data (`exists_uniform_injRadius_of_basepoint_volume_seq`).
-/

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Curvature

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- The pointed smooth Riemannian manifold `(M, g, p)` of an aligned manifold. -/
@[reducible] noncomputable def alignedPointed {n : ℕ} (M : Type u) [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)] [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) (p : M) :
    PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) :=
  { M := M, basepoint := p, metric := g }

/-- **LFR08, aligned binding.** For `n ≥ 2` and `r, v, S, A > 0` there is `ι > 0` such that for
every complete smooth `n`-manifold `M` whose distance is the Riemannian distance of `g`, every
`p` with `Vol_g B(p,r) ≥ v` and `|Rm_g| ≤ A` on `B(p, 2S + r + 2)`, the injectivity radius of
`(M, g)` is at least `ι` at every point of `B(p, S)`. -/
theorem exists_uniform_injRadius_of_basepoint_volume (n : ℕ) (hn : 2 ≤ n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    ∃ ι : ℝ, 0 < ι ∧ ∀ (M : Type u) [MetricSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
      [T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)] [SigmaCompactSpace M]
      [CompleteSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M),
      (∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) →
      ∀ p : M, ENNReal.ofReal v ≤ ballVolume g p r →
      (∀ y ∈ ball p (2 * S + r + 2),
        Real.sqrt (Tensor0SBundle.normSq0S g y 4 (metricRm04At g y)) ≤ A) →
      ∀ x ∈ ball p S, HasInjRadiusAt (alignedPointed M g p) x ι := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by simpa using (show n ≠ 0 by omega)⟩
  obtain ⟨ι, hι, hinj⟩ := exists_uniform_injRadius_of_base_volume.{u} n hn hr hv hS hA
  refine ⟨ι, hι, ?_⟩
  intro M _ _ _ _ _ _ g hmetric p hvol hRm x hx
  have hmem : ∀ {y : M} {R : ℝ}, y ∈ riemannianBallOf g p R ↔ y ∈ ball p R := by
    intro y R
    change riemannianEDistOf g p y < ENNReal.ofReal R ↔ _
    rw [hmetric, mem_ball, dist_comm]
    constructor
    · intro h
      exact (ENNReal.ofReal_lt_ofReal_iff'.1 h).1
    · intro h
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg h)).2 h
  have hcomplete : RiemannianMetricComplete g :=
    (riemannianMetricComplete_iff_completeSpace hmetric).mpr inferInstance
  exact hinj (alignedPointed M g p) hcomplete.complete hvol
    (fun y hy => hRm y (hmem.1 hy)) x (hmem.2 hx)

/-- **LFR08 for a sequence.** One injectivity radius for every member of a sequence of complete
smooth aligned `n`-manifolds with a common basepoint volume bound and common curvature bound on
`B(p i, 2S + r + 2)`. -/
theorem exists_uniform_injRadius_of_basepoint_volume_seq (n : ℕ) (hn : 2 ≤ n) {r v S A : ℝ}
    (hr : 0 < r) (hv : 0 < v) (hS : 0 < S) (hA : 0 < A)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) (hvol : ∀ i, ENNReal.ofReal v ≤ ballVolume (g i) (p i) r) :
    letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
      ⟨by simpa using (show n ≠ 0 by omega)⟩
    (∀ i, ∀ y ∈ ball (p i) (2 * S + r + 2),
      Real.sqrt (Tensor0SBundle.normSq0S (g i) y 4 (metricRm04At (g i) y)) ≤ A) →
    ∃ ι : ℝ, 0 < ι ∧ ∀ i, ∀ x ∈ ball (p i) S,
      HasInjRadiusAt (alignedPointed (X i) (g i) (p i)) x ι := by
  intro hRm
  obtain ⟨ι, hι, h⟩ := exists_uniform_injRadius_of_basepoint_volume.{u} n hn hr hv hS hA
  exact ⟨ι, hι, fun i => h (X i) (g i) (hmetric i) (p i) (hvol i) (hRm i)⟩

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
