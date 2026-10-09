import DifferentialGeometry.Geometry.Metric.Distance.Differential
import DifferentialGeometry.Geometry.Measure.LocalIsometry

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Measure

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

theorem measurePreserving_diffeomorph_of_riemannian_distance_eq
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J⟯ N)
    (hdist : ∀ x y : M, riemannianEDistOf h (Φ x) (Φ y) = riemannianEDistOf g x y) :
    MeasureTheory.MeasurePreserving Φ
      (Integral.Measure.riemannianVolumeMeasure I M g) (Integral.Measure.riemannianVolumeMeasure J N h) := by
  have hmetric (x : M) (v w : TangentSpace I x) :
      g.inner x v w = h.inner (Φ x) (mfderiv I J Φ x v) (mfderiv I J Φ x w) := by
    by_cases hzero : Module.finrank ℝ E = 0
    · let _ : Subsingleton E := Module.finrank_zero_iff.mp hzero
      have hv : v = 0 := by
        change (v : E) = (0 : E)
        exact @Subsingleton.elim E inferInstance (v : E) 0
      simp only [hv, map_zero, zero_apply]
    · let _ : NeZero (Module.finrank ℝ E) := ⟨hzero⟩
      have hdim : Module.finrank ℝ E = Module.finrank ℝ F :=
        (Φ.mfderivToContinuousLinearEquiv (by decide) x).toLinearEquiv.finrank_eq
      let _ : NeZero (Module.finrank ℝ F) := ⟨fun h => hzero (hdim.trans h)⟩
      have he := Riemannian.inner_mfderiv_eq_mul_of_eventually_riemannian_distance_eq g h Φ x 1
        (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by decide))
        (Filter.Eventually.of_forall fun y => by rw [hdist, one_mul]) v w
      simpa only [one_pow, one_mul] using he.symm
  refine ⟨Φ.contMDiff.continuous.measurable, ?_⟩
  rw [riemannianVolumeMeasure_map_of_injective_local_isometry g h Φ Φ.isLocalDiffeomorph
    Φ.injective hmetric]
  have hr : Set.range (Φ : M → N) = Set.univ := Φ.surjective.range_eq
  rw [hr, MeasureTheory.Measure.restrict_univ]

end DifferentialGeometry.Geometry.Measure
