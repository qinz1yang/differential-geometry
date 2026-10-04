import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.BallImage


set_option autoImplicit false
noncomputable section
open Bundle Set Manifold Metric
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Riemannian
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem rotated_image_ball
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (Q : E ≃ₗᵢ[ℝ] E) (Φ : OpenPartialHomeomorph E M)
    {R r : ℝ}
    (hmap : EqOn Φ (intrinsicFramedExp g hEnorm p ∘ Q) (ball 0 R))
    (hr : r ≤ R) : (Φ : E → M) '' ball 0 r = ball p r := by
  calc
    (Φ : E → M) '' ball 0 r =
        (intrinsicFramedExp g hEnorm p ∘ Q) '' ball 0 r :=
      image_congr (fun z hz => hmap (ball_subset_ball hr hz))
    _ = intrinsicFramedExp g hEnorm p '' ball 0 r := by
      rw [image_comp, Q.image_ball, map_zero]
    _ = ball p r := by rw [intrinsicFramedExp_image_ball, eball_ofReal]

theorem radial_geometry_of_eqOn_intrinsicFramedExp
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) (Q : E ≃ₗᵢ[ℝ] E) (Φ : OpenPartialHomeomorph E M)
    {R : ℝ} (hsource : ball (0 : E) R ⊆ Φ.source)
    (hmap : EqOn Φ (intrinsicFramedExp g hEnorm p ∘ Q) (ball 0 R)) :
    (∀ z ∈ ball 0 R, dist (Φ z) p = ‖z‖) ∧
      (∀ r ≤ R, (Φ : E → M) '' ball 0 r = ball p r) ∧
      ∀ r < R, (Φ : E → M) '' closedBall 0 r = closedBall p r := by
  have himage {r : ℝ} (hr : r ≤ R) : (Φ : E → M) '' ball 0 r = ball p r :=
    rotated_image_ball g hEnorm p Q Φ hmap hr
  have hrad (z : E) (hz : z ∈ ball 0 R) : dist (Φ z) p = ‖z‖ := by
    have hzin : z ∈ Φ.source := hsource hz
    have hball : Φ z ∈ ball p R := by rw [← himage le_rfl]; exact mem_image_of_mem _ hz
    have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    have hdR : dist (Φ z) p < R := hball
    apply le_antisymm
    · by_contra! hlt
      let r := (‖z‖ + dist (Φ z) p) / 2
      have hrR : r ≤ R := by dsimp [r]; linarith
      have hzr : z ∈ ball 0 r := by simp only [mem_ball, dist_zero_right]; dsimp [r]; linarith
      have hy : Φ z ∈ ball p r := by rw [← himage hrR]; exact mem_image_of_mem _ hzr
      change dist (Φ z) p < r at hy
      dsimp [r] at hy
      linarith
    · by_contra! hlt
      have hy : Φ z ∈ ball p ‖z‖ := hlt
      rw [← himage hzR.le] at hy
      obtain ⟨w, hw, heq⟩ := hy
      have hwsrc : w ∈ Φ.source := hsource (ball_subset_ball hzR.le hw)
      have hwz : w = z := Φ.toPartialEquiv.injOn hwsrc hzin heq
      rw [hwz] at hw
      simp only [mem_ball, dist_zero_right, lt_self_iff_false] at hw
  refine ⟨hrad, fun r hr => himage hr, ?_⟩
  intro r hr
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_closedBall, hrad z (closedBall_subset_ball hr hz)]
    simpa only [mem_closedBall, dist_zero_right] using hz
  · intro hy
    have hyR : y ∈ ball p R := closedBall_subset_ball hr hy
    rw [← himage le_rfl] at hyR
    obtain ⟨z, hz, rfl⟩ := hyR
    refine ⟨z, ?_, rfl⟩
    simpa only [mem_closedBall, dist_zero_right, hrad z hz] using hy
end

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
