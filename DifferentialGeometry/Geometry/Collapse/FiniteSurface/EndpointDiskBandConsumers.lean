import DifferentialGeometry.Geometry.Collapse.FiniteSurface.EndpointDiskBand

/-!
# Consumers of LFR22 and LFR23

* `nonempty_homeomorph_disk_closedBall_of_endpoint`: under LFR23's hypotheses the closed balls
  `B̄(z₀, a)`, `a ∈ [1, 9]`, are homeomorphic to the closed unit disk, by a homeomorphism carrying
  the boundary circle onto the level `{r = a}`;
* `finiteSurface_noncompact_plane_or_cylinder`: LFR22's noncompact clause on the model `𝓡 2`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric Function Topology
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {Z : Type*} [MetricSpace Z] [ChartedSpace E2 Z] [IsManifold (𝓡 2) ∞ Z]
  [RiemannianBundle (fun x : Z => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) Z]
  [CompleteSpace Z] [ConnectedSpace Z]

/-- **Consumer (LFR23).** The closed balls of radius `a ∈ [1, 9]` are closed disks. -/
theorem nonempty_homeomorph_disk_closedBall_of_endpoint (o : ManifoldOrientation (𝓡 2) Z 2)
    {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w)
    {z₀ : Z} {q : Z → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 24000000) (hq0 : q z₀ = 0)
    (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10,
      |dist (q y) (q y') - dist y y'| ≤ δ)
    (hdense : ∀ t ∈ Icc (0 : ℝ) 10, ∃ y ∈ closedBall z₀ 10, |q y - t| ≤ δ) {a : ℝ}
    (ha : a ∈ Icc (1 : ℝ) 9) :
    ∃ h : Disk 2 ≃ₜ closedBall z₀ a, ∀ x ∈ diskSphere 2, (h x : Z) ∈ sphere z₀ a := by
  obtain ⟨-, -, hdisk⟩ := finiteSurface_endpoint_disk_band o k hr hnorm hK hδ hδ' hq0 hqnn hdist
    hdense
  obtain ⟨-, e, he, hrange, hbd⟩ := hdisk a ha
  refine ⟨he.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange), fun x hx => ?_⟩
  rw [← hbd]
  exact ⟨x, hx, rfl⟩

/-- **Consumer (LFR22, noncompact clause).** -/
theorem finiteSurface_noncompact_plane_or_cylinder [NoncompactSpace Z]
    (o : ManifoldOrientation (𝓡 2) Z 2) {r : ℕ∞}
    (k : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2 (TangentSpace (𝓡 2) : Z → Type _))
    (hr : 3 ≤ r)
    (hnorm : ∀ (x : Z) (w : TangentSpace (𝓡 2) x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (k.inner x w w)))
    (hK : ∀ x (v w : TangentSpace (𝓡 2) x), 0 ≤ k.sectionalCurvature x v w) :
    Nonempty (Z ≃ₜ E2) ∨ Nonempty (Z ≃ₜ AddCircle (1 : ℝ) × ℝ) := by
  rcases finiteSurface_types o k hr hnorm hK with ⟨hc, -⟩ | ⟨-, h⟩
  · exact absurd hc (not_compactSpace_iff.mpr inferInstance)
  · exact h

end DifferentialGeometry.Geometry.Collapse
