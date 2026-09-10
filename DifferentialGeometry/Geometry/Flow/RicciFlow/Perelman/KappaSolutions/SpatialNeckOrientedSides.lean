import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckReflection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeckPositiveTopology

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [T2Space (TangentBundle I N)] [SigmaCompactSpace N]
  [ConnectedSpace N] [NoncompactSpace N]

namespace SpatialNeckWitness

theorem exists_oriented_compact_end_sides
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) h) :
    ∃ W' : SpatialNeckWitness h yStar p epsilon,
      (W' = W ∨ W' = W.reflect) ∧ W'.centralSphere = W.centralSphere ∧
      W'.core = W.core ∧ W'.image = W.image ∧
      ∃ B U : Set N,
        IsConnected B ∧ IsConnected U ∧ IsOpen B ∧ IsOpen U ∧ Disjoint B U ∧
        B ∪ U = W.centralSphereᶜ ∧
        IsCompact (closure B) ∧ ¬ IsCompact (closure U) ∧
        closure B = B ∪ W.centralSphere ∧ interior (closure B) = B ∧
        frontier (closure B) = W.centralSphere ∧ frontier U = W.centralSphere ∧
        (∀ x : spatialNeckBuffer epsilon, x.val.2 < 0 → W'.embedding x ∈ B) ∧
        (∀ x : spatialNeckBuffer epsilon, 0 < x.val.2 → W'.embedding x ∈ U) := by
  obtain ⟨B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc, hcl, hint, hfr, hUfr,
    hsides⟩ := W.compact_end_sides hsec
  rcases hsides with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · exact ⟨W, Or.inl rfl, rfl, rfl, rfl, B, U, hB, hU, hBop, hUop, hBU,
      hcover, hBc, hUnc, hcl, hint, hfr, hUfr, hn, hp⟩
  · refine ⟨W.reflect, Or.inr rfl, W.reflect_centralSphere, W.reflect_core,
      W.reflect_image, B, U, hB, hU, hBop, hUop, hBU, hcover, hBc, hUnc,
      hcl, hint, hfr, hUfr, ?_, ?_⟩
    · intro x hx
      rw [W.reflect_embedding]
      apply hp
      rw [spatialNeckReflection_val]
      exact neg_pos.mpr hx
    · intro x hx
      rw [W.reflect_embedding]
      apply hn
      rw [spatialNeckReflection_val]
      exact neg_neg_of_pos hx

end SpatialNeckWitness

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
