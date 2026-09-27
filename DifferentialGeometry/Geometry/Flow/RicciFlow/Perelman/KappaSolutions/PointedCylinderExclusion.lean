import DifferentialGeometry.Topology.ProjectiveSpace.CylinderProjectiveSlice
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.CompactEmbedding

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Set _root_.Topology
open DifferentialGeometry.CheegerGromovCompactness

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Phi : PointedRiemannianConvergenceMaps (I := I) X L subseq)

private local instance pointedExclusionLimitTopology : TopologicalSpace L.M := L.topology
private local instance pointedExclusionApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology

include Phi

theorem pointedLimit_not_projectiveEmbedding
    (hEuclidean : ∀ k : ℕ, Nonempty ((X.obj k).M ≃ₜ EuclideanSpace ℝ (Fin 3)))
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ IsEmbedding f) :
    ∀ e : SphereAntipodalQuotient → L.M, ¬ IsEmbedding e := by
  intro e he
  obtain ⟨k0, hk0⟩ := pointedMaps_eventually_compactEmbedding Phi e he
  obtain ⟨f, hf, _⟩ := hk0 k0 le_rfl
  obtain ⟨d⟩ := hEuclidean (subseq k0)
  exact hnoEmbedding (d ∘ f) (d.isEmbedding.comp hf.isEmbedding)

theorem pointedLimit_not_nontrivialCylinderQuotient
    (hEuclidean : ∀ k : ℕ, Nonempty ((X.obj k).M ≃ₜ EuclideanSpace ℝ (Fin 3)))
    (hnoEmbedding : ∀ f : SphereAntipodalQuotient → EuclideanSpace ℝ (Fin 3),
      ¬ IsEmbedding f) :
    ¬ Nonempty ((SphereAntipodalQuotient × ℝ) ≃ₜ L.M) ∧
      ¬ Nonempty (CylinderDiagonalQuotient ≃ₜ L.M) := by
  have hlimit := pointedLimit_not_projectiveEmbedding Phi hEuclidean hnoEmbedding
  constructor
  · rintro ⟨d⟩
    exact hlimit (d ∘ SphereAntipodalQuotient.zeroSlice)
      (d.isEmbedding.comp SphereAntipodalQuotient.isClosedEmbedding_zeroSlice.isEmbedding)
  · rintro ⟨d⟩
    exact hlimit (d ∘ CylinderDiagonalQuotient.projectiveSlice)
      (d.isEmbedding.comp CylinderDiagonalQuotient.isClosedEmbedding_projectiveSlice.isEmbedding)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
