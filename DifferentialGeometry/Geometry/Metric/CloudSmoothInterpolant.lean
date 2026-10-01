import DifferentialGeometry.Geometry.Metric.CloudNormalGraphJets
import DifferentialGeometry.Geometry.Metric.CloudZeroSetManifold

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold
namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_smooth_interpolant (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        let α : ℝ := ℓ / 4
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          let η : H → H := fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)
          ContDiffOn ℝ ∞ η (⋃ i ∈ I, ball i (6 * ℓ * r i)) ∧
          let Ω : Set H := ⋃ i ∈ I, ball i (6*ℓ*r i)
          let Z : Set H := {z | z ∈ Ω ∧ η z=0}
          IsProperMap (fun z : Z => (⟨z.1,z.2.1⟩ : Ω)) ∧
          (∃ cs : ChartedSpace (Fin k → ℝ) Z,
            let _ := cs
            IsManifold 𝓘(ℝ,Fin k → ℝ) ∞ Z ∧
            Manifold.IsSmoothEmbedding 𝓘(ℝ,Fin k → ℝ) 𝓘(ℝ,H) ∞ (Subtype.val : Z → H)) ∧
          ∀ i ∈ I, ∃ g : P i → (P i)ᗮ,
            ContDiffOn ℝ ∞ g (ball 0 (α * r i)) ∧
            (∀ t ∈ ball 0 (α * r i), ‖g t‖ ≤ α * r i / 4 ∧
              η (i + orthogonalCoordinateSum (P i) (t, g t)) = 0) ∧
            (∀ t ∈ ball 0 (α * r i), ∀ n ∈ closedBall 0 (α * r i),
              η (i + orthogonalCoordinateSum (P i) (t,n)) = 0 ↔ n = g t) ∧
            ∀ m, ∀ t ∈ ball 0 (α * r i), ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j g t‖ ≤ F m * δ * r i * ((r i)⁻¹)^j := by
  obtain ⟨δ₀,hδ₀,F,hF,hprod⟩ := exists_uniform_cloud_normal_graph_jets.{u} k C hC
  refine ⟨δ₀,hδ₀,F,hF,?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  obtain ⟨I,hI,hIS,hdisj,hcover,hη,hlocal,hgraphs⟩ :=
    hprod H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  refine ⟨I,hI,hIS,hdisj,hcover,hη,?_,?_,hgraphs⟩
  · exact DifferentialGeometry.Topology.isProperMap_relativeZeroSetInclusion _ _ hη.continuousOn
  · exact exists_buffered_normal_zero_set_manifold k I r P _ (by positivity)
      (fun i hi => hrmin.trans_le (hlower i (hIS hi)))
      (fun i hi => hdim i (hIS hi)) _ hη hlocal

end GC.MetricGeometry
