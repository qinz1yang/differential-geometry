import DifferentialGeometry.Geometry.Metric.MarkerCloudApplications
import DifferentialGeometry.Geometry.Metric.CloudNormalGraphJets
import DifferentialGeometry.Geometry.Metric.CloudZeroSetManifold

/-! The SAME small-cloud section, graph jets and properly embedded zero manifold from markers. -/

set_option autoImplicit false
noncomputable section

open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff Manifold

namespace GC.MetricGeometry

universe u

theorem exists_uniform_small_marker_cloud_interpolant (k : ℕ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∃ F : ℕ → ℝ, (∀ m, 0 ≤ F m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ δ₀ →
        ∀ (MP MI : Type u) (f : MP → H) (ρ : MP → ℝ)
          (marker : MI → H → ℝ) (Rmarker : MI → ℝ) (select : H → MP) (σ : ℝ),
        (∀ i, 0 < Rmarker i) → (∀ i, LipschitzWith 1 (marker i)) →
        (∀ p, ∃ i, marker i (f p) = Rmarker i) →
        (∀ i p, 0 < marker i (f p) →
          3 * Rmarker i / 4 ≤ ρ p ∧ ρ p ≤ 5 * Rmarker i / 4) →
        (∀ x ∈ S, f (select x) = x) → (∀ x ∈ S, r x = σ * ρ (select x)) →
        0 ≤ σ → σ ≤ 1 / 2 →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * ((2 : ℝ) + 1))
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
          (∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5*ℓ*r x₀),
            (∀ z ∈ ball v (ℓ*r x₀), Manifold.IsSubmersionAt
              𝓘(ℝ,H) 𝓘(ℝ,(P x₀)ᗮ) ∞
                (fun y => (P x₀)ᗮ.orthogonalProjectionOnto (η y)) z) ∧
            {z : H | z ∈ ball v (ℓ*r x₀) ∧ (P x₀)ᗮ.orthogonalProjectionOnto (η z)=0} =
            {z : H | z ∈ ball v (ℓ*r x₀) ∧ η z=0}) ∧
          (let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
           let Z : Set H := {z | z ∈ Ω ∧ η z = 0}
           IsProperMap (fun z : Z => (⟨z.1, z.2.1⟩ : Ω)) ∧
             ∃ cs : ChartedSpace (Fin k → ℝ) Z,
               letI := cs
               IsManifold 𝓘(ℝ, Fin k → ℝ) ∞ Z ∧
                 Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin k → ℝ) 𝓘(ℝ, H) ∞
                   (Subtype.val : Z → H)) ∧
          ∀ i ∈ I, ∃ g : P i → (P i)ᗮ,
            ContDiffOn ℝ ∞ g (ball 0 (α * r i)) ∧
            (∀ t ∈ ball 0 (α * r i), ‖g t‖ ≤ α * r i / 4 ∧
              η (i + orthogonalCoordinateSum (P i) (t, g t)) = 0) ∧
            (∀ t ∈ ball 0 (α * r i), ∀ n ∈ closedBall 0 (α * r i),
              η (i + orthogonalCoordinateSum (P i) (t,n)) = 0 ↔ n = g t) ∧
            ∀ m, ∀ t ∈ ball 0 (α * r i), ∀ j, j ≤ m →
              ‖iteratedFDeriv ℝ j g t‖ ≤ F m * δ * r i * ((r i)⁻¹)^j := by
  classical
  obtain ⟨δ₀, hδ₀, F, hF, hproduce⟩ :=
    exists_uniform_cloud_normal_graph_jets.{u} k 2 (by norm_num)
  refine ⟨δ₀, hδ₀, F, hF, ?_⟩
  intro H instNorm instInner instFinite S T hST hS r P hdim rmin R δ
    hrmin hlower hupper hδ hδsmall MP MI f ρ marker Rmarker select σ
    hRmarker hmarker hfull hsupport hselect hr hσ hσhalf hcloud
  have hscale := markerChosenRadius_coarse_control f ρ marker Rmarker hRmarker
    hmarker hfull hsupport S select hselect r hr hσ hσhalf
  obtain ⟨I, hI, hIS, hdisj, hcover, hη, hlocal, hgraphs⟩ :=
    hproduce H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  refine ⟨I, hI, hIS, hdisj, hcover, hη, hlocal, ?_, hgraphs⟩
  refine ⟨DifferentialGeometry.Topology.isProperMap_relativeZeroSetInclusion _ _
    hη.continuousOn, ?_⟩
  exact exists_buffered_normal_zero_set_manifold k I r P _ (by norm_num)
    (fun i hi => hrmin.trans_le (hlower i (hIS hi)))
    (fun i hi => hdim i (hIS hi)) _ hη hlocal

end GC.MetricGeometry
