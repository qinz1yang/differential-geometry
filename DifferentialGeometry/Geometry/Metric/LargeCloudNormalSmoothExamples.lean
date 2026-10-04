import DifferentialGeometry.Topology.Manifold.ActualNormalProjectorSmooth
import DifferentialGeometry.Geometry.Metric.LargeCloudNormalDiscProperExamples

/-! Smooth actual normal projectors of the same nonempty two-centre nearest-disc supplier. -/

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis GC.MetricGeometry
open scoped BigOperators ContDiff Manifold
namespace GC.MetricGeometry.NearestJetsExamples

theorem two_center_cloud_has_smooth_actual_normal_projector :
    dist (center false) (center true) = 1 ∧
      offset ∈ (domain false : Set H) ∩ (domain true : Set H) ∧
    let S : Set H := range center
    let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) 2, isOpen_ball⟩
    let Ω : TopologicalSpace.Opens H :=
      ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∃ δ : ℝ, 0 < δ ∧
    ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
      I.PairwiseDisjoint (fun i => ball i (2 : ℝ)) ∧
      let w : H → H → ℝ := fun i y =>
        ballCutoff i (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y /
          (∑ a ∈ hI.toFinset,
            ballCutoff a (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y)
      let Q₀ : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
        Module.End.eigenspace
          (∑ i ∈ hI.toFinset, w i y • tangentᗮ.starProjection).toLinearMap μ
      let η : H → H := fun y => (Q₀ y).starProjection
        (y - ∑ i ∈ hI.toFinset, w i y • i)
      let U : Set H := ⋃ i ∈ I, ball i (20 * (1 / 20 : ℝ)⁻¹ * 2)
      let W : Set H := {z | z ∈ U ∧ η z = 0}
      W.Nonempty ∧
        ∃ cs : ChartedSpace (Fin 1 → ℝ) W,
          let _ := cs
          IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ W ∧
          _root_.Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, H) ∞
            (Subtype.val : W → H) ∧
          ∃ q : C^∞⟮𝓘(ℝ, H), Ω; 𝓘(ℝ, Fin 1 → ℝ), W⟯,
            _root_.Manifold.IsSubmersion 𝓘(ℝ, H) 𝓘(ℝ, Fin 1 → ℝ) ∞ q ∧
            (∀ z : Ω, IsMinOn (fun y => dist (z : H) y) W (q z : H) ∧
              (∀ y ∈ W, IsMinOn (fun v => dist (z : H) v) W y → y = (q z : H))) ∧
            (∀ x : S, ∀ z : V x,
              ‖(q ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩ : H) -
                ((x : H) + tangent.starProjection ((z : H) - x))‖ ≤ 1 / 10 ∧
              (let D : H →L[ℝ] H :=
                mfderiv 𝓘(ℝ, H) 𝓘(ℝ, H) (fun y : Ω => (q y : H))
                  ⟨(z : H), mem_iUnion.mpr ⟨x, z.property⟩⟩
              ‖D - tangent.starProjection‖ ≤ 1 / 20 ∧
                19 / 20 ≤ ‖D tangentVector‖)) ∧
            (let qAmbient : H → H := nearestAmbientExtension Ω W q
             ∀ x : S, ∀ z ∈ ball (x : H) 2, ∀ j : ℕ,
               ‖iteratedFDeriv ℝ j
                 (fun y => qAmbient y - ((x : H) + tangent.starProjection (y - x))) z‖ ≤
                   C j * δ * 2 * ((2 : ℝ)⁻¹) ^ j) ∧
            (∀ y : W, y ∈ nearestQuarterBase S (fun _point => 2) W → ∀ n : H, ‖n‖ ≤ 2 / 4 →
              n ∈ (actualZeroSetTangentSpace 1 W y)ᗮ →
              ∃ hz : (y : H) + n ∈ Ω, q ⟨(y : H) + n, hz⟩ = y) ∧
            (∃ e : nearestDiscDomain Ω W q (nearestQuarterBase S (fun _point => 2) W) (2 / 4) ≃ₜ
                actualNormalDisc 1 W (nearestQuarterBase S (fun _point => 2) W) (2 / 4),
              (∀ z, (e z : W × H) = nearestResidualCoordinates Ω W q z) ∧
                (nearestQuarterBase S (fun _point => 2) W : Set W).Nonempty ∧
                IsProperMap (actualNormalDiscProjection 1 W
                  (nearestQuarterBase S (fun _point => 2) W) (2 / 4)) ∧
                IsProperMap (nearestDiscProjection Ω q
                  (nearestQuarterBase S (fun _point => 2) W) (2 / 4)) ∧
                Function.Surjective (nearestDiscProjection Ω q
                  (nearestQuarterBase S (fun _point => 2) W) (2 / 4)) ∧
                ContMDiff 𝓘(ℝ, Fin 1 → ℝ) 𝓘(ℝ, H →L[ℝ] H) ∞
                  (actualZeroSetNormalProjector 1 W)) := by
  classical
  let S : Set H := range center
  let V : S → TopologicalSpace.Opens H := fun x => ⟨ball (x : H) 2, isOpen_ball⟩
  let Ω : TopologicalSpace.Opens H :=
    ⟨⋃ x, (V x : Set H), isOpen_iUnion (fun x => (V x).isOpen)⟩
  obtain ⟨hdist, hoverlap, C, hC, δ, hδ, I, hI, hIS, hdisj,
    hW, cs, hcs, hemb, q, hq, hnearest, hbounds, hjets, hinverse, e, he, hV, hPN, hP, honto⟩ :=
    two_center_cloud_has_proper_actual_normal_disc_projection
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y /
      (∑ a ∈ hI.toFinset,
        ballCutoff a (40 * (1 / 20 : ℝ)⁻¹ * 2) (2 * (40 * (1 / 20 : ℝ)⁻¹ * 2)) y)
  let Q₀ : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2),
    Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • tangentᗮ.starProjection).toLinearMap μ
  let η : H → H := fun y => (Q₀ y).starProjection
    (y - ∑ i ∈ hI.toFinset, w i y • i)
  let U : Set H := ⋃ i ∈ I, ball i (20 * (1 / 20 : ℝ)⁻¹ * 2)
  let W : Set H := {z | z ∈ U ∧ η z = 0}
  let : ChartedSpace (Fin 1 → ℝ) W := cs
  let : IsManifold 𝓘(ℝ, Fin 1 → ℝ) ∞ W := hcs
  exact ⟨hdist, hoverlap, C, hC, δ, hδ, I, hI, hIS, hdisj,
    hW, cs, hcs, hemb, q, hq, hnearest, hbounds, hjets, hinverse, e, he, hV,
    hPN, hP, honto, contMDiff_actualZeroSetNormalProjector hemb⟩

end GC.MetricGeometry.NearestJetsExamples
