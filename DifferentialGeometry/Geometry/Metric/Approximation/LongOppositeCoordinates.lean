import DifferentialGeometry.Geometry.Metric.Approximation.OppositeEndpointCoordinates
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionFactorGeometry

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {σ : ℕ → ℝ}

theorem PointedGHConverges.exists_line_coordinates_of_long_opposite_angles
    (h : PointedGHConverges o p)
    (hs : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (aPlus aMinus : ∀ i, ι → A i)
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (hp : ∀ i j, dist (o i) (aPlus i j) = (σ i)⁻¹)
    (hm : ∀ i j, dist (o i) (aMinus i j) = (σ i)⁻¹)
    (hangle : ∀ j, ∀ᶠ i in atTop, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (o i) (aPlus i j)) (dist (o i) (aMinus i j)) (dist (aPlus i j) (aMinus i j))) :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => o (ψ i)) p ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (o (ψ i)) p (R i) (ε i),
      ∃ q : ∀ i _j, Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹) → A (ψ i),
      (∀ i j, LipschitzWith 1 (q i j)) ∧
      (∀ i j, q i j ⟨0, ⟨by linarith [inv_pos.mpr (hσpos (ψ i))], (inv_pos.mpr (hσpos (ψ i))).le⟩⟩ = o (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((σ (ψ i))⁻¹),
        t.val - σ (ψ i) ≤ (σ (ψ i))⁻¹ - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ≤ t.val ∧
        -t.val ≤ (σ (ψ i))⁻¹ - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ≤
          -t.val + (2 * (σ (ψ i))⁻¹ - dist (aPlus (ψ i) j) (aMinus (ψ i) j)) + σ (ψ i)) ∧
      ∃ γ : ι → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (σ (ψ i))⁻¹ ∧
          ∀ t : Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (q i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨q i j t, ht⟩) (γ j t.val) < ζ) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (o (ψ i)) (R i), dist x.val (o (ψ i)) ≤ S →
            |dist (o (ψ i)) (aPlus (ψ i) j) - dist x.val (aPlus (ψ i) j) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun i => (σ i)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hwithin
  exact h.exists_line_coordinates_of_opposite_endpoints hs hsegments hcurves aPlus aMinus
    (L := fun i _ => (σ i)⁻¹) (fun i _ => inv_pos.mpr (hσpos i)) (fun _ => hL) hp hm
    (fun j => tendsto_opposite_endpoint_excess_zero hσpos hσ (fun i => inv_pos.mpr (hσpos i))
      (fun i => hp i j) (fun i => hm i j) (hangle j)) hσpos hσ

theorem PointedGHConverges.exists_line_coordinates_of_reciprocal_local_geometry
    [∀ i, CompleteSpace (A i)] (h : PointedGHConverges o p) {n : ℕ}
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (ball (o i) ((σ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (o i) ((σ i)⁻¹),
      ∃ Ω : Set (A i), IsOpen Ω ∧ fourPointComparison (σ i) Ω ∧ z ∈ Ω)
    (aPlus aMinus : ∀ i, ι → A i)
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (hp : ∀ i j, dist (o i) (aPlus i j) = (σ i)⁻¹)
    (hm : ∀ i j, dist (o i) (aMinus i j) = (σ i)⁻¹)
    (hangle : ∀ j, ∀ᶠ i in atTop, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (o i) (aPlus i j)) (dist (o i) (aMinus i j)) (dist (aPlus i j) (aMinus i j))) :
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => o (ψ i)) p ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (o (ψ i)) p (R i) (ε i),
      ∃ q : ∀ i _j, Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹) → A (ψ i),
      (∀ i j, LipschitzWith 1 (q i j)) ∧
      (∀ i j, q i j ⟨0, ⟨by linarith [inv_pos.mpr (hσpos (ψ i))], (inv_pos.mpr (hσpos (ψ i))).le⟩⟩ = o (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((σ (ψ i))⁻¹),
        t.val - σ (ψ i) ≤ (σ (ψ i))⁻¹ - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist (q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ≤ t.val ∧
        -t.val ≤ (σ (ψ i))⁻¹ - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist (q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ≤
          -t.val + (2 * (σ (ψ i))⁻¹ - dist (aPlus (ψ i) j) (aMinus (ψ i) j)) + σ (ψ i)) ∧
      ∃ γ : ι → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (σ (ψ i))⁻¹ ∧
          ∀ t : Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (q i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨q i j t, ht⟩) (γ j t.val) < ζ) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (o (ψ i)) (R i), dist x.val (o (ψ i)) ≤ S →
            |dist (o (ψ i)) (aPlus (ψ i) j) - dist x.val (aPlus (ψ i) j) -
              lineCoordinate (γ j) ((f i).toFun x)| < ζ) ∧
        ∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-lineCoordinate (γ j) x)) := by
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun i => (σ i)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hwithin
  apply h.exists_line_coordinates_of_long_opposite_angles
    (h.fourPointComparison_zero_of_eventual_comparison (fun i => (hσpos i).le) hσ
      (fun R hR => eventual_fourPointComparison_of_growing_local_geometry o hcurves
        (fun i => (hσpos i).le) hL hdim hlocal hR))
    (h.exists_metric_segment_of_source_curves hcurves) hcurves aPlus aMinus hσpos hσ hp hm hangle

end GC.MetricGeometry
