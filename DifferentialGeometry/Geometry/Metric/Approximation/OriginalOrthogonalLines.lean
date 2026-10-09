import DifferentialGeometry.Geometry.Metric.Approximation.RadialPrefixOrthogonality
import DifferentialGeometry.Geometry.Metric.Approximation.PointedRadialEndpointLines
import DifferentialGeometry.Topology.MetricSpace.BoundaryRadialSegment
import DifferentialGeometry.Geometry.Comparison.OppositeAngleExcess
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionGeometry
import DifferentialGeometry.Geometry.Metric.Approximation.ComparisonLimit
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer

open Set Filter Metric
open scoped Topology

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

variable {A : ℕ → Type*} [∀ i, MetricSpace (A i)] [∀ i, CompleteSpace (A i)]
variable {Y ι : Type*} [MetricSpace Y] [ProperSpace Y] [Finite ι]
variable {o : ∀ i, A i} {p : Y} {σ : ℕ → ℝ}

theorem PointedGHConverges.exists_orthogonal_calibrated_lines_of_reciprocal_local_geometry
    (h : PointedGHConverges o p) {n : ℕ}
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
    (hopposite : ∀ j, ∀ᶠ i in atTop, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (o i) (aPlus i j)) (dist (o i) (aMinus i j)) (dist (aPlus i j) (aMinus i j)))
    (hcrossPlus : ∀ j k, j ≠ k → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aPlus i k)))
    (hcrossMinus : ∀ j k, j ≠ k → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aMinus i k))) :
    fourPointComparison 0 (univ : Set Y) ∧
    (∀ a b : Y, ∃ c : Icc (0 : ℝ) 1 → Y,
      Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
        ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
    (∀ j, Tendsto (fun i => 2 * (σ i)⁻¹ - dist (aPlus i j) (aMinus i j)) atTop (𝓝 0)) ∧
    ∃ qPlus qMinus : ∀ i, ι → Icc (0 : ℝ) ((σ i)⁻¹) → A i,
      (∀ i j, Isometry (qPlus i j)) ∧ (∀ i j, Isometry (qMinus i j)) ∧
      (∀ i j, qPlus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i) ∧
      (∀ i j, qMinus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i) ∧
      (∀ i j, qPlus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aPlus i j) ∧
      (∀ i j, qMinus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aMinus i j) ∧
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => o (ψ i)) p ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (o (ψ i)) p (R i) (ε i),
      ∃ Q : ∀ i, ι → Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹) → A (ψ i),
      (∀ i j, LipschitzWith 1 (Q i j)) ∧
      (∀ i j, Q i j ⟨0, ⟨by linarith [inv_pos.mpr (hσpos (ψ i))],
        (inv_pos.mpr (hσpos (ψ i))).le⟩⟩ = o (ψ i)) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((σ (ψ i))⁻¹),
        Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩ = qPlus (ψ i) j t ∧
        Q i j ⟨-t.val, ⟨by linarith [t.property.2],
          by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩ = qMinus (ψ i) j t) ∧
      (∀ i j, ∀ t : Icc (0 : ℝ) ((σ (ψ i))⁻¹),
        t.val ≤ (σ (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist
          (Q i j ⟨t.val, ⟨by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))], t.property.2⟩⟩) (aPlus (ψ i) j) ≤ t.val ∧
        -t.val ≤ (σ (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ∧
        (σ (ψ i))⁻¹ - dist
          (Q i j ⟨-t.val, ⟨by linarith [t.property.2],
            by linarith [t.property.1, inv_pos.mpr (hσpos (ψ i))]⟩⟩) (aPlus (ψ i) j) ≤
          -t.val + (2 * (σ (ψ i))⁻¹ - dist (aPlus (ψ i) j) (aMinus (ψ i) j))) ∧
      ∃ γ : ι → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (σ (ψ i))⁻¹ ∧
          ∀ t : Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (Q i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) ∧
        ∀ j k, j ≠ k → germComparisonAngle 0 (γ j) (γ k) = Real.pi / 2 := by
  classical
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun i => (σ i)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hwithin
  have hs : fourPointComparison 0 (univ : Set Y) :=
    h.fourPointComparison_zero_of_eventual_comparison (fun i => (hσpos i).le) hσ
      (fun S hS => eventual_fourPointComparison_of_growing_local_geometry o hcurves
        (fun i => (hσpos i).le) hL hdim hlocal hS)
  have hE (j : ι) : Tendsto
      (fun i => 2 * (σ i)⁻¹ - dist (aPlus i j) (aMinus i j)) atTop (𝓝 0) :=
    tendsto_opposite_endpoint_excess_zero hσpos hσ (fun i => inv_pos.mpr (hσpos i))
      (fun i => hp i j) (fun i => hm i j) (hopposite j)
  have hsegment (i : ℕ) (a : A i) (ha : dist (o i) a = (σ i)⁻¹) :
      ∃ q : Icc (0 : ℝ) ((σ i)⁻¹) → A i, Isometry q ∧
        q ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i ∧
        q ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = a := by
    let : LocallyCompactSpace (ball (o i) ((σ i)⁻¹)) :=
      locallyCompactSpace_of_nonnegative_parameter_local_comparison_and_dimH
        (hcurves i) (hσpos i).le isOpen_ball (hdim i) (hlocal i)
    exact exists_isometric_segment_to_boundary_of_locallyCompact_ball
      (hcurves i) (o i) (inv_pos.mpr (hσpos i)) ha
  choose qPlus hqPlus hqPlus0 hqPlusEnd using fun i j => hsegment i (aPlus i j) (hp i j)
  choose qMinus hqMinus hqMinus0 hqMinusEnd using fun i j => hsegment i (aMinus i j) (hm i j)
  obtain ⟨ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase, halign, hcal, γ, hγ, hγ0, hconv⟩ :=
    h.exists_calibrated_lines_of_opposite_radial_isometries aPlus aMinus
      (L := fun i (_ : ι) => (σ i)⁻¹) (fun i _ => inv_pos.mpr (hσpos i)) (fun _ => hL)
      qPlus qMinus hqPlus hqMinus hqPlus0 hqMinus0 hqPlusEnd hqMinusEnd hE
  refine ⟨hs, h.exists_metric_segment_of_source_curves hcurves, hE,
    qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0, hqPlusEnd, hqMinusEnd,
    ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase, halign, hcal,
    γ, hγ, hγ0, hconv, ?_⟩
  exact germComparisonAngle_eq_pi_div_two_of_converging_radial_prefixes hs
    (fun i => hcurves (ψ i)) (fun i => hdim (ψ i)) (fun i => hlocal (ψ i))
    (fun i => hσpos (ψ i)) (hσ.comp hψ.tendsto_atTop)
    (fun i => aPlus (ψ i)) (fun i => aMinus (ψ i))
    (fun i => qPlus (ψ i)) (fun i => qMinus (ψ i))
    (fun i => hqPlus (ψ i)) (fun i => hqMinus (ψ i))
    (fun i => hqPlus0 (ψ i)) (fun i => hqMinus0 (ψ i))
    (fun i => hqPlusEnd (ψ i)) (fun i => hqMinusEnd (ψ i))
    (fun j k hjk => hψ.tendsto_atTop.eventually (hcrossPlus j k hjk))
    (fun j k hjk => hψ.tendsto_atTop.eventually (hcrossMinus j k hjk))
    Q hLip hbase (fun i j t => (halign i j t).1) (fun i j t => (halign i j t).2)
    f hε γ hγ hγ0 hconv

end GC.MetricGeometry
