import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction
import DifferentialGeometry.Geometry.Metric.Approximation.OriginalOrientedProduct
import DifferentialGeometry.Geometry.Metric.Approximation.ScalarPrescribedCoordinates

open Set Filter Metric
open scoped Topology


open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe v
variable {A : ℕ → Type v} [∀ i, MetricSpace (A i)] [∀ i, CompleteSpace (A i)]

theorem exists_subsequence_prescribed_kleinerLott_approximations_of_reciprocal_local_geometry
    (o : ∀ i, A i) {σ : ℕ → ℝ} {n k : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : A i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → A i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (ball (o i) ((σ i)⁻¹)) ≤ n)
    (hlocal : ∀ i, ∀ z ∈ ball (o i) ((σ i)⁻¹),
      ∃ Ω : Set (A i), IsOpen Ω ∧ fourPointComparison (σ i) Ω ∧ z ∈ Ω)
    (aPlus aMinus : ∀ i, Fin k → A i)
    (hσpos : ∀ i, 0 < σ i) (hσ : Tendsto σ atTop (𝓝 0))
    (hp : ∀ i j, dist (o i) (aPlus i j) = (σ i)⁻¹)
    (hm : ∀ i j, dist (o i) (aMinus i j) = (σ i)⁻¹)
    (hopposite : ∀ j, ∀ᶠ i in atTop, Real.pi - σ i ≤ comparisonAngleNegCurvature (σ i)
      (dist (o i) (aPlus i j)) (dist (o i) (aMinus i j)) (dist (aPlus i j) (aMinus i j)))
    (hcrossPlus : ∀ j l, j ≠ l → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aPlus i l)))
    (hcrossMinus : ∀ j l, j ≠ l → ∀ᶠ i in atTop,
      Real.pi / 2 - σ i ≤ comparisonAngleNegCurvature (σ i) ((σ i)⁻¹) ((σ i)⁻¹)
        (dist (aPlus i j) (aMinus i l))) :
    ∃ χ : ℕ → ℕ, StrictMono χ ∧
      ∃ (Z : Type) (m : MetricSpace Z), letI := m
        ∃ z : Z, ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
          (∀ a b : Z, ∃ c : Icc (0 : ℝ) 1 → Z,
            Continuous c ∧ c ⟨0, by norm_num⟩ = a ∧ c ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (c s) (c t) = dist a b * dist s t) ∧
          ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ᶠ i in atTop,
            ∃ F : KleinerLottApprox (o (χ i))
              (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), z)) δ,
              ∀ x : A (χ i), (F.toFun x).fst =
                WithLp.toLp 2 (fun j => dist (o (χ i)) (aPlus (χ i) j) - dist x (aPlus (χ i) j)) := by
  have hwithin : Tendsto σ atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hσ, Eventually.of_forall hσpos⟩
  have hL : Tendsto (fun i => (σ i)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp hwithin
  obtain ⟨Y, mY, p, φ, hφ, hYcomplete, hYproper, hpointed, _⟩ :=
    exists_pointed_limit_of_growing_local_geometry o hn hcurves
      (fun i => (hσpos i).le) hσ hL hdim hlocal
  let := mY
  let := hYcomplete
  let := hYproper
  obtain ⟨_, _, _, _qPlus, _qMinus, _hqPlus, _hqMinus, _hqPlus0, _hqMinus0,
      _hqPlusEnd, _hqMinusEnd, ψ, R, ε, hψ, _hsub, hR, hε, f, _Q, _hLip, _hbase,
      _halign, _hcal, _γ, _hγ, _hγ0, _hconv, _hangle,
      Z, mZ, z, e, he0, _haxes, _hcoord, _hbus, hclose, hZproper, hZcomplete, hZcomp, hZsegments⟩ :=
    hpointed.exists_oriented_product_of_reciprocal_local_geometry
      (fun i => hcurves (φ i)) (fun i => hdim (φ i)) (fun i => hlocal (φ i))
      (fun i => aPlus (φ i)) (fun i => aMinus (φ i))
      (fun i => hσpos (φ i)) (hσ.comp hφ.tendsto_atTop)
      (fun i => hp (φ i)) (fun i => hm (φ i))
      (fun j => hφ.tendsto_atTop.eventually (hopposite j))
      (fun j l hjl => hφ.tendsto_atTop.eventually (hcrossPlus j l hjl))
      (fun j l hjl => hφ.tendsto_atTop.eventually (hcrossMinus j l hjl))
  let := mZ
  refine ⟨φ ∘ ψ, hφ.comp hψ, Z, mZ, z, hZproper, hZcomplete, hZcomp, hZsegments, ?_⟩
  intro δ hδ hδone
  exact eventually_distance_coordinates_kleinerLott_approximation e z he0 f hR hε
    (fun i => aPlus (φ (ψ i)))
    (fun S hS η hη => (hclose S hS η hη).mono fun _ hi => hi.2) hδ hδone

end GC.MetricGeometry
