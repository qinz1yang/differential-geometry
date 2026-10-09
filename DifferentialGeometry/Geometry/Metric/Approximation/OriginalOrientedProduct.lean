import DifferentialGeometry.Geometry.Metric.Approximation.OriginalOrthogonalLines
import DifferentialGeometry.Geometry.Metric.Approximation.CalibratedOrthogonalCoordinates

open Set Filter Metric
open scoped Topology

open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

variable {A : ℕ → Type v} [∀ i, MetricSpace (A i)] [∀ i, CompleteSpace (A i)]
variable {Y : Type u} [MetricSpace Y] [ProperSpace Y] {k : ℕ}
variable {o : ∀ i, A i} {p : Y} {σ : ℕ → ℝ}

theorem PointedGHConverges.exists_oriented_product_of_reciprocal_local_geometry
    (h : PointedGHConverges o p) {n : ℕ}
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
    ∃ qPlus qMinus : ∀ i, Fin k → Icc (0 : ℝ) ((σ i)⁻¹) → A i,
      (∀ i j, Isometry (qPlus i j)) ∧ (∀ i j, Isometry (qMinus i j)) ∧
      (∀ i j, qPlus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i) ∧
      (∀ i j, qMinus i j ⟨0, ⟨le_rfl, (inv_pos.mpr (hσpos i)).le⟩⟩ = o i) ∧
      (∀ i j, qPlus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aPlus i j) ∧
      (∀ i j, qMinus i j ⟨(σ i)⁻¹, ⟨(inv_pos.mpr (hσpos i)).le, le_rfl⟩⟩ = aMinus i j) ∧
    ∃ (ψ : ℕ → ℕ) (R ε : ℕ → ℝ), StrictMono ψ ∧
      PointedGHConverges (fun i => o (ψ i)) p ∧ Tendsto R atTop atTop ∧ Tendsto ε atTop (𝓝 0) ∧
      ∃ f : ∀ i, PointedBallApprox (o (ψ i)) p (R i) (ε i),
      ∃ Q : ∀ i, Fin k → Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹) → A (ψ i),
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
      ∃ γ : Fin k → ℝ → Y,
        (∀ j, Isometry (γ j)) ∧ (∀ j, γ j 0 = p) ∧
        (∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, S ≤ (σ (ψ i))⁻¹ ∧
          ∀ t : Icc (-((σ (ψ i))⁻¹)) ((σ (ψ i))⁻¹), |t.val| ≤ S →
            ∀ ht : dist (Q i j t) (o (ψ i)) ≤ R i,
              dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) ∧
        (∀ j l, j ≠ l → germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2) ∧
        ∃ (Z : Type u) (m : MetricSpace Z), letI := m
          ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)),
            e p = WithLp.toLp 2 (0, z) ∧
            (∀ j t, e (γ j t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) ∧
            (∀ j x, lineCoordinate (γ j) x = (e x).fst j) ∧
            (∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-(e x).fst j))) ∧
            (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
              S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (o (ψ i)) (R i), dist x.val (o (ψ i)) ≤ S →
                |dist (o (ψ i)) (aPlus (ψ i) j) - dist x.val (aPlus (ψ i) j) -
                  (e ((f i).toFun x)).fst j| < ζ) ∧
            ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
            (∀ a b : Z, ∃ g : Icc (0 : ℝ) 1 → Z,
              Continuous g ∧ g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
              ∀ s t, dist (g s) (g t) = dist a b * dist s t) := by
  obtain ⟨hs, hsegments, hE, qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0,
    hqPlusEnd, hqMinusEnd, ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase,
    halign, hcal, γ, hγ, hγ0, hconv, hangle⟩ :=
    h.exists_orthogonal_calibrated_lines_of_reciprocal_local_geometry
      hcurves hdim hlocal aPlus aMinus hσpos hσ hp hm hopposite hcrossPlus hcrossMinus
  have hEnonneg (i : ℕ) (j : Fin k) :
      0 ≤ 2 * (σ (ψ i))⁻¹ - dist (aPlus (ψ i) j) (aMinus (ψ i) j) := by
    have hh := dist_triangle (aPlus (ψ i) j) (o (ψ i)) (aMinus (ψ i) j)
    rw [dist_comm (aPlus (ψ i) j) (o (ψ i)), hp, hm] at hh
    linarith
  refine ⟨hs, hsegments, hE, qPlus, qMinus, hqPlus, hqMinus, hqPlus0, hqMinus0,
    hqPlusEnd, hqMinusEnd, ψ, R, ε, hψ, hsub, hR, hε, f, Q, hLip, hbase,
    halign, hcal, γ, hγ, hγ0, hconv, hangle, ?_⟩
  exact exists_oriented_product_with_converging_distance_coordinates
    (L := fun i (_ : Fin k) => (σ (ψ i))⁻¹)
    (E := fun i j => 2 * (σ (ψ i))⁻¹ - dist (aPlus (ψ i) j) (aMinus (ψ i) j))
    (η := fun _ => 0) hs hsegments γ hγ hγ0 hangle f hR hε
    (fun i => aPlus (ψ i)) (fun i => hp (ψ i))
    (fun i _ => (inv_pos.mpr (hσpos (ψ i))).le) hEnonneg
    (fun j => (hE j).comp hψ.tendsto_atTop) tendsto_const_nhds
    Q hLip hbase
    (fun i j t => by
      simpa only [sub_zero, add_zero] using And.intro (hcal i j t).1 (hcal i j t).2.2.2)
    hconv

end GC.MetricGeometry
