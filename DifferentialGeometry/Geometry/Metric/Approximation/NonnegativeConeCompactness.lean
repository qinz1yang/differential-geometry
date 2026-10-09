import DifferentialGeometry.Geometry.Metric.Approximation.RadialConeLimit
import DifferentialGeometry.Geometry.Metric.Approximation.GrowingRegionExtraction

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Metric Real Filter
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

universe u
variable {X : ℕ → Type u} [∀ i, MetricSpace (X i)] [∀ i, CompleteSpace (X i)]

theorem exists_pointed_cone_limit_of_nonnegative_geometry
    (p : ∀ i, X i) {n : ℕ} (hn : 1 ≤ n)
    (hcurves : ∀ i, ∀ a b : X i, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + η))
    (hdim : ∀ i, dimH (univ : Set (X i)) ≤ n)
    (hcomp : ∀ i, fourPointComparison 0 (univ : Set (X i)))
    (H : ∀ i, RadialConeData (p i)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧ Nonempty (RadialConeData q) ∧
        dimH (univ : Set Y) ≤ n ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) ∧
        ∀ R : ℝ, 0 < R → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
          (T.card : ℝ) ≤
            (2 + 16 * (pairedChartDistortion n) ^ 2 * sqrt n * sinh (2 * (R + 1))) ^ n *
              δ ^ (-(n : ℝ)) ∧
          (∀ y ∈ T, dist y q ≤ R) ∧
          ∀ y : Y, dist y q ≤ R → ∃ z ∈ T, dist y z < δ := by
  have hR : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
  obtain ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv, hdimY, hcompY,
      hsegments, hside, hnets⟩ := exists_pointed_limit_of_growing_local_geometry p hn hcurves
    (κ := fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds hR
    (fun i => (dimH_mono (subset_univ _)).trans (hdim i))
    (fun i z _ => ⟨univ, isOpen_univ, hcomp i, mem_univ z⟩)
  let := m
  let := hproper
  exact ⟨Y, m, q, φ, hφ, hcomplete, hproper, hconv,
    hconv.nonempty_radialConeData (fun i => H (φ i)),
    hdimY, hcompY, hsegments, hside, hnets⟩

end GC.MetricGeometry
