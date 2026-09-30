import DifferentialGeometry.Geometry.Metric.TangentCone

set_option autoImplicit false

open Set Metric Filter Topology
open scoped NNReal

namespace Metric

variable {X ι : Type*} [MetricSpace X] [Finite ι] {q : X} [HasAnglesAt q]

theorem exists_common_shortening_of_separated_directions
    {δ S : ℝ} (hδ : 0 < δ) (hS : 0 < S) (ξ : ι → SpaceOfDirections q)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (ξ i) (ξ j)) :
    ∃ (σ : ι → GeodesicRepresentative q) (s : ℝ), 0 < s ∧ s < S ∧
      (∀ i, dist (ξ i) (σ i).direction < δ / 8) ∧
      (∀ i, s ≤ (σ i).length) ∧ (∀ i, dist q ((σ i).path s) = s) ∧
      ∀ i j, i ≠ j → δ / Real.pi * s < dist ((σ i).path s) ((σ j).path s) := by
  choose σ hσ using fun i => (ξ i).exists_representative_dist_lt (by positivity : 0 < δ / 8)
  have hdir (i j : ι) (hij : i ≠ j) :
      3 * δ / 4 < dist (σ i).direction (σ j).direction := by
    have h₁ := dist_triangle (ξ i) (σ i).direction (ξ j)
    have h₂ := dist_triangle (σ i).direction (σ j).direction (ξ j)
    rw [dist_comm (σ j).direction (ξ j)] at h₂
    linarith [hσ i, hσ j, hsep i j hij]
  have hcone (i j : ι) (hij : i ≠ j) :
      δ / Real.pi < dist ((σ i).tangentVector 1) ((σ j).tangentVector 1) := by
    have hc := two_mul_radius_mul_min_dist_le_pi_mul_coneDistance
      (x := ((1 : ℝ), (σ i).direction)) (y := ((1 : ℝ), (σ j).direction))
      (ρ := 1) (by norm_num) le_rfl le_rfl
    rw [min_eq_right (SpaceOfDirections.dist_le_pi _ _)] at hc
    have heq : coneDistance ((1 : ℝ), (σ i).direction) ((1 : ℝ), (σ j).direction) =
        dist ((σ i).tangentVector 1) ((σ j).tangentVector 1) := by
      exact (EuclideanCone.dist_mk 1 1 (σ i).direction (σ j).direction).symm
    rw [heq] at hc
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith [hdir i j hij]
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i : ι, s ≤ (σ i).length := by
    apply eventually_all.mpr
    intro i
    filter_upwards [Ioc_mem_nhdsGT (σ i).length_pos] with s hs using hs.2
  have hdist : ∀ᶠ s in 𝓝[>] (0 : ℝ), ∀ i j : ι, i ≠ j →
      δ / Real.pi < dist ((σ i).path s) ((σ j).path s) / s := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun _ h => (h hij).elim)
    have hlim : Tendsto (fun s : ℝ => dist ((σ i).path s) ((σ j).path s) / s)
        (𝓝[>] (0 : ℝ))
        (𝓝 (dist ((σ i).tangentVector 1) ((σ j).tangentVector 1))) := by
      simpa only [NNReal.coe_one, one_mul] using (σ i).dist_div_tendsto_tangentVector (σ j) 1 1
    filter_upwards [hlim.eventually (eventually_gt_nhds (hcone i j hij))] with s hs _ using hs
  have hSev : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 S := Ioo_mem_nhdsGT hS
  obtain ⟨s, hs, hsr, hd⟩ := (hSev.and (hsmall.and hdist)).exists
  exact ⟨σ, s, hs.1, hs.2, hσ, hsr,
    (fun i => (σ i).dist_base_path ⟨hs.1.le, hsr i⟩),
    fun i j hij => (lt_div_iff₀ hs.1).mp (hd i j hij)⟩

end Metric
