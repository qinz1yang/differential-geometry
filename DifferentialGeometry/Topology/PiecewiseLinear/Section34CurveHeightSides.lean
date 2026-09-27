import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurveHeightLevels

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem mem_closure_height_sides_of_notMem_vertex_image
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hcard : ∀ s ∈ K.faces, s.card ≤ 2) (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ}
    (hr : r ∉ ℓ '' K.vertices) {x : E} (hx : x ∈ K.space ∩ {y | ℓ y = r}) :
    x ∈ closure (K.space ∩ {y | ℓ y < r}) ∧
      x ∈ closure (K.space ∩ {y | r < ℓ y}) := by
  obtain ⟨a, b, -, -, hab, -, hgerm⟩ :=
    exists_edge_of_mem_fiber_of_notMem_vertex_image K hcard ℓ hr hx
  let v : E := (ℓ b - ℓ a)⁻¹ • (b - a)
  have hv : ℓ v = 1 := by
    simp only [v, map_smul, map_sub, smul_eq_mul]
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm)
  let γ : ℝ → E := fun t => x + t • v
  have hγ : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  have hγ0 : γ 0 = x := by simp [γ]
  have ht : Filter.Tendsto γ (𝓝 0) (𝓝 x) := by
    have ht0 : Filter.Tendsto γ (𝓝 0) (𝓝 (γ 0)) := hγ.continuousAt
    rwa [hγ0] at ht0
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ K.space := by
    filter_upwards [ht.eventually hgerm] with t htg
    apply htg.mpr
    exact ⟨t * (ℓ b - ℓ a)⁻¹, by simp only [γ, v, mul_smul]⟩
  have hxr : ℓ x = r := hx.2
  have hheight (t : ℝ) : ℓ (γ t) = r + t := by
    simp only [γ, map_add, map_smul, hv, smul_eq_mul, mul_one, hxr]
  constructor
  · have : (𝓝[Iio (0 : ℝ)] 0).NeBot := nhdsWithin_Iio_neBot le_rfl
    apply mem_closure_of_tendsto (b := 𝓝[Iio (0 : ℝ)] 0)
      (ht.mono_left nhdsWithin_le_nhds)
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htm ht0
    exact ⟨htm, by change ℓ (γ t) < r; rw [hheight]; simpa using ht0⟩
  · have : (𝓝[Ioi (0 : ℝ)] 0).NeBot := nhdsWithin_Ioi_neBot le_rfl
    apply mem_closure_of_tendsto (b := 𝓝[Ioi (0 : ℝ)] 0)
      (ht.mono_left nhdsWithin_le_nhds)
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t htm ht0
    exact ⟨htm, by change r < ℓ (γ t); rw [hheight]; simpa using ht0⟩

end DifferentialGeometry.Topology.PiecewiseLinear
