import Mathlib.Analysis.Convex.Deriv

open Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem tendsto_deriv_of_concaveOn
    {ι : Type*} {L : Filter ι} {D : Set ℝ} {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hx : x ∈ interior D)
    (hconcave : ∀ᶠ i in L, ConcaveOn ℝ D (F i))
    (hF : ∀ᶠ i in L, DifferentiableAt ℝ (F i) x)
    (hlim : ∀ y ∈ D, Tendsto (fun i => F i y) L (𝓝 (f y)))
    (hf : DifferentiableAt ℝ f x) :
    Tendsto (fun i => deriv (F i) x) L (𝓝 (deriv f x)) := by
  have hxD : x ∈ D := interior_subset hx
  have hD : D ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hx
  have hslope (a b : ℝ) (ha : a ∈ D) (hb : b ∈ D) :
      Tendsto (fun i => slope (F i) a b) L (𝓝 (slope f a b)) := by
    simp only [slope_def_field]
    exact ((hlim b hb).sub (hlim a ha)).div_const (b - a)
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    have hright : ∀ᶠ y in 𝓝[>] x, a < slope f x y :=
      (hf.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)).eventually
        (Ioi_mem_nhds ha)
    have hDright : ∀ᶠ y in 𝓝[>] x, y ∈ D := nhdsWithin_le_nhds hD
    obtain ⟨y, hy, hyD, hxy⟩ :=
      (hright.and (hDright.and self_mem_nhdsWithin)).exists
    have hybound : ∀ᶠ i in L, a < slope (F i) x y :=
      (hslope x y hxD hyD).eventually (Ioi_mem_nhds hy)
    filter_upwards [hconcave, hF, hybound] with i hi hFi hibound
    exact hibound.trans_le (hi.slope_le_deriv hxD hyD hxy hFi)
  · intro b hb
    have hleft : ∀ᶠ y in 𝓝[<] x, slope f x y < b :=
      (hf.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)).eventually
        (Iio_mem_nhds hb)
    have hDleft : ∀ᶠ y in 𝓝[<] x, y ∈ D := nhdsWithin_le_nhds hD
    obtain ⟨y, hy, hyD, hyx⟩ :=
      (hleft.and (hDleft.and self_mem_nhdsWithin)).exists
    have hybound : ∀ᶠ i in L, slope (F i) y x < b := by
      have h := (hslope x y hxD hyD).eventually (Iio_mem_nhds hy)
      filter_upwards [h] with i hi
      rwa [slope_comm] at hi
    filter_upwards [hconcave, hF, hybound] with i hi hFi hibound
    exact (hi.deriv_le_slope hyD hxD hyx hFi).trans_lt hibound

end DifferentialGeometry.Analysis
