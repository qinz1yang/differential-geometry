/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HeightFiber

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem IsHPolytope.eventually_mem_iff_sub_smul_of_openSimplex
    {P : Set E} (hP : IsHPolytope P) {s : Finset E} {x : E} (hx : x ∈ openSimplex s)
    (hsP : convexHull ℝ (s : Set E) ⊆ P) {u v : E} (hu : u ∈ s) (hv : v ∈ s)
    {f : E → ℝ} (hf : ContinuousAt f x) (hfx : f x = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ P ↔ y - f y • (v - u) ∈ P := by
  obtain ⟨_, ι, hι, l, c, hP_eq⟩ := hP
  let _ : Finite ι := hι
  have hxP : ∀ i, l i x ≤ c i := by
    have h := hsP (openSimplex_subset_convexHull s hx)
    rwa [hP_eq] at h
  have hsbound (i : ι) (w : E) (hw : w ∈ s) : l i w ≤ c i :=
    (hP_eq ▸ hsP (subset_convexHull ℝ _ hw)) i
  have hproj : ContinuousAt (fun y => y - f y • (v - u)) x := continuousAt_id.sub (hf.smul
      continuousAt_const)
  have hprojx : x - f x • (v - u) = x := by rw [hfx, zero_smul, sub_zero]
  have hineq : ∀ i : ι, ∀ᶠ y in 𝓝 x, l i y ≤ c i ↔ l i (y - f y • (v - u)) ≤ c i := by
    intro i
    by_cases hactive : l i x = c i
    · have hvertices := (affineMap_eq_iff_of_mem_openSimplex_of_le (l i).toAffineMap hx (hsbound
        i)).mp hactive
      change ∀ w ∈ s, l i w = c i at hvertices
      have hdir : l i (v - u) = 0 := by rw [map_sub, hvertices v hv, hvertices u hu, sub_self]
      exact Filter.Eventually.of_forall fun y => by rw [map_sub, map_smul, hdir, smul_zero,
          sub_zero]
    · have hstrict : l i x < c i := lt_of_le_of_ne (hxP i) hactive
      have hnear : ∀ᶠ y in 𝓝 x, l i y < c i :=
        (isOpen_lt (l i).continuous_of_finiteDimensional continuous_const).mem_nhds hstrict
      have hnear' : ∀ᶠ y in 𝓝 x, l i (y - f y • (v - u)) < c i :=
        (by simpa only [ContinuousAt, hprojx] using hproj : Filter.Tendsto (fun y => y - f y • (v -
            u)) (𝓝 x) (𝓝 x)).eventually hnear
      filter_upwards [hnear, hnear'] with y hy hy'
      exact iff_of_true hy.le hy'.le
  filter_upwards [Filter.eventually_all.mpr hineq] with y hy
  rw [hP_eq]
  exact forall_congr' hy

theorem eventually_mem_space_iff_sub_smul_of_mem_openSimplex
    (K L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s)
    {u v : E} (hu : u ∈ s) (hv : v ∈ s)
    {f : E → ℝ} (hf : ContinuousAt f x) (hfx : f x = 0) :
    ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ y - f y • (v - u) ∈ L.space := by
  have hproj : ContinuousAt (fun y => y - f y • (v - u)) x := continuousAt_id.sub (hf.smul
      continuousAt_const)
  have hprojx : x - f x • (v - u) = x := by rw [hfx, zero_smul, sub_zero]
  have hface : ∀ t : L.faces, ∀ᶠ y in 𝓝 x,
      y ∈ convexHull ℝ (t.val : Set E) ↔ y - f y • (v - u) ∈ convexHull ℝ (t.val : Set E) := by
    intro t
    have hT := isHPolytope_convexHull_of_affineIndependent t.val (L.indep t.property)
    by_cases hxt : x ∈ convexHull ℝ (t.val : Set E)
    · have hst := face_subset_of_mem_openSimplex_of_mem_convexHull K hs (hLK t.property) hx hxt
      exact hT.eventually_mem_iff_sub_smul_of_openSimplex hx (convexHull_mono (Finset.coe_subset.mpr
          hst)) hu hv hf hfx
    · have hnear : ∀ᶠ y in 𝓝 x, y ∉ convexHull ℝ (t.val : Set E) :=
        hT.isClosed.isOpen_compl.mem_nhds hxt
      have hnear' : ∀ᶠ y in 𝓝 x, y - f y • (v - u) ∉ convexHull ℝ (t.val : Set E) :=
        (by simpa only [ContinuousAt, hprojx] using hproj : Filter.Tendsto (fun y => y - f y • (v -
            u)) (𝓝 x) (𝓝 x)).eventually hnear
      filter_upwards [hnear, hnear'] with y hy hy'
      exact iff_of_false hy hy'
  filter_upwards [Filter.eventually_all.mpr hface] with y hy
  constructor
  · intro hyL
    obtain ⟨t, ht, hyt⟩ := L.mem_space_iff.mp hyL
    exact L.convexHull_subset_space ht ((hy ⟨t, ht⟩).mp hyt)
  · intro hyL
    obtain ⟨t, ht, hyt⟩ := L.mem_space_iff.mp hyL
    exact L.convexHull_subset_space ht ((hy ⟨t, ht⟩).mpr hyt)

theorem mem_interior_space_iff_mem_nhdsWithin_fiber
    (K L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hLK : L.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s)
    {u v : E} (hu : u ∈ s) (hv : v ∈ s) (ℓ : E →ₗ[ℝ] ℝ) (hℓuv : ℓ v ≠ ℓ u) :
    x ∈ interior L.space ↔ (L.space ∩ {y | ℓ y = ℓ x}) ∈ 𝓝[{y | ℓ y = ℓ x}] x := by
  let f : E → ℝ := fun y => (ℓ y - ℓ x) / (ℓ v - ℓ u)
  have hf : ContinuousAt f x := (ℓ.continuous_of_finiteDimensional.continuousAt.sub
      continuousAt_const).div_const _
  have hfx : f x = 0 := by simp only [f, sub_self, zero_div]
  have hprojection := eventually_mem_space_iff_sub_smul_of_mem_openSimplex K L hLK hs hx hu hv hf
      hfx
  have hheight (y : E) : ℓ (y - f y • (v - u)) = ℓ x := by
    rw [map_sub, map_smul, map_sub, smul_eq_mul]
    change ℓ y - ((ℓ y - ℓ x) / (ℓ v - ℓ u)) * (ℓ v - ℓ u) = ℓ x
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hℓuv), sub_sub_cancel]
  have hprojx : x - f x • (v - u) = x := by rw [hfx, zero_smul, sub_zero]
  have hprojcont : ContinuousAt (fun y => y - f y • (v - u)) x :=
    continuousAt_id.sub (hf.smul continuousAt_const)
  have hcont : Filter.Tendsto (fun y => y - f y • (v - u)) (𝓝 x) (𝓝 x) := by
    simpa only [ContinuousAt, hprojx] using hprojcont
  have hwithin : Filter.Tendsto (fun y => y - f y • (v - u)) (𝓝 x) (𝓝[{y | ℓ y = ℓ x}] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨hcont, Filter.Eventually.of_forall hheight⟩
  constructor
  · intro hint
    exact Filter.inter_mem (nhdsWithin_le_nhds (mem_interior_iff_mem_nhds.mp hint))
        self_mem_nhdsWithin
  · intro hsection
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [hprojection, hwithin hsection] with y hy hy'
    exact hy.mpr hy'.1

end DifferentialGeometry.Topology.PiecewiseLinear
