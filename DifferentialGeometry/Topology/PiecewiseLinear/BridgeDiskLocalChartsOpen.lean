/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLHomeomorphOn.exists_open_restriction_of_finite_germs
    {ι : Type*} [Finite ι] {P : Set E} {Q : Set F} {f : E → F} {x : E} {y : F}
    (hf : IsPLHomeomorphOn f P Q) (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (hP : P ∈ 𝓝 x) (hxy : f x = y) {S A : ι → Set E} {T B : ι → Set F}
    (hSP : ∀ i, S i ⊆ P) (hmap : ∀ i, f '' S i = T i)
    (hsource : ∀ i, ∀ᶠ z in 𝓝 x, z ∈ S i ↔ z ∈ A i)
    (htarget : ∀ i, ∀ᶠ z in 𝓝 y, z ∈ T i ↔ z ∈ B i) :
    ∃ (U : Set E) (V : Set F), IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ y ∈ V ∧
      U ⊆ P ∧ V ⊆ Q ∧ IsPLHomeomorphOn f U V ∧
      ∀ i, f '' (U ∩ A i) = V ∩ B i := by
  have hcont : ContinuousAt f x := hf.isPiecewiseAffineOn.continuousOn.continuousAt hP
  have hlocal : ∀ i, ∀ᶠ z in 𝓝 x, z ∈ A i ↔ f z ∈ B i := by
    intro i
    have htarget' : ∀ᶠ z in 𝓝 x, f z ∈ T i ↔ f z ∈ B i :=
      hcont.eventually (hxy.symm ▸ htarget i)
    filter_upwards [hP, hsource i, htarget'] with z hzP hzS hzT
    have hmem : z ∈ S i ↔ f z ∈ T i := by
      constructor
      · intro hz
        exact (hmap i).subset ⟨z, hz, rfl⟩
      · intro hz
        obtain ⟨w, hw, heq⟩ := (hmap i).symm.subset hz
        exact hf.bijOn.injOn (hSP i hw) hzP heq ▸ hw
    exact hzS.symm.trans (hmem.trans hzT)
  have hall : ∀ᶠ z in 𝓝 x, ∀ i, z ∈ A i ↔ f z ∈ B i := Filter.eventually_all.mpr hlocal
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (Filter.inter_mem hP hall)
  have hUP : U ⊆ P := hUsub.trans inter_subset_left
  have hV : IsOpen (f '' U) := invariance_of_domain_isOpen_image_of_finrank_eq hdim hU
    (hf.isPiecewiseAffineOn.continuousOn.mono hUP) (hf.bijOn.injOn.mono hUP)
  refine ⟨U, f '' U, hU, hV, hxU, ⟨x, hxU, hxy⟩, hUP,
    (image_mono hUP).trans hf.image_eq.subset, hf.restrict_isOpen hU hUP hV, ?_⟩
  intro i
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w, hw.1, rfl⟩, ((hUsub hw.1).2 i).mp hw.2⟩
  · rintro ⟨⟨w, hw, rfl⟩, hz⟩
    exact ⟨w, ⟨hw, ((hUsub hw).2 i).mpr hz⟩, rfl⟩

end DifferentialGeometry.Topology.PiecewiseLinear
