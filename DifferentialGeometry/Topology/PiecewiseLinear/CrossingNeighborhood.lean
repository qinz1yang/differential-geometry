/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphTopology
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubspace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem HasPLCrossingAt.of_openPartialHomeomorph
    {A B A' B' : Set E} {x : E} (e : OpenPartialHomeomorph E E)
    (he : IsPiecewiseAffineOn e e.source) (hx : x ∈ e.source)
    (hcross : HasPLCrossingAt A' B' (e x))
    (hA : ∀ᶠ z in 𝓝 x, z ∈ A ↔ e z ∈ A')
    (hB : ∀ᶠ z in 𝓝 x, z ∈ B ↔ e z ∈ B') : HasPLCrossingAt A B x := by
  have hback := hcross.image_openPartialHomeomorph e.symm he.symm (e.map_source hx)
  rw [e.left_inv hx] at hback
  apply hback.congr
  · filter_upwards [e.open_source.mem_nhds hx, hA] with z hz hza
    rw [e.symm.image_source_inter_eq']
    change (z ∈ e.source ∧ e z ∈ A') ↔ z ∈ A
    simpa only [hz, true_and] using hza.symm
  · filter_upwards [e.open_source.mem_nhds hx, hB] with z hz hzb
    rw [e.symm.image_source_inter_eq']
    change (z ∈ e.source ∧ e z ∈ B') ↔ z ∈ B
    simpa only [hz, true_and] using hzb.symm

theorem HasPLCrossingAt.of_isPLHomeomorphOn_mem_nhds
    {A B A' B' P Q : Set E} {x : E} {f : E → E} (hf : IsPLHomeomorphOn f P Q)
    (hx : P ∈ 𝓝 x) (hA : f '' (P ∩ A) = Q ∩ A') (hB : f '' (P ∩ B) = Q ∩ B')
    (hcross : HasPLCrossingAt A' B' (f x)) : HasPLCrossingAt A B x := by
  let e : OpenPartialHomeomorph E E :=
    { toFun := f
      invFun := Function.invFunOn f P
      source := interior P
      target := interior Q
      map_source' := fun z hz => hf.image_interior rfl ▸ mem_image_of_mem f hz
      map_target' := fun z hz => hf.symm.image_interior rfl ▸ mem_image_of_mem (Function.invFunOn f
          P) hz
      left_inv' := fun z hz => hf.bijOn.invOn_invFunOn.1 (interior_subset hz)
      right_inv' := fun z hz => hf.bijOn.invOn_invFunOn.2 (interior_subset hz)
      open_source := isOpen_interior
      open_target := isOpen_interior
      continuousOn_toFun := hf.isPiecewiseAffineOn.continuousOn.mono interior_subset
      continuousOn_invFun := hf.isPiecewiseAffineOn_invFunOn.continuousOn.mono interior_subset }
  have he : IsPiecewiseAffineOn e e.source := by
    change IsPiecewiseAffineOn f (interior P)
    simpa only [inter_eq_right.mpr interior_subset] using
      hf.isPiecewiseAffineOn.inter_of_isOpen (O := interior P) isOpen_interior
  have hmem {C D : Set E} (himage : f '' (P ∩ C) = Q ∩ D) {z : E} (hz : z ∈ P) :
      z ∈ C ↔ f z ∈ D := by
    constructor
    · intro hzc
      exact (himage.subset (mem_image_of_mem f ⟨hz, hzc⟩)).2
    · intro hzD
      obtain ⟨w, ⟨hwP, hwC⟩, hfw⟩ := himage.symm.subset ⟨hf.bijOn.mapsTo hz, hzD⟩
      exact hf.bijOn.injOn hwP hz hfw ▸ hwC
  refine HasPLCrossingAt.of_openPartialHomeomorph e he (mem_interior_iff_mem_nhds.mpr hx) hcross ?_
      ?_
  · filter_upwards [hx] with z hz
    exact hmem hA hz
  · filter_upwards [hx] with z hz
    exact hmem hB hz

omit [FiniteDimensional ℝ E] in
private theorem closedStar_subset_of_faces_subset {K M : Geometry.SimplicialComplex ℝ E}
    (hM : M.faces ⊆ K.faces) (p : E) : closedStar M p ⊆ closedStar K p := by
  intro x hx
  obtain ⟨s, ⟨hs, hps⟩, hxs⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨s, ⟨hM hs, hps⟩, hxs⟩

theorem HasPLCrossingAt.of_closedStar_pair
    (K K' M M' : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite K'.faces]
    (hM : M.faces ⊆ K.faces) (hM' : M'.faces ⊆ K'.faces)
    {p q : E} (hK : K.space ∈ 𝓝 p) {g : E → E}
    (hg : IsPLHomeomorphOn g (closedStar K p) (closedStar K' q)) (hgp : g p = q)
    (hgM : g '' closedStar M p = closedStar M' q)
    {B B' : Set E} (hgB : g '' (closedStar K p ∩ B) = closedStar K' q ∩ B')
    (hcross : HasPLCrossingAt M'.space B' q) : HasPLCrossingAt M.space B p := by
  let _ : Finite M.faces := ((Set.toFinite K.faces).subset hM).to_subtype
  let _ : Finite M'.faces := ((Set.toFinite K'.faces).subset hM').to_subtype
  have hc : HasPLCrossingAt (closedStar M' q) B' (g p) := by
    rw [hgp]
    exact hcross.congr ((eventually_mem_closedStar_iff M' q).mono fun _ h => h.symm)
      (Filter.Eventually.of_forall fun _ => Iff.rfl)
  have hgA : g '' (closedStar K p ∩ closedStar M p) = closedStar K' q ∩ closedStar M' q := by
    rw [inter_eq_right.mpr (closedStar_subset_of_faces_subset hM p),
      inter_eq_right.mpr (closedStar_subset_of_faces_subset hM' q), hgM]
  have hc' := hc.of_isPLHomeomorphOn_mem_nhds hg (closedStar_mem_nhds K hK) hgA hgB
  exact hc'.congr (eventually_mem_closedStar_iff M p) (Filter.Eventually.of_forall fun _ => Iff.rfl)

end DifferentialGeometry.Topology.PiecewiseLinear
