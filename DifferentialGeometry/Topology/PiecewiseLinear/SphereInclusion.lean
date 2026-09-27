/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.InvarianceOfDomainManifold
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLSphere.surjOn_of_continuousOn_injOn {n : ℕ} {S : Set E} {T : Set F}
    (hS : IsPLSphere (n + 1) S) (hT : IsPLSphere (n + 1) T) {f : E → F}
    (hf : ContinuousOn f S) (hinj : InjOn f S) (hmap : MapsTo f S T) : SurjOn f S T := by
  classical
  obtain ⟨K, hKfin, hKS⟩ := hS.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLT⟩ := hT.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLSphere (n + 1) K.space := hKS.symm ▸ hS
  have hL : IsPLSphere (n + 1) L.space := hLT.symm ▸ hT
  let _ := combinatorialChartedSpace K hK.isCombinatorialManifold
  let _ := combinatorialChartedSpace L hL.isCombinatorialManifold
  let _ : CompactSpace K.space := isCompact_iff_compactSpace.mp (isPolyhedron_space K).isCompact
  let _ : Nonempty K.space := hK.nonempty.to_subtype
  let _ : ConnectedSpace L.space := Subtype.connectedSpace hL.isConnected
  let g : K.space → L.space := fun x => ⟨f x, hLT.symm.subset (hmap (hKS.subset x.2))⟩
  have hfK : ContinuousOn f K.space := hKS.symm ▸ hf
  have hg : Continuous g := hfK.domRestrict.subtype_mk _
  have hginj : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hinj (hKS.subset x.2) (hKS.subset y.2) (congrArg Subtype.val hxy))
  have hsurj : Function.Surjective g :=
    surjective_of_continuous_injective (E := EuclideanSpace ℝ (Fin (n + 1))) hg hginj
  intro y hy
  obtain ⟨x, hx⟩ := hsurj ⟨y, hLT.symm.subset hy⟩
  exact ⟨x, hKS.subset x.2, congrArg Subtype.val hx⟩

theorem eq_of_subset_of_isPLSphere {n : ℕ} {S T : Set E}
    (hS : IsPLSphere (n + 1) S) (hT : IsPLSphere (n + 1) T) (hST : S ⊆ T) : S = T := by
  have hsurj := hS.surjOn_of_continuousOn_injOn hT continuous_id.continuousOn (injOn_id S) hST
  exact Subset.antisymm hST (fun x hx => by
    obtain ⟨y, hy, hxy⟩ := hsurj hx
    exact hxy ▸ hy)

theorem IsPLSphere.image_eq_of_mapsTo {n : ℕ} {S : Set E} (hS : IsPLSphere (n + 1) S)
    {f : E → E} (hf : ContinuousOn f S) (hinj : InjOn f S) (hmap : MapsTo f S S) : f '' S = S :=
  Subset.antisymm (image_subset_iff.mpr hmap) (hS.surjOn_of_continuousOn_injOn hS hf hinj hmap)

end DifferentialGeometry.Topology.PiecewiseLinear
