/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.SmallChains.IntersectionPreimage
import DifferentialGeometry.Topology.PiecewiseLinear.MayerVietorisSubcomplex

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

theorem exists_mem_inter_of_maps_eq {k : Type} [Ring k] (R : ModuleCat k)
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces) (n : ℕ)
    (z : (((singularHomologyFunctor (ModuleCat k) n).obj R).obj (TopCat.of L.space)))
    (w : (((singularHomologyFunctor (ModuleCat k) n).obj R).obj (TopCat.of M.space)))
    (hzw : (((singularHomologyFunctor (ModuleCat k) n).obj R).map
      (TopCat.ofHom (subcomplexInclusion hL))) z =
      (((singularHomologyFunctor (ModuleCat k) n).obj R).map
        (TopCat.ofHom (subcomplexInclusion hM))) w) :
    ∃ y : (((singularHomologyFunctor (ModuleCat k) n).obj R).obj
        (TopCat.of (intersectionComplex L M).space)),
      (((singularHomologyFunctor (ModuleCat k) n).obj R).map
        (TopCat.ofHom (subcomplexInclusion (K := L) (L := intersectionComplex L M)
          (fun _ hs => hs.1)))) y = z ∧
      (((singularHomologyFunctor (ModuleCat k) n).obj R).map
        (TopCat.ofHom (subcomplexInclusion (K := M) (L := intersectionComplex L M)
          (fun _ hs => hs.2)))) y = w := by
  let H := (singularHomologyFunctor (ModuleCat k) n).obj R
  let U := subcomplexOpenNeighborhood K L
  let V := subcomplexOpenNeighborhood K M
  let A := intersectionComplex L M
  let jL : TopCat.of L.space ⟶ TopCat.of U :=
    TopCat.ofHom (subcomplexOpenNeighborhoodInclusion hL)
  let jM : TopCat.of M.space ⟶ TopCat.of V :=
    TopCat.ofHom (subcomplexOpenNeighborhoodInclusion hM)
  let jA : TopCat.of A.space ⟶ TopCat.of (U ∩ V : Set K.space) :=
    TopCat.ofHom (subcomplexOpenNeighborhoodInterInclusion hL hM)
  let iL : TopCat.of U ⟶ TopCat.of K.space :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iM : TopCat.of V ⟶ TopCat.of K.space :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iIL := Homology.subspaceInclusion (TopCat.of K.space)
    (show U ∩ V ⊆ U from Set.inter_subset_left)
  let iIM := Homology.subspaceInclusion (TopCat.of K.space)
    (show U ∩ V ⊆ V from Set.inter_subset_right)
  let iAL := TopCat.ofHom (subcomplexInclusion (K := L) (L := A) (fun _ hs => hs.1))
  let iAM := TopCat.ofHom (subcomplexInclusion (K := M) (L := A) (fun _ hs => hs.2))
  let _ : IsIso (H.map jL) := isIso_subcomplexOpenNeighborhoodInclusion_map R hL n
  let _ : IsIso (H.map jM) := isIso_subcomplexOpenNeighborhoodInclusion_map R hM n
  let _ : IsIso (H.map jA) :=
    isIso_subcomplexOpenNeighborhoodInterInclusion_map R hL hM n
  have hLK : jL ≫ iL = TopCat.ofHom (subcomplexInclusion hL) := by
    ext x
    rfl
  have hMK : jM ≫ iM = TopCat.ofHom (subcomplexInclusion hM) := by
    ext x
    rfl
  have hAL : iAL ≫ jL = jA ≫ iIL := by
    ext x
    rfl
  have hAM : iAM ≫ jM = jA ≫ iIM := by
    ext x
    rfl
  have hzwUV : H.map iL (H.map jL z) = H.map iM (H.map jM w) := by
    change (H.map jL ≫ H.map iL) z = (H.map jM ≫ H.map iM) w
    rw [← H.map_comp, ← H.map_comp, hLK, hMK]
    exact hzw
  obtain ⟨v, hvL, hvM⟩ := Homology.exists_intersection_preimage_of_inclusion_maps_eq
    (TopCat.of K.space) U V R (isOpen_subcomplexOpenNeighborhood K L)
      (isOpen_subcomplexOpenNeighborhood K M) (subcomplexOpenNeighborhood_union hL hM hcover)
      n (H.map jL z) (H.map jM w) hzwUV
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (H.map jA)).mp inferInstance v
  refine ⟨y, ?_, ?_⟩
  · apply (ModuleCat.mono_iff_injective (H.map jL)).mp inferInstance
    change (H.map iAL ≫ H.map jL) y = H.map jL z
    rw [← H.map_comp, hAL, H.map_comp]
    change H.map iIL (H.map jA y) = H.map jL z
    rw [hy]
    exact hvL
  · apply (ModuleCat.mono_iff_injective (H.map jM)).mp inferInstance
    change (H.map iAM ≫ H.map jM) y = H.map jM w
    rw [← H.map_comp, hAM, H.map_comp]
    change H.map iIM (H.map jA y) = H.map jM w
    rw [hy]
    exact hvM

end DifferentialGeometry.Topology.PiecewiseLinear
