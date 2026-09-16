import DifferentialGeometry.Topology.Homology.HomotopyEquivalence
import DifferentialGeometry.Topology.Homology.SmallChains.BettiBound
import DifferentialGeometry.Topology.Homology.SmallChains.Exactness
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNeighborhood

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L M : Geometry.SimplicialComplex ℝ E} [Finite K.faces]

theorem isIso_subcomplexOpenNeighborhoodInclusion_map
    {k : Type} [Ring k] (R : ModuleCat k) (hL : L.faces ⊆ K.faces) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat k) n).obj R).map
      (TopCat.ofHom (subcomplexOpenNeighborhoodInclusion hL))) :=
  Homology.isIso_singularHomologyMap_of_homotopyEquiv R
    (X := TopCat.of L.space) (Y := TopCat.of (subcomplexOpenNeighborhood K L))
    (subcomplexOpenNeighborhoodHomotopyEquiv hL).symm n

theorem isIso_subcomplexOpenNeighborhoodInterInclusion_map
    {k : Type} [Ring k] (R : ModuleCat k)
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) (n : ℕ) :
    IsIso (((singularHomologyFunctor (ModuleCat k) n).obj R).map
      (TopCat.ofHom (subcomplexOpenNeighborhoodInterInclusion hL hM))) := by
  rw [← subcomplexOpenNeighborhoodInterHomotopyEquiv_invFun hL hM]
  exact Homology.isIso_singularHomologyMap_of_homotopyEquiv R
    (X := TopCat.of (intersectionComplex L M).space)
    (Y := TopCat.of (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space))
    (subcomplexOpenNeighborhoodInterHomotopyEquiv hL hM).symm n

theorem exists_mem_inter_of_map_eq_zero {k : Type} [Ring k] (R : ModuleCat k)
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces) (n : ℕ)
    (z : (((singularHomologyFunctor (ModuleCat k) n).obj R).obj (TopCat.of L.space)))
    (hz : (((singularHomologyFunctor (ModuleCat k) n).obj R).map
      (TopCat.ofHom (subcomplexInclusion hL))) z = 0) :
    ∃ y : (((singularHomologyFunctor (ModuleCat k) n).obj R).obj
        (TopCat.of (intersectionComplex L M).space)),
      (((singularHomologyFunctor (ModuleCat k) n).obj R).map
        (TopCat.ofHom (subcomplexInclusion (K := L) (L := intersectionComplex L M)
          (fun _ hs => hs.1)))) y = z ∧
      (((singularHomologyFunctor (ModuleCat k) n).obj R).map
        (TopCat.ofHom (subcomplexInclusion (K := M) (L := intersectionComplex L M)
          (fun _ hs => hs.2)))) y = 0 := by
  let H := (singularHomologyFunctor (ModuleCat k) n).obj R
  let U := subcomplexOpenNeighborhood K L
  let V := subcomplexOpenNeighborhood K M
  let A := intersectionComplex L M
  let jL : TopCat.of L.space ⟶ TopCat.of U := TopCat.ofHom (subcomplexOpenNeighborhoodInclusion hL)
  let jM : TopCat.of M.space ⟶ TopCat.of V := TopCat.ofHom (subcomplexOpenNeighborhoodInclusion hM)
  let jA : TopCat.of A.space ⟶ TopCat.of (U ∩ V : Set K.space) :=
    TopCat.ofHom (subcomplexOpenNeighborhoodInterInclusion hL hM)
  let iL : TopCat.of U ⟶ TopCat.of K.space := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let iIL := Homology.subspaceInclusion (TopCat.of K.space)
    (show U ∩ V ⊆ U from Set.inter_subset_left)
  let iIM := Homology.subspaceInclusion (TopCat.of K.space)
    (show U ∩ V ⊆ V from Set.inter_subset_right)
  let iAL := TopCat.ofHom (subcomplexInclusion (K := L) (L := A) (fun _ hs => hs.1))
  let iAM := TopCat.ofHom (subcomplexInclusion (K := M) (L := A) (fun _ hs => hs.2))
  let _ : IsIso (H.map jL) := isIso_subcomplexOpenNeighborhoodInclusion_map R hL n
  let _ : IsIso (H.map jM) := isIso_subcomplexOpenNeighborhoodInclusion_map R hM n
  let _ : IsIso (H.map jA) := isIso_subcomplexOpenNeighborhoodInterInclusion_map R hL hM n
  have hLK : jL ≫ iL = TopCat.ofHom (subcomplexInclusion hL) := by
    ext x
    rfl
  have hAL : iAL ≫ jL = jA ≫ iIL := by
    ext x
    rfl
  have hAM : iAM ≫ jM = jA ≫ iIM := by
    ext x
    rfl
  have hzU : H.map iL (H.map jL z) = 0 := by
    change (H.map jL ≫ H.map iL) z = 0
    rw [← H.map_comp, hLK]
    exact hz
  obtain ⟨v, hvL, hvM⟩ := Homology.exists_intersection_preimage_of_inclusion_map_eq_zero
    (TopCat.of K.space) U V R (isOpen_subcomplexOpenNeighborhood K L)
      (isOpen_subcomplexOpenNeighborhood K M) (subcomplexOpenNeighborhood_union hL hM hcover)
      n (H.map jL z) hzU
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective (H.map jA)).mp inferInstance v
  refine ⟨y, ?_, ?_⟩
  · apply (ModuleCat.mono_iff_injective (H.map jL)).mp inferInstance
    change (H.map iAL ≫ H.map jL) y = H.map jL z
    rw [← H.map_comp, hAL, H.map_comp]
    change H.map iIL (H.map jA y) = H.map jL z
    rw [hy]
    exact hvL
  · apply (ModuleCat.mono_iff_injective (H.map jM)).mp inferInstance
    rw [map_zero]
    change (H.map iAM ≫ H.map jM) y = 0
    rw [← H.map_comp, hAM, H.map_comp]
    change H.map iIM (H.map jA y) = 0
    rw [hy]
    exact hvM

theorem finiteHomologyType_subcomplexOpenNeighborhood (k : Type) [Field k]
    (hL : L.faces ⊆ K.faces) :
    Homology.finiteHomologyType k (TopCat.of (subcomplexOpenNeighborhood K L)) := by
  let _ : Finite L.faces := ((Set.toFinite K.faces).subset hL).to_subtype
  exact (Homology.finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of (subcomplexOpenNeighborhood K L)) (Y := TopCat.of L.space)
    (subcomplexOpenNeighborhoodHomotopyEquiv hL)).mpr
    (SimplicialComplex.finiteHomologyType_geometricSpace L k)

theorem finiteHomologyType_subcomplexOpenNeighborhood_inter (k : Type) [Field k]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces) :
    Homology.finiteHomologyType k
      (TopCat.of (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space)) := by
  let _ : Finite L.faces := ((Set.toFinite K.faces).subset hL).to_subtype
  exact (Homology.finiteHomologyType_iff_of_homotopyEquiv k
    (X := TopCat.of (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space))
    (Y := TopCat.of (intersectionComplex L M).space)
    (subcomplexOpenNeighborhoodInterHomotopyEquiv hL hM)).mpr
    (SimplicialComplex.finiteHomologyType_geometricSpace (intersectionComplex L M) k)

theorem bettiNumber_union_le (k : Type) [Field k]
    (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces) (n : ℕ) :
    Homology.bettiNumber k (TopCat.of K.space) (n + 1) ≤
      Homology.bettiNumber k (TopCat.of L.space) (n + 1) +
      Homology.bettiNumber k (TopCat.of M.space) (n + 1) +
      Homology.bettiNumber k (TopCat.of (intersectionComplex L M).space) n := by
  have h := Homology.bettiNumber_union_le k (TopCat.of K.space)
    (subcomplexOpenNeighborhood K L) (subcomplexOpenNeighborhood K M)
    (isOpen_subcomplexOpenNeighborhood K L) (isOpen_subcomplexOpenNeighborhood K M)
    (subcomplexOpenNeighborhood_union hL hM hcover)
    (finiteHomologyType_subcomplexOpenNeighborhood k hL)
    (finiteHomologyType_subcomplexOpenNeighborhood k hM)
    (finiteHomologyType_subcomplexOpenNeighborhood_inter k hL hM) n
  rw [Homology.bettiNumber_eq_of_homotopyEquiv k
      (X := TopCat.of (subcomplexOpenNeighborhood K L)) (Y := TopCat.of L.space)
      (subcomplexOpenNeighborhoodHomotopyEquiv hL),
    Homology.bettiNumber_eq_of_homotopyEquiv k
      (X := TopCat.of (subcomplexOpenNeighborhood K M)) (Y := TopCat.of M.space)
      (subcomplexOpenNeighborhoodHomotopyEquiv hM),
    Homology.bettiNumber_eq_of_homotopyEquiv k
      (X := TopCat.of (subcomplexOpenNeighborhood K L ∩ subcomplexOpenNeighborhood K M : Set K.space))
      (Y := TopCat.of (intersectionComplex L M).space)
      (subcomplexOpenNeighborhoodInterHomotopyEquiv hL hM)] at h
  exact h

theorem bettiOne_union_le (hL : L.faces ⊆ K.faces) (hM : M.faces ⊆ K.faces)
    (hcover : K.faces ⊆ L.faces ∪ M.faces) :
    Homology.bettiOne K.space ≤ Homology.bettiOne L.space + Homology.bettiOne M.space +
      Homology.bettiNumber ℚ (TopCat.of (intersectionComplex L M).space) 0 :=
  bettiNumber_union_le ℚ hL hM hcover 0

end DifferentialGeometry.Topology.PiecewiseLinear
