import DifferentialGeometry.Topology.Homotopy.RayComplement
import DifferentialGeometry.Topology.Homology.SimplexDegreeChainLevel
import DifferentialGeometry.Topology.Homology.ChainSupport
import DifferentialGeometry.Topology.Homology.AffineSimplex
import DifferentialGeometry.Topology.Homology.SubspaceCarriers

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

abbrev puncturedThreeSpace := ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1))

def negativeDiagonalRayComplement : Set (liftedSphereSpace.{u} 1) :=
  {x | ¬ ∃ r : ℝ, r ≤ 0 ∧ ∀ i : Fin 3, x.down i = r}

def positiveDiagonalRayComplement : Set (liftedSphereSpace.{u} 1) :=
  {x | ¬ ∃ r : ℝ, 0 ≤ r ∧ ∀ i : Fin 3, x.down i = r}

theorem standardTetrahedronSimplex_face_zero_mem_negativeDiagonalRayComplement
    (q : stdSimplex ℝ (Fin 3)) :
    standardTetrahedronSimplex (orientedSimplexFace 0 q) ∈
      negativeDiagonalRayComplement := by
  rintro ⟨r, hr, hc⟩
  have hzero : (orientedSimplexFace 0 q).val 0 = 0 := by
    change FunOnFinite.linearMap ℝ ℝ (0 : Fin 4).succAbove (q : Fin 3 → ℝ) 0 = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact False.elim (Fin.succAbove_ne 0 j (Finset.mem_filter.mp hj).2)
  have h (i : Fin 3) : (orientedSimplexFace 0 q).val i.succ = r := by
    have hh := hc i
    change positiveTetrahedron (orientedSimplexFace 0 q) i = r at hh
    rwa [positiveTetrahedron_coordinate, hzero, sub_zero] at hh
  have hs := (orientedSimplexFace 0 q).property.2
  rw [Fin.sum_univ_succ, hzero] at hs
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  norm_num at hs
  linarith

theorem standardTetrahedronSimplex_face_succ_mem_positiveDiagonalRayComplement
    (j : Fin 3) (q : stdSimplex ℝ (Fin 3)) :
    standardTetrahedronSimplex (orientedSimplexFace j.succ q) ∈
      positiveDiagonalRayComplement := by
  rintro ⟨r, hr, hc⟩
  have hzero : (orientedSimplexFace j.succ q).val j.succ = 0 := by
    change FunOnFinite.linearMap ℝ ℝ j.succ.succAbove (q : Fin 3 → ℝ) j.succ = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro k hk
    exact False.elim (Fin.succAbove_ne j.succ k (Finset.mem_filter.mp hk).2)
  have hh := hc j
  change positiveTetrahedron (orientedSimplexFace j.succ q) j = r at hh
  rw [positiveTetrahedron_coordinate, hzero, zero_sub] at hh
  have hn := (orientedSimplexFace j.succ q).property.1 0
  have hrzero : r = 0 := by linarith
  have he : positiveTetrahedron (orientedSimplexFace j.succ q) = 0 := by
    ext i
    exact (hc i).trans hrzero
  exact positiveTetrahedron_face_ne_zero (orientedSimplexFace j.succ q) j.succ hzero he


def puncturedPositiveRayComplement : Set puncturedThreeSpace.{u} :=
  {x | x.val ∈ positiveDiagonalRayComplement}

def puncturedNegativeRayComplement : Set puncturedThreeSpace.{u} :=
  {x | x.val ∈ negativeDiagonalRayComplement}

private def tetrahedronFaceMap (i : Fin 4) :
    C(stdSimplex ℝ (Fin 3), puncturedThreeSpace.{u}) :=
  ⟨fun q => ⟨standardTetrahedronSimplex (orientedSimplexFace i q),
      standardTetrahedronSimplex_face_ne_zero i q⟩,
    (standardTetrahedronSimplex.continuous.comp (orientedSimplexFace i).continuous).subtype_mk _⟩

private theorem simplexChain_comp {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) (f : C(X, Y)) (σ : C(stdSimplex ℝ (Fin (n + 1)), X)) :
    integralSimplexChain n σ ≫ (integralSingularChainMap f).f n =
      integralSimplexChain n (f.comp σ) :=
  SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of X))
    (TopCat.toSSet.obj (TopCat.of Y)) (TopCat.toSSet.map (TopCat.ofHom f))
    integralSingularCoefficients
    ((TopCat.toSSetObjEquiv (TopCat.of X) (.op ⦋n⦌)).symm σ)

private def tetrahedronPositiveFace (i : Fin 3) :
    C(stdSimplex ℝ (Fin 3), puncturedPositiveRayComplement.{u}) :=
  ⟨fun q => ⟨tetrahedronFaceMap i.succ q,
      standardTetrahedronSimplex_face_succ_mem_positiveDiagonalRayComplement.{u} i q⟩,
    (tetrahedronFaceMap i.succ).continuous.subtype_mk _⟩

private def tetrahedronNegativeFace :
    C(stdSimplex ℝ (Fin 3), puncturedNegativeRayComplement.{u}) :=
  ⟨fun q => ⟨tetrahedronFaceMap 0 q,
      standardTetrahedronSimplex_face_zero_mem_negativeDiagonalRayComplement.{u} q⟩,
    (tetrahedronFaceMap 0).continuous.subtype_mk _⟩

def tetrahedronPositiveFaceChain : integralSingularCoefficients ⟶
    (integralSingularChains puncturedPositiveRayComplement.{u}).X 2 :=
  ∑ i : Fin 3, (-1 : ℤ) ^ (i.val + 1) • integralSimplexChain 2 (tetrahedronPositiveFace i)

def tetrahedronNegativeFaceChain : integralSingularCoefficients ⟶
    (integralSingularChains puncturedNegativeRayComplement.{u}).X 2 :=
  integralSimplexChain 2 tetrahedronNegativeFace

theorem tetrahedronFaceChain_split :
    tetrahedronPositiveFaceChain ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedPositiveRayComplement)).f 2 +
      tetrahedronNegativeFaceChain ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedNegativeRayComplement)).f 2 =
      euclideanStandardSimplexBoundaryChain.{u} := by
  have hpos (i : Fin 3) :
      integralSimplexChain 2 (tetrahedronPositiveFace.{u} i) ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedPositiveRayComplement)).f 2 =
      integralSimplexChain 2 (tetrahedronFaceMap i.succ) := simplexChain_comp _ _ _
  have hneg : tetrahedronNegativeFaceChain ≫
        (integralSingularChainMap (singularSubspaceInclusion puncturedNegativeRayComplement)).f 2 =
      integralSimplexChain 2 (tetrahedronFaceMap 0) := simplexChain_comp _ _ _
  rw [tetrahedronPositiveFaceChain, Preadditive.sum_comp]
  simp only [Linear.smul_comp, hpos]
  rw [hneg, euclideanStandardSimplexBoundaryChain, puncturedSimplexBoundary]
  conv_rhs => rw [Fin.sum_univ_succ]
  change (∑ i : Fin 3, (-1 : ℤ) ^ (i.val + 1) • integralSimplexChain 2 (tetrahedronFaceMap i.succ)) +
    integralSimplexChain 2 (tetrahedronFaceMap 0) =
      (-1 : ℤ) ^ 0 • integralSimplexChain 2 (tetrahedronFaceMap 0) +
        ∑ i : Fin 3, (-1 : ℤ) ^ (i.val + 1) • integralSimplexChain 2 (tetrahedronFaceMap i.succ)
  simp only [pow_zero, one_smul]
  exact add_comm _ _


private theorem split_boundary_mem_intersection {X : Type u} [TopologicalSpace X]
    (A B : Set X) (n : ℕ)
    (z : integralSingularCoefficients ⟶ (integralSingularChains X).X (n + 2))
    (hz : z ≫ (integralSingularChains X).d (n + 2) (n + 1) = 0)
    (zA : integralSingularCoefficients ⟶ (integralSingularChains A).X (n + 2))
    (zB : integralSingularCoefficients ⟶ (integralSingularChains B).X (n + 2))
    (hsplit : zA ≫ (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 2) +
      zB ≫ (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 2) = z) :
    (integralSingularChains B).d (n + 2) (n + 1) (zB (ULift.up 1)) ∈
      integralSingularChainsIn (n + 1) (subspaceIntersection A B) := by
  rw [integralSingularChainsIn_subspace_iff, integralSingularChainsIn_eq_range]
  refine ⟨-((integralSingularChains A).d (n + 2) (n + 1) (zA (ULift.up 1))), ?_⟩
  have h := congrArg (fun k : integralSingularCoefficients ⟶
    (integralSingularChains X).X (n + 2) => k ≫ (integralSingularChains X).d (n + 2) (n + 1)) hsplit
  rw [hz, Preadditive.add_comp, Category.assoc, Category.assoc,
    (integralSingularChainMap (singularSubspaceInclusion A)).comm,
    (integralSingularChainMap (singularSubspaceInclusion B)).comm] at h
  have he := congrArg (fun k : integralSingularCoefficients ⟶
    (integralSingularChains X).X (n + 1) => k (ULift.up 1)) h
  change (integralSingularChainMap (singularSubspaceInclusion A)).f (n + 1)
    ((integralSingularChains A).d (n + 2) (n + 1) (zA (ULift.up 1))) +
    (integralSingularChainMap (singularSubspaceInclusion B)).f (n + 1)
    ((integralSingularChains B).d (n + 2) (n + 1) (zB (ULift.up 1))) = 0 at he
  rw [map_neg]
  exact (neg_eq_iff_add_eq_zero).mpr he

theorem tetrahedronNegativeFaceChain_boundary_mem :
    (integralSingularChains puncturedNegativeRayComplement.{u}).d 2 1
        (tetrahedronNegativeFaceChain (ULift.up 1)) ∈
      integralSingularChainsIn 1 (subspaceIntersection puncturedPositiveRayComplement
        puncturedNegativeRayComplement) :=
  split_boundary_mem_intersection _ _ 0 euclideanStandardSimplexBoundaryChain
    euclideanStandardSimplexBoundaryChain_boundary tetrahedronPositiveFaceChain
    tetrahedronNegativeFaceChain tetrahedronFaceChain_split

def tetrahedronFaceBoundaryChain :
    (integralSingularChains (subspaceIntersection puncturedPositiveRayComplement.{u}
      puncturedNegativeRayComplement)).X 1 :=
  integralSingularChainRestriction 1 _
    ⟨(integralSingularChains puncturedNegativeRayComplement.{u}).d 2 1
      (tetrahedronNegativeFaceChain (ULift.up 1)), tetrahedronNegativeFaceChain_boundary_mem⟩

theorem tetrahedronFaceBoundaryChain_inclusion :
    (integralSingularChainMap (singularSubspaceInclusion
      (subspaceIntersection puncturedPositiveRayComplement puncturedNegativeRayComplement))).f 1
        tetrahedronFaceBoundaryChain =
      (integralSingularChains puncturedNegativeRayComplement.{u}).d 2 1
        (tetrahedronNegativeFaceChain (ULift.up 1)) :=
  integralSingularChainRestriction_inclusion 1 _ _

theorem tetrahedronFaceBoundaryChain_boundary :
    (integralSingularChains (subspaceIntersection puncturedPositiveRayComplement.{u}
      puncturedNegativeRayComplement)).d 1 0 tetrahedronFaceBoundaryChain = 0 := by
  apply integralSingularChainInclusion_injective 0
    (subspaceIntersection puncturedPositiveRayComplement puncturedNegativeRayComplement)
  rw [← integralSingularChainMap_d, tetrahedronFaceBoundaryChain_inclusion, map_zero]
  exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    ((integralSingularChains puncturedNegativeRayComplement).d_comp_d 2 1 0))
      (tetrahedronNegativeFaceChain (ULift.up 1))


private def diagonalVector : liftedSphereSpace.{u} 1 :=
  ULift.up (WithLp.toLp 2 (fun _ : Fin 3 => (1 : ℝ)))

private theorem diagonalVector_ne_zero : diagonalVector.{u} ≠ 0 := by
  intro h
  have hc := congrArg (fun x : liftedSphereSpace.{u} 1 => x.down 0) h
  norm_num [diagonalVector] at hc

private theorem negativeDiagonalRayComplement_eq :
    negativeDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 1 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • diagonalVector) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨-r, by linarith, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = -(-r) * 1
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨-c, by linarith, fun i => by simp [diagonalVector]⟩

private theorem positiveDiagonalRayComplement_eq :
    positiveDiagonalRayComplement.{u} =
      (Set.ofPred fun x : liftedSphereSpace.{u} 1 => ¬ ∃ c : ℝ, 0 ≤ c ∧ x = -c • (-diagonalVector)) := by
  ext x
  apply not_congr
  constructor
  · rintro ⟨r, hr, hx⟩
    refine ⟨r, hr, ?_⟩
    apply ULift.ext
    ext i
    change x.down i = (-r) * (-1)
    rw [hx]
    ring
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, hc, fun i => by simp [diagonalVector]⟩

private theorem negativeDiagonalRayComplement_ne_zero
    (x : negativeDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

private theorem positiveDiagonalRayComplement_ne_zero
    (x : positiveDiagonalRayComplement.{u}) : x.val ≠ 0 := by
  intro h
  exact x.property ⟨0, le_rfl, by rw [h]; exact fun _ => rfl⟩

private def negativeRayPuncturedHomeomorph :
    puncturedNegativeRayComplement.{u} ≃ₜ negativeDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, negativeDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private def positiveRayPuncturedHomeomorph :
    puncturedPositiveRayComplement.{u} ≃ₜ positiveDiagonalRayComplement.{u} where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, positiveDiagonalRayComplement_ne_zero x⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

theorem puncturedNegativeRayComplement_contractibleSpace :
    ContractibleSpace puncturedNegativeRayComplement.{u} := by
  have : ContractibleSpace negativeDiagonalRayComplement.{u} := by
    rw [negativeDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray diagonalVector diagonalVector_ne_zero
  exact negativeRayPuncturedHomeomorph.contractibleSpace

theorem puncturedPositiveRayComplement_contractibleSpace :
    ContractibleSpace puncturedPositiveRayComplement.{u} := by
  have : ContractibleSpace positiveDiagonalRayComplement.{u} := by
    rw [positiveDiagonalRayComplement_eq]
    exact contractibleSpace_compl_nonpositive_ray (-diagonalVector) (neg_ne_zero.mpr diagonalVector_ne_zero)
  exact positiveRayPuncturedHomeomorph.contractibleSpace


private theorem isClosed_diagonal :
    IsClosed (Set.ofPred fun x : liftedSphereSpace.{u} 1 =>
      ∀ i : Fin 3, x.down i = x.down 0) := by
  have hc (i : Fin 3) : Continuous (fun x : liftedSphereSpace.{u} 1 => x.down i) := by fun_prop
  have heq : (Set.ofPred fun x : liftedSphereSpace.{u} 1 => ∀ i : Fin 3,
      x.down i = x.down 0) = ⋂ i, {y | y.down i = y.down 0} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq (hc i) (hc 0)

theorem isOpen_negativeDiagonalRayComplement :
    IsOpen negativeDiagonalRayComplement.{u} := by
  have he : negativeDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 1 => x.down 0 ≤ 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 1 => ∀ i : Fin 3, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change x.down 0 ≤ 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le (show Continuous (fun x : liftedSphereSpace.{u} 1 => x.down 0) by
    fun_prop) continuous_const).inter isClosed_diagonal).isOpen_compl

theorem isOpen_positiveDiagonalRayComplement :
    IsOpen positiveDiagonalRayComplement.{u} := by
  have he : positiveDiagonalRayComplement.{u} =
      ((Set.ofPred fun x : liftedSphereSpace.{u} 1 => 0 ≤ x.down 0) ∩
        (Set.ofPred fun x : liftedSphereSpace.{u} 1 => ∀ i : Fin 3, x.down i = x.down 0))ᶜ := by
    ext x
    apply not_congr
    constructor
    · rintro ⟨r, hr, hx⟩
      exact ⟨by change 0 ≤ x.down 0; rw [hx]; exact hr, fun i => (hx i).trans (hx 0).symm⟩
    · rintro ⟨h, hx⟩
      exact ⟨x.down 0, h, hx⟩
  rw [he]
  exact ((isClosed_le continuous_const (show Continuous (fun x : liftedSphereSpace.{u} 1 => x.down 0) by
    fun_prop)).inter isClosed_diagonal).isOpen_compl

theorem isOpen_puncturedNegativeRayComplement : IsOpen puncturedNegativeRayComplement.{u} :=
  isOpen_negativeDiagonalRayComplement.preimage continuous_subtype_val

theorem isOpen_puncturedPositiveRayComplement : IsOpen puncturedPositiveRayComplement.{u} :=
  isOpen_positiveDiagonalRayComplement.preimage continuous_subtype_val

theorem puncturedRayComplements_cover :
    puncturedPositiveRayComplement.{u} ∪ puncturedNegativeRayComplement = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_contra h
  have hp : ¬ x ∈ puncturedPositiveRayComplement := fun hx => h (Or.inl hx)
  have hn : ¬ x ∈ puncturedNegativeRayComplement := fun hx => h (Or.inr hx)
  obtain ⟨r, hr, hx⟩ := Classical.not_not.mp hp
  obtain ⟨s, hs, hy⟩ := Classical.not_not.mp hn
  have hrs : r = s := (hx 0).symm.trans (hy 0)
  have hr0 : r = 0 := by linarith
  apply x.property
  apply ULift.ext
  ext i
  exact (hx i).trans hr0


private theorem tetrahedronFaceBoundaryChain_inclusion_hom :
    integralChainHom 1 tetrahedronFaceBoundaryChain.{u} ≫
      (integralSingularChainMap (singularSubspaceInclusion
        (subspaceIntersection puncturedPositiveRayComplement puncturedNegativeRayComplement))).f 1 =
      tetrahedronNegativeFaceChain ≫
        (integralSingularChains puncturedNegativeRayComplement).d 2 1 := by
  rw [integralChainHom_comp_map, tetrahedronFaceBoundaryChain_inclusion, ← integralChainHom_d]
  have he : integralChainHom 2 (tetrahedronNegativeFaceChain.{u} (ULift.up 1)) =
      tetrahedronNegativeFaceChain := (integralChainHom_ext rfl).symm
  rw [he]

def tetrahedronBoundaryConnectingEquiv :
    integralSingularHomology 2 puncturedThreeSpace.{u} ≃ₗ[ℤ]
      integralSingularHomology 1
        (subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement) := by
  have : ContractibleSpace puncturedPositiveRayComplement.{u} :=
    puncturedPositiveRayComplement_contractibleSpace
  have : ContractibleSpace puncturedNegativeRayComplement.{u} :=
    puncturedNegativeRayComplement_contractibleSpace
  exact integralHomologyContractibleCoverEquiv 0 puncturedPositiveRayComplement
    puncturedNegativeRayComplement isOpen_puncturedPositiveRayComplement
    isOpen_puncturedNegativeRayComplement puncturedRayComplements_cover

theorem tetrahedronBoundaryConnectingEquiv_euclideanStandardSimplexBoundaryClass :
    tetrahedronBoundaryConnectingEquiv euclideanStandardSimplexBoundaryClass.{u} =
      integralHomologyClass 0 tetrahedronFaceBoundaryChain tetrahedronFaceBoundaryChain_boundary := by
  have : ContractibleSpace puncturedPositiveRayComplement.{u} :=
    puncturedPositiveRayComplement_contractibleSpace
  have : ContractibleSpace puncturedNegativeRayComplement.{u} :=
    puncturedNegativeRayComplement_contractibleSpace
  exact integralHomologyContractibleCoverEquiv_liftCycles_apply 0
    puncturedPositiveRayComplement puncturedNegativeRayComplement
    isOpen_puncturedPositiveRayComplement isOpen_puncturedNegativeRayComplement
    puncturedRayComplements_cover euclideanStandardSimplexBoundaryChain
    euclideanStandardSimplexBoundaryChain_boundary tetrahedronPositiveFaceChain
    tetrahedronNegativeFaceChain tetrahedronFaceChain_split
    (integralChainHom 1 tetrahedronFaceBoundaryChain)
    (by rw [integralChainHom_d, tetrahedronFaceBoundaryChain_boundary, integralChainHom_zero])
    tetrahedronFaceBoundaryChain_inclusion_hom


def tetrahedronProjection : C(liftedSphereSpace.{u} 1, liftedSphereSpace.{u} 0) where
  toFun x := ULift.up (WithLp.toLp 2 ![x.down 0 - x.down 2, x.down 1 - x.down 2])
  continuous_toFun := continuous_uliftUp.comp (by fun_prop)

def standardTriangleVertex : Fin 3 → liftedSphereSpace.{u} 0 :=
  ![ULift.up (WithLp.toLp 2 ![1, 0]), ULift.up (WithLp.toLp 2 ![0, 1]),
    ULift.up (WithLp.toLp 2 ![-1, -1])]

def standardTriangleSimplex : C(stdSimplex ℝ (Fin 3), liftedSphereSpace.{u} 0) :=
  affineSimplexMap standardTriangleVertex

private theorem orientedSimplexFace_zero_succ (q : stdSimplex ℝ (Fin 3)) (i : Fin 3) :
    (orientedSimplexFace 0 q).val i.succ = q.val i := by
  change FunOnFinite.linearMap ℝ ℝ (0 : Fin 4).succAbove (q : Fin 3 → ℝ) i.succ = q.val i
  rw [FunOnFinite.linearMap_apply_apply]
  simp only [Fin.succAbove_zero, Fin.succ_inj, Finset.filter_eq', Finset.mem_univ,
    if_true, Finset.sum_singleton]
  rfl

theorem tetrahedronProjection_face_zero :
    tetrahedronProjection.comp (standardTetrahedronSimplex.comp (orientedSimplexFace 0)) =
      standardTriangleSimplex.{u} := by
  apply ContinuousMap.ext
  intro q
  apply ULift.ext
  ext i
  fin_cases i
  · change positiveTetrahedron (orientedSimplexFace 0 q) 0 -
      positiveTetrahedron (orientedSimplexFace 0 q) 2 = _
    rw [positiveTetrahedron_coordinate, positiveTetrahedron_coordinate,
      orientedSimplexFace_zero_succ, orientedSimplexFace_zero_succ]
    simp [standardTriangleSimplex, affineSimplexMap, standardTriangleVertex, Fin.sum_univ_succ]
    ring
  · change positiveTetrahedron (orientedSimplexFace 0 q) 1 -
      positiveTetrahedron (orientedSimplexFace 0 q) 2 = _
    rw [positiveTetrahedron_coordinate, positiveTetrahedron_coordinate,
      orientedSimplexFace_zero_succ, orientedSimplexFace_zero_succ]
    simp [standardTriangleSimplex, affineSimplexMap, standardTriangleVertex, Fin.sum_univ_succ]
    ring

private theorem tetrahedronProjection_ne_zero
    (x : subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement) :
    tetrahedronProjection x.val.val.val ≠ 0 := by
  intro h
  have h0 := congrArg (fun y : liftedSphereSpace.{u} 0 => y.down 0) h
  have h1 := congrArg (fun y : liftedSphereSpace.{u} 0 => y.down 1) h
  change x.val.val.val.down 0 - x.val.val.val.down 2 = 0 at h0
  change x.val.val.val.down 1 - x.val.val.val.down 2 = 0 at h1
  have he (i : Fin 3) : x.val.val.val.down i = x.val.val.val.down 2 := by
    fin_cases i
    · exact sub_eq_zero.mp h0
    · exact sub_eq_zero.mp h1
    · rfl
  rcases le_total (0 : ℝ) (x.val.val.val.down 2) with hp | hn
  · exact x.property ⟨x.val.val.val.down 2, hp, he⟩
  · exact x.val.property ⟨x.val.val.val.down 2, hn, he⟩

def tetrahedronOverlapProjection :
    C(subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement,
      ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))) :=
  ⟨fun x => ⟨tetrahedronProjection x.val.val.val, tetrahedronProjection_ne_zero x⟩,
    (tetrahedronProjection.continuous.comp
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _⟩

private def tetrahedronNegativeProjection :
    C(puncturedNegativeRayComplement.{u}, liftedSphereSpace.{u} 0) :=
  tetrahedronProjection.comp
    ((singularSubspaceInclusion ({(0 : liftedSphereSpace.{u} 1)}ᶜ : Set (liftedSphereSpace.{u} 1))).comp
      (singularSubspaceInclusion puncturedNegativeRayComplement))

private theorem tetrahedronNegativeProjection_chain :
    tetrahedronNegativeFaceChain ≫ (integralSingularChainMap tetrahedronNegativeProjection).f 2 =
      integralSimplexChain 2 standardTriangleSimplex.{u} := by
  rw [tetrahedronNegativeFaceChain, simplexChain_comp]
  have he : tetrahedronNegativeProjection.comp tetrahedronNegativeFace = standardTriangleSimplex.{u} :=
    tetrahedronProjection_face_zero
  rw [he]

private theorem tetrahedronOverlapProjection_square :
    (singularSubspaceInclusion ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))).comp
        tetrahedronOverlapProjection =
      tetrahedronNegativeProjection.comp
        (singularSubspaceInclusion
          (subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement)) := rfl

def standardTriangleChain : (integralSingularChains (liftedSphereSpace.{u} 0)).X 2 :=
  integralSimplexChain 2 standardTriangleSimplex (ULift.up 1)

theorem tetrahedronOverlapProjection_faceBoundaryChain :
    (integralSingularChainMap
        (singularSubspaceInclusion ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)))).f 1
      ((integralSingularChainMap tetrahedronOverlapProjection).f 1 tetrahedronFaceBoundaryChain) =
    (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain := by
  have hsq := congrArg (fun φ => (integralSingularChainMap φ).f 1) tetrahedronOverlapProjection_square
  simp only [integralSingularChainMap_comp, HomologicalComplex.comp_f] at hsq
  have he := congrArg (fun φ :
      (integralSingularChains
        (subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement)).X 1 ⟶
        (integralSingularChains (liftedSphereSpace.{u} 0)).X 1 => φ tetrahedronFaceBoundaryChain) hsq
  change (integralSingularChainMap
      (singularSubspaceInclusion ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)))).f 1
      ((integralSingularChainMap tetrahedronOverlapProjection).f 1 tetrahedronFaceBoundaryChain) =
    (integralSingularChainMap tetrahedronNegativeProjection).f 1
      ((integralSingularChainMap (singularSubspaceInclusion
        (subspaceIntersection puncturedPositiveRayComplement.{u} puncturedNegativeRayComplement))).f 1
          tetrahedronFaceBoundaryChain) at he
  rw [he, tetrahedronFaceBoundaryChain_inclusion, ← integralSingularChainMap_d]
  have hh := congrArg (fun φ : integralSingularCoefficients ⟶
    (integralSingularChains (liftedSphereSpace.{u} 0)).X 2 => φ (ULift.up 1)) tetrahedronNegativeProjection_chain
  exact congrArg ((integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1) hh


theorem standardTriangleChain_boundary_mem :
    (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain ∈
      integralSingularChainsIn 1 ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)) := by
  rw [integralSingularChainsIn_eq_range]
  exact ⟨(integralSingularChainMap tetrahedronOverlapProjection).f 1 tetrahedronFaceBoundaryChain,
    tetrahedronOverlapProjection_faceBoundaryChain⟩

def standardTriangleBoundaryChain :
    (integralSingularChains ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))).X 1 :=
  integralSingularChainRestriction 1 _
    ⟨(integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain,
      standardTriangleChain_boundary_mem⟩

theorem standardTriangleBoundaryChain_inclusion :
    (integralSingularChainMap
      (singularSubspaceInclusion ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)))).f 1
        standardTriangleBoundaryChain =
      (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 standardTriangleChain :=
  integralSingularChainRestriction_inclusion 1 _ _

theorem tetrahedronOverlapProjection_faceBoundaryChain_eq :
    (integralSingularChainMap tetrahedronOverlapProjection).f 1 tetrahedronFaceBoundaryChain =
      standardTriangleBoundaryChain.{u} := by
  apply integralSingularChainInclusion_injective 1 _
  rw [standardTriangleBoundaryChain_inclusion, tetrahedronOverlapProjection_faceBoundaryChain]

theorem standardTriangleBoundaryChain_boundary :
    (integralSingularChains ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0))).d 1 0
      standardTriangleBoundaryChain = 0 := by
  rw [← tetrahedronOverlapProjection_faceBoundaryChain_eq, integralSingularChainMap_d,
    tetrahedronFaceBoundaryChain_boundary, map_zero]

def standardTriangleBoundaryClass :
    integralSingularHomology 1 ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)) :=
  integralHomologyClass 0 standardTriangleBoundaryChain standardTriangleBoundaryChain_boundary

theorem tetrahedronOverlapProjection_faceBoundaryClass :
    integralSingularHomologyMap 1 tetrahedronOverlapProjection
      (integralHomologyClass 0 tetrahedronFaceBoundaryChain tetrahedronFaceBoundaryChain_boundary) =
      standardTriangleBoundaryClass.{u} := by
  rw [integralHomologyClass, integralSingularHomologyMap_integralHomologyClassOf]
  have he : integralChainHom 1 tetrahedronFaceBoundaryChain ≫
      (integralSingularChainMap tetrahedronOverlapProjection).f 1 =
      integralChainHom 1 standardTriangleBoundaryChain.{u} := by
    rw [integralChainHom_comp_map, tetrahedronOverlapProjection_faceBoundaryChain_eq]
  exact integralHomologyClassOf_congr he

def tetrahedronToTriangleHomology :
    integralSingularHomology 2 puncturedThreeSpace.{u} →ₗ[ℤ]
      integralSingularHomology 1 ({(0 : liftedSphereSpace.{u} 0)}ᶜ : Set (liftedSphereSpace.{u} 0)) :=
  (integralSingularHomologyMap 1 tetrahedronOverlapProjection).comp
    tetrahedronBoundaryConnectingEquiv.toLinearMap

theorem tetrahedronToTriangleHomology_euclideanStandardSimplexBoundaryClass :
    tetrahedronToTriangleHomology euclideanStandardSimplexBoundaryClass.{u} =
      standardTriangleBoundaryClass := by
  rw [tetrahedronToTriangleHomology, LinearMap.comp_apply,
    LinearEquiv.coe_coe, tetrahedronBoundaryConnectingEquiv_euclideanStandardSimplexBoundaryClass,
    tetrahedronOverlapProjection_faceBoundaryClass]

end DifferentialGeometry.Topology.SimplexDegree
