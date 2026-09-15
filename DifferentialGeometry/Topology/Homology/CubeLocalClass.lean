import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CubeTetrahedralChainBridge
import DifferentialGeometry.Topology.Homology.SimplexDegreeNaturality

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Topology Simplicial

universe u

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

def cubeStaircasePoint : Fin 3 → unitInterval := ![⟨3/4, by norm_num⟩,⟨1/2, by norm_num⟩,⟨1/4, by norm_num⟩]

private theorem staircasePoint_coordinate (e : Equiv.Perm (Fin 3)) (q : stdSimplex ℝ (Fin 4)) (k : Fin 3)
 (h : staircaseSimplex e q = cubeStaircasePoint) :
 ((cubeStaircasePoint (e k) : unitInterval) : ℝ) = ∑ j : Fin 4, if k.val < j.val then q.val j else 0 := by
  have hh := congrArg (fun z => (z (e k) : unitInterval) : (Fin 3 → unitInterval) → unitInterval) h
  change (cubeStaircasePoint (e k) : ℝ) = _
  rw [← hh]
  simp [staircaseSimplex, staircaseCoordinate]

private theorem staircasePoint_antitone (e : Equiv.Perm (Fin 3)) (q : stdSimplex ℝ (Fin 4))
 (h : staircaseSimplex e q = cubeStaircasePoint) :
 ((cubeStaircasePoint (e 0) : unitInterval) : ℝ) ≥ ((cubeStaircasePoint (e 1) : unitInterval) : ℝ) ∧
 ((cubeStaircasePoint (e 1) : unitInterval) : ℝ) ≥ ((cubeStaircasePoint (e 2) : unitInterval) : ℝ) := by
  have h0 := staircasePoint_coordinate e q 0 h
  have h1 := staircasePoint_coordinate e q 1 h
  have h2 := staircasePoint_coordinate e q 2 h
  constructor
  · rw [h0, h1]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs <;> first
    | exact le_rfl
    | exact q.property.1 j
    | omega
  · rw [h1, h2]
    apply Finset.sum_le_sum
    intro j hj
    split_ifs <;> first
    | exact le_rfl
    | exact q.property.1 j
    | omega

theorem staircaseSimplex_ne_cubeStaircasePoint (e : Equiv.Perm (Fin 3))
    (he : e ≠ Equiv.refl (Fin 3)) (q : stdSimplex ℝ (Fin 4)) :
    staircaseSimplex e q ≠ cubeStaircasePoint := by
  intro h
  have hm := staircasePoint_antitone e q h
  have hn01 := e.injective.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hn02 := e.injective.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hn12 := e.injective.ne (show (1 : Fin 3) ≠ 2 by decide)
  generalize h0 : e 0 = a at hm hn01 hn02
  generalize h1 : e 1 = b at hm hn01 hn12
  generalize h2 : e 2 = c at hm hn02 hn12
  fin_cases a <;> fin_cases b <;> fin_cases c <;> try { norm_num [cubeStaircasePoint] at * }
  apply he
  ext i
  fin_cases i <;> simp_all

theorem staircaseSimplex_refl_eq_cubeStaircasePoint_coordinates
    (q : stdSimplex ℝ (Fin 4))
    (h : staircaseSimplex (Equiv.refl (Fin 3)) q = cubeStaircasePoint) (i : Fin 4) :
    q.val i = (1/4 : ℝ) := by
  have h0 := staircasePoint_coordinate (Equiv.refl (Fin 3)) q 0 h
  have h1 := staircasePoint_coordinate (Equiv.refl (Fin 3)) q 1 h
  have h2 := staircasePoint_coordinate (Equiv.refl (Fin 3)) q 2 h
  have hsum := q.property.2
  norm_num [cubeStaircasePoint, Fin.sum_univ_succ, Matrix.cons_val_two] at h0 h1 h2 hsum
  fin_cases i
  · dsimp
    linarith
  · dsimp
    linarith
  · dsimp
    linarith
  · exact h2.symm

theorem staircaseSimplex_refl_face_ne_cubeStaircasePoint (i : Fin 4)
    (q : stdSimplex ℝ (Fin 3)) :
    staircaseSimplex (Equiv.refl (Fin 3)) (SimplexDegree.orientedSimplexFace i q) ≠
      cubeStaircasePoint := by
  intro h
  have hh := staircaseSimplex_refl_eq_cubeStaircasePoint_coordinates _ h i
  have hi : (SimplexDegree.orientedSimplexFace i q).val i = 0 := by
    change FunOnFinite.linearMap ℝ ℝ i.succAbove (q : Fin 3 → ℝ) i = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro j hj
    exact False.elim (Fin.succAbove_ne i j (Finset.mem_filter.mp hj).2)
  rw [hi] at hh
  norm_num at hh


private theorem singularSimplexChain_comp_projection_of_mem {X : Type u} [TopologicalSpace X]
    (n : ℕ) (A : Set X) (σ : C(stdSimplex ℝ (Fin (n + 1)), X))
    (hσ : ∀ t, σ t ∈ A) :
    SimplexDegree.integralSimplexChain n σ ≫ (integralRelativeProjection A).f n = 0 := by
  let τ : C(stdSimplex ℝ (Fin (n + 1)), A) :=
    ⟨fun t => ⟨σ t, hσ t⟩, σ.continuous.subtype_mk _⟩
  have hchain : SimplexDegree.integralSimplexChain n τ ≫
      (integralSingularChainMap (singularSubspaceInclusion A)).f n =
      SimplexDegree.integralSimplexChain n σ :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj (TopCat.of A))
      (TopCat.toSSet.obj (TopCat.of X))
      (TopCat.toSSet.map (TopCat.ofHom (singularSubspaceInclusion A)))
      integralSingularCoefficients
      ((TopCat.toSSetObjEquiv (TopCat.of A) (.op ⦋n⦌)).symm τ)
  have hπ : (integralSingularChainMap (singularSubspaceInclusion A)).f n ≫
      (integralRelativeProjection A).f n = 0 :=
    congrArg (fun f => f.f n) (integralRelativeProjection_condition A)
  rw [← hchain]
  erw [Category.assoc, hπ, Limits.comp_zero]

private theorem moduleCat_sum_apply {ι : Type*} {M N : ModuleCat.{u} ℤ} (s : Finset ι)
    (f : ι → (M ⟶ N)) (x : M) : s.sum f x = s.sum (fun i => f i x) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha]

private theorem cubeTetrahedralChain_eq_sum :
    cubeTetrahedralChain =
      ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
        DifferentialGeometry.Topology.integralSimplexChain 3
          ((TopCat.toSSetObjEquiv (TopCat.of (Fin 3 → unitInterval)) (.op ⦋3⦌)).symm
            (staircaseSimplex e)) := by
  rw [cubeTetrahedralChain, cubeChain]
  erw [moduleCat_sum_apply]
  exact Finset.sum_congr rfl fun e _ => rfl

private theorem integralChainHom_cubeTetrahedralChain_image {X : Type u} [TopologicalSpace X]
    (f : C(Fin 3 → unitInterval, X)) :
    integralChainHom 3 (singularChainImageGen 3 f cubeTetrahedralChain) =
      ∑ e : Equiv.Perm (Fin 3), ((e.sign : ℤˣ) : ℤ) •
        SimplexDegree.integralSimplexChain 3 (f.comp (staircaseSimplex e)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  rcases y with ⟨k⟩
  have hk : (ULift.up k : ULift.{u} ℤ) = k • (ULift.up (1 : ℤ) : ULift.{u} ℤ) := by
    ext
    simp
  rw [hk, map_zsmul, map_zsmul]
  congr 1
  rw [integralChainHom_hom, LinearMap.comp_apply]
  erw [LinearMap.toSpanSingleton_apply_one, moduleCat_sum_apply]
  rw [cubeTetrahedralChain_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [map_zsmul, singularChainImageGen_simplex]
  rfl

private theorem cubeChain_image_comp_projection_eq_simplex {X : Type u} [TopologicalSpace X]
    (f : C(Fin 3 → unitInterval, X)) (p : X)
    (hp : ∀ e : Equiv.Perm (Fin 3), e ≠ Equiv.refl (Fin 3) →
      ∀ t, f (staircaseSimplex e t) ≠ p) :
    integralChainHom 3 (singularChainImageGen 3 f cubeTetrahedralChain) ≫
        (integralRelativeProjection ({p}ᶜ : Set X)).f 3 =
      SimplexDegree.integralSimplexChain 3 (f.comp (staircaseSimplex (Equiv.refl (Fin 3)))) ≫
        (integralRelativeProjection ({p}ᶜ : Set X)).f 3 := by
  classical
  rw [integralChainHom_cubeTetrahedralChain_image]
  erw [Preadditive.sum_comp]
  rw [Finset.sum_eq_single (Equiv.refl (Fin 3))]
  · simp only [Equiv.Perm.sign_refl, Units.val_one, one_smul]
  · intro e he hne
    erw [Linear.smul_comp,
      singularSimplexChain_comp_projection_of_mem 3 ({p}ᶜ : Set X)
        (f.comp (staircaseSimplex e)) (fun t => hp e hne t), smul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

def liftedCubeUp : C(Fin 3 → unitInterval, ULift.{u} (Fin 3 → unitInterval)) :=
  ⟨ULift.up, continuous_uliftUp⟩

def liftedCubeTetrahedralChain :
    (integralSingularChains (ULift.{u} (Fin 3 → unitInterval))).X 3 :=
  singularChainImageGen 3 liftedCubeUp cubeTetrahedralChain

theorem liftedCubeTetrahedralChain_comp_projection :
    integralChainHom 3 liftedCubeTetrahedralChain.{u} ≫
        (integralRelativeProjection ({ULift.up cubeStaircasePoint}ᶜ :
          Set (ULift.{u} (Fin 3 → unitInterval)))).f 3 =
      SimplexDegree.integralSimplexChain 3
          (liftedCubeUp.comp (staircaseSimplex (Equiv.refl (Fin 3)))) ≫
        (integralRelativeProjection ({ULift.up cubeStaircasePoint}ᶜ :
          Set (ULift.{u} (Fin 3 → unitInterval)))).f 3 :=
  cubeChain_image_comp_projection_eq_simplex liftedCubeUp (ULift.up cubeStaircasePoint)
    (fun e he q h => staircaseSimplex_ne_cubeStaircasePoint e he q (ULift.up_inj.mp h))

private theorem liftedCubeSimplex_faces (i : Fin 4) (q : stdSimplex ℝ (Fin 3)) :
    (liftedCubeUp.{u}.comp (staircaseSimplex (Equiv.refl (Fin 3))))
        (SimplexDegree.orientedSimplexFace i q) ≠ ULift.up cubeStaircasePoint :=
  fun h => staircaseSimplex_refl_face_ne_cubeStaircasePoint i q (ULift.up_inj.mp h)

theorem liftedCubeTetrahedralChain_local_boundary :
    (integralChainHom 3 liftedCubeTetrahedralChain.{u} ≫
        (integralRelativeProjection ({ULift.up cubeStaircasePoint}ᶜ :
          Set (ULift.{u} (Fin 3 → unitInterval)))).f 3) ≫
      (integralRelativeChains ({ULift.up cubeStaircasePoint}ᶜ :
        Set (ULift.{u} (Fin 3 → unitInterval)))).d 3 2 = 0 := by
  rw [liftedCubeTetrahedralChain_comp_projection]
  exact integralRelativeChain_projection_boundary 1 _
    (SimplexDegree.integralSimplexChain 3
      (liftedCubeUp.comp (staircaseSimplex (Equiv.refl (Fin 3)))))
    (SimplexDegree.puncturedSimplexBoundary (ULift.up cubeStaircasePoint) _
      liftedCubeSimplex_faces)
    (SimplexDegree.puncturedSimplexBoundary_chain (ULift.up cubeStaircasePoint) _
      liftedCubeSimplex_faces)

def liftedCubeLocalClass : integralLocalHomology 3
    (ULift.up cubeStaircasePoint : ULift.{u} (Fin 3 → unitInterval)) :=
  integralRelativeClassOf 2 _ (integralChainHom 3 liftedCubeTetrahedralChain ≫
    (integralRelativeProjection ({ULift.up cubeStaircasePoint}ᶜ :
      Set (ULift.{u} (Fin 3 → unitInterval)))).f 3)
    liftedCubeTetrahedralChain_local_boundary

theorem liftedCubeLocalClass_eq_simplexLocalClass :
    liftedCubeLocalClass.{u} = SimplexDegree.simplexLocalClass (ULift.up cubeStaircasePoint)
      (liftedCubeUp.comp (staircaseSimplex (Equiv.refl (Fin 3))))
      liftedCubeSimplex_faces := by
  unfold liftedCubeLocalClass SimplexDegree.simplexLocalClass
  apply congrArg (fun k : integralSingularCoefficients ⟶
    (integralRelativeChains ({ULift.up cubeStaircasePoint}ᶜ :
      Set (ULift.{u} (Fin 3 → unitInterval)))).homology 3 => k (ULift.up 1))
  exact chainComplex_liftCycles_homologyπ_congr 2 _ _ _ _
    liftedCubeTetrahedralChain_comp_projection

theorem integralRelativeHomologyMap_liftedCubeLocalClass {X : Type u} [TopologicalSpace X]
    (f : C(ULift.{u} (Fin 3 → unitInterval), X)) (p : X)
    (hf : MapsTo f ({ULift.up cubeStaircasePoint}ᶜ :
      Set (ULift.{u} (Fin 3 → unitInterval))) ({p}ᶜ : Set X))
    {x : X} (c : GenLoop (Fin 3) X x) (hc : f.comp liftedCubeUp = c.val) :
    integralRelativeHomologyMap 3 f hf liftedCubeLocalClass =
      integralAbsoluteToRelative 3 ({p}ᶜ : Set X) (hurewiczCubeClass c) := by
  have hchain :
      (integralChainHom 3 liftedCubeTetrahedralChain ≫
        (integralRelativeProjection ({ULift.up cubeStaircasePoint}ᶜ :
          Set (ULift.{u} (Fin 3 → unitInterval)))).f 3) ≫
          (integralRelativeChainMap f hf).f 3 =
      integralChainHom 3 (singularChainImageGen 3 c.val cubeTetrahedralChain) ≫
        (integralRelativeProjection ({p}ᶜ : Set X)).f 3 := by
    rw [Category.assoc, integralRelativeProjection_chainMap_component, ← Category.assoc,
      integralChainHom_comp_map, integralSingularChainMap_apply_eq_singularChainImageGen,
      liftedCubeTetrahedralChain,
      ← LinearMap.comp_apply (singularChainImageGen 3 f) (singularChainImageGen 3 liftedCubeUp),
      ← singularChainImageGen_comp, hc]
  unfold liftedCubeLocalClass
  rw [integralAbsoluteToRelative_hurewiczCubeClass_eq_integralRelativeClassOf_cubeTetrahedralChain]
  exact (integralRelativeHomologyMap_liftCycles_apply 2 f hf _
      liftedCubeTetrahedralChain_local_boundary
      (hchain.symm ▸ cubeTetrahedralChain_image_relative_boundary c ({p}ᶜ : Set X))).trans
    (integralRelativeClassOf_congr 2 ({p}ᶜ : Set X) hchain)

end DifferentialGeometry.Topology
