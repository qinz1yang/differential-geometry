import DifferentialGeometry.Topology.Homology.SphereHurewicz
import DifferentialGeometry.Topology.Homology.SphereGenerator
import DifferentialGeometry.Topology.Homology.HurewiczFrontier
import DifferentialGeometry.Topology.Homotopy.CubeSphereProjection
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LoopClass

noncomputable section

open CategoryTheory CategoryTheory.Limits ContinuousMap Metric

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type u} [TopologicalSpace Y]

theorem hurewiczCubeClass_congr_val {y z : X}
    {c : GenLoop (Fin 3) X y} {d : GenLoop (Fin 3) X z}
    (h : c.val = d.val) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass c =
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass d := by
  have hd : d = ⟨c.val, fun y hy => h.symm ▸ d.property y hy⟩ := Subtype.ext h.symm
  rw [hd]
  rfl

theorem hurewiczCubeClass_natural {x : X} (f : C(X, Y)) (c : GenLoop (Fin 3) X x) :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose f c) =
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralHomologyMap 3 f
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass c) := by
  let F : DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains X ⟶
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralChainsFunctor.map (TopCat.ofHom f)
  have he :
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains X).liftCycles
          (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain c) 2
          ((ComplexShape.down ℕ).next_eq' (by rfl))
          (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain_boundary c) ≫
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains X).homologyπ 3 ≫
          HomologicalComplex.homologyMap F 3 =
      (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y).liftCycles
          (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain
            (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose f c)) 2
          ((ComplexShape.down ℕ).next_eq' (by rfl))
          (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain_boundary _) ≫
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y).homologyπ 3 := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
      HomologicalComplex.liftCycles_comp_cyclesMap]
    apply congrArg (fun k :
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients ⟶
        (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y).cycles 3 =>
      k ≫ (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y).homologyπ 3)
    apply (cancel_mono
      ((DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralChains Y).iCycles 3)).1
    simp only [HomologicalComplex.liftCycles_i]
    exact DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeChain_natural f c
  exact (congrArg (fun k :
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.integralCoefficients ⟶
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.IntegralHomology Y 3 => k (ULift.up 1)) he).symm

def cubeSphereCollapse (n : ℕ) : GenLoop (Fin (n + 1)) (liftedHomotopySphere.{u} n)
    (ULift.up (cubeSphereBasepoint n)) where
  val := ⟨fun t => ULift.up (cubeSphereProjection n t),
    continuous_uliftUp.comp (cubeSphereProjection n).continuous⟩
  property := fun t ht => by
    rw [ContinuousMap.coe_mk, cubeSphereProjection_boundary n t ht]

def cubeSphereFundamentalClass : integralSingularHomology 3 (liftedHomotopySphere.{u} 2) :=
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczCubeClass (cubeSphereCollapse 2)

theorem genLoopPostcompose_val_cubeSphereCollapse (x : X) (c : GenLoop (Fin 3) X x) :
    (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.genLoopPostcompose
      ((genLoopSphereHomeomorph 2 x c).val.comp (liftedHomotopySphereDown 2))
      (cubeSphereCollapse 2)).val = c.val := by
  refine ContinuousMap.ext fun t => ?_
  exact genLoopSphereHomeomorph_projection 2 x c t

theorem sphereHurewicz_cubeSphereFundamentalClass (x : X) :
    sphereHurewicz 2 x cubeSphereFundamentalClass =
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczThree x := by
  funext a
  induction a using Quotient.inductionOn with | h c =>
    rw [sphereHurewicz_mk,
      DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczThree_mk]
    rw [← hurewiczCubeClass_congr_val (genLoopPostcompose_val_cubeSphereCollapse x c)]
    exact (hurewiczCubeClass_natural
      ((genLoopSphereHomeomorph 2 x c).val.comp (liftedHomotopySphereDown 2))
      (cubeSphereCollapse 2)).symm

theorem hurewiczThree_bijective_iff_sphereHurewicz_cubeSphereFundamentalClass (x : X) :
    Function.Bijective (DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczThree x) ↔
      Function.Bijective (sphereHurewicz 2 x cubeSphereFundamentalClass) :=
  iff_of_eq (congrArg Function.Bijective (sphereHurewicz_cubeSphereFundamentalClass x).symm)

theorem sphereHurewicz_cubeSphereFundamentalClass_mul (x : X) (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x cubeSphereFundamentalClass (a * b) =
      sphereHurewicz 2 x cubeSphereFundamentalClass a +
        sphereHurewicz 2 x cubeSphereFundamentalClass b := by
  rw [sphereHurewicz_cubeSphereFundamentalClass,
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.hurewiczThree_mul]
  rfl

theorem sphereHurewicz_zsmul_cubeSphereFundamentalClass (k : ℤ) (x : X) :
    sphereHurewicz 2 x (k • cubeSphereFundamentalClass) =
      k • sphereHurewicz 2 x cubeSphereFundamentalClass := by
  funext a
  exact sphereHurewicz_zsmul 2 k x cubeSphereFundamentalClass a

theorem sphereHurewicz_mul_of_eq_zsmul_cubeSphereFundamentalClass
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) (k : ℤ)
    (hc : c = k • cubeSphereFundamentalClass) (x : X) (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x c (a * b) =
      sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  subst hc
  rw [sphereHurewicz_zsmul 2 k x cubeSphereFundamentalClass (a * b),
    sphereHurewicz_zsmul 2 k x cubeSphereFundamentalClass a,
    sphereHurewicz_zsmul 2 k x cubeSphereFundamentalClass b,
    sphereHurewicz_cubeSphereFundamentalClass_mul x a b]
  simp only [zsmul_add]

theorem sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (x : X) (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) (a b : HomotopyGroup (Fin 3) X x) :
    sphereHurewicz 2 x c (a * b) =
      sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  rcases IsSphereHomologyGenerator.eq_or_eq_neg.{u} 2 hc hgen with h | h
  · exact sphereHurewicz_mul_of_eq_zsmul_cubeSphereFundamentalClass c 1
      (h.trans (one_smul ℤ cubeSphereFundamentalClass).symm) x a b
  · exact sphereHurewicz_mul_of_eq_zsmul_cubeSphereFundamentalClass c (-1)
      (h.trans (by simp : -cubeSphereFundamentalClass =
        (-1 : ℤ) • cubeSphereFundamentalClass)) x a b

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {X : Type u} [TopologicalSpace X]

theorem bijective_neg_comp {α : Type*} {β : Type*} [AddGroup β] {f : α → β} :
    Function.Bijective (fun a => -f a) ↔ Function.Bijective f :=
  Equiv.comp_bijective f (Equiv.neg β)

theorem hurewicz_three_isomorphism_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    (x : X) (hg : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hb : Function.Bijective (hurewiczThree x))
    (c : integralSingularHomology 3 (liftedHomotopySphere.{u} 2))
    (hc : IsSphereHomologyGenerator 2 c) :
    Function.Bijective (sphereHurewicz 2 x c) ∧
      ∀ a b : HomotopyGroup (Fin 3) X x,
        sphereHurewicz 2 x c (a * b) = sphereHurewicz 2 x c a + sphereHurewicz 2 x c b := by
  refine ⟨?_, sphereHurewicz_mul_of_cubeSphereFundamentalClass_isSphereHomologyGenerator
    hg x c hc⟩
  rcases IsSphereHomologyGenerator.eq_or_eq_neg.{u} 2 hc hg with h | h
  · rw [h, sphereHurewicz_cubeSphereFundamentalClass]
    exact hb
  · rw [h]
    have hneg : sphereHurewicz 2 x (-cubeSphereFundamentalClass) =
        fun a => -sphereHurewicz 2 x cubeSphereFundamentalClass a := by
      funext a
      simpa using sphereHurewicz_zsmul 2 (-1) x cubeSphereFundamentalClass a
    rw [hneg, sphereHurewicz_cubeSphereFundamentalClass]
    exact bijective_neg_comp.mpr hb

theorem hurewiczThree_eq_freeSphereHomologyImage (x : X) (a : HomotopyGroup (Fin 3) X x) :
    hurewiczThree x a =
      freeSphereHomologyImage 2 cubeSphereFundamentalClass (homotopyGroupToFreeSphere 2 x a) :=
  (congrFun (sphereHurewicz_cubeSphereFundamentalClass x) a).symm

theorem hurewiczCubeClass_eq_freeSphereHomologyImage (x : X) (c : GenLoop (Fin 3) X x) :
    hurewiczCubeClass c =
      freeSphereHomologyImage 2 cubeSphereFundamentalClass
        (homotopyGroupToFreeSphere 2 x (Quotient.mk _ c)) :=
  hurewiczThree_eq_freeSphereHomologyImage x (Quotient.mk _ c)

theorem hurewiczThree_bijective_of_isSphereHurewiczIsomorphism_cubeSphereFundamentalClass
    (x : X) (h : IsSphereHurewiczIsomorphism 2 X x cubeSphereFundamentalClass) :
    Function.Bijective (hurewiczThree x) :=
  (hurewiczThree_bijective_iff_sphereHurewicz_cubeSphereFundamentalClass x).mpr h.1

theorem isSphereHomologyGenerator_cubeSphereFundamentalClass_iff_coordinate :
    IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass ↔
      integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass = 1 ∨
        integralLiftedSphereTopEquiv.{u} 2 cubeSphereFundamentalClass = -1 := by
  constructor
  · intro h
    rcases (isSphereHomologyGenerator_iff_eq_or_eq_neg_integralLiftedSphereGenerator 2
      cubeSphereFundamentalClass).mp h with h' | h'
    · exact Or.inl (by rw [h', integralLiftedSphereGenerator_coordinate])
    · exact Or.inr (by rw [h', map_neg, integralLiftedSphereGenerator_coordinate])
  · rintro (h | h)
    · exact ⟨integralLiftedSphereTopEquiv 2, h⟩
    · refine ⟨(integralLiftedSphereTopEquiv 2).trans (LinearEquiv.neg ℤ), ?_⟩
      rw [LinearEquiv.trans_apply, h]
      simp

variable {M : Type u} [TopologicalSpace M] [SimplyConnectedSpace M]

theorem sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism :
    SphereHurewiczTwoCanonical M :=
  (sphereHurewicz_two_isomorphism_iff_canonical_generator (X := M)).mp
    (fun x c hc => hurewicz_two_isomorphism x c hc)

theorem sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism :
    SphereHurewiczThreeCanonical M :=
  (sphereHurewicz_three_isomorphism_iff_canonical_generator (X := M)).mp
    (fun x hπ₂ c hc => hurewicz_three_isomorphism x hπ₂ c hc)

theorem homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical
    (h : SphereHurewiczTwoCanonical M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M)) (x : M) :
    Subsingleton (HomotopyGroup (Fin 2) M x) :=
  @Function.Injective.subsingleton _ _ _ (h x).1.1 hH₂

theorem hurewiczThree_bijective_of_sphereHurewiczThreeCanonical (x : M)
    (hπ₂ : Subsingleton (HomotopyGroup (Fin 2) M x))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (h : SphereHurewiczThreeCanonical M) :
    Function.Bijective (hurewiczThree x) :=
  hurewiczThree_bijective_of_isSphereHurewiczIsomorphism_cubeSphereFundamentalClass x
    (IsSphereHurewiczIsomorphism.of_isSphereHomologyGenerator 2 x hgen (h x hπ₂))

theorem rfs_homotopy_groups_of_sphereHurewiczCanonical (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass)
    (hcanonTwo : SphereHurewiczTwoCanonical M)
    (hcanonThree : SphereHurewiczThreeCanonical M) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  ⟨homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hcanonTwo hH₂ q,
    hurewiczThree_bijective_of_sphereHurewiczThreeCanonical q
      (homotopyTwo_subsingleton_of_sphereHurewiczTwoCanonical hcanonTwo hH₂ q)
      hgen hcanonThree⟩

theorem rfs_homotopy_groups_of_subsingleton_homology_two (q : M)
    (hH₂ : Subsingleton (integralSingularHomology 2 M))
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    Subsingleton (HomotopyGroup (Fin 2) M q) ∧ Function.Bijective (hurewiczThree q) :=
  rfs_homotopy_groups_of_sphereHurewiczCanonical q hH₂ hgen
    sphereHurewiczTwoCanonical_of_hurewicz_two_isomorphism
    sphereHurewiczThreeCanonical_of_hurewicz_three_isomorphism

end DifferentialGeometry.Topology
