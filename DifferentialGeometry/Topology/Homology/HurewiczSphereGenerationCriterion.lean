import DifferentialGeometry.Topology.Homology.ChainSupportCompact
import DifferentialGeometry.Topology.Homology.HurewiczLowDegreeFrontierInstances
import DifferentialGeometry.Topology.Homology.HurewiczSphereCriterion
import DifferentialGeometry.Topology.Homology.HurewiczThreeWitness
import DifferentialGeometry.Topology.Homology.OpenExcision
import DifferentialGeometry.Topology.Homology.RelativeMaps

noncomputable section

open ContinuousMap Metric Set

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]

theorem hurewiczThreeSphereGeneration_iff_closure_range_eq_top_of_additive
    [SimplyConnectedSpace X] (x : X)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) b) :
    HurewiczThreeSphereGeneration X ↔
      AddSubgroup.closure (Set.range (fun f : C(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) =>
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f))) = ⊤ :=
  (surjective_sphereHurewicz_iff_forall_exists_map_eq 2 x
      (integralLiftedSphereGenerator.{u} 2)).symm.trans
    (surjective_sphereHurewicz_iff_closure_range_eq_top_of_additive 2 x
      (integralLiftedSphereGenerator.{u} 2) hmul)

theorem hurewiczThreeSphereGeneration_of_closure_range_eq_top_of_additive
    [SimplyConnectedSpace X] (x : X)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x,
      sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz 2 x (integralLiftedSphereGenerator.{u} 2) b)
    (hspan : AddSubgroup.closure (Set.range
      (fun f : C(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) =>
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f))) = ⊤) :
    HurewiczThreeSphereGeneration X :=
  (hurewiczThreeSphereGeneration_iff_closure_range_eq_top_of_additive x hmul).mpr hspan

theorem hurewiczThreeSphereGeneration_iff_closure_range_eq_top_of_cubeSphereFundamentalClass
    [SimplyConnectedSpace X]
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) (x : X) :
    HurewiczThreeSphereGeneration X ↔
      AddSubgroup.closure (Set.range (fun f : C(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X) =>
        freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
          (ZerothHomotopy.mk f))) = ⊤ :=
  hurewiczThreeSphereGeneration_iff_closure_range_eq_top_of_additive x
    (sphereHurewicz_integralLiftedSphereGenerator_mul_of_cubeSphereFundamentalClass hgen x)

theorem sphereHomologyGeneration_of_forall_isCompact_subspace (n : ℕ)
    (h : ∀ K : Set X, IsCompact K →
      ∀ y : integralSingularHomology (n + 1) ↥K,
        ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, ↥K),
          freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk f) = y) :
    ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y := by
  intro y
  obtain ⟨K, hK, β, hβ⟩ := exists_isCompact_integralSingularHomologyMap_eq n y
  obtain ⟨f, hf⟩ := h K hK β
  refine ⟨(singularSubspaceInclusion K).comp f, ?_⟩
  rw [← freeSpherePostcompose_mk n (singularSubspaceInclusion K) f,
    freeSphereHomologyImage_natural n (integralLiftedSphereGenerator.{u} n)
      (singularSubspaceInclusion K) (ZerothHomotopy.mk f), hf, hβ]

theorem hurewiczThreeSphereGeneration_of_forall_isCompact_subspace
    (h : ∀ K : Set X, IsCompact K → HurewiczThreeSphereGeneration ↥K) :
    HurewiczThreeSphereGeneration X :=
  sphereHomologyGeneration_of_forall_isCompact_subspace 2 h

theorem hurewiczTwoSphereGeneration_of_forall_isCompact_subspace
    (h : ∀ K : Set X, IsCompact K → HurewiczTwoSphereGeneration ↥K) :
    HurewiczTwoSphereGeneration X :=
  sphereHomologyGeneration_of_forall_isCompact_subspace 1 h

theorem sphereHomologyGeneration_of_surjective_homologyMap (n : ℕ) {Y : Type u}
    [TopologicalSpace Y] (f : C(Y, X))
    (hf : Function.Surjective (integralSingularHomologyMap (n + 1) f))
    (h : ∀ y : integralSingularHomology (n + 1) Y,
      ∃ g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, Y),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk g) = y) :
    ∀ y : integralSingularHomology (n + 1) X,
      ∃ h' : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk h') = y := by
  intro y
  obtain ⟨z, hz⟩ := hf y
  obtain ⟨g, hg⟩ := h z
  exact ⟨f.comp g, by
    rw [← freeSpherePostcompose_mk n f g,
      freeSphereHomologyImage_natural n (integralLiftedSphereGenerator.{u} n) f
        (ZerothHomotopy.mk g), hg, hz]⟩

theorem hurewiczThreeSphereGeneration_of_surjective_homologyMap {Y : Type u}
    [TopologicalSpace Y] (f : C(Y, X))
    (hf : Function.Surjective (integralSingularHomologyMap 3 f))
    (hY : HurewiczThreeSphereGeneration Y) : HurewiczThreeSphereGeneration X :=
  sphereHomologyGeneration_of_surjective_homologyMap 2 f hf hY

theorem sphereHomologyGeneration_of_open_cover_of_subsingleton (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology (n + 1) ↥A))
    (hI : Subsingleton (integralSingularHomology n ↥(subspaceIntersection A B)))
    (hgen : ∀ y : integralSingularHomology (n + 1) ↥B,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, ↥B),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y) :
    ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y := by
  have hsurj : Function.Surjective
      (integralSingularHomologyMap (n + 1) (singularSubspaceInclusion B)) := by
    intro y
    have hinj : Function.Injective (integralAbsoluteToRelative (n + 1) A) :=
      integralAbsoluteToRelative_injective_of_subsingleton (n + 1) A hA'
    let e := integralRelativeOpenExcisionIso (n + 1) A B hA hB hcover
    have hrel : integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion B)
        (subspaceIntersection_mapsTo A B) = e.toLinearEquiv := by
      rw [← integralRelativeOpenExcisionIso_hom (n + 1) A B hA hB hcover]
      exact CategoryTheory.Iso.toLinearMap_toLinearEquiv e
    have hz : e.toLinearEquiv.symm (integralAbsoluteToRelative (n + 1) A y) ∈
        LinearMap.range (integralAbsoluteToRelative (n + 1) (subspaceIntersection A B)) := by
      rw [← LinearMap.exact_iff.mp
        (integralRelative_exact_relative n (subspaceIntersection A B))]
      exact LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
    refine ⟨w, hinj ?_⟩
    have hnat : integralAbsoluteToRelative (n + 1) A
        (integralSingularHomologyMap (n + 1) (singularSubspaceInclusion B) w) =
        integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion B)
          (subspaceIntersection_mapsTo A B)
          (integralAbsoluteToRelative (n + 1) (subspaceIntersection A B) w) :=
      LinearMap.congr_fun (integralAbsoluteToRelative_natural (n + 1)
        (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) w
    rw [hnat, hw, hrel]
    exact LinearEquiv.apply_symm_apply e.toLinearEquiv _
  exact sphereHomologyGeneration_of_surjective_homologyMap n (singularSubspaceInclusion B)
    hsurj hgen

theorem hurewiczThreeSphereGeneration_of_open_cover_of_subsingleton (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology 3 ↥A))
    (hI : Subsingleton (integralSingularHomology 2 ↥(subspaceIntersection A B)))
    (hgen : HurewiczThreeSphereGeneration ↥B) :
    HurewiczThreeSphereGeneration X :=
  sphereHomologyGeneration_of_open_cover_of_subsingleton 2 A B hA hB hcover hA' hI hgen

theorem hurewiczTwoSphereGeneration_of_open_cover_of_subsingleton (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology 2 ↥A))
    (hI : Subsingleton (integralSingularHomology 1 ↥(subspaceIntersection A B)))
    (hgen : HurewiczTwoSphereGeneration ↥B) :
    HurewiczTwoSphereGeneration X :=
  sphereHomologyGeneration_of_open_cover_of_subsingleton 1 A B hA hB hcover hA' hI hgen

theorem exists_freeSphereHomologyImage_eq_add_of_additive [PathConnectedSpace X] (n : ℕ)
    (x : X)
    (hmul : ∀ a b : HomotopyGroup (Fin (n + 1)) X x,
      sphereHurewicz n x (integralLiftedSphereGenerator.{u} n) (a * b) =
        sphereHurewicz n x (integralLiftedSphereGenerator.{u} n) a +
          sphereHurewicz n x (integralLiftedSphereGenerator.{u} n) b)
    (f g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X)) :
    ∃ h : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk h) =
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk f) +
          freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
            (ZerothHomotopy.mk g) := by
  obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk f)
  obtain ⟨b, hb⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk g)
  obtain ⟨h, hh⟩ : ∃ h : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
      ZerothHomotopy.mk h = homotopyGroupToFreeSphere n x (a * b) :=
    ⟨Quotient.out _, Quotient.out_eq _⟩
  exact ⟨h, by rw [hh, ← ha, ← hb]; exact hmul a b⟩

def integralOpenCoverLinkingMap (n : ℕ) (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcover : A ∪ B = univ) :
    integralSingularHomology (n + 1) X →ₗ[ℤ]
      integralSingularHomology n ↥(subspaceIntersection A B) :=
  let e := integralRelativeOpenExcisionIso (n + 1) A B hA hB hcover
  (integralRelativeConnecting n (subspaceIntersection A B)).comp
    (e.toLinearEquiv.symm.toLinearMap.comp (integralAbsoluteToRelative (n + 1) A))

theorem exists_subspace_class_of_integralOpenCoverLinkingMap_eq_zero (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology (n + 1) ↥A))
    (y : integralSingularHomology (n + 1) X)
    (hy : integralOpenCoverLinkingMap n A B hA hB hcover y = 0) :
    ∃ w : integralSingularHomology (n + 1) ↥B,
      integralSingularHomologyMap (n + 1) (singularSubspaceInclusion B) w = y := by
  have hinj : Function.Injective (integralAbsoluteToRelative (n + 1) A) :=
    integralAbsoluteToRelative_injective_of_subsingleton (n + 1) A hA'
  let e := integralRelativeOpenExcisionIso (n + 1) A B hA hB hcover
  have hrel : integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion B)
      (subspaceIntersection_mapsTo A B) = e.toLinearEquiv := by
    rw [← integralRelativeOpenExcisionIso_hom (n + 1) A B hA hB hcover]
    exact CategoryTheory.Iso.toLinearMap_toLinearEquiv e
  have hz : e.toLinearEquiv.symm (integralAbsoluteToRelative (n + 1) A y) ∈
      LinearMap.range (integralAbsoluteToRelative (n + 1) (subspaceIntersection A B)) := by
    rw [← LinearMap.exact_iff.mp
      (integralRelative_exact_relative n (subspaceIntersection A B))]
    exact LinearMap.mem_ker.mpr (by
      simpa only [integralOpenCoverLinkingMap, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap] using hy)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hz
  refine ⟨w, hinj ?_⟩
  have hnat : integralAbsoluteToRelative (n + 1) A
      (integralSingularHomologyMap (n + 1) (singularSubspaceInclusion B) w) =
      integralRelativeHomologyMap (n + 1) (singularSubspaceInclusion B)
        (subspaceIntersection_mapsTo A B)
        (integralAbsoluteToRelative (n + 1) (subspaceIntersection A B) w) :=
    LinearMap.congr_fun (integralAbsoluteToRelative_natural (n + 1)
      (singularSubspaceInclusion B) (subspaceIntersection_mapsTo A B)) w
  rw [hnat, hw, hrel]
  exact LinearEquiv.apply_symm_apply e.toLinearEquiv _

theorem hurewiczThreeSphereGeneration_of_open_cover_of_linkingRealization
    [PathConnectedSpace X] (x₀ : X) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology 3 ↥A))
    (hgen : HurewiczThreeSphereGeneration ↥B)
    (hmul : ∀ a b : HomotopyGroup (Fin 3) X x₀,
      sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) (a * b) =
        sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) a +
          sphereHurewicz 2 x₀ (integralLiftedSphereGenerator.{u} 2) b)
    (hlink : ∀ y : integralSingularHomology 3 X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, X),
        integralOpenCoverLinkingMap 2 A B hA hB hcover
            (freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
              (ZerothHomotopy.mk f)) =
          integralOpenCoverLinkingMap 2 A B hA hB hcover y) :
    HurewiczThreeSphereGeneration X := by
  intro y
  obtain ⟨f, hf⟩ := hlink y
  obtain ⟨w, hw⟩ := exists_subspace_class_of_integralOpenCoverLinkingMap_eq_zero 2 A B
    hA hB hcover hA' (y - freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
      (ZerothHomotopy.mk f)) (by
        rw [map_sub, hf, sub_self])
  obtain ⟨g, hg⟩ := hgen w
  have hgc : freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
      (ZerothHomotopy.mk ((singularSubspaceInclusion B).comp g)) =
      y - freeSphereHomologyImage 2 (integralLiftedSphereGenerator.{u} 2)
        (ZerothHomotopy.mk f) := by
    rw [← freeSpherePostcompose_mk 2 (singularSubspaceInclusion B) g,
      freeSphereHomologyImage_natural 2 (integralLiftedSphereGenerator.{u} 2)
        (singularSubspaceInclusion B) (ZerothHomotopy.mk g), hg, hw]
  obtain ⟨h, hh⟩ := exists_freeSphereHomologyImage_eq_add_of_additive 2 x₀ hmul f
    ((singularSubspaceInclusion B).comp g)
  exact ⟨h, by rw [hh, hgc]; abel⟩

theorem integralOpenCoverLinkingMap_injective_of_subsingleton (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hA' : Subsingleton (integralSingularHomology (n + 1) ↥A))
    (hB' : Subsingleton (integralSingularHomology (n + 1) ↥B)) :
    Function.Injective (integralOpenCoverLinkingMap n A B hA hB hcover) := by
  intro y z hyz
  have hzy : integralOpenCoverLinkingMap n A B hA hB hcover (y - z) = 0 := by
    rw [map_sub, hyz, sub_self]
  obtain ⟨w, hw⟩ := exists_subspace_class_of_integralOpenCoverLinkingMap_eq_zero n A B
    hA hB hcover hA' (y - z) hzy
  rw [Subsingleton.elim w 0, map_zero] at hw
  exact sub_eq_zero.mp hw.symm

theorem exists_integralOpenCoverLinkingMap_eq_of_sphereGeneration (n : ℕ) (A B : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ)
    (hgen : ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y) :
    ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        integralOpenCoverLinkingMap n A B hA hB hcover
            (freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
              (ZerothHomotopy.mk f)) =
          integralOpenCoverLinkingMap n A B hA hB hcover y := by
  intro y
  obtain ⟨f, hf⟩ := hgen y
  exact ⟨f, by rw [hf]⟩

theorem subsingleton_homology_of_sphereGeneration_of_subsingleton_homotopyGroup
    [PathConnectedSpace X] (n : ℕ) (x : X)
    (hpi : Subsingleton (HomotopyGroup (Fin (n + 1)) X x))
    (hgen : ∀ y : integralSingularHomology (n + 1) X,
      ∃ f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1, X),
        freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
          (ZerothHomotopy.mk f) = y) :
    Subsingleton (integralSingularHomology (n + 1) X) := by
  have hzero : ∀ y : integralSingularHomology (n + 1) X, y = 0 := by
    intro y
    obtain ⟨f, hf⟩ := hgen y
    obtain ⟨a, ha⟩ := homotopyGroupToFreeSphere_surjective n x (ZerothHomotopy.mk f)
    have hy : sphereHurewicz n x (integralLiftedSphereGenerator.{u} n) a = y := by
      change freeSphereHomologyImage n (integralLiftedSphereGenerator.{u} n)
        (homotopyGroupToFreeSphere n x a) = y
      rw [ha, hf]
    rw [← hy, Subsingleton.elim a 1, sphereHurewicz_one]
  exact ⟨fun y₁ y₂ => by rw [hzero y₁, hzero y₂]⟩

theorem subsingleton_homology_three_of_hurewiczThreeSphereGeneration_of_subsingleton_homotopyGroup
    [PathConnectedSpace X] (x : X) (hpi : Subsingleton (HomotopyGroup (Fin 3) X x))
    (hgen : HurewiczThreeSphereGeneration X) :
    Subsingleton (integralSingularHomology 3 X) :=
  subsingleton_homology_of_sphereGeneration_of_subsingleton_homotopyGroup 2 x hpi hgen

theorem not_hurewiczThreeSphereGeneration_of_subsingleton_homotopyGroup_of_not_subsingleton_homology
    [PathConnectedSpace X] (x : X) (hpi : Subsingleton (HomotopyGroup (Fin 3) X x))
    (h : ¬ Subsingleton (integralSingularHomology 3 X)) :
    ¬ HurewiczThreeSphereGeneration X :=
  fun hgen =>
    h (subsingleton_homology_three_of_hurewiczThreeSphereGeneration_of_subsingleton_homotopyGroup
      x hpi hgen)

theorem hurewiczThreeSphereNullhomotopic_and_not_hurewiczThreeSphereGeneration
    [PathConnectedSpace X] (x : X) (hpi : Subsingleton (HomotopyGroup (Fin 3) X x))
    (h : ¬ Subsingleton (integralSingularHomology 3 X)) :
    HurewiczThreeSphereNullhomotopic X ∧ ¬ HurewiczThreeSphereGeneration X :=
  ⟨hurewiczThreeSphereNullhomotopic_of_subsingleton_homotopyGroup x,
    not_hurewiczThreeSphereGeneration_of_subsingleton_homotopyGroup_of_not_subsingleton_homology
      x hpi h⟩

theorem not_subsingleton_integralSingularHomology_three_liftedHomotopySphere :
    ¬ Subsingleton (integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) :=
  fun h => integralLiftedSphereGenerator_ne_zero 2 (h.elim _ _)

theorem hurewiczThreeSphereGeneration_liftedHomotopySphere_nontrivial
    (hgen : IsSphereHomologyGenerator.{u} 2 cubeSphereFundamentalClass) :
    HurewiczThreeSphereGeneration (liftedHomotopySphere.{u} 2) ∧
      ¬ Subsingleton (integralSingularHomology 3 (liftedHomotopySphere.{u} 2)) :=
  ⟨hurewiczThreeSphereGeneration_liftedHomotopySphere_of_cubeSphereFundamentalClass hgen,
    not_subsingleton_integralSingularHomology_three_liftedHomotopySphere⟩

end DifferentialGeometry.Topology
