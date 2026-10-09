/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.CarrierRestriction
import DifferentialGeometry.Topology.Homology.HurewiczOne
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.ModuleHomologyMaps
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.RelativeMaps
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SimplexMaps
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SmallCycles
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.TwoSetSmallChains
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary

open Set CategoryTheory

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

noncomputable def integralOneCycleClass (c : integralSingularCycles 0 X) :
    integralSingularHomology 1 X :=
  (integralSingularHomologyCycleEquiv 0 X).symm (Submodule.Quotient.mk c)

theorem integralOneCycleClass_surjective :
    Function.Surjective (integralOneCycleClass (X := X)) := by
  intro a
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (integralSingularHomologyCycleEquiv 0 X a)
  exact ⟨c, by rw [integralOneCycleClass, hc, AddEquiv.symm_apply_apply]⟩

theorem integralOneCycleClass_eq_iff (c d : integralSingularCycles 0 X) :
    integralOneCycleClass c = integralOneCycleClass d ↔
      ∃ b : (integralSingularChains X).X 2, (integralSingularChains X).d 2 1 b = c.val - d.val := by
  rw [integralOneCycleClass, integralOneCycleClass,
    (integralSingularHomologyCycleEquiv 0 X).symm.injective.eq_iff, Submodule.Quotient.eq]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, Subtype.ext hb⟩

theorem mem_ker_sc_one_of_mem_integralSingularCycles (c : integralSingularCycles 0 X) :
    c.val ∈ LinearMap.ker ((integralSingularChains X).sc 1).g.hom := by
  change (integralSingularChains X).d 1 ((ComplexShape.down ℕ).next 1) c.val = 0
  rw [ChainComplex.next_nat_succ 0]
  exact c.property

theorem integralOneCycleClass_eq_moduleHomologyClass (c : integralSingularCycles 0 X) :
    integralOneCycleClass c = moduleHomologyClass ((integralSingularChains X).sc 1)
      ⟨c.val, mem_ker_sc_one_of_mem_integralSingularCycles c⟩ := by
  apply (integralSingularHomologyCycleEquiv 0 X).injective
  rw [integralOneCycleClass, AddEquiv.apply_symm_apply]
  change _ = ((integralSingularChains X).sc' (0 + 2) (0 + 1) 0).moduleCatHomologyIso.hom
    (ShortComplex.homologyMap ((integralSingularChains X).isoSc' (0 + 2) (0 + 1) 0
      (by simp) (by simp)).hom (moduleHomologyClass _ _))
  rw [moduleHomologyClass_map, moduleHomologyClass_quotient]
  rfl

theorem integralSingularChainMap_mem_integralSingularCycles (f : C(X, Y))
    (c : integralSingularCycles 0 X) :
    (integralSingularChainMap f).f 1 c.val ∈ integralSingularCycles 0 Y := by
  rw [LinearMap.mem_ker]
  change (integralSingularChains Y).d (0 + 1) 0 ((integralSingularChainMap f).f (0 + 1) c.val) = 0
  rw [← integralSingularChainMap_boundary 0 f c.val,
    show (integralSingularChains X).d (0 + 1) 0 c.val = 0 from c.property, map_zero]

theorem integralOneCycleClass_map (f : C(X, Y)) (c : integralSingularCycles 0 X)
    (d : integralSingularCycles 0 Y) (h : (integralSingularChainMap f).f 1 c.val = d.val) :
    integralSingularHomologyMap 1 f (integralOneCycleClass c) = integralOneCycleClass d := by
  rw [integralOneCycleClass_eq_moduleHomologyClass, integralOneCycleClass_eq_moduleHomologyClass]
  refine (moduleHomologyClass_map
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) 1).map
      (integralSingularChainMap f)) _).trans ?_
  congr 1
  exact Subtype.ext h

theorem integralPathChain_map (f : C(X, Y)) {x y : X} (p : Path x y) :
    (integralSingularChainMap f).f 1 (integralPathChain p) =
      integralPathChain (p.map f.continuous) := by
  unfold integralPathChain
  rw [integralSimplexChain_map]
  congr 1

theorem integralLoopHomologyClass_map (f : C(X, Y)) {x : X} (p : Path x x) :
    integralSingularHomologyMap 1 f (integralLoopHomologyClass p) =
      integralLoopHomologyClass (p.map f.continuous) :=
  integralOneCycleClass_map f (integralLoopCycle p) (integralLoopCycle (p.map f.continuous))
    (integralPathChain_map f p)

theorem hurewiczOne_map (f : C(X, Y)) (x : X) (γ : FundamentalGroup X x) :
    (hurewiczOne (f x) (FundamentalGroup.map f x γ)).toAdd =
      integralSingularHomologyMap 1 f (hurewiczOne x γ).toAdd := by
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p =>
    change integralLoopHomologyClass (p.map f.continuous) =
      integralSingularHomologyMap 1 f (integralLoopHomologyClass p)
    exact (integralLoopHomologyClass_map f p).symm

end DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Carrying

variable {Y : Type u} [TopologicalSpace Y]

theorem CarriesFundamentalGroupOnto.carriesFirstHomologyOnto {J T : Set Y}
    (h : CarriesFundamentalGroupOnto J T) (hJ : J.Nonempty) (hT : IsPathConnected T) :
    CarriesFirstHomologyOnto J T := by
  refine ⟨h.1, fun hJT a => ?_⟩
  obtain ⟨j, hj⟩ := hJ
  have : PathConnectedSpace T := isPathConnected_iff_pathConnectedSpace.mp hT
  obtain ⟨γ, hγ⟩ := hurewiczOne_surjective
    ((⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T)) ⟨j, hj⟩) (Multiplicative.ofAdd a)
  obtain ⟨β, rfl⟩ := h.2 hJT ⟨j, hj⟩ γ
  refine ⟨(hurewiczOne (⟨j, hj⟩ : J) β).toAdd, ?_⟩
  rw [← hurewiczOne_map, hγ]
  rfl

theorem CarriesFirstHomologyOnto.mono {J J' T : Set Y} (h : CarriesFirstHomologyOnto J T)
    (hJJ' : J ⊆ J') (hJ'T : J' ⊆ T) : CarriesFirstHomologyOnto J' T := by
  refine ⟨hJ'T, fun hsub t => ?_⟩
  obtain ⟨s, hs⟩ := h.2 h.1 t
  refine ⟨integralSingularHomologyMap 1 ⟨inclusion hJJ', continuous_inclusion hJJ'⟩ s, ?_⟩
  rw [← LinearMap.comp_apply, ← integralSingularHomologyMap_comp]
  exact hs

theorem CarriesFirstHomologyOnto.of_homotopic {S S' T : Set Y}
    (h : CarriesFirstHomologyOnto S T) (hS'T : S' ⊆ T) (g : C(S, S'))
    (hg : ContinuousMap.Homotopic (⟨inclusion h.1, continuous_inclusion h.1⟩ : C(S, T))
      ((⟨inclusion hS'T, continuous_inclusion hS'T⟩ : C(S', T)).comp g)) :
    CarriesFirstHomologyOnto S' T := by
  refine ⟨hS'T, fun hsub t => ?_⟩
  obtain ⟨s, hs⟩ := h.2 h.1 t
  refine ⟨integralSingularHomologyMap 1 g s, ?_⟩
  have hmap := congrArg (fun F => F s) (integralSingularHomologyMap_homotopic 1 hg)
  rw [integralSingularHomologyMap_comp] at hmap
  exact hmap.symm.trans hs

theorem integralSingularChainMap_inclusion_apply {J T : Set Y} (hJT : J ⊆ T) (n : ℕ)
    (c : (integralSingularChains J).X n) :
    (integralSingularChainMap (singularSubspaceInclusion T)).f n
      ((integralSingularChainMap ⟨inclusion hJT, continuous_inclusion hJT⟩).f n c) =
    (integralSingularChainMap (singularSubspaceInclusion J)).f n c :=
  (congrArg (fun φ : integralSingularChains J ⟶ integralSingularChains Y => φ.f n c)
    (integralSingularChainMap_comp (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, T))
      (singularSubspaceInclusion T))).symm

theorem integralSingularChains_d_eq_zero_of_inclusion {Z : Set Y}
    {c : (integralSingularChains Z).X 1}
    (h : (integralSingularChains Y).d 1 0
      ((integralSingularChainMap (singularSubspaceInclusion Z)).f 1 c) = 0) :
    (integralSingularChains Z).d 1 0 c = 0 := by
  apply integralSingularChainInclusion_injective 0 Z
  exact (integralSingularChainMap_boundary 0 (singularSubspaceInclusion Z) c).trans
    (h.trans (map_zero _).symm)

theorem integralSingularChains_d_inclusion_eq_zero {Z : Set Y}
    {c : (integralSingularChains Z).X 1} (h : (integralSingularChains Z).d 1 0 c = 0) :
    (integralSingularChains Y).d 1 0
      ((integralSingularChainMap (singularSubspaceInclusion Z)).f 1 c) = 0 :=
  (integralSingularChainMap_boundary 0 (singularSubspaceInclusion Z) c).symm.trans
    ((congrArg (fun x => (integralSingularChainMap (singularSubspaceInclusion Z)).f 0 x) h).trans
      (map_zero _))

theorem CarriesFirstHomologyOnto.exists_cycle {J T : Set Y} (h : CarriesFirstHomologyOnto J T)
    {z : (integralSingularChains Y).X 1} (hz : z ∈ integralSingularChainsIn 1 T)
    (hzc : (integralSingularChains Y).d 1 0 z = 0) :
    ∃ w ∈ integralSingularChainsIn 1 J, (integralSingularChains Y).d 1 0 w = 0 ∧
      ∃ b ∈ integralSingularChainsIn 2 T, (integralSingularChains Y).d 2 1 b = z - w := by
  rw [integralSingularChainsIn_eq_range] at hz
  obtain ⟨z', rfl⟩ := hz
  have hz' : z' ∈ integralSingularCycles 0 T :=
    LinearMap.mem_ker.mpr (integralSingularChains_d_eq_zero_of_inclusion hzc)
  obtain ⟨s, hs⟩ := h.2 h.1 (integralOneCycleClass ⟨z', hz'⟩)
  obtain ⟨w', rfl⟩ := integralOneCycleClass_surjective s
  rw [integralOneCycleClass_map _ w' ⟨_, integralSingularChainMap_mem_integralSingularCycles
    ⟨inclusion h.1, continuous_inclusion h.1⟩ w'⟩ rfl, integralOneCycleClass_eq_iff] at hs
  obtain ⟨b', hb'⟩ := hs
  refine ⟨(integralSingularChainMap (singularSubspaceInclusion J)).f 1 w'.val, ?_,
    integralSingularChains_d_inclusion_eq_zero w'.property,
    -(integralSingularChainMap (singularSubspaceInclusion T)).f 2 b', ?_, ?_⟩
  · rw [integralSingularChainsIn_eq_range]
    exact ⟨w'.val, rfl⟩
  · rw [integralSingularChainsIn_eq_range]
    exact ⟨-b', map_neg _ b'⟩
  · have hd : (integralSingularChainMap (singularSubspaceInclusion T)).f 1
        ((integralSingularChains T).d 2 1 b') = (integralSingularChains Y).d 2 1
          ((integralSingularChainMap (singularSubspaceInclusion T)).f 2 b') :=
      integralSingularChainMap_boundary 1 _ b'
    have hmap := congrArg (fun x => (integralSingularChainMap (singularSubspaceInclusion T)).f 1 x)
      hb'
    simp only at hmap
    rw [map_sub, integralSingularChainMap_inclusion_apply, hd] at hmap
    rw [map_neg, hmap]
    abel

theorem carriesFirstHomologyOnto_of_forall_cycle {J T : Set Y} (hJT : J ⊆ T)
    (h : ∀ z ∈ integralSingularChainsIn 1 T, (integralSingularChains Y).d 1 0 z = 0 →
      ∃ w ∈ integralSingularChainsIn 1 J, (integralSingularChains Y).d 1 0 w = 0 ∧
        ∃ b ∈ integralSingularChainsIn 2 T, (integralSingularChains Y).d 2 1 b = z - w) :
    CarriesFirstHomologyOnto J T := by
  refine ⟨hJT, fun hsub t => ?_⟩
  obtain ⟨z', rfl⟩ := integralOneCycleClass_surjective t
  have hzT : (integralSingularChainMap (singularSubspaceInclusion T)).f 1 z'.val ∈
      integralSingularChainsIn 1 T := by
    rw [integralSingularChainsIn_eq_range]
    exact ⟨z'.val, rfl⟩
  obtain ⟨w, hw, hwc, b, hb, hbd⟩ := h _ hzT (integralSingularChains_d_inclusion_eq_zero
    z'.property)
  rw [integralSingularChainsIn_eq_range] at hw hb
  obtain ⟨w', rfl⟩ := hw
  obtain ⟨b', rfl⟩ := hb
  have hw' : w' ∈ integralSingularCycles 0 J :=
    LinearMap.mem_ker.mpr (integralSingularChains_d_eq_zero_of_inclusion hwc)
  refine ⟨integralOneCycleClass ⟨w', hw'⟩, ?_⟩
  rw [integralOneCycleClass_map _ ⟨w', hw'⟩ ⟨_, integralSingularChainMap_mem_integralSingularCycles
    ⟨inclusion hsub, continuous_inclusion hsub⟩ ⟨w', hw'⟩⟩ rfl, integralOneCycleClass_eq_iff]
  refine ⟨-b', integralSingularChainInclusion_injective 1 T ?_⟩
  have hd : (integralSingularChainMap (singularSubspaceInclusion T)).f 1
      ((integralSingularChains T).d 2 1 b') = (integralSingularChains Y).d 2 1
        ((integralSingularChainMap (singularSubspaceInclusion T)).f 2 b') :=
    integralSingularChainMap_boundary 1 _ b'
  rw [map_neg, map_neg, hd, hbd, map_sub, integralSingularChainMap_inclusion_apply]
  abel

theorem exists_boundary_of_subsingleton_integralSingularHomology {Z : Set Y}
    (hZ : Subsingleton (integralSingularHomology 1 Z)) {z : (integralSingularChains Y).X 1}
    (hz : z ∈ integralSingularChainsIn 1 Z) (hzc : (integralSingularChains Y).d 1 0 z = 0) :
    ∃ b ∈ integralSingularChainsIn 2 Z, (integralSingularChains Y).d 2 1 b = z := by
  rw [integralSingularChainsIn_eq_range] at hz
  obtain ⟨z', rfl⟩ := hz
  obtain ⟨b', hb'⟩ := (integralSingularHomology_vanishing_iff 0 Z).mp hZ z'
    (integralSingularChains_d_eq_zero_of_inclusion hzc)
  refine ⟨(integralSingularChainMap (singularSubspaceInclusion Z)).f 2 b', ?_, ?_⟩
  · rw [integralSingularChainsIn_eq_range]
    exact ⟨b', rfl⟩
  · exact (integralSingularChainMap_boundary 1 (singularSubspaceInclusion Z) b').symm.trans
      (congrArg (fun x => (integralSingularChainMap (singularSubspaceInclusion Z)).f 1 x) hb')

end Carrying

section MayerVietoris

variable {X : Type u} [TopologicalSpace X]

theorem exists_boundary_sub_mem_integralSingularChainsIn_inter {A B : Set X} (hA : IsOpen A)
    (hB : IsOpen B) (hcover : A ∪ B = univ) {z : (integralSingularChains X).X 1}
    (hz : z ∈ integralSingularChainsIn 1 A) (hzc : (integralSingularChains X).d 1 0 z = 0)
    {b : (integralSingularChains X).X 2} (hb : (integralSingularChains X).d 2 1 b = z) :
    ∃ w ∈ integralSingularChainsIn 1 (A ∩ B), (integralSingularChains X).d 1 0 w = 0 ∧
      ∃ a ∈ integralSingularChainsIn 2 A, (integralSingularChains X).d 2 1 a = z - w := by
  have hU : ∀ i, IsOpen (twoSetCover A B i) := by
    intro i
    cases i
    · simpa [twoSetCover] using hA
    · simpa [twoSetCover] using hB
  have hcov : ∀ x, ∃ i, x ∈ twoSetCover A B i := by
    intro x
    have hx : x ∈ A ∪ B := hcover ▸ mem_univ x
    rcases hx with hx | hx
    · exact ⟨false, by simpa [twoSetCover] using hx⟩
    · exact ⟨true, by simpa [twoSetCover] using hx⟩
  have hsmall : z ∈ integralSingularSmallChains 1 (twoSetCover A B) := by
    rw [integralSingularTwoSetSmallChains_eq]
    exact Submodule.mem_sup_left hz
  obtain ⟨c, hc, hcz⟩ :=
    exists_small_boundary_of_boundary 0 (twoSetCover A B) hU hcov z hsmall hzc b hb
  rw [integralSingularTwoSetSmallChains_eq, Submodule.mem_sup] at hc
  obtain ⟨c₁, hc₁, c₂, hc₂, rfl⟩ := hc
  have hsplit : (integralSingularChains X).d 2 1 c₂ = z - (integralSingularChains X).d 2 1 c₁ := by
    rw [← hcz, map_add]
    abel
  refine ⟨(integralSingularChains X).d 2 1 c₂, ?_, ?_, c₁, hc₁, ?_⟩
  · rw [integralSingularChainsIn_inter]
    refine ⟨?_, integralSingularChainsIn_boundary 1 B hc₂⟩
    rw [hsplit]
    exact Submodule.sub_mem _ hz (integralSingularChainsIn_boundary 1 A hc₁)
  · exact congrArg (fun f : (integralSingularChains X).X 2 ⟶ (integralSingularChains X).X 0 =>
      f c₂) ((integralSingularChains X).d_comp_d 2 1 0)
  · rw [hsplit]
    abel

end MayerVietoris

section Transfer

variable {Y : Type u} [TopologicalSpace Y]

theorem CarriesFirstHomologyOnto.of_mayerVietoris {P Z A B T : Set Y}
    (hP : CarriesFirstHomologyOnto P T) (hA : IsOpen A) (hB : IsOpen B) (hZAB : Z ⊆ A ∪ B)
    (hZ : Subsingleton (integralSingularHomology 1 Z)) (hPZA : P ⊆ Z ∩ A)
    (hZAT : Z ∩ A ⊆ T) : CarriesFirstHomologyOnto (Z ∩ A ∩ B) T := by
  refine carriesFirstHomologyOnto_of_forall_cycle (inter_subset_left.trans hZAT)
    fun t ht htc => ?_
  obtain ⟨w₀, hw₀, hw₀c, b₀, hb₀, hb₀d⟩ := hP.exists_cycle ht htc
  have hw₀Z : w₀ ∈ integralSingularChainsIn 1 Z :=
    integralSingularChainsIn_mono 1 (hPZA.trans inter_subset_left) hw₀
  obtain ⟨b₁, hb₁, hb₁d⟩ := exists_boundary_of_subsingleton_integralSingularHomology hZ hw₀Z hw₀c
  rw [integralSingularChainsIn_eq_range] at hb₁
  obtain ⟨b₁', rfl⟩ := hb₁
  have hw₀Z' := hw₀Z
  rw [integralSingularChainsIn_eq_range] at hw₀Z'
  obtain ⟨w₀', hw₀'⟩ := hw₀Z'
  change (integralSingularChainMap (singularSubspaceInclusion Z)).f 1 w₀' = w₀ at hw₀'
  have hw₀'A : w₀' ∈ integralSingularChainsIn 1 (subspaceIntersection A Z) := by
    rw [integralSingularChainsIn_subspace_iff, hw₀']
    exact integralSingularChainsIn_mono 1 (hPZA.trans inter_subset_right) hw₀
  have hw₀'c : (integralSingularChains Z).d 1 0 w₀' = 0 :=
    integralSingularChains_d_eq_zero_of_inclusion (by rw [hw₀']; exact hw₀c)
  have hb₁' : (integralSingularChains Z).d 2 1 b₁' = w₀' := by
    apply integralSingularChainInclusion_injective 1 Z
    exact (integralSingularChainMap_boundary 1 (singularSubspaceInclusion Z) b₁').trans
      (hb₁d.trans hw₀'.symm)
  have hAZ : IsOpen (subspaceIntersection A Z) := hA.preimage continuous_subtype_val
  have hBZ : IsOpen (subspaceIntersection B Z) := hB.preimage continuous_subtype_val
  have hcov : subspaceIntersection A Z ∪ subspaceIntersection B Z = univ := by
    apply eq_univ_of_forall
    intro x
    exact hZAB x.property
  obtain ⟨w', hw', hw'c, a', ha', ha'd⟩ :=
    exists_boundary_sub_mem_integralSingularChainsIn_inter hAZ hBZ hcov hw₀'A hw₀'c hb₁'
  have hrange : ∀ {n : ℕ} (c : (integralSingularChains Z).X n),
      (integralSingularChainMap (singularSubspaceInclusion Z)).f n c ∈
        integralSingularChainsIn n Z := by
    intro n c
    rw [integralSingularChainsIn_eq_range]
    exact ⟨c, rfl⟩
  refine ⟨(integralSingularChainMap (singularSubspaceInclusion Z)).f 1 w', ?_,
    integralSingularChains_d_inclusion_eq_zero hw'c,
    b₀ + (integralSingularChainMap (singularSubspaceInclusion Z)).f 2 a', ?_, ?_⟩
  · have hAB : (integralSingularChainMap (singularSubspaceInclusion Z)).f 1 w' ∈
        integralSingularChainsIn 1 (A ∩ B) :=
      (integralSingularChainsIn_subspace_iff 1 (A ∩ B) Z w').mp hw'
    rw [inter_assoc, integralSingularChainsIn_inter]
    exact ⟨hrange w', hAB⟩
  · refine Submodule.add_mem _ hb₀ (integralSingularChainsIn_mono 2 hZAT ?_)
    rw [integralSingularChainsIn_inter]
    exact ⟨hrange a', (integralSingularChainsIn_subspace_iff 2 A Z a').mp ha'⟩
  · have hd : (integralSingularChainMap (singularSubspaceInclusion Z)).f 1
        ((integralSingularChains Z).d 2 1 a') = (integralSingularChains Y).d 2 1
          ((integralSingularChainMap (singularSubspaceInclusion Z)).f 2 a') :=
      integralSingularChainMap_boundary 1 _ a'
    have hmap := congrArg (fun x => (integralSingularChainMap (singularSubspaceInclusion Z)).f 1 x)
      ha'd
    simp only at hmap
    rw [map_sub, hw₀', hd] at hmap
    rw [map_add, hb₀d, hmap]
    abel

end Transfer

end DifferentialGeometry.Topology.PiecewiseLinear
