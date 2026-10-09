/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.CyclicProductMap
import DifferentialGeometry.Topology.PiecewiseLinear.BallHomotopy
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorusHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitAnnulus

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLSphere.nonempty_fundamentalGroup_equiv_int
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J : Set E} (hJ : IsPLSphere 1 J) (x : J) :
    Nonempty (FundamentalGroup J x ≃* Multiplicative ℤ) := by
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ
  exact ⟨(fundamentalGroupMulEquivOfHomotopyEquiv e.symm.toHomotopyEquiv x (e.symm x) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e.symm x) 0).trans
      fundamentalGroupUnitAddCircleEquivInt)⟩

theorem surjective_longitude_fundamentalGroup_of_meridian_disk
    {T J M Q D : Set E3} (hT : IsTopologicalSolidTorus T)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (φ : (M × Q) ≃ₜ frontier T) (hJT : J ⊆ frontier T)
    (hcarry : CarriesFirstHomologyOnto J T) (hD : IsPLBall 2 D) (hDT : D ⊆ T)
    (q : Q) (hfiber : ∀ m : M, (φ (m, q) : E3) ∈ D) (x : J) :
    Function.Surjective (FundamentalGroup.map
      (ContinuousMap.snd.comp ((φ.symm : C(frontier T, M × Q)).comp
        (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, frontier T)))) x) := by
  classical
  have hclosed : IsClosed T := by
    obtain ⟨e⟩ := hT
    let _ : CompactSpace T := e.symm.compactSpace
    exact (isCompact_iff_compactSpace.mpr inferInstance).isClosed
  let i : C(frontier T, T) :=
    ⟨inclusion hclosed.frontier_subset, continuous_inclusion hclosed.frontier_subset⟩
  let f : C(M × Q, T) := i.comp (φ : C(M × Q, frontier T))
  let g : C(J, M × Q) := (φ.symm : C(frontier T, M × Q)).comp
    ⟨inclusion hJT, continuous_inclusion hJT⟩
  let a : C(M, M × Q) :=
    ContinuousMap.prodMk (ContinuousMap.id M) (ContinuousMap.const M q)
  let d : C(M, D) :=
    ⟨fun m => ⟨φ (m, q), hfiber m⟩,
      (continuous_subtype_val.comp (φ.continuous.comp
        (continuous_id.prodMk continuous_const))).subtype_mk _⟩
  let j : C(D, T) := ⟨inclusion hDT, continuous_inclusion hDT⟩
  have hfa : f.comp a = j.comp d := by
    ext m
    rfl
  have hnullq : (f.comp a).Nullhomotopic := by
    rw [hfa]
    let _ := hD.contractibleSpace
    exact ((id_nullhomotopic D).comp_left d).comp_right j
  let _ : PathConnectedSpace Q := isPathConnected_iff_pathConnectedSpace.mp hQ.isPathConnected_one
  let p : Path (g x).2 q := PathConnectedSpace.somePath _ _
  let H : ContinuousMap.Homotopy
      (f.comp (ContinuousMap.prodMk (ContinuousMap.id M)
        (ContinuousMap.const M (g x).2))) (f.comp a) :=
    { toFun := fun z => f (z.2, p z.1)
      continuous_toFun := f.continuous.comp
        (continuous_snd.prodMk (p.continuous.comp continuous_fst))
      map_zero_left := fun m => by simp only [p.source]; rfl
      map_one_left := fun m => by simp only [p.target]; rfl }
  have hnull : (f.comp (ContinuousMap.prodMk (ContinuousMap.id M)
      (ContinuousMap.const M (g x).2))).Nullhomotopic := by
    obtain ⟨c, hc⟩ := hnullq
    exact ⟨c, (show ContinuousMap.Homotopic _ _ from ⟨H⟩).trans hc⟩
  have hfg : f.comp g =
      (⟨inclusion hcarry.1, continuous_inclusion hcarry.1⟩ : C(J, T)) := by
    apply ContinuousMap.ext
    intro y
    apply Subtype.ext
    change ((φ (φ.symm ⟨y, hJT y.property⟩)) : E3) = (y : E3)
    exact congrArg Subtype.val (φ.apply_symm_apply ⟨y, hJT y.property⟩)
  have honto : Function.Surjective (FundamentalGroup.map (f.comp g) x) := by
    rw [hfg]
    exact (hcarry.carriesFundamentalGroupOnto_of_isTopologicalSolidTorus
      hT hJ.isPathConnected_one).2 hcarry.1 x
  obtain ⟨eQ⟩ := hQ.nonempty_fundamentalGroup_equiv_int (g x).2
  obtain ⟨eT⟩ := hT.nonempty_fundamentalGroup_equiv_int (f (g x))
  exact surjective_fundamentalGroup_snd_of_nullhomotopic_fiber f g x eQ eT hnull honto

theorem surjective_longitude_homology_of_meridian_disk
    {T J M Q D : Set E3} (hT : IsTopologicalSolidTorus T)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (φ : (M × Q) ≃ₜ frontier T) (hJT : J ⊆ frontier T)
    (hcarry : CarriesFirstHomologyOnto J T) (hD : IsPLBall 2 D) (hDT : D ⊆ T)
    (q : Q) (hfiber : ∀ m : M, (φ (m, q) : E3) ∈ D) :
    Function.Surjective (integralSingularHomologyMap 1
      (ContinuousMap.snd.comp ((φ.symm : C(frontier T, M × Q)).comp
        (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, frontier T))))) := by
  let ρ := ContinuousMap.snd.comp ((φ.symm : C(frontier T, M × Q)).comp
    (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, frontier T)))
  obtain ⟨y, hy⟩ := hJ.isConnected.nonempty
  let x : J := ⟨y, hy⟩
  let _ : PathConnectedSpace Q := isPathConnected_iff_pathConnectedSpace.mp hQ.isPathConnected_one
  intro a
  obtain ⟨γ, hγ⟩ := hurewiczOne_surjective (ρ x) (Multiplicative.ofAdd a)
  obtain ⟨β, hβ⟩ := surjective_longitude_fundamentalGroup_of_meridian_disk
    hT hJ hQ φ hJT hcarry hD hDT q hfiber x γ
  refine ⟨(hurewiczOne x β).toAdd, ?_⟩
  rw [← hurewiczOne_map, hβ, hγ]
  rfl

theorem longitude_generator_eq_one_or_neg_one_of_meridian_disk
    {T J M Q D : Set E3} (hT : IsTopologicalSolidTorus T)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (φ : (M × Q) ≃ₜ frontier T) (hJT : J ⊆ frontier T)
    (hcarry : CarriesFirstHomologyOnto J T) (hD : IsPLBall 2 D) (hDT : D ⊆ T)
    (q : Q) (hfiber : ∀ m : M, (φ (m, q) : E3) ∈ D)
    (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
    (eQ : integralSingularHomology 1 Q ≃ₗ[ℤ] ℤ) :
    let ρ := ContinuousMap.snd.comp ((φ.symm : C(frontier T, M × Q)).comp
      (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, frontier T)))
    eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = 1 ∨
      eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = -1 := by
  exact integralSingularHomologyMap_generator_eq_one_or_neg_one_of_surjective 1 _
    (surjective_longitude_homology_of_meridian_disk hT hJ hQ φ hJT hcarry hD hDT q hfiber) eJ eQ

theorem exists_primitive_longitude_coordinates_of_meridian_disk
    {T J M Q D : Set E3} (hT : IsTopologicalSolidTorus T)
    (hJ : IsPLSphere 1 J) (hQ : IsPLSphere 1 Q)
    (φ : (M × Q) ≃ₜ frontier T) (hJT : J ⊆ frontier T)
    (hcarry : CarriesFirstHomologyOnto J T) (hD : IsPLBall 2 D) (hDT : D ⊆ T)
    (q : Q) (hfiber : ∀ m : M, (φ (m, q) : E3) ∈ D) :
    ∃ (eJ : integralSingularHomology 1 J ≃ₗ[ℤ] ℤ)
      (eQ : integralSingularHomology 1 Q ≃ₗ[ℤ] ℤ),
      let ρ := ContinuousMap.snd.comp ((φ.symm : C(frontier T, M × Q)).comp
        (⟨inclusion hJT, continuous_inclusion hJT⟩ : C(J, frontier T)))
      eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = 1 ∨
        eQ (integralSingularHomologyMap 1 ρ (eJ.symm 1)) = -1 := by
  obtain ⟨eJ⟩ := hJ.nonempty_integralSingularHomology_one_equiv_int
  obtain ⟨eQ⟩ := hQ.nonempty_integralSingularHomology_one_equiv_int
  exact ⟨eJ, eQ,
    longitude_generator_eq_one_or_neg_one_of_meridian_disk hT hJ hQ φ hJT hcarry hD hDT q
      hfiber eJ eQ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
