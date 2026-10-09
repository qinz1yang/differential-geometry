/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import DifferentialGeometry.Topology.Homology.LiftedSphere
import DifferentialGeometry.Topology.Homotopy.ConvexProduct
import DifferentialGeometry.Topology.PiecewiseLinear.FirstHomologyCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import Mathlib.RingTheory.Noetherian.Orzech

open Set
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "D2" => Metric.closedBall (0 : E2) 1
local notation "S1" => Metric.sphere (0 : E2) 1

private noncomputable def circleSphereHomeomorph : Circle ≃ₜ S1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]

private noncomputable def solidTorusCircleHomotopyEquiv
    {Y : Type u} [TopologicalSpace Y] {T : Set Y} (hT : IsTopologicalSolidTorus T) :
    T ≃ₕ S1 :=
  (Classical.choice hT).toHomotopyEquiv.trans
    ((Homeomorph.prodComm D2 S1).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex S1 (convex_closedBall _ _)
        ⟨0, Metric.mem_closedBall_self zero_le_one⟩))

noncomputable def IsTopologicalSolidTorus.integralSingularHomologyOneEquivInt
    {Y : Type u} [TopologicalSpace Y] {T : Set Y} (hT : IsTopologicalSolidTorus T) :
    integralSingularHomology 1 T ≃ₗ[ℤ] ℤ :=
  let e : T ≃ₕ liftedHomotopySphere.{u} 0 :=
    (solidTorusCircleHomotopyEquiv hT).trans Homeomorph.ulift.symm.toHomotopyEquiv
  (integralSingularHomologyHomotopyEquiv 1 e).trans (integralLiftedSphereTopEquiv 0)

private noncomputable def IsTopologicalSolidTorus.fundamentalGroupEquivInt
    {Y : Type u} [TopologicalSpace Y] {T : Set Y} (hT : IsTopologicalSolidTorus T) (x : T) :
    FundamentalGroup T x ≃* Multiplicative ℤ :=
  let e : T ≃ₕ Circle :=
    (solidTorusCircleHomotopyEquiv hT).trans circleSphereHomeomorph.symm.toHomotopyEquiv
  (fundamentalGroupMulEquivOfHomotopyEquiv e x (e x) rfl).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (e x) (1 : Circle)).trans
      fundamentalGroupCircleEquivInt)

theorem IsTopologicalSolidTorus.hurewiczOne_bijective
    {Y : Type u} [TopologicalSpace Y] {T : Set Y} (hT : IsTopologicalSolidTorus T) (x : T) :
    Function.Bijective (hurewiczOne x) := by
  let φ := Classical.choice hT
  let _ : PathConnectedSpace D2 := isPathConnected_iff_pathConnectedSpace.mp
    ((convex_closedBall (0 : E2) 1).isPathConnected
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩)
  let _ : PathConnectedSpace S1 := circleSphereHomeomorph.surjective.pathConnectedSpace
    circleSphereHomeomorph.continuous
  let _ : PathConnectedSpace T := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let eG := hT.fundamentalGroupEquivInt x
  let eH := hT.integralSingularHomologyOneEquivInt.toAddEquiv.toMultiplicative
  let F := eH.toMonoidHom.comp ((hurewiczOne x).comp eG.symm.toMonoidHom)
  let f : ℤ →+ ℤ := MonoidHom.toAdditiveRight F
  have heHsurj : Function.Surjective
      (eH : Multiplicative (integralSingularHomology 1 T) ≃* Multiplicative ℤ) :=
    eH.surjective
  have heGsurj : Function.Surjective
      (eG.symm : Multiplicative ℤ ≃* FundamentalGroup T x) := eG.symm.surjective
  have huresurj : Function.Surjective (hurewiczOne x) := hurewiczOne_surjective x
  have hFsurj : Function.Surjective F := by
    intro z
    obtain ⟨h, hh⟩ := heHsurj z
    obtain ⟨g, hg⟩ := huresurj h
    obtain ⟨a, ha⟩ := heGsurj g
    refine ⟨a, ?_⟩
    change eH (hurewiczOne x (eG.symm a)) = z
    rw [ha, hg, hh]
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨a, ha⟩ := hFsurj (Multiplicative.ofAdd z)
    refine ⟨Multiplicative.toAdd a, ?_⟩
    change Multiplicative.toAdd (F a) = z
    exact congrArg Multiplicative.toAdd ha
  have hfi : Function.Injective f :=
    IsNoetherian.injective_of_surjective_endomorphism f.toIntLinearMap hf
  have hFi : Function.Injective F := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    exact hfi (congrArg Multiplicative.toAdd hab)
  refine ⟨?_, hurewiczOne_surjective x⟩
  intro a b hab
  apply eG.injective
  apply hFi
  simpa [F] using congrArg eH hab

theorem CarriesFirstHomologyOnto.carriesFundamentalGroupOnto_of_hurewiczOne_injective
    {Y : Type u} [TopologicalSpace Y] {G T : Set Y} (hH : CarriesFirstHomologyOnto G T)
    (hG : IsPathConnected G) (hT : ∀ x : T, Function.Injective (hurewiczOne x)) :
    CarriesFundamentalGroupOnto G T := by
  refine ⟨hH.1, fun hGT x γ => ?_⟩
  let i : C(G, T) := ⟨inclusion hGT, continuous_inclusion hGT⟩
  let _ : PathConnectedSpace G := isPathConnected_iff_pathConnectedSpace.mp hG
  obtain ⟨a, ha⟩ := hH.2 hGT (hurewiczOne (i x) γ).toAdd
  obtain ⟨β, hβ⟩ := hurewiczOne_surjective x (Multiplicative.ofAdd a)
  refine ⟨β, hT (i x) ?_⟩
  apply Multiplicative.toAdd.injective
  rw [hurewiczOne_map, hβ]
  exact ha

theorem IsTopologicalSolidTorus.carriesFundamentalGroupOnto_of_carriesFirstHomologyOnto
    {Y : Type u} [TopologicalSpace Y] {G T : Set Y} (hT : IsTopologicalSolidTorus T)
    (hH : CarriesFirstHomologyOnto G T) (hG : IsPathConnected G) :
    CarriesFundamentalGroupOnto G T :=
  hH.carriesFundamentalGroupOnto_of_hurewiczOne_injective hG
    fun x => (hT.hurewiczOne_bijective x).1

end DifferentialGeometry.Topology.PiecewiseLinear
