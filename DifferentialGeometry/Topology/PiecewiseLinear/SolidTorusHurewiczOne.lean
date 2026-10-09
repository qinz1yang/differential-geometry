/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homology.HurewiczOne
import Mathlib.Analysis.Normed.Module.Connected
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.SphereTopHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Moise308Nested

open Set Topology
open scoped ContinuousMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "DiskModelQ4" => Metric.closedBall (0 : E2) 1
local notation "CircleModelQ4" => Metric.sphere (0 : E2) 1

private noncomputable def circleModelHomeomorphQ4 : Circle ≃ₜ CircleModelQ4 := by
  let e : ℂ ≃ₗᵢ[ℝ] E2 :=
    Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)
  refine
    { toFun := fun z =>
        ⟨e z, by
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.norm_map]
          exact Circle.norm_coe z⟩
      invFun := fun y =>
        ⟨e.symm y, by
          change e.symm (y : E2) ∈ Metric.sphere (0 : ℂ) 1
          apply mem_sphere_zero_iff_norm.mpr
          rw [e.symm.norm_map]
          exact mem_sphere_zero_iff_norm.mp y.property⟩
      left_inv := by
        intro z
        apply Subtype.ext
        exact e.symm_apply_apply z
      right_inv := by
        intro y
        apply Subtype.ext
        exact e.apply_symm_apply y
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

private theorem int_add_endomorphism_injective_of_surjective (f : ℤ →+ ℤ)
    (hs : Function.Surjective f) : Function.Injective f := by
  have hf (z : ℤ) : f z = z * f 1 := by
    conv_lhs => rw [show z = z • (1 : ℤ) by simp]
    rw [map_zsmul]
    simp
  obtain ⟨n, hn⟩ := hs 1
  have hmul : n * f 1 = 1 := by rw [← hf n]; exact hn
  have hnonzero : f 1 ≠ 0 := by
    intro h
    simp [h] at hmul
  intro a b hab
  have hab' : a * f 1 = b * f 1 := by
    calc
      a * f 1 = f a := (hf a).symm
      _ = f b := hab
      _ = b * f 1 := hf b
  exact mul_right_cancel₀ hnonzero hab'

open Classical in
theorem IsTopologicalSolidTorus.hurewiczOne_injective {S : Set E3}
    (hS : IsTopologicalSolidTorus S) (x : S) : Function.Injective (hurewiczOne x) := by
  let φ : S ≃ₜ (DiskModelQ4 × CircleModelQ4) := Classical.choice hS
  let p : DiskModelQ4 := ⟨0, by simp⟩
  let e : S ≃ₕ CircleModelQ4 := φ.toHomotopyEquiv.trans
    ((Homeomorph.prodComm DiskModelQ4 CircleModelQ4).toHomotopyEquiv.trans
      (DifferentialGeometry.HomotopyEquiv.productConvex CircleModelQ4
        (convex_closedBall (0 : E2) 1) p))
  let eCircle : S ≃ₕ Circle := e.trans circleModelHomeomorphQ4.symm.toHomotopyEquiv
  let q : Path (eCircle x) (1 : Circle) := PathConnectedSpace.somePath _ _
  let eG : FundamentalGroup S x ≃* Multiplicative ℤ :=
    (fundamentalGroupMulEquivOfHomotopyEquiv eCircle x (eCircle x) rfl).trans
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath q).trans fundamentalGroupCircleEquivInt)
  let eHAdd : integralSingularHomology 1 S ≃+ ℤ :=
    ((integralSingularHomologyHomotopyEquiv 1 e).trans
      (integralSphereTopHomologyEquiv 0 E2 (by simp))).toAddEquiv
  let eH : Multiplicative (integralSingularHomology 1 S) ≃* Multiplicative ℤ :=
    eHAdd.toMultiplicative
  have : PathConnectedSpace DiskModelQ4 :=
    isPathConnected_iff_pathConnectedSpace.mp (Metric.isPathConnected_closedBall (by norm_num))
  have : PathConnectedSpace CircleModelQ4 :=
    circleModelHomeomorphQ4.surjective.pathConnectedSpace
      circleModelHomeomorphQ4.continuous
  have : PathConnectedSpace S := φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  let fM : Multiplicative ℤ →* Multiplicative ℤ :=
    (eH.toMonoidHom.comp (hurewiczOne x)).comp eG.symm.toMonoidHom
  let f : ℤ →+ ℤ := AddMonoidHom.toMultiplicative.symm fM
  have hfM : Function.Surjective fM :=
    eH.surjective.comp ((hurewiczOne_surjective x).comp eG.symm.surjective)
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := hfM (Multiplicative.ofAdd z)
    exact ⟨w.toAdd, congrArg Multiplicative.toAdd hw⟩
  have hfi := int_add_endomorphism_injective_of_surjective f hf
  have hfMi : Function.Injective fM := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    exact hfi (congrArg Multiplicative.toAdd hab)
  intro a b hab
  apply eG.injective
  apply hfMi
  simpa [fM] using congrArg eH hab

end DifferentialGeometry.Topology.PiecewiseLinear
