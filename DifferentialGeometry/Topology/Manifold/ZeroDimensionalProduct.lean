import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import DifferentialGeometry.Topology.LocalDegree.EuclideanReal
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped ContDiff Topology
namespace Poincare.Manifold
open Poincare.LocalDegree
variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  (J : ModelWithCorners ℝ E H)


def zeroDimensionalProductChart (p : B) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
      (EuclideanSpace ℝ (Fin 1)) (B × ℝ) 1 := by
  let _ : DiscreteTopology B := DifferentialGeometry.discrete_topology_of_subsingleton_model J
  exact {
    toFun x := (p, realEuclideanIsometry.symm x)
    invFun y := realEuclideanIsometry y.2
    source := univ
    target := {y | y.1 = p}
    map_source' _ _ := rfl
    map_target' _ _ := trivial
    left_inv' x _ := realEuclideanIsometry.apply_symm_apply x
    right_inv' y hy := Prod.ext hy.symm (realEuclideanIsometry.symm_apply_apply y.2)
    open_source := isOpen_univ
    open_target := (isOpen_discrete {p}).preimage continuous_fst
    contMDiffOn_toFun :=
      (contMDiff_const.prodMk realEuclideanIsometry.symm.toContinuousLinearEquiv.contDiff.contMDiff).contMDiffOn
    contMDiffOn_invFun :=
      (realEuclideanIsometry.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_snd).contMDiffOn }


theorem zeroDimensionalProductChart_apply (p : B) (x : EuclideanSpace ℝ (Fin 1)) :
    zeroDimensionalProductChart J p x = (p, realEuclideanIsometry.symm x) := rfl


theorem zeroDimensionalProductChart_source (p : B) :
    (zeroDimensionalProductChart J p).source = univ := rfl


theorem zeroDimensionalProductChart_target (p : B) :
    (zeroDimensionalProductChart J p).target = {y | y.1 = p} := rfl


theorem mfderiv_zeroDimensionalProductChart (p : B) (x v : EuclideanSpace ℝ (Fin 1)) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
      (zeroDimensionalProductChart J p) x v = (0, realEuclideanIsometry.symm v) := by
  change mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (J.prod 𝓘(ℝ, ℝ))
    (fun y => (p, realEuclideanIsometry.symm y)) x v = _
  erw [mfderiv_prodMk mdifferentiableAt_const
    realEuclideanIsometry.symm.toContinuousLinearEquiv.differentiableAt.mdifferentiableAt,
    mfderiv_const, mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  rfl

end Poincare.Manifold
