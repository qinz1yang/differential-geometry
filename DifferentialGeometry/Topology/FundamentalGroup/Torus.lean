/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.FundamentalGroup.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DifferentialGeometry.Topology

private noncomputable def euclideanCircleHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]).symm

noncomputable def fundamentalGroupTorusEquivIntProd
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    FundamentalGroup _ p ≃* Multiplicative ℤ × Multiplicative ℤ := by
  let e := euclideanCircleHomeomorph.prodCongr euclideanCircleHomeomorph
  let c := fun z : Circle =>
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected z (1 : Circle)).trans
      fundamentalGroupCircleEquivInt
  exact (fundamentalGroupMulEquivOfHomotopyEquiv e.toHomotopyEquiv p (e p) rfl).trans
    ((fundamentalGroupProdEquiv (e p).1 (e p).2).trans ((c (e p).1).prodCongr (c (e p).2)))

end DifferentialGeometry.Topology
