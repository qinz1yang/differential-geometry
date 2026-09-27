/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTransfer
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLSphere.surjective_of_fundamentalGroup_map_surjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Set E} (hQ : IsPLSphere 1 Q) {X : Type*} [TopologicalSpace X]
    (f : C(X, Q)) (x : X) (h : Function.Surjective (FundamentalGroup.map f x)) :
    Function.Surjective f := by
  obtain ⟨e⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hQ
  let a : Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]
  exact surjective_of_fundamentalGroup_map_surjective_to_homeomorphic_circle
    (e.symm.trans ((AddCircle.homeomorphCircle one_ne_zero).trans a)) f x h

end DifferentialGeometry.Topology.PiecewiseLinear
