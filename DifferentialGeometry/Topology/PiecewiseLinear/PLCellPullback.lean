/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.InwardPushStages
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {P D J : Set M} {Q : Set (EuclideanSpace ℝ (Fin 3))}
  {u : EuclideanSpace ℝ (Fin 3) → M}

theorem IsPLCellOn.exists_isPLHomeomorphOn_invFunOn
    {d : ℕ} (hD : IsPLCellOn d D J)
    (hu : IsPLHomeomorphInto 3 u Q) (hDQ : D ⊆ u '' Q) :
    ∃ q : (Fin (d + 1) → ℝ) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
        (Function.invFunOn u Q '' D) ∧
      Function.invFunOn u Q '' J = q '' stdSimplexBoundary d := by
  obtain ⟨R, r, v, hr, hv, rfl, rfl⟩ := hD
  let g := Function.invFunOn u Q ∘ v
  have hmaps : MapsTo v R (u '' Q) := fun x hx => hDQ ⟨x, hx, rfl⟩
  have hpl : IsPLOn 3 3 g R :=
    IsPLOn.comp_of_mapsTo
      (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hv.isPLOn hmaps
  have hpa : IsPiecewiseAffineOn g R := isPLOn_iff_isPiecewiseAffineOn.mp hpl
  have hinj : InjOn g R := by
    intro x hx y hy hxy
    apply hv.injOn hx hy
    have hx' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hmaps hx)
    have hy' := hu.injOn.bijOn_image.invOn_invFunOn.2 (hmaps hy)
    change u (g x) = v x at hx'
    change u (g y) = v y at hy'
    rw [← hx', ← hy', hxy]
  have hR : IsPolyhedron R := (IsPLBall.isPolyhedron ⟨r, hr⟩)
  have hg : IsPLHomeomorphOn g R (g '' R) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hR hpa hinj.bijOn_image
  refine ⟨g ∘ r, ?_, ?_⟩
  · rw [← image_comp]
    change IsPLHomeomorphOn (g ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin (d + 1)))
      (g '' R)
    exact hr.trans hg
  · simp only [g, image_comp]

end DifferentialGeometry.Topology.PiecewiseLinear
