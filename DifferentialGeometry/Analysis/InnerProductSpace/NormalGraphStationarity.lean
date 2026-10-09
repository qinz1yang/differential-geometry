import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic
import DifferentialGeometry.Analysis.InnerProductSpace.OrthogonalErrorCoordinates

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology

namespace DifferentialGeometry.Analysis
section

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem normal_equation_of_isLocalMin_graph_squaredDistance
    (g : E → F) (u t : E) (v : F) (hg : DifferentiableAt ℝ g t)
    (hmin : IsLocalMin (fun s => ‖s - u‖ ^ 2 + ‖g s - v‖ ^ 2) t) :
    t - u + (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v) = 0 := by
  have hd := ((hasFDerivAt_id (𝕜 := ℝ) t).sub_const u).norm_sq.add
    (hg.hasFDerivAt.sub_const v).norm_sq
  have hzero := hmin.hasFDerivAt_eq_zero hd
  let w : E := t - u + (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v)
  have heval := congrArg (fun A : E →L[ℝ] ℝ => A w) hzero
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply, zero_apply,
    innerSL_apply_apply, nsmul_eq_mul, id_eq] at heval
  norm_num at heval
  have hw : inner ℝ w w = 0 := by
    change inner ℝ (t - u + (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v)) w = 0
    rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]
    linarith
  exact (inner_self_eq_zero (𝕜 := ℝ)).mp hw

end
end DifferentialGeometry.Analysis

namespace DifferentialGeometry.Analysis
section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem normal_equation_of_isMinOn_normal_graph
    (L : Submodule ℝ H) [CompleteSpace L] [CompleteSpace Lᗮ]
    (o : H) (g : L → Lᗮ) (U : Set L) (W : Set H)
    (u t : L) (v : Lᗮ) (hU : U ∈ 𝓝 t)
    (hg : DifferentiableAt ℝ g t)
    (hgraph : ∀ s ∈ U, o + orthogonalCoordinateSum L (s, g s) ∈ W)
    (hmin : IsMinOn (fun y => dist (o + orthogonalCoordinateSum L (u, v)) y)
      W (o + orthogonalCoordinateSum L (t, g t))) :
    t - u + (ContinuousLinearMap.adjoint (fderiv ℝ g t)) (g t - v) = 0 := by
  let z : H := o + orthogonalCoordinateSum L (u, v)
  let q : L → H := fun s => o + orthogonalCoordinateSum L (s, g s)
  have hpyth (s : L) : (dist z (q s)) ^ 2 = ‖s - u‖ ^ 2 + ‖g s - v‖ ^ 2 := by
    have heq : q s - z = ((s - u : L) : H) + ((g s - v : Lᗮ) : H) := by
      change (o + ((s : H) + (g s : H))) - (o + ((u : H) + (v : H))) =
        ((s : H) - (u : H)) + ((g s : H) - (v : H))
      abel
    rw [dist_comm, dist_eq_norm, heq]
    have horth : inner ℝ ((s - u : L) : H) ((g s - v : Lᗮ) : H) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K := L) (s - u).property (g s - v).property
    simpa only [pow_two, Submodule.norm_coe] using
      norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  have hlocal : IsMinOn (fun s => ‖s - u‖ ^ 2 + ‖g s - v‖ ^ 2) U t := by
    intro s hs
    have hh : dist z (q t) ≤ dist z (q s) := hmin (hgraph s hs)
    have ht0 : 0 ≤ dist z (q t) := dist_nonneg
    have hs0 : 0 ≤ dist z (q s) := dist_nonneg
    change ‖t - u‖ ^ 2 + ‖g t - v‖ ^ 2 ≤ ‖s - u‖ ^ 2 + ‖g s - v‖ ^ 2
    rw [← hpyth t, ← hpyth s]
    nlinarith
  exact normal_equation_of_isLocalMin_graph_squaredDistance g u t v hg
    (hlocal.isLocalMin hU)

end
end DifferentialGeometry.Analysis
