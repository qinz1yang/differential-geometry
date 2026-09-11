import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add



noncomputable section

open Set Function Bundle Manifold
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem continuousOn_source_tangentMap {r : V → M} {U : Set V} (hU : IsOpen U)
    (hr : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) 1 r U) :
    ContinuousOn (fun p : V × V =>
      TotalSpace.mk' E (r p.1) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r p.1 p.2)) (U ×ˢ univ) := by
  have htr := hr.continuousOn_tangentMapWithin le_rfl hU.uniqueMDiffOn
  have hv : Continuous (fun p : V × V =>
      (TotalSpace.mk' V p.1 p.2 : TangentBundle 𝓘(ℝ, V) V)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, V)).symm.continuous
  apply (htr.comp hv.continuousOn (fun p hp => hp.1)).congr
  intro p hp
  dsimp only [comp_apply, tangentMapWithin]
  rw [mfderivWithin_of_mem_nhds (hU.mem_nhds hp.1)]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
set_option backward.isDefEq.respectTransparency false in
theorem tangent_velocity_comp {r : V → M} {v : ℝ → V} {t : ℝ}
    (hr : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t)) (hv : DifferentiableAt ℝ v t) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (r ∘ v) (TotalSpace.mk' ℝ t (1 : ℝ)) =
      TotalSpace.mk' E (r (v t)) (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (v t) (deriv v t)) := by
  rw [tangentMap_comp_at _ hr hv.mdifferentiableAt]
  have hDv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, V) v t (1 : ℝ) = deriv v t := by
    rw [mfderiv_eq_fderiv]
    exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := v) (x := t)
  simp only [tangentMap, hDv]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem source_mfderiv_line {r : V → M} {z : V}
    (hr : MDifferentiableAt 𝓘(ℝ, V) 𝓘(ℝ, E) r z) (v : V) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => r (z + t • v)) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r z v := by
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have h := tangent_velocity_comp (r := r) (v := fun t : ℝ => z + t • v)
    (t := 0) (by simpa using hr) hl.differentiableAt
  have heq := congrArg (fun p : TangentBundle 𝓘(ℝ, E) M => (p.2 : E)) h
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => r (z + t • v)) 0 (1 : ℝ) =
    mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) r (z + 0 • v) (deriv (fun t : ℝ => z + t • v) 0) at heq
  erw [hl.deriv, zero_smul, add_zero] at heq
  exact heq

end DifferentialGeometry.Geometry
