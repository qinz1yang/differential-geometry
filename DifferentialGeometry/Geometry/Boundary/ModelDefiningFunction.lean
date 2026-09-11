import DifferentialGeometry.Geometry.Boundary.ModelCoordinates
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [hI : HasSmoothBoundary E H I]

theorem exists_modelBoundary_definingFunction (p : hI.boundaryE) :
    ∃ U : Set E, IsOpen U ∧ modelBoundaryParam I p ∈ U ∧
      ∃ ρ : E → ℝ, ContDiffOn ℝ ∞ ρ U ∧ ρ (modelBoundaryParam I p) = 0 ∧
        (∀ y ∈ U, y ∈ range I ↔ 0 ≤ ρ y) ∧
        (∀ y ∈ U, y ∈ interior (range I) ↔ 0 < ρ y) ∧
        (∀ y ∈ U, y ∈ frontier (range I) ↔ ρ y = 0) ∧
        ∀ (w : hI.boundaryE) (c : ℝ),
          fderiv ℝ ρ (modelBoundaryParam I p)
            (fderiv ℝ (modelBoundaryParam I) p w + c • hI.inwardCoordE) = c := by
  obtain ⟨e, hp, _, hi, heq⟩ := exists_modelBoundary_coordinates I p
  have hezero : e (p, 0) = modelBoundaryParam I p := by simp [heq]
  have hyp : modelBoundaryParam I p ∈ e.target := hezero ▸ e.map_source hp
  let ρ : E → ℝ := fun y ↦ (e.symm y).2
  have hρ : ContDiffOn ℝ ∞ ρ e.target := hi.snd
  have hρzero : ρ (modelBoundaryParam I p) = 0 := by
    change (e.symm (modelBoundaryParam I p)).2 = 0
    rw [← hezero, e.left_inv hp]
  have heρ : (ρ ∘ e) =ᶠ[𝓝 (p, (0 : ℝ))] Prod.snd := by
    filter_upwards [e.open_source.mem_nhds hp] with z hz
    change (e.symm (e z)).2 = z.2
    rw [e.left_inv hz]
  let A : hI.boundaryE × ℝ →L[ℝ] E := (fderiv ℝ (modelBoundaryParam I) p).coprod
    (ContinuousLinearMap.toSpanSingleton ℝ hI.inwardCoordE)
  have hde : HasFDerivAt e A (p, 0) := by
    have hparam : HasFDerivAt (modelBoundaryParam I) (fderiv ℝ (modelBoundaryParam I) p) p :=
      (hI.I_inclH_boundaryI_symm_contDiff.differentiable (by simp) p).hasFDerivAt
    have hsnd : HasFDerivAt (fun z : hI.boundaryE × ℝ ↦ z.2)
        (ContinuousLinearMap.snd ℝ hI.boundaryE ℝ) (p, 0) := hasFDerivAt_snd
    have hefun : (e : hI.boundaryE × ℝ → E) =
        fun z ↦ modelBoundaryParam I z.1 + z.2 • hI.inwardCoordE := funext heq
    rw [hefun]
    convert! (hparam.comp (p, 0) hasFDerivAt_fst).add (hsnd.smul_const hI.inwardCoordE) using 1
  have hdρ : DifferentiableAt ℝ ρ (e (p, 0)) := by
    rw [hezero]
    exact (hρ.contDiffAt (e.open_target.mem_nhds hyp)).differentiableAt (by simp)
  have hchain : (fderiv ℝ ρ (modelBoundaryParam I p)).comp A =
      ContinuousLinearMap.snd ℝ hI.boundaryE ℝ := by
    rw [← hezero, ← hde.fderiv, ← fderiv_comp (p, 0) hdρ hde.differentiableAt,
      heρ.fderiv_eq, fderiv_snd]
  refine ⟨e.target, e.open_target, hyp, ρ, hρ, hρzero, ?_, ?_, ?_, ?_⟩
  · intro y hy
    have h := modelBoundaryParam_add_mem_range_iff I (e.symm y).1 (e.symm y).2
    rw [← heq, e.right_inv hy] at h
    exact h
  · intro y hy
    have h := modelBoundaryParam_add_mem_interior_iff I (e.symm y).1 (e.symm y).2
    rw [← heq, e.right_inv hy] at h
    exact h
  · intro y hy
    have h := modelBoundaryParam_add_mem_frontier_iff I (e.symm y).1 (e.symm y).2
    rw [← heq, e.right_inv hy] at h
    exact h
  · intro w c
    exact congrArg (fun L : hI.boundaryE × ℝ →L[ℝ] ℝ ↦ L (w, c)) hchain

end DifferentialGeometry.Geometry.Boundary
