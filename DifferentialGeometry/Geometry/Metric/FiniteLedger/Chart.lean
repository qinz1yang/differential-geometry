import DifferentialGeometry.Geometry.Metric.Pullback.DerivativeOrder
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Set Manifold
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

theorem contDiffOn_chart_inner_derivatives {n : ℕ∞ω} {K : ℕ}
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) n E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (hKn : (K : ℕ∞ω) ≤ n) (hK : 2 ≤ K)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ((K + 1 : ℕ) : ℕ∞ω) M) :
    let _ : AddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    let _ : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
    let b : E → E →L[ℝ] E →L[ℝ] ℝ := fun y => (g.inner (e.symm y) : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (E := E) (F := E) (E' := E) (F' := E)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y : E →L[ℝ] E)
    ContDiffOn ℝ K b e.target ∧
      ContDiffOn ℝ ((K - 1 : ℕ) : ℕ∞ω)
        (fun y => DifferentialGeometry.MetricKoszul.raisedKoszulOp (E := E)
          (b y) (fderiv ℝ b y)) e.target ∧
      ∀ X Y Z W : E, ContDiffOn ℝ ((K - 2 : ℕ) : ℕ∞ω)
        (fun y => DifferentialGeometry.Analysis.coefficientRm04 b y X Y Z W) e.target := by
  let φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ((K + 1 : ℕ) : ℕ∞ω) :=
    { toPartialEquiv := e.symm.toPartialEquiv
      open_source := e.open_target
      open_target := e.open_source
      contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas he
      contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas he }
  have himm : ∀ x ∈ e.target,
      Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm x : E →L[ℝ] E) := by
    intro x hx
    exact ((φ.isLocalDiffeomorphAt _ _ _ hx).mfderivToContinuousLinearEquiv
      (by exact_mod_cast Nat.succ_ne_zero K)).injective
  have hKs : (K : ℕ∞ω) + 1 ≤ ((K + 1 : ℕ) : ℕ∞ω) := by
    simp only [Nat.cast_add, Nat.cast_one, le_refl]
  refine ⟨g.contDiffOn_pullback_inner hKn hKs e.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas he), ?_, fun X Y Z W => ?_⟩
  · exact g.contDiffOn_pullback_christoffel hKn hKs (by omega) e.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas he) himm
  · exact g.contDiffOn_pullback_curvature hKn hKs hK e.open_target
      (contMDiffOn_symm_of_mem_maximalAtlas he) himm X Y Z W

end Bundle.ContMDiffRiemannianMetric
