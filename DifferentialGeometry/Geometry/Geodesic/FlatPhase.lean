import DifferentialGeometry.Analysis.ODE.Flow.Variational

set_option autoImplicit false

/-!
# Flat phase-space flow

This file packages the linear comparison model for a geodesic phase-space
flow: `(x, v)' = (v, 0)`.  Its explicit flow is `(x, v) ↦ (x + t v, v)`.
-/

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]

/-- The flat phase-space vector field `(x, v) ↦ (v, 0)` as a continuous
linear map. -/
def flatPhaseCLM : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.snd Real E E).prod (0 : (E × E) →L[Real] E)

@[simp]
theorem flatPhaseCLM_apply (z : E × E) :
    flatPhaseCLM (E := E) z = (z.2, 0) := by
  simp [flatPhaseCLM]

/-- The time-`t` flow of the flat phase-space vector field. -/
def flatPhaseFlowCLM (t : Real) : (E × E) →L[Real] (E × E) :=
  (ContinuousLinearMap.fst Real E E +
      t • ContinuousLinearMap.snd Real E E).prod
    (ContinuousLinearMap.snd Real E E)

@[simp]
theorem flatPhaseFlowCLM_apply (t : Real) (z : E × E) :
    flatPhaseFlowCLM (E := E) t z = (z.1 + t • z.2, z.2) := by
  simp [flatPhaseFlowCLM]

@[simp]
theorem flatPhaseFlowCLM_zero :
    flatPhaseFlowCLM (E := E) 0 = ContinuousLinearMap.id Real (E × E) := by
  ext z <;> simp

/-- Each flat phase orbit solves the linear phase equation globally. -/
theorem flatPhaseFlow_hasDerivAt (z : E × E) (t : Real) :
    HasDerivAt (fun s : Real => flatPhaseFlowCLM (E := E) s z)
      (flatPhaseCLM (E := E) (flatPhaseFlowCLM (E := E) t z)) t := by
  have hx := ((hasDerivAt_id t).smul_const z.2).const_add z.1
  have hv := hasDerivAt_const t z.2
  simpa using hx.prodMk hv

/-- If a time-dependent vector field has the flat phase linearization along
the zero orbit, the explicit flat flow is its global variational solution. -/
theorem flatPhase_is_var
    {f : Real → (E × E) → (E × E)}
    (hfd : ∀ t,
      fderiv Real (f t) (0 : E × E) = flatPhaseCLM (E := E))
    (δ : E × E) :
    Analysis.ODE.IsVariationalSolution f (fun _ => (0 : E × E)) δ 0
      (fun t => flatPhaseFlowCLM (E := E) t δ) := by
  constructor
  · simp
  · intro t
    rw [hfd t]
    exact flatPhaseFlow_hasDerivAt δ t

end Geodesic
end Riemannian
end Geometry
end DifferentialGeometry

