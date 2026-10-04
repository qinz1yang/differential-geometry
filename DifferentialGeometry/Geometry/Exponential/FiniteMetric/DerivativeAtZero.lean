import DifferentialGeometry.Geometry.Geodesic.FiniteMetric.Speed
import DifferentialGeometry.Bundle.TangentSpace

/-!
# The differential of the exponential map of a finite-regularity metric at the origin (CM1.c)

`exp_x (t • w)` is the base point of the geodesic flow from `w` at time `t`
(`expMap_smul_eq_proj_geodesicFlow`), whose velocity at `t = 0` is `w`; since `exp_x` is
differentiable at `0`, its differential sends every `w` to `w`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {r : ℕ∞}
  (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))

/-- The exponential map at `x`, as a map on the model fibre, is `C^r` on its (open) domain. -/
theorem contMDiffOn_expMap_fiber (hr : 1 ≤ r) (x : M) :
    ContMDiffOn 𝓘(ℝ, E) I r (fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M))
      {v : E | (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain} :=
  (g.contMDiffOn_expMap hr).comp
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) x).contMDiffOn (fun _ hv => hv)

theorem isOpen_expDomain_fiber (hr : 1 ≤ r) (x : M) :
    IsOpen {v : E | (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain} :=
  (g.isOpen_expDomain hr).preimage
    (DifferentialGeometry.contMDiff_tangentFiber (I := I) (n := 1) x).continuous

/-- **CM1.c** The differential of `exp_x` at the origin is the identity. -/
theorem hasMFDerivAt_expMap_zero (hr : 1 ≤ r) (x : M) :
    HasMFDerivAt 𝓘(ℝ, E) I (fun v : E => g.expMap (⟨x, v⟩ : TangentBundle I M)) 0
      (ContinuousLinearMap.id ℝ E) := by
  set f : E → M := fun v => g.expMap (⟨x, v⟩ : TangentBundle I M) with hf
  have h0 : (0 : E) ∈ {v : E | (⟨x, v⟩ : TangentBundle I M) ∈ g.expDomain} :=
    g.zero_mem_expDomain x
  have hdiff : MDifferentiableAt 𝓘(ℝ, E) I f 0 :=
    ((g.contMDiffOn_expMap_fiber hr x).contMDiffAt
      ((g.isOpen_expDomain_fiber hr x).mem_nhds h0)).mdifferentiableAt
      (by exact_mod_cast (zero_lt_one.trans_le hr).ne')
  have hL := hdiff.hasMFDerivAt
  refine hL.congr_mfderiv (ContinuousLinearMap.ext fun (w : E) => ?_)
  -- the ray derivative
  have hlin : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun t : ℝ => t • w) 0
      ((1 : ℝ →L[ℝ] ℝ).smulRight w) := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const w).hasFDerivAt
    simp only [one_smul] at h
    exact h.hasMFDerivAt
  have hcomp := mfderiv_comp_of_eq hdiff hlin.mdifferentiableAt (zero_smul ℝ w)
  have hflow := g.hasMFDerivAt_geodesicFlow_proj hr
    (g.mem_geodesicFlowDomain_zero hr (⟨x, w⟩ : TangentBundle I M))
  have hev : (fun t : ℝ => (g.geodesicFlow (⟨x, w⟩ : TangentBundle I M) t).proj) =ᶠ[𝓝 0]
      f ∘ (fun t : ℝ => t • w) := by
    have hopen : IsOpen {t : ℝ | ((⟨x, w⟩ : TangentBundle I M), t) ∈ g.geodesicFlowDomain} :=
      (g.isOpen_geodesicFlowDomain hr).preimage (continuous_const.prodMk continuous_id)
    filter_upwards [hopen.mem_nhds (g.mem_geodesicFlowDomain_zero hr _)] with t ht
    exact (g.expMap_smul_eq_proj_geodesicFlow hr x w t ht).symm
  have huniq := hflow.mfderiv.symm.trans (hev.mfderiv_eq.trans hcomp)
  rw [hlin.mfderiv] at huniq
  have hw := congrArg (fun L => L 1) huniq
  rw [g.geodesicFlow_zero hr] at hw
  change ((1 : ℝ →L[ℝ] ℝ) 1) • w =
    mfderiv 𝓘(ℝ, E) I f ((0 : ℝ) • w) (((1 : ℝ →L[ℝ] ℝ) 1) • w) at hw
  simp only [one_apply_eq_self, one_smul] at hw
  have key : ∀ y : E, y = 0 → mfderiv 𝓘(ℝ, E) I f y w = w → mfderiv 𝓘(ℝ, E) I f 0 w = w := by
    rintro y rfl h
    exact h
  exact key _ (zero_smul ℝ w) hw.symm

end Bundle.ContMDiffRiemannianMetric
