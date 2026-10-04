import DifferentialGeometry.External.TauCeti.Geometry.Manifold.IntegralCurve.Flow
import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.DiffeomorphismFamily.ManifoldIntegralFlow

/-!
# The suspension of a finite-order time-dependent vector field

For a time-dependent vector field `V : ℝ → (x : M) → TangentSpace I x` the autonomous field
`autonomizedFlowVF V = (1, V)` on `ℝ × M` is its suspension. This file records, for a field that
is jointly `C^n` as a map `ℝ × M → TM` (any order `n`, in particular finite), that the suspension
is a `C^n` section, and the basic facts about its maximal integral curves (TauCeti's
`maximalIntegralCurve`): the time component runs at unit speed, and solutions of the
time-dependent equation are exactly the spatial parts of the maximal curves.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle TauCeti
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The suspension of a `C^n` time-dependent field is a `C^n` section.** If
`(t, x) ↦ V t x` is jointly `C^n` as a map `ℝ × M → TM`, then `(t, x) ↦ (1, V t x)` is a `C^n`
section of `T(ℝ × M)`. Any order `n`; the tree's `autonomizedFlowVF_section_contMDiff` is the
case `n = ∞`. -/
theorem contMDiff_autonomizedFlowVF_section {n : WithTop ℕ∞} [IsManifold I 1 M]
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent n
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) := by
  have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) n
      (fun x : ℝ =>
        (⟨x, ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro x₀
    exact (contMDiffAt_vectorSpace_iff_contDiffAt
      (V := fun x : ℝ => ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) x))).2 contDiffAt_const
  have hpair : ContMDiff (𝓘(ℝ, ℝ).prod I)
      ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod (I.prod 𝓘(ℝ, E))) n
      (fun p : ℝ × M =>
        ((⟨p.1, ((1 : ℝ) : TangentSpace 𝓘(ℝ, ℝ) p.1)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ),
          (⟨p.2, V p.1 p.2⟩ : TangentBundle I M))) :=
    (hone.comp contMDiff_fst).prodMk hV
  exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, ℝ)) (M := ℝ) (I' := I)
    (M' := M)).comp hpair

/-- The `C^1` instance of `contMDiff_autonomizedFlowVF_section`, in the form TauCeti's maximal
flow API consumes. -/
theorem contMDiff_one_autonomizedFlowVF_section {n : WithTop ℕ∞} (hn : 1 ≤ n)
    [IsManifold I 1 M] (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M))) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))) :=
  (contMDiff_autonomizedFlowVF_section V hV).of_le hn

/-- **Solutions of the time-dependent equation lift to integral curves of the suspension.** If
`γ' t = V t (γ t)` for every `t`, then `τ ↦ (s + τ, γ (s + τ))` is a global integral curve of
`(1, V)`. -/
theorem isMIntegralCurve_autonomizedFlowVF_of_hasMFDerivAt
    (V : ℝ → (x : M) → TangentSpace I x) {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t)))) (s : ℝ) :
    IsMIntegralCurve (fun τ : ℝ => ((s + τ, γ (s + τ)) : ℝ × M)) (autonomizedFlowVF V) := by
  intro τ
  have hshift : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ : ℝ => s + σ) τ (ContinuousLinearMap.id ℝ ℝ) :=
    ((hasFDerivAt_id τ).const_add s).hasMFDerivAt
  have hsp := (hγ (s + τ)).comp τ hshift
  refine (hshift.prodMk hsp).congr_mfderiv ?_
  refine ContinuousLinearMap.ext_ring ?_
  refine Prod.ext ?_ ?_
  · change (1 : ℝ) = ((1 : ℝ) • ((1 : ℝ), V (s + τ) (γ (s + τ)))).1
    simp
  · rfl

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **The maximal curve through a solution.** For a `C^1` suspension, a global solution `γ` of the
time-dependent equation gives the maximal integral curve of `(1, V)` through `(s, γ s)`: it is
defined for all time and equals `τ ↦ (s + τ, γ (s + τ))`. -/
theorem maximalIntegralCurve_autonomizedFlowVF_eq_of_hasMFDerivAt
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t)))) (s : ℝ) :
    maximalIntegralCurveInterval (autonomizedFlowVF V) ((s, γ s) : ℝ × M) = univ ∧
      ∀ τ, maximalIntegralCurve (autonomizedFlowVF V) ((s, γ s) : ℝ × M) τ =
        ((s + τ, γ (s + τ)) : ℝ × M) := by
  have hc := isMIntegralCurve_autonomizedFlowVF_of_hasMFDerivAt V hγ s
  have hc0 : (fun τ : ℝ => ((s + τ, γ (s + τ)) : ℝ × M)) 0 = (s, γ s) := by simp
  refine ⟨(maximalIntegralCurveInterval_eq_univ_iff hW).2 ⟨_, hc0, hc⟩, fun τ => ?_⟩
  have h0 : (0 : ℝ) ∈ Ioo (-(|τ| + 1)) (|τ| + 1) := ⟨by linarith [abs_nonneg τ], by
    linarith [abs_nonneg τ]⟩
  have hτ : τ ∈ Ioo (-(|τ| + 1)) (|τ| + 1) :=
    ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
  exact (hc.isMIntegralCurveOn _).eqOn_maximalIntegralCurve hW h0 hc0 hτ

/-- **The time component of a maximal curve of the suspension runs at unit speed.** -/
theorem maximalIntegralCurve_autonomizedFlowVF_fst
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    (p : ℝ × M) {τ : ℝ} (hτ : τ ∈ maximalIntegralCurveInterval (autonomizedFlowVF V) p) :
    (maximalIntegralCurve (autonomizedFlowVF V) p τ).1 = p.1 + τ := by
  set J := maximalIntegralCurveInterval (autonomizedFlowVF V) p
  set γ := maximalIntegralCurve (autonomizedFlowVF V) p
  have hJ : IsOpen J := isOpen_maximalIntegralCurveInterval
  have h0 : (0 : ℝ) ∈ J := by
    obtain ⟨c, a, b, hc, hc0, h0ab, -⟩ := hτ
    exact hc.subset_maximalIntegralCurveInterval h0ab hc0 h0ab
  have hd : ∀ σ ∈ J, HasDerivAt (fun σ => (γ σ).1 - σ) 0 σ := by
    intro σ hσ
    have h := autonomizedFlow_fst_hasDerivAt V γ σ
      ((isMIntegralCurveOn_maximalIntegralCurve hW σ hσ).hasMFDerivAt (hJ.mem_nhds hσ))
    have h2 : HasDerivAt (fun σ => (γ σ).1 - σ) (1 - 1) σ := h.sub (hasDerivAt_id' σ)
    rwa [sub_self] at h2
  have hconst := hJ.is_const_of_deriv_eq_zero isPreconnected_maximalIntegralCurveInterval
    (fun σ hσ => (hd σ hσ).differentiableAt.differentiableWithinAt)
    (fun σ hσ => (hd σ hσ).deriv) hτ h0
  have hγ0 : γ 0 = p := maximalIntegralCurve_zero h0
  simp only [hγ0, sub_zero] at hconst
  linarith

end DifferentialGeometry.Analysis.ODE
