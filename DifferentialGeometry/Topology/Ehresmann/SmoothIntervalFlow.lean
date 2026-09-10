import DifferentialGeometry.Topology.Ehresmann.ProperSubmersion
import Mathlib.Analysis.Calculus.BumpFunction.Basic

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open DifferentialGeometry.Analysis.ODE

set_option backward.isDefEq.respectTransparency false in
private theorem exists_scalar_interval_field {a b : ℝ} (hab : a ≤ b) :
    ∃ Z : Cₛ^∞⟮𝓘(ℝ); ℝ, TangentSpace 𝓘(ℝ)⟯,
      IsCompact (tsupport Z) ∧ ∀ y ∈ Ioo (a - 1) (b + 1), Z y = (1 : ℝ) := by
  let β : ContDiffBump ((a + b) / 2) :=
    ⟨(b - a) / 2 + 1, (b - a) / 2 + 2, by linarith, by linarith⟩
  have hβ : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
      (fun y : ℝ ↦ (⟨y, β y⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr β.contDiff
  let Z : Cₛ^∞⟮𝓘(ℝ); ℝ, TangentSpace 𝓘(ℝ)⟯ := ⟨β, hβ⟩
  refine ⟨Z, β.hasCompactSupport, ?_⟩
  intro y hy
  apply β.one_of_mem_closedBall
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -((b - a) / 2 + 1) ≤ y - (a + b) / 2 ∧ y - (a + b) / 2 ≤ (b - a) / 2 + 1
  constructor <;> linarith [hy.1, hy.2]

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_flow_eq_add
    (Z : (y : ℝ) → TangentSpace 𝓘(ℝ) y)
    (hZ : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle 𝓘(ℝ) ℝ)))
    (hc : IsCompact (tsupport Z)) {A B s t : ℝ}
    (hone : ∀ y ∈ Ioo A B, Z y = (1 : ℝ))
    (hs : s ∈ Ioo A B) (ht : t ∈ Ioo A B) :
    compactSupportFlowDiffeomorph Z hZ hc (t - s) s = t := by
  let γ : ℝ → ℝ := fun r ↦ s + r
  have hγ : IsMIntegralCurveOn γ Z (Ioo (A - s) (B - s)) := by
    intro r hr
    have hyr : s + r ∈ Ioo A B := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    change HasMFDerivWithinAt 𝓘(ℝ) 𝓘(ℝ) γ (Ioo (A - s) (B - s)) r
      ((1 : ℝ →L[ℝ] ℝ).smulRight (Z (s + r)))
    rw [hone _ hyr]
    exact ((hasDerivAt_id r).const_add s).hasDerivWithinAt.hasFDerivWithinAt.hasMFDerivWithinAt
  let hcomplete := exists_globalIntegralCurve_of_compactSupport Z hZ hc
  have hzero : (0 : ℝ) ∈ Ioo (A - s) (B - s) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero
    (hZ.of_le (by norm_num)) ((curveAt_integralCurve Z hcomplete s).isMIntegralCurveOn _) hγ
    (by simpa only [γ, add_zero] using curveAt_zero Z hcomplete s)
  have hh := heq (show t - s ∈ Ioo (A - s) (B - s) from
    ⟨sub_lt_sub_right ht.1 s, sub_lt_sub_right ht.2 s⟩)
  change curveAt Z hcomplete s (t - s) = t
  simpa only [γ, add_sub_cancel] using hh

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_interval_transport_of_proper
    (f : M → ℝ) (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hp : IsProperMap f)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) f x ≠ 0) {a b : ℝ} (hab : a ≤ b) :
    ∃ D : ℝ → M ≃ₘ⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M ↦ D p.1 p.2) ∧
      D 0 = Diffeomorph.refl I M ∞ ∧
      (∀ s t, (D s).trans (D t) = D (s + t)) ∧
      (∀ s, (D s).symm = D (-s)) ∧
      ∀ x, f x ∈ Icc a b → ∀ t ∈ Icc a b, f (D (t - f x) x) = t := by
  have hsurj (x : M) : Function.Surjective (mfderiv I 𝓘(ℝ) f x) := by
    apply surjective_of_nonzero_of_finrank_eq_one (K := ℝ)
      (f := (mfderiv I 𝓘(ℝ) f x).toLinearMap)
    · exact Module.finrank_self ℝ
    · intro h
      apply hreg x
      ext v
      exact congrArg (fun L : TangentSpace I x →ₗ[ℝ] TangentSpace 𝓘(ℝ) (f x) ↦ L v) h
  obtain ⟨Z, hZc, hZ1⟩ := exists_scalar_interval_field hab
  obtain ⟨X, hrel, _, hXc⟩ := exists_compactlySupported_smoothDerivativeLift_of_surjective
    f hp hf hsurj Z Z.contMDiff hZc
  let D := compactSupportFlowDiffeomorph X X.contMDiff hXc
  refine ⟨D, contMDiff_globalFlow_joint_of_compactSupport X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_zero X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_trans X X.contMDiff hXc,
    compactSupportFlowDiffeomorph_symm X X.contMDiff hXc, ?_⟩
  intro x hx t ht
  rw [show f (D (t - f x) x) =
      compactSupportFlowDiffeomorph Z Z.contMDiff hZc (t - f x) (f x) from
    compactSupportFlowDiffeomorph_map_of_mfderiv_eq f (hf.of_le (by norm_num))
      X X.contMDiff hXc Z Z.contMDiff hZc hrel (t - f x) x]
  exact scalar_flow_eq_add Z Z.contMDiff hZc hZ1
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

end Poincare.Topology.Ehresmann
