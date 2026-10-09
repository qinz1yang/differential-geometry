import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.IsometryTransport
import DifferentialGeometry.Geometry.Comparison.FactorGeometry

/-!
# LPA05: the model metric on the smooth model `Ns`

LPA02 (`lpa02_uniform_joint_zero_witnesses`) identifies the core balls with a SMOOTH manifold
`Ns` (a topological space with an `E3` atlas) which is homeomorphic, `h : Ns ≃ₜ N`, to the metric
`C^{K-1}` model `N`. LC80's zero-model data (`ZeroModelBall`, `ZeroModelFamily`) and LCP04's model
clauses need ONE type that is both a smooth manifold and a metric model. This file pulls the
metric of `N` back along `h`, keeping the topology of `Ns` (`Topology.IsEmbedding.comapMetricSpace`),
and transports LCP04's model clauses:

* `homeomorphComapMetric h`: the pulled-back metric (its topology is the topology of `Ns`);
* `homeomorphComapMetric_model_clauses`: `h` is an isometry, `Ns` is proper, has four-point
  comparison `0` and metric segments, and its blow-downs at `h⁻¹ q` have the Kleiner–Lott maps of
  `N` (in LCP04's quantifier order).
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Geometry.Collapse

open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

/-- The metric of `N` pulled back along a homeomorphism `h : Ns ≃ₜ N`; its topology is the given
topology of `Ns`. -/
abbrev homeomorphComapMetric {Ns N : Type*} [TopologicalSpace Ns] [MetricSpace N]
    (h : Ns ≃ₜ N) : MetricSpace Ns :=
  h.isEmbedding.comapMetricSpace h

/-- **LCP04's model clauses on the smooth model.** For `h : Ns ≃ₜ N` with `N` proper, with
four-point comparison `0`, metric segments and Kleiner–Lott maps from its blow-downs at `q`, the
pulled-back metric makes `h` an isometry, `Ns` proper, with four-point comparison `0`, metric
segments, and Kleiner–Lott maps from its blow-downs at `h⁻¹ q` (LCP04's quantifier order). -/
theorem homeomorphComapMetric_model_clauses {Ns N C : Type*} [TopologicalSpace Ns]
    [mN : MetricSpace N] [ProperSpace N] [mC : MetricSpace C] (h : Ns ≃ₜ N) {q : N} {o : C}
    (hfour : fourPointComparison 0 (univ : Set N))
    (hseg : ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
      f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
      Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) :
    letI := homeomorphComapMetric h
    Isometry h ∧ ProperSpace Ns ∧ fourPointComparison 0 (univ : Set Ns) ∧
      (∀ x y : Ns, ∃ f : Icc (0 : ℝ) 1 → Ns, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
        f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
      ∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ hR : 0 < R,
        Nonempty (@KleinerLottApprox Ns C ((homeomorphComapMetric h).rescale R⁻¹
          (inv_pos.mpr hR)) mC (h.symm q) o δ₁) := by
  let mNs_LPA02 : MetricSpace Ns := homeomorphComapMetric h
  have hiso : Isometry h := Isometry.of_dist_eq fun _ _ => rfl
  let κ : Ns ≃ᵢ N := { toEquiv := h.toEquiv, isometry_toFun := hiso }
  refine ⟨hiso, LipschitzWith.properSpace h.isProperMap hiso.lipschitzWith,
    hfour.of_isometry hiso, fun x y => ?_, fun δ₁ hδ₁ hδ₁1 => ?_⟩
  · obtain ⟨f, hfc, hf0, hf1, hfd⟩ := hseg (h x) (h y)
    refine ⟨fun t => h.symm (f t), h.symm.continuous.comp hfc, ?_, ?_, fun t₁ t₂ => ?_⟩
    · simp only [hf0, Homeomorph.symm_apply_apply]
    · simp only [hf1, Homeomorph.symm_apply_apply]
    · rw [← hiso.dist_eq, ← hiso.dist_eq x y, Homeomorph.apply_symm_apply,
        Homeomorph.apply_symm_apply]
      exact hfd t₁ t₂
  · obtain ⟨R₀, hR₀⟩ := hcone_of_isometryEquiv κ hcone δ₁ hδ₁ hδ₁1
    exact ⟨R₀, fun R hR hRpos => hR₀ R hRpos hR⟩

end DifferentialGeometry.Geometry.Collapse
