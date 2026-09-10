import DifferentialGeometry.Topology.Manifold.NonvanishingHomotopy
import DifferentialGeometry.Analysis.ODE.Flow.Planar.ParameterizedConstantFlow

noncomputable section
open Set Topology
open scoped ContDiff Manifold

namespace Poincare.Topology.Manifold

set_option backward.isDefEq.respectTransparency false in
theorem exists_nonvanishing_deformation_with_smooth_flows
    {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (hne : ∀ z, f z ≠ 0)
    (hc : HasCompactMulSupport f) :
    ∃ V : ℝ × ℂ → ℂ,
      ContDiff ℝ ∞ V ∧
      (∀ p z, V (p, z) ≠ 0) ∧
      (∀ z, V (0, z) = f z) ∧
      (∀ z, V (1, z) = 1) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ p, mulTSupport (fun z ↦ V (p, z)) ⊆ Metric.closedBall 0 r) ∧
      ∃ D : ℝ → ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ ↦ D q.1 q.2.1 q.2.2) ∧
        (∀ p ∈ Icc (0 : ℝ) 1, ∀ z t,
          HasDerivAt (fun r ↦ D p r z) (V (p, D p t z)) t) ∧
        (∀ p, D p 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞) ∧
        (∀ p s t, D p (s + t) = (D p s).trans (D p t)) ∧
        (∀ p t, (D p t).symm = D p (-t)) ∧
        ∀ z t, D 1 t z = z + t • (1 : ℂ) := by
  obtain ⟨V, hV, hnonzero, hVzero, hVone, r, hr, hsupp⟩ :=
    exists_smooth_nonvanishing_homotopy_of_compactMulSupport hf hne hc
  have hfixed (p : ℝ) (z : ℂ) (hz : z ∉ Metric.closedBall 0 r) : V (p, z) = 1 :=
    image_eq_one_of_notMem_mulTSupport (f := fun z ↦ V (p, z)) (fun hs ↦ hz (hsupp p hs))
  obtain ⟨D, hD, hderiv, hzero, hadd, hinv⟩ :=
    Poincare.Analysis.exists_smoothFlow_family_of_uniform_const_off_compact hV (1 : ℂ)
      (isCompact_Icc (a := (0 : ℝ)) (b := 1)) (isCompact_closedBall (0 : ℂ) r) hfixed
  refine ⟨V, hV, hnonzero, hVzero, hVone, ⟨r, hr, hsupp⟩,
    D, hD, hderiv, hzero, hadd, hinv, ?_⟩
  intro z t
  have hd (s : ℝ) : HasDerivAt (fun s ↦ D 1 s z) (1 : ℂ) s := by
    simpa only [hVone] using hderiv 1 (by norm_num) z s
  have hsub (s : ℝ) : HasDerivAt (fun s ↦ D 1 s z - s • (1 : ℂ)) 0 s := by
    convert (hd s).sub ((hasDerivAt_id s).smul_const (1 : ℂ)) using 1 <;>
      first | rfl | simp only [one_smul, sub_self]
  have he := is_const_of_deriv_eq_zero (fun s ↦ (hsub s).differentiableAt)
    (fun s ↦ (hsub s).deriv) t 0
  have hz : D 1 0 z = z := by rw [hzero]; rfl
  simpa only [hz, zero_smul, sub_zero, sub_eq_iff_eq_add] using he

end Poincare.Topology.Manifold
