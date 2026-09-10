import DifferentialGeometry.Geometry.VectorField.ConstantPushforward
import DifferentialGeometry.Topology.Manifold.PlanarFieldDeformation

noncomputable section
open Set Topology
open scoped ContDiff Manifold

namespace Poincare.Geometry.VectorField

set_option backward.isDefEq.respectTransparency false in
theorem exists_planar_field_deformation_of_diffeomorph
    (f : Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞)
    (hc : HasCompactSupport (fun z ↦ f z - z)) :
    ∃ V : ℝ × ℂ → ℂ,
      ContDiff ℝ ∞ V ∧
      (∀ p z, V (p, z) ≠ 0) ∧
      (∀ z, V (0, z) = DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ (1 : ℂ)) z) ∧
      (∀ z, V (1, z) = 1) ∧
      (∃ r : ℝ, 0 < r ∧ ∀ p, mulTSupport (fun z ↦ V (p, z)) ⊆ Metric.closedBall 0 r) ∧
      ∃ D : ℝ → ℝ → Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞,
        ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℂ ↦ D q.1 q.2.1 q.2.2) ∧
        (∀ p ∈ Icc (0 : ℝ) 1, ∀ z t,
          HasDerivAt (fun r ↦ D p r z) (V (p, D p t z)) t) ∧
        (∀ p, D p 0 = Diffeomorph.refl 𝓘(ℝ, ℂ) ℂ ∞) ∧
        (∀ p s t, D p (s + t) = (D p s).trans (D p t)) ∧
        (∀ p t, (D p t).symm = D p (-t)) ∧
        (∀ z t, D 0 t z = f (f.symm z + t • (1 : ℂ))) ∧
        ∀ z t, D 1 t z = z + t • (1 : ℂ) := by
  let W : ℂ → ℂ := DifferentialGeometry.Diffeomorph.pushforward f (fun _ ↦ (1 : ℂ))
  have hW : ContDiff ℝ ∞ W := contDiff_pushforward_const f 1
  have hWne (z : ℂ) : W z ≠ 0 := pushforward_const_ne_zero f one_ne_zero z
  have hcompact : HasCompactSupport (fun z ↦ W z - 1) :=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_pushforward_const_sub_subset f 1)
  have hWcompact : HasCompactMulSupport W := by
    simpa only [HasCompactSupport, HasCompactMulSupport, tsupport, mulTSupport,
      Function.support, Function.mulSupport, sub_ne_zero] using hcompact
  obtain ⟨V, hV, hnonzero, hVzero, hVone, hsupp, D, hD, hderiv, hzero, hadd, hinv, hterminal⟩ :=
    Poincare.Topology.Manifold.exists_nonvanishing_deformation_with_smooth_flows hW hWne hWcompact
  refine ⟨V, hV, hnonzero, hVzero, hVone, hsupp, D, hD, hderiv, hzero, hadd, hinv, ?_, hterminal⟩
  intro z t
  let R := |t| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hd (s : ℝ) : HasDerivAt (fun s ↦ D 0 s z) (W (D 0 s z)) s := by
    simpa only [hVzero] using hderiv 0 (by norm_num) z s
  have he := DifferentialGeometry.Analysis.ODE.Flow.orbit_unique_smooth (hW.of_le (by norm_num))
    (a := -R) (b := R) (t₀ := 0) ⟨by linarith, hR⟩ (fun s _ ↦ hd s)
    (fun s _ ↦ hasDerivAt_pushforward_const_orbit f (1 : ℂ) z s)
    (by rw [hzero]; simp)
  exact he ⟨by dsimp [R]; linarith [neg_abs_le t], by dsimp [R]; linarith [le_abs_self t]⟩

end Poincare.Geometry.VectorField
