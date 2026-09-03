import DifferentialGeometry.Geometry.Operator.MetricFamily
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem derivWithin_nonpos_at_interval_right_min
    {phi : Real → Real} {s t : Real}
    (hst : s < t) (hmin : IsLocalMinOn phi (Set.Icc s t) t) :
    derivWithin phi (Set.Icc s t) t ≤ 0 := by
  have hdir : s - t ∈ posTangentConeAt (Set.Icc s t) t := by
    have hseg : segment Real t s ⊆ Set.Icc s t := by
      rw [segment_symm, segment_eq_Icc hst.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      0 ≤ (fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real) (s - t) :=
    hmin.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real) (s - t) =
        (s - t) * derivWithin phi (Set.Icc s t) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Set.Icc s t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real).map_smul
        (s - t) (1 : Real))
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg (sub_neg.mpr hst)

theorem derivWithin_sub_heatOperatorWithDrift_nonpos_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (X : Real → (x : M) → TangentSpace I x)
    {psi : Real → M → Real} {s t : Real} (hst : s < t) {x : M}
    (hmin : IsLocalMinOn (fun p : Real × M ↦ psi p.1 p.2)
      (Set.Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hx : I.IsInteriorPoint x)
    (hpsi : MDifferentiableAt I 𝓘(Real, Real) (psi t) x)
    (hpsi_near : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x ≤ 0 := by
  have htime_min : IsLocalMinOn (fun q : Real ↦ psi q x) (Set.Icc s t) t := by
    have hcomp := hmin.comp_continuousOn
      (s := Set.Icc s t) (g := fun q : Real ↦ (q, x))
      (by intro q hq; exact ⟨hq, Set.mem_univ x⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hst.le, le_rfl⟩
    exact hcomp
  have htime_nonpos :
      derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t ≤ 0 :=
    derivWithin_nonpos_at_interval_right_min hst htime_min
  have hspace_min : IsLocalMin (psi t) x := by
    rw [← isLocalMinOn_univ_iff]
    have hcomp := hmin.comp_continuousOn
      (s := Set.univ) (g := fun y : M ↦ (t, y))
      (by intro y hy; exact ⟨⟨hst.le, le_rfl⟩, hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
    exact hcomp
  have hheat_nonneg :
      0 ≤ heatOperatorWithDrift (I := I) G t (X t) (psi t) x :=
    heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
      (I := I) G t (X t) hspace_min hx hpsi hpsi_near hgrad
  linarith

theorem derivWithin_sub_heatOperatorWithDrift_nonpos_of_lower_support
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (X : Real → (x : M) → TangentSpace I x)
    {theta psi : Real → M → Real} {s t : Real} (hst : s < t) {x : M}
    (htheta_nonneg : ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ theta p.1 p.2)
    (hsupport : ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      theta p.1 p.2 ≤ psi p.1 p.2)
    (heq : psi t x = theta t x) (hzero : theta t x = 0)
    (hx : I.IsInteriorPoint x)
    (hpsi : MDifferentiableAt I 𝓘(Real, Real) (psi t) x)
    (hpsi_near : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x ≤ 0 := by
  apply derivWithin_sub_heatOperatorWithDrift_nonpos_at_spacetime_min
    (I := I) G X hst
  · unfold IsLocalMinOn IsMinFilter
    change ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      psi t x ≤ psi p.1 p.2
    rw [heq, hzero]
    filter_upwards [htheta_nonneg, hsupport] with p hpnonneg hple
    exact hpnonneg.trans hple
  · exact hx
  · exact hpsi
  · exact hpsi_near
  · exact hgrad

end

end DifferentialGeometry.Analysis.Parabolic
