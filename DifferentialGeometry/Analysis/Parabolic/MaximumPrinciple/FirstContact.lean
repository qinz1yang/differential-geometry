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

private theorem derivWithin_nonneg_at_interval_right_max
    {phi : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (hmax : IsLocalMaxOn phi (Icc s t) t) :
    0 ≤ derivWithin phi (Icc s t) t := by
  have hdir : s - t ∈ posTangentConeAt (Icc s t) t := by
    have hseg : segment ℝ t s ⊆ Icc s t := by
      rw [segment_symm, segment_eq_Icc hst.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonpos := hmax.fderivWithin_nonpos hdir
  have hlin :
      (fderivWithin ℝ phi (Icc s t) t : ℝ →L[ℝ] ℝ) (s - t) =
        (s - t) * derivWithin phi (Icc s t) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Icc s t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin ℝ phi (Icc s t) t : ℝ →L[ℝ] ℝ).map_smul
        (s - t) (1 : ℝ))
  rw [hlin] at hnonpos
  exact nonneg_of_mul_nonpos_right hnonpos (sub_neg.mpr hst)

theorem derivWithin_sub_heatOperatorWithDrift_nonneg_at_spacetime_max
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {psi : ℝ → M → ℝ} {s t : ℝ} (hst : s < t) {x : M}
    (hmax : IsLocalMaxOn (fun p : ℝ × M ↦ psi p.1 p.2)
      (Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hx : I.IsInteriorPoint x)
    (hpsi : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    0 ≤ derivWithin (fun q : ℝ ↦ psi q x) (Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x := by
  have htime_max : IsLocalMaxOn (fun q : ℝ ↦ psi q x) (Icc s t) t := by
    exact hmax.comp_continuousOn
      (s := Icc s t) (g := fun q : ℝ ↦ (q, x))
      (by intro q hq; exact ⟨hq, Set.mem_univ x⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hst.le, le_rfl⟩
  have htime_nonneg := derivWithin_nonneg_at_interval_right_max hst htime_max
  have hspace_max : IsLocalMax (psi t) x := by
    rw [← isLocalMaxOn_univ_iff]
    exact hmax.comp_continuousOn
      (s := Set.univ) (g := fun y : M ↦ (t, y))
      (by intro y hy; exact ⟨⟨hst.le, le_rfl⟩, hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
  have hlap_nonpos := laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint
    (I := I) G t hspace_max hx hpsi.self_of_nhds hpsi hgrad
  have hdrift : driftTerm (I := I) G t (X t) (psi t) x = 0 := by
    have hneg := driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
      (I := I) G t (X t) hspace_max.neg hx hpsi.self_of_nhds.neg
    have heq : (fun y => -psi t y) = (-1 : ℝ) • psi t := by funext y; simp
    rw [heq, driftTerm_const_smul (I := I) G t (X t) (-1) hpsi.self_of_nhds] at hneg
    linarith
  unfold heatOperatorWithDrift
  rw [hdrift, add_zero]
  exact sub_nonneg.mpr (hlap_nonpos.trans htime_nonneg)

theorem derivWithin_sub_heatOperatorWithDrift_nonneg_of_lower_support
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {theta psi : ℝ → M → ℝ} {s t : ℝ} (hst : s < t) {x : M}
    (hmax : IsLocalMaxOn (fun p : ℝ × M ↦ theta p.1 p.2)
      (Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hsupport : ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      psi p.1 p.2 ≤ theta p.1 p.2)
    (heq : psi t x = theta t x)
    (hx : I.IsInteriorPoint x)
    (hpsi : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    0 ≤ derivWithin (fun q : ℝ ↦ psi q x) (Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x := by
  apply derivWithin_sub_heatOperatorWithDrift_nonneg_at_spacetime_max
    (I := I) G X hst _ hx hpsi hgrad
  change ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x), psi p.1 p.2 ≤ psi t x
  filter_upwards [hmax, hsupport] with p hmaxp hsupp
  exact hsupp.trans (hmaxp.trans_eq heq.symm)

end

end DifferentialGeometry.Analysis.Parabolic
