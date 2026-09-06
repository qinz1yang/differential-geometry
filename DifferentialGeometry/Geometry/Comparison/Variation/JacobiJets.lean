import DifferentialGeometry.Geometry.Connection.AlongCurveHom
import DifferentialGeometry.Bundle.PartialMfderiv.TimeDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.JacobiField
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open CovariantDerivativeAlong AlongCurve
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem curveVelocity_contMDiffAt
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, curveVelocity γ s⟩ : TangentBundle I M)) t := by
  exact hγ.time_mfderiv (m := 1) (by norm_num)

omit [I.Boundaryless] [T2Space M] in
private theorem derivAlongWithin_univ_eq_covDerivAlong_of_eq_zero
    (g : SmoothRiemannianMetric I M) (cov : CovariantDerivative I E (TangentSpace I))
    (γ : ℝ → M) (Z : ∀ t, TangentSpace I (γ t)) {t : ℝ} (hZ : Z t = 0) :
    cov.derivAlongWithin γ Z univ t = covDerivAlong g γ Z t := by
  simp only [CovariantDerivative.derivAlongWithin, covDerivAlong_def,
    chartCovDerivAlong_def, chartRepAt, hZ, map_zero,
    ChartChristoffel.contraction_zero_right, add_zero, derivWithin_univ]
  rfl

private theorem curvature_contraction_contMDiffAt
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (Y Z : ∀ t, TangentSpace I (γ t)) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hY : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, Y s⟩ : TangentBundle I M)) t)
    (hZ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, Z s⟩ : TangentBundle I M)) t) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun s => (⟨γ s, ((riemannOp (LeviCivita g) (γ s)).flip (Y s)).flip (Z s)⟩ :
        TotalSpace (E →L[ℝ] E) (fun x => TangentSpace I x →L[ℝ] TangentSpace I x))) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let e := trivializationAt E (TangentSpace I) (γ t)
  have he : γ t ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ _
  have hpre : ∀ᶠ s in 𝓝 t, γ s ∈ e.baseSet :=
    hγ.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds he)
  rw [contMDiffAt_hom_bundle]
  refine ⟨hγ, contMDiffAt_clm_of_pointwise fun v => ?_⟩
  have hv : ContMDiffAt I I.tangent 1
      (fun x => (⟨x, e.symmL ℝ x v⟩ : TangentBundle I M)) (γ t) := by
    rw [e.contMDiffAt_section_iff he]
    apply (contMDiffAt_const (c := v)).congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with x hx
    rw [← e.continuousLinearMapAt_apply_of_mem ℝ hx,
      e.continuousLinearMapAt_symmL hx]
  have hR := ((riemannOp_section_contMDiff g).contMDiffAt.of_le (show 1 ≤ ∞ by simp)).comp t hγ
  have hR1 := ContMDiffAt.clm_bundle_apply
    (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    (b := γ) (ϕ := fun s => riemannOp (LeviCivita g) (γ s))
    (v := fun s => e.symmL ℝ (γ s) v) hR (hv.comp t hγ)
  have hR2 := ContMDiffAt.clm_bundle_apply
    (F₁ := E) (F₂ := E →L[ℝ] E)
    (E₁ := fun x : M => TangentSpace I x)
    (E₂ := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
    (b := γ) (ϕ := fun s => riemannOp (LeviCivita g) (γ s) (e.symmL ℝ (γ s) v))
    (v := Y) hR1 hY
  have hR3 := ContMDiffAt.clm_bundle_apply
    (F₁ := E) (F₂ := E)
    (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
    (b := γ) (ϕ := fun s => riemannOp (LeviCivita g) (γ s) (e.symmL ℝ (γ s) v) (Y s))
    (v := Z) hR2 hZ
  have hc := (Bundle.contMDiffAt_totalSpace.mp hR3).2
  apply hc.congr_of_eventuallyEq
  filter_upwards [hpre] with s hs
  rw [ContinuousLinearMap.inCoordinates_eq hs hs]
  change e.continuousLinearEquivAt ℝ (γ s) hs
      (riemannOp (LeviCivita g) (γ s)
        ((e.continuousLinearEquivAt ℝ (γ s) hs).symm v) (Y s) (Z s)) =
    (e (⟨γ s, riemannOp (LeviCivita g) (γ s) (e.symmL ℝ (γ s) v) (Y s) (Z s)⟩ :
      TangentBundle I M)).2
  rw [e.symm_continuousLinearEquivAt_eq hs,
    Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) e hs,
    e.continuousLinearMapAt_apply_of_mem ℝ hs]

private theorem covDerivAlong_curvature_of_eq_zero
    (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (J Y Z : ∀ t, TangentSpace I (γ t)) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ t)
    (hJ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γ s, J s⟩ : TangentBundle I M)) t)
    (hY : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, Y s⟩ : TangentBundle I M)) t)
    (hZ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun s => (⟨γ s, Z s⟩ : TangentBundle I M)) t)
    (hzero : J t = 0) :
    covDerivAlong g γ (fun s => riemannOp (LeviCivita g) (γ s) (J s) (Y s) (Z s)) t =
      riemannOp (LeviCivita g) (γ t) (covDerivAlong g γ J t) (Y t) (Z t) := by
  let A : ∀ s, TangentSpace I (γ s) →L[ℝ] TangentSpace I (γ s) :=
    fun s => ((riemannOp (LeviCivita g) (γ s)).flip (Y s)).flip (Z s)
  have hA := curvature_contraction_contMDiffAt g Y Z hγ hY hZ
  have hprod := (LeviCivita g).derivAlongWithin_clm_apply_of_eq_zero (LeviCivita g) γ A J (J := univ)
    (hA.mdifferentiableAt (by simp)).mdifferentiableWithinAt
    hJ.mdifferentiableWithinAt hzero
  have hAzero : A t (J t) = 0 := by rw [hzero, map_zero]
  rw [derivAlongWithin_univ_eq_covDerivAlong_of_eq_zero g _ _ _ hAzero,
    derivAlongWithin_univ_eq_covDerivAlong_of_eq_zero g _ _ _ hzero] at hprod
  exact hprod

theorem jacobi_second_covariant_derivative_eq_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {t : ℝ}
    (hJac : IsJacobiAt g γ J t) (hJ : J t = 0) :
    covDerivAlong g γ (fun s => covDerivAlong g γ J s) t = 0 := by
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let _ : SeminormedAddCommGroup
      (TangentSpace I (γ t) →L[ℝ] TangentSpace I (γ t) →L[ℝ] TangentSpace I (γ t)) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E)).toSeminormedAddCommGroup
  rw [jacobi_d2_eq g γ J hJac, hJ, map_zero, zero_apply, zero_apply, neg_zero]

theorem jacobi_third_covariant_derivative_of_eq_zero
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (J : ∀ t, TangentSpace I (γ t)) {t : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t)
    (hJ : MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
      (fun s => (⟨γ s, J s⟩ : TangentBundle I M)) t)
    (hJac : ∀ᶠ s in 𝓝 t, IsJacobiAt g γ J s) (hzero : J t = 0) :
    covDerivAlong g γ
      (fun s => covDerivAlong g γ (fun r => covDerivAlong g γ J r) s) t =
      -riemannOp (LeviCivita g) (γ t) (covDerivAlong g γ J t)
        (curveVelocity γ t) (curveVelocity γ t) := by
  have heq : ∀ᶠ s in 𝓝 t,
      covDerivAlong g γ (fun r => covDerivAlong g γ J r) s =
        (-1 : ℝ) • riemannOp (LeviCivita g) (γ s) (J s)
          (curveVelocity γ s) (curveVelocity γ s) := by
    filter_upwards [hJac] with s hs
    simpa only [neg_one_smul] using jacobi_d2_eq g γ J hs
  rw [covDerivAlong_congr_of_eventuallyEq g γ heq, covDerivAlong_smul]
  have hv := curveVelocity_contMDiffAt hγ
  rw [covDerivAlong_curvature_of_eq_zero g J (curveVelocity γ) (curveVelocity γ)
    (hγ.of_le (by norm_num)) hJ hv hv hzero, neg_one_smul]

end DifferentialGeometry.Geometry.Riemannian.Variation
