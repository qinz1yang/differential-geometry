import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Variation
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth

open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open AlongCurve CovariantDerivativeAlong Variation Geodesic Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

noncomputable def radialJacobiField (g : SmoothRiemannianMetric I M) (p : M)
    (x w : E) (t : ℝ) :
    TangentSpace I
      ((expMap (I := I) g p (show TangentSpace I p from (t • x)) : M)) :=
  (tangentSpaceModelContinuousLinearEquiv (I := I)
      (expMap (I := I) g p (show TangentSpace I p from (t • x)))).symm
    (tangentSpaceModelContinuousLinearEquiv (I := I)
      (expMap (I := I) g p
        (show TangentSpace I p from (t • (x + (0 : ℝ) • w))))
      (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from (t • (x + s • w))) : M)) 0 (1 : ℝ)))

omit [I.Boundaryless] [T2Space M] in
lemma radialJacobiField_eq
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ) :
    radialJacobiField (I := I) g p x w t =
      (show TangentSpace I
          (expMap (I := I) g p (show TangentSpace I p from (t • x))) from
        mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from (t • (x + s • w))) : M)) 0 (1 : ℝ)) := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I)
    (expMap (I := I) g p (show TangentSpace I p from (t • x)))).injective
  rw [radialJacobiField, ContinuousLinearEquiv.apply_symm_apply]
  have hbase :
      (expMap (I := I) g p
          (show TangentSpace I p from (t • (x + (0 : ℝ) • w))) : M) =
        expMap (I := I) g p (show TangentSpace I p from (t • x)) := by
    apply congrArg (fun z : E =>
      (expMap (I := I) g p (show TangentSpace I p from z) : M))
    module
  rw [hbase]

omit [FiniteDimensional ℝ E] in
private theorem exists_dom_clamps
    (U : Set E) (hU : IsOpen U) (x w : E) (t₀ : ℝ) (hx : t₀ • x ∈ U) :
    ∃ ψ σ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ ∧ ContDiff ℝ ∞ σ ∧
      ψ =ᶠ[𝓝 t₀] id ∧ σ =ᶠ[𝓝 (0 : ℝ)] id ∧
      ∀ s t : ℝ, ψ t • (x + σ s • w) ∈ U := by
  have hcont : ContinuousAt (fun q : ℝ × ℝ => q.2 • (x + q.1 • w)) (0, t₀) :=
    (continuous_snd.smul (continuous_const.add (continuous_fst.smul continuous_const))).continuousAt
  have hmem : U ∈ 𝓝 ((fun q : ℝ × ℝ => q.2 • (x + q.1 • w)) (0, t₀)) := by
    simpa only [zero_smul, add_zero] using hU.mem_nhds hx
  obtain ⟨σ, ψ, hσ, hψ, hσid, hψid, h⟩ :=
    exists_contDiff_prodMap_range_subset (hcont hmem)
  exact ⟨ψ, σ, hψ, hσ, hψid, hσid, fun s t => h ⟨(s, t), rfl⟩⟩

private lemma riemannOp_congr_point (g : SmoothRiemannianMetric I M)
    {x y : M} (h : x = y)
    (A B C : TangentSpace I x) (A' B' C' : TangentSpace I y)
    (hA : (A : E) = (A' : E)) (hB : (B : E) = (B' : E))
    (hC : (C : E) = (C' : E)) :
    ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) x) A B C : E)
    = ((DifferentialGeometry.Geometry.Curvature.riemannOp
      (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) y) A' B' C' : E) := by
  subst y
  rw [show A = A' from hA, show B = B' from hB, show C = C' from hC]

private theorem radialJacobiField_properties
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t₀ : ℝ}
    (ht₀U : (show TangentSpace I p from t₀ • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun t => expMap (I := I) g p (show TangentSpace I p from t • x)
    let J := radialJacobiField (I := I) g p x w
    DifferentiableAt ℝ (chartRepAt (I := I) γ J t₀) t₀ ∧
    DifferentiableAt ℝ (chartRepAt (I := I) γ
      (fun u => covDerivAlong (I := I) g γ J u) t₀) t₀ ∧
    IsJacobiAt (I := I) g γ J t₀ := by
  let γ : ℝ → M := fun t => expMap (I := I) g p (show TangentSpace I p from t • x)
  let J := radialJacobiField (I := I) g p x w
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by exact isOpen_expDomain (I := I) g p
  obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
    exists_dom_clamps U hU x w t₀ ht₀U
  let F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ s • w)) : M)
  have hlaunch : ∀ s t : ℝ,
      (show TangentSpace I p from ψ t • (x + σ s • w)) ∈
        expDomain (I := I) g p := by
    intro s t
    simpa only [U] using! hlaunchU s t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]
      exact hψ
    have hσMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := by
      rw [contMDiff_iff_contDiff]
      exact hσ
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + σ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hσMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun a : E =>
          (expMap (I := I) g p (show TangentSpace I p from a) : M))
        (ψ q.2 • (x + σ q.1 • w)) :=
      (contMDiffAt_expMap (I := I) g p (hlaunch q.1 q.2)).of_le
        ENat.LEInfty.out
    exact hexp.comp q (hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out)
  have hσ0 : σ 0 = 0 := by
    simpa only [id_eq] using hσev.eq_of_nhds
  have hcentral_ev : (fun t : ℝ => F 0 t) =ᶠ[𝓝 t₀] γ := by
    filter_upwards [hψev] with t ht
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ 0 • w)) : M) = γ t
    rw [ht, hσ0]
    simp only [id_eq, zero_smul, add_zero, γ]
  let Vc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 (1 : ℝ)
  have hJ_ev : (fun t : ℝ => (Vc t : E)) =ᶠ[𝓝 t₀]
      (fun t : ℝ => (J t : E)) := by
    filter_upwards [hψev] with t ht
    have hgerm : (fun s : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) := by
      filter_upwards [hσev] with s hs
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht, hs]
      simp only [id_eq]
    have hmf :
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 =
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • (x + s • w)) : M)) 0 :=
      hgerm.mfderiv_eq
    change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0) (1 : ℝ) : E) =
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0) (1 : ℝ) : E)
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
  let Dc : ∀ t : ℝ, TangentSpace I (F 0 t) := fun t =>
    covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t
  let D : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    covDerivAlong (I := I) g γ J t
  have hD_ev : ∀ᶠ t in 𝓝 t₀, (Dc t : E) = (D t : E) := by
    filter_upwards [hcentral_ev.eventually_nhds, hJ_ev.eventually_nhds]
      with t hcurve hfield
    exact covDerivAlong_congr_curve (I := I) g Vc J hcurve hfield
  have hVdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ J t₀) t₀ := by
    have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun t : ℝ => F 0 t) Vc t₀) t₀ := by
      exact variationField_chartRep_differentiableAt (I := I) F hFsmooth t₀
    have hrep := chartRep_congr_curve (I := I) Vc J hcentral_ev hJ_ev
    exact hrep.differentiableAt_iff.mp hclamped
  have hDVdiff : DifferentiableAt ℝ
      (chartRepAt (I := I) γ D t₀) t₀ := by
    have hclamped : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun t : ℝ => F 0 t) Dc t₀) t₀ := by
      exact variationField_covDeriv_chartRep_differentiableAt
        (I := I) g F hFsmooth t₀
    have hrep := chartRep_congr_curve (I := I) Dc D hcentral_ev hD_ev
    exact hrep.differentiableAt_iff.mp hclamped
  have hzero : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun t : ℝ => F s t)
        (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) t (1 : ℝ)) t₀ = 0 := by
    intro s
    let a : E := x + σ s • w
    have hψt₀ : ψ t₀ = t₀ := by
      simpa only [id_eq] using hψev.eq_of_nhds
    have hatdom : (show TangentSpace I p from t₀ • a) ∈
        expDomain (I := I) g p := by
      simpa only [a, hψt₀] using hlaunch s t₀
    have hgeo_raw : HasGeodesicEquationAt (I := I) g
        (fun t : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from t • a) : M)) t₀ :=
      hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from a) hatdom
    have hF_raw : (fun t : ℝ => F s t) =ᶠ[𝓝 t₀]
        (fun t : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from t • a) : M)) := by
      filter_upwards [hψev] with t ht
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht]
      simp only [id_eq, a]
    have hgeo_F : HasGeodesicEquationAt (I := I) g (fun t : ℝ => F s t) t₀ :=
      HasGeodesicEquationAt.congr_of_eventuallyEq_at
        hF_raw.eq_of_nhds hF_raw hgeo_raw
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun t : ℝ => (s, t)) := contMDiff_const.prodMk contMDiff_id
    have hsliceC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun t : ℝ => F s t) t₀ :=
      ((hFsmooth : ContMDiff _ _ _ _).comp hincl).contMDiffAt.of_le (by norm_num)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g _ t₀ hsliceC2 hgeo_F
  have hjac_clamped := isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero
    (I := I) g F hFsmooth t₀ hzero
  have houter_eq :
      ((covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
        (fun t : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t)
        t₀ : E))
      = ((covDerivAlong (I := I) g γ
        (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀ : E)) :=
    covDerivAlong_congr_curve (I := I) g Dc D hcentral_ev hD_ev
  have hfoot : F 0 t₀ = γ t₀ := hcentral_ev.eq_of_nhds
  have hfield : (Vc t₀ : E) = (J t₀ : E) := hJ_ev.eq_of_nhds
  have hvelocity :
      (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ) : E)
        = (curveVelocity (I := I) γ t₀ : E) := by
    have hmf : mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ =
        mfderiv (𝓘(ℝ, ℝ)) I γ t₀ := hcentral_ev.mfderiv_eq
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => (L (1 : ℝ) : E)) hmf
  have hfinal :
      (covDerivAlong (I := I) g γ
        (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀ : E)
      = -((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
          (J t₀) (curveVelocity (I := I) γ t₀)
          (curveVelocity (I := I) γ t₀) : E) := by
    rw [← houter_eq]
    change (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
        (fun t : ℝ => covDerivAlong (I := I) g
          (fun u : ℝ => F 0 u) Vc t) t₀ : E)
      = -((DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
          (J t₀) (curveVelocity (I := I) γ t₀)
          (curveVelocity (I := I) γ t₀) : E)
    have hclamped :
        (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => covDerivAlong (I := I) g
            (fun u : ℝ => F 0 u) Vc t) t₀ : E)
        = -((DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
            (Vc t₀)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ)) : E) := by
      change covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => covDerivAlong (I := I) g (fun u : ℝ => F 0 u) Vc t) t₀
        + (DifferentialGeometry.Geometry.Curvature.riemannOp
            (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (F 0 t₀))
            (Vc t₀)
            (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ))
            (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F 0 t) t₀ (1 : ℝ)) = 0
        at hjac_clamped
      linear_combination (norm := module) hjac_clamped
    rw [hclamped]
    exact congrArg Neg.neg
      (riemannOp_congr_point (I := I) g hfoot _ _ _ _ _ _ hfield hvelocity hvelocity)
  have hJ : IsJacobiAt (I := I) g γ J t₀ := by
    change covDerivAlong (I := I) g γ
        (fun t : ℝ => covDerivAlong (I := I) g γ J t) t₀
      + (DifferentialGeometry.Geometry.Curvature.riemannOp
          (DifferentialGeometry.Geometry.Connection.LeviCivita (I := I) g) (γ t₀))
          (J t₀) (curveVelocity (I := I) γ t₀)
          (curveVelocity (I := I) γ t₀) = 0
    linear_combination (norm := module) hfinal
  exact ⟨hVdiff, hDVdiff, hJ⟩

variable [T2Space (TangentBundle I M)]

omit [T2Space M] in
theorem differentiableAt_chartRep_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    DifferentiableAt ℝ
      (chartRepAt (I := I)
        (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
        (radialJacobiField (I := I) g p x w) t) t := by
  have : T2Space M := gauss_t2Space_base (I := I)
  exact (radialJacobiField_properties (I := I) g p x w ht).1

omit [T2Space M] in
theorem differentiableAt_chartRep_covDerivAlong_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun u => expMap (I := I) g p (show TangentSpace I p from u • x)
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun u => covDerivAlong (I := I) g γ (radialJacobiField (I := I) g p x w) u) t) t := by
  have : T2Space M := gauss_t2Space_base (I := I)
  exact (radialJacobiField_properties (I := I) g p x w ht).2.1

omit [T2Space (TangentBundle I M)] in
theorem isJacobiAt_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    IsJacobiAt (I := I) g
      (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
      (radialJacobiField (I := I) g p x w) t :=
  (radialJacobiField_properties (I := I) g p x w ht).2.2

omit [T2Space (TangentBundle I M)] in
theorem isJacobiAt_radialJacobiField_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    IsJacobiAt (I := I) g
      (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
      (radialJacobiField (I := I) g p x w) 0 :=
  isJacobiAt_radialJacobiField (I := I) g p x w
    (by simpa only [zero_smul] using! zero_mem_expDomain (I := I) g p)

omit [T2Space M] in
theorem covDerivAlong_radialJacobiField_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    (covDerivAlong (I := I) g
      (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
      (radialJacobiField (I := I) g p x w) 0 : E) = w := by
  let _ := FiniteDimensional.complete ℝ E
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by
    exact isOpen_expDomain (I := I) g p
  have hzeroU : (0 : ℝ) • x ∈ U := by
    simpa only [U, zero_smul] using! zero_mem_expDomain (I := I) g p
  obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
    exists_dom_clamps U hU x w 0 hzeroU
  let F : ℝ → ℝ → M := fun s t =>
    (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ s • w)) : M)
  have hlaunch : ∀ s t : ℝ,
      (show TangentSpace I p from ψ t • (x + σ s • w)) ∈
        expDomain (I := I) g p := by
    intro s t
    simpa only [U] using! hlaunchU s t
  have hFsmooth : IsSmoothVariation (I := I) F := by
    have hψMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ := by
      rw [contMDiff_iff_contDiff]
      exact hψ
    have hσMD : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ σ := by
      rw [contMDiff_iff_contDiff]
      exact hσ
    have hlaunchMD : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × ℝ => ψ q.2 • (x + σ q.1 • w)) :=
      (hψMD.comp contMDiff_snd).smul
        (contMDiff_const.add ((hσMD.comp contMDiff_fst).smul contMDiff_const))
    intro q
    have hexp : ContMDiffAt 𝓘(ℝ, E) I (8 : ℕ)
        (fun a : E =>
          (expMap (I := I) g p (show TangentSpace I p from a) : M))
        (ψ q.2 • (x + σ q.1 • w)) :=
      (contMDiffAt_expMap (I := I) g p (hlaunch q.1 q.2)).of_le
        ENat.LEInfty.out
    exact hexp.comp q (hlaunchMD.contMDiffAt.of_le ENat.LEInfty.out)
  let γ : ℝ → M := fun t =>
    (expMap (I := I) g p (show TangentSpace I p from t • x) : M)
  let J : ∀ t : ℝ, TangentSpace I (γ t) := fun t =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
      (expMap (I := I) g p
        (show TangentSpace I p from t • (x + s • w)) : M)) 0 (1 : ℝ)
  have hψ0 : ψ 0 = 0 := by
    simpa only [id_eq] using hψev.eq_of_nhds
  have hσ0 : σ 0 = 0 := by
    simpa only [id_eq] using hσev.eq_of_nhds
  have hcentral_ev : (fun t : ℝ => F 0 t) =ᶠ[𝓝 (0 : ℝ)] γ := by
    filter_upwards [hψev] with t ht
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ t • (x + σ 0 • w)) : M) = γ t
    rw [ht, hσ0]
    simp only [id_eq, zero_smul, add_zero, γ]
  have hJ_ev : (fun t : ℝ =>
      (mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 (1 : ℝ) : E)) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ => (J t : E)) := by
    filter_upwards [hψev] with t ht
    have hgerm : (fun s : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + s • w)) : M)) := by
      filter_upwards [hσev] with s hs
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht, hs]
      simp only [id_eq]
    have hmf :
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0 =
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from t • (x + s • w)) : M)) 0 :=
      hgerm.mfderiv_eq
    change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s t) 0) (1 : ℝ) : E) =
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from t • (x + s • w)) : M)) 0) (1 : ℝ) : E)
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
  have hF0 : ∀ s : ℝ, F s 0 = p := by
    intro s
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ 0 • (x + σ s • w)) : M) = p
    rw [hψ0, zero_smul]
    exact expMap_zero (I := I) g p
  have hF0_ev : (fun s : ℝ => F s 0) =ᶠ[𝓝 (0 : ℝ)] (fun _ : ℝ => p) :=
    Filter.Eventually.of_forall hF0
  have hlaunch_vel : ∀ s : ℝ,
      (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F s t) 0 (1 : ℝ) : E)
        = x + σ s • w := by
    intro s
    have hgerm : (fun t : ℝ => F s t) =ᶠ[𝓝 (0 : ℝ)]
        (fun t : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from t • (x + σ s • w)) : M)) := by
      filter_upwards [hψev] with t ht
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ t • (x + σ s • w)) : M) = _
      rw [ht]
      simp only [id_eq]
    rw [hgerm.mfderiv_eq]
    exact radialCurve_launch_velocity (I := I) g p (x + σ s • w)
  have hlaunch_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      (mfderiv (𝓘(ℝ, ℝ)) I (fun t : ℝ => F s t) 0 (1 : ℝ) : E)
        = ((show TangentSpace I p from x + σ s • w : E)) :=
    Filter.Eventually.of_forall hlaunch_vel
  have hσderiv : HasDerivAt σ 1 0 :=
    (hasDerivAt_id (0 : ℝ)).congr_of_eventuallyEq hσev
  have hline : HasDerivAt (fun s : ℝ => x + σ s • w) w 0 := by
    have h := (hσderiv.smul_const w).const_add x
    simpa using h
  have hLHS := covDerivAlong_congr_curve (I := I) g
    (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun t : ℝ => F s t) 0 (1 : ℝ))
    (fun s : ℝ => (show TangentSpace I p from x + σ s • w)) hF0_ev hlaunch_ev
  have hconst := covDerivAlong_const (I := I) g p
    (fun s : ℝ => (show TangentSpace I p from x + σ s • w)) 0 hline.differentiableAt
  have hcomm := commute_ds_dt_intrinsic (I := I) g F hFsmooth 0
  have hcomm_E :
      (covDerivAlong (I := I) g (fun s : ℝ => F s 0)
          (fun s : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun t : ℝ => F s t) 0 (1 : ℝ)) 0 : E)
        = (covDerivAlong (I := I) g (fun t : ℝ => F 0 t)
          (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
            (fun s : ℝ => F s t) 0 (1 : ℝ)) 0 : E) := by
    rw [hcomm]
  have hRHS := covDerivAlong_congr_curve (I := I) g
    (fun t : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
      (fun s : ℝ => F s t) 0 (1 : ℝ)) J hcentral_ev hJ_ev
  change (covDerivAlong (I := I) g γ J 0 : E) = w
  exact hRHS.symm.trans
    (hcomm_E.symm.trans (hLHS.trans (hconst.trans hline.deriv)))

omit [T2Space M] in
theorem radialJacobiField_eq_mfderiv_expMap
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) (t : ℝ)
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    radialJacobiField (I := I) g p x w t =
      mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
        (t • x) (t • w) := by
  have hfun : (fun s : ℝ =>
      expMap (I := I) g p (show TangentSpace I p from t • (x + s • w))) =
      (fun s : ℝ => expMap (I := I) g p
        (show TangentSpace I p from t • x + s • (t • w))) := by
    funext s
    apply congrArg (fun v : E =>
      expMap (I := I) g p (show TangentSpace I p from v))
    module
  have h := mfderiv_expMap_add_smul (I := I) g p (t • x) (t • w) 0
    (by simpa only [zero_smul, add_zero] using! ht)
  rw [radialJacobiField_eq, hfun]
  have hfoot : (t • x + (0 : ℝ) • (t • w) : E) = t • x := by simp
  have hCLM : (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
      (t • x + (0 : ℝ) • (t • w)) : E →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
        (t • x) : E →L[ℝ] E) := by
    rw [hfoot]
  exact h.trans (congrArg (fun L : E →L[ℝ] E => L (t • w)) hCLM)

omit [T2Space M] in
theorem radialJacobiField_one
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p) :
    radialJacobiField (I := I) g p x w 1 =
      mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x w := by
  have h := radialJacobiField_eq_mfderiv_expMap (I := I) g p x w 1
    (by simpa only [one_smul] using! hx)
  have hCLM : (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
      ((1 : ℝ) • x) : E →L[ℝ] E) =
      (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
        x : E →L[ℝ] E) := by rw [one_smul]
  exact h.trans ((congrArg (fun L : E →L[ℝ] E => L ((1 : ℝ) • w)) hCLM).trans
    (congrArg
      (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x)
      (one_smul ℝ w)))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
