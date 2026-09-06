import DifferentialGeometry.Geometry.Exponential.Smoothness.Domain
import DifferentialGeometry.Bundle.FiberBundleHausdorff
import DifferentialGeometry.Geometry.Exponential.GaussLemma.Pullback
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Variation
import DifferentialGeometry.Geometry.Comparison.Variation.Field.Smoothness
import DifferentialGeometry.Analysis.Calculus.Cutoff.Clamp.Smooth
import Mathlib.LinearAlgebra.LinearIndependent.Basic

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

omit [I.Boundaryless] [T2Space M] in
theorem radialJacobiField_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) :
    radialJacobiField (I := I) g p x w 0 = 0 := by
  rw [radialJacobiField_eq]
  have hcurve : (fun s : ℝ => expMap (I := I) g p
      (show TangentSpace I p from (0 : ℝ) • (x + s • w))) =
      (fun _ : ℝ => expMap (I := I) g p (0 : TangentSpace I p)) := by
    funext s
    exact congrArg (fun v : E => expMap (I := I) g p (show TangentSpace I p from v))
      (zero_smul ℝ (x + s • w))
  have hmf : (mfderiv 𝓘(ℝ, ℝ) I
      (fun s : ℝ => expMap (I := I) g p (show TangentSpace I p from (0 : ℝ) • (x + s • w)))
      0 : ℝ →L[ℝ] E) = 0 := by
    rw [hcurve]
    exact mfderiv_const
  exact congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hmf

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

theorem isJacobiAt_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    IsJacobiAt (I := I) g
      (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
      (radialJacobiField (I := I) g p x w) t := by
  let γ : ℝ → M := fun r => expMap (I := I) g p (show TangentSpace I p from r • x)
  let J := radialJacobiField (I := I) g p x w
  let U : Set E := {v | (show TangentSpace I p from v) ∈ expDomain (I := I) g p}
  have hU : IsOpen U := by exact isOpen_expDomain (I := I) g p
  obtain ⟨ψ, σ, hψ, hσ, hψev, hσev, hlaunchU⟩ :=
    exists_dom_clamps U hU x w t ht
  let F : ℝ → ℝ → M := fun s r =>
    (expMap (I := I) g p
      (show TangentSpace I p from ψ r • (x + σ s • w)) : M)
  have hlaunch : ∀ s r : ℝ,
      (show TangentSpace I p from ψ r • (x + σ s • w)) ∈
        expDomain (I := I) g p := by
    intro s r
    simpa only [U] using! hlaunchU s r
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
  have hcentral_ev : (fun r : ℝ => F 0 r) =ᶠ[𝓝 t] γ := by
    filter_upwards [hψev] with r ht
    change (expMap (I := I) g p
      (show TangentSpace I p from ψ r • (x + σ 0 • w)) : M) = γ r
    rw [ht, hσ0]
    simp only [id_eq, zero_smul, add_zero, γ]
  let Vc : ∀ r : ℝ, TangentSpace I (F 0 r) := fun r =>
    mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s r) 0 (1 : ℝ)
  have hJ_ev : (fun r : ℝ => (Vc r : E)) =ᶠ[𝓝 t]
      (fun r : ℝ => (J r : E)) := by
    filter_upwards [hψev] with r ht
    have hgerm : (fun s : ℝ => F s r) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ =>
          (expMap (I := I) g p
            (show TangentSpace I p from r • (x + s • w)) : M)) := by
      filter_upwards [hσev] with s hs
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ r • (x + σ s • w)) : M) = _
      rw [ht, hs]
      simp only [id_eq]
    have hmf :
        mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s r) 0 =
          mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
            (expMap (I := I) g p
              (show TangentSpace I p from r • (x + s • w)) : M)) 0 :=
      hgerm.mfderiv_eq
    change ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ => F s r) 0) (1 : ℝ) : E) =
      ((mfderiv (𝓘(ℝ, ℝ)) I (fun s : ℝ =>
        (expMap (I := I) g p
          (show TangentSpace I p from r • (x + s • w)) : M)) 0) (1 : ℝ) : E)
    exact congrArg (fun L : ℝ →L[ℝ] TangentSpace I _ => L (1 : ℝ)) hmf
  have hzero : ∀ s : ℝ,
      covDerivAlong (I := I) g (fun r : ℝ => F s r)
        (fun r : ℝ => mfderiv (𝓘(ℝ, ℝ)) I
          (fun u : ℝ => F s u) r (1 : ℝ)) t = 0 := by
    intro s
    let a : E := x + σ s • w
    have hψt : ψ t = t := by
      simpa only [id_eq] using hψev.eq_of_nhds
    have hatdom : (show TangentSpace I p from t • a) ∈
        expDomain (I := I) g p := by
      simpa only [a, hψt] using hlaunch s t
    have hgeo_raw : HasGeodesicEquationAt (I := I) g
        (fun r : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from r • a) : M)) t :=
      hasGeodesicEquationAt_expMap_smul (I := I) g p (show TangentSpace I p from a) hatdom
    have hF_raw : (fun r : ℝ => F s r) =ᶠ[𝓝 t]
        (fun r : ℝ =>
          (expMap (I := I) g p (show TangentSpace I p from r • a) : M)) := by
      filter_upwards [hψev] with r ht
      change (expMap (I := I) g p
        (show TangentSpace I p from ψ r • (x + σ s • w)) : M) = _
      rw [ht]
      simp only [id_eq, a]
    have hgeo_F : HasGeodesicEquationAt (I := I) g (fun r : ℝ => F s r) t :=
      HasGeodesicEquationAt.congr_of_eventuallyEq_at
        hF_raw.eq_of_nhds hF_raw hgeo_raw
    have hincl : ContMDiff 𝓘(ℝ, ℝ)
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (8 : ℕ)
        (fun r : ℝ => (s, r)) := contMDiff_const.prodMk contMDiff_id
    have hsliceC2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun r : ℝ => F s r) t :=
      ((hFsmooth : ContMDiff _ _ _ _).comp hincl).contMDiffAt.of_le (by norm_num)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2
      (I := I) g _ t hsliceC2 hgeo_F
  have hjac_clamped := isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero
    (I := I) g F hFsmooth t hzero
  exact hjac_clamped.congr_of_eventuallyEq (by
    filter_upwards [hcentral_ev, hJ_ev] with r hcurve hfield
    exact Bundle.TotalSpace.ext hcurve (heq_of_eq hfield))

variable [T2Space (TangentBundle I M)]

omit [T2Space M] in
theorem contMDiffAt_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r => (Bundle.TotalSpace.mk' E
        (expMap (I := I) g p (show TangentSpace I p from r • x))
        (radialJacobiField (I := I) g p x w r) : TangentBundle I M)) t := by
  let f : ℝ → ℝ → M := fun s r =>
    expMap (I := I) g p (show TangentSpace I p from r • (x + s • w))
  have hlaunch : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E) ∞
      (fun q : ℝ × ℝ => q.2 • (x + q.1 • w)) :=
    contMDiff_snd.smul (contMDiff_const.add (contMDiff_fst.smul contMDiff_const))
  have hf : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I ∞
      (fun q : ℝ × ℝ => f q.1 q.2) (0, t) := by
    have hdom : (show TangentSpace I p from t • (x + (0 : ℝ) • w)) ∈
        expDomain (I := I) g p := by simpa only [zero_smul, add_zero] using ht
    exact (contMDiffAt_expMap (I := I) g p hdom).comp (0, t) hlaunch.contMDiffAt
  have heq :
      (fun r => (Bundle.TotalSpace.mk' E
        (expMap (I := I) g p (show TangentSpace I p from r • x))
        (radialJacobiField (I := I) g p x w r) : TangentBundle I M)) =
      (fun r => (Bundle.TotalSpace.mk' E (f 0 r)
        (mfderiv 𝓘(ℝ, ℝ) I (fun s => f s r) 0 (1 : ℝ)) : TangentBundle I M)) := by
    funext r
    apply Bundle.TotalSpace.ext
    · simp only [f, zero_smul, add_zero]
      rfl
    · exact heq_of_eq (radialJacobiField_eq (I := I) g p x w r)
  rw [heq]
  exact varField_smoothAt (I := I) f hf

omit [T2Space M] in
theorem differentiableAt_chartRep_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    DifferentiableAt ℝ
      (chartRepAt (I := I)
        (fun u : ℝ => expMap (I := I) g p (show TangentSpace I p from u • x))
        (radialJacobiField (I := I) g p x w) t) t := by
  exact (mdifferentiableAt_tangentField_iff.mp
    ((contMDiffAt_radialJacobiField (I := I) g p x w ht).mdifferentiableAt (by simp))).2

omit [T2Space M] in
theorem differentiableAt_chartRep_covDerivAlong_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun u => expMap (I := I) g p (show TangentSpace I p from u • x)
    DifferentiableAt ℝ
      (chartRepAt (I := I) γ
        (fun u => covDerivAlong (I := I) g γ (radialJacobiField (I := I) g p x w) u) t) t := by
  exact (mdifferentiableAt_tangentField_iff.mp
    ((contMDiffAt_covDerivAlong (I := I) g (m := ⊤) (n := ⊤) (by simp)
      (contMDiffAt_radialJacobiField (I := I) g p x w ht)).mdifferentiableAt (by simp))).2

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

omit [T2Space M] in
theorem linearIndependent_radialJacobiField
    {ι : Type*} {v : ι → E}
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) {t : ℝ}
    (hv : LinearIndependent ℝ v) (ht : t ≠ 0)
    (hdom : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun b : E => expMap (I := I) g p (show TangentSpace I p from b)) (t • x))) :
    LinearIndependent ℝ (fun i => radialJacobiField (I := I) g p x (v i) t) := by
  let L := mfderiv 𝓘(ℝ, E) I
    (fun b : E => expMap (I := I) g p (show TangentSpace I p from b)) (t • x)
  have hscaled : LinearIndependent ℝ (fun i => t • v i) :=
    hv.units_smul (fun _ => Units.mk0 t ht)
  have hmapped : LinearIndependent ℝ (fun i => L (t • v i)) :=
    hscaled.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have hfield : (fun i => radialJacobiField (I := I) g p x (v i) t) =
      fun i => L (t • v i) := by
    funext i
    exact radialJacobiField_eq_mfderiv_expMap (I := I) g p x (v i) t hdom
  rw [hfield]
  exact hmapped

omit [T2Space M] in
theorem inner_curveVelocity_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun r => expMap (I := I) g p (show TangentSpace I p from r • x)
    g.inner (γ t) (curveVelocity (I := I) γ t) (radialJacobiField (I := I) g p x w t) =
      t * g.inner p x w := by
  let A : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
    (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • x)
  let G : E →L[ℝ] E →L[ℝ] ℝ :=
    g.inner (expMap (I := I) g p (show TangentSpace I p from t • x))
  have hv := mfderiv_expMap_smul (I := I) g p x t ht
  have hJ := radialJacobiField_eq_mfderiv_expMap (I := I) g p x w t ht
  have hg : G (A x) (A w) = g.inner p x w := gauss_lemma_smul (I := I) g p x w ht
  have hscaled : G (A x) (A (t • w)) = t * g.inner p x w := by
    rw [A.map_smul, map_smul, smul_eq_mul, hg]
  exact (congrArg₂ (fun v w : E => G v w) hv hJ).trans hscaled

omit [T2Space M] in
theorem inner_curveVelocity_covDerivAlong_radialJacobiField
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    let γ : ℝ → M := fun r => expMap (I := I) g p (show TangentSpace I p from r • x)
    g.inner (γ t) (curveVelocity (I := I) γ t)
      (covDerivAlong (I := I) g γ (radialJacobiField (I := I) g p x w) t) =
      g.inner p x w := by
  let γ : ℝ → M := fun r => expMap (I := I) g p (show TangentSpace I p from r • x)
  let J := radialJacobiField (I := I) g p x w
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ t :=
    ((contMDiffAt_expMap (I := I) g p ht).comp t
      (contMDiff_id.smul (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun _ : ℝ => x))).contMDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hd := inner_deriv_at (I := I) (n := 2) (by norm_num) g γ
    (curveVelocity (I := I) γ) J t hγ (differentiableAt_chartRepAt_curveVelocity hγ)
    (differentiableAt_chartRep_radialJacobiField (I := I) g p x w ht)
  have hpar := covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 (I := I) g γ t hγ
    (hasGeodesicEquationAt_expMap_smul (I := I) g p x ht)
  change covDerivAlong (I := I) g γ (curveVelocity (I := I) γ) t = 0 at hpar
  rw [hpar, map_zero, zero_apply, zero_add] at hd
  have hU : IsOpen {r : ℝ | (show TangentSpace I p from r • x) ∈ expDomain (I := I) g p} := by
    have hUE : IsOpen {v : E | (show TangentSpace I p from v) ∈ expDomain (I := I) g p} :=
      isOpen_expDomain (I := I) g p
    exact hUE.preimage (continuous_id.smul (continuous_const : Continuous (fun _ : ℝ => x)))
  have heq : (fun r => g.inner (γ r) (curveVelocity (I := I) γ r) (J r)) =ᶠ[𝓝 t]
      (fun r => r * g.inner p x w) := by
    filter_upwards [hU.mem_nhds ht] with r hr
    exact inner_curveVelocity_radialJacobiField (I := I) g p x w hr
  exact hd.unique ((hasDerivAt_mul_const (g.inner p x w)).congr_of_eventuallyEq heq)

omit [T2Space M] in
theorem jacobiWronskian_radialJacobiField_eq_zero
    (g : SmoothRiemannianMetric I M) (p : M) (x w z : E) {t : ℝ}
    (ht : (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    jacobiWronskian (I := I) g
      (fun r => expMap (I := I) g p (show TangentSpace I p from r • x))
      (radialJacobiField (I := I) g p x w) (radialJacobiField (I := I) g p x z) t = 0 := by
  have : T2Space M := gauss_t2Space_base (I := I)
  obtain ⟨η, S, hS, hconn, h0S, htS, hη⟩ := smul_mem_expDomain_iff.mp ht
  have hdom r (hr : r ∈ uIcc (0 : ℝ) t) :
      (show TangentSpace I p from r • x) ∈ expDomain (I := I) g p :=
    smul_mem_expDomain_iff.mpr
      ⟨η, S, hS, hconn, h0S, hconn.ordConnected.uIcc_subset h0S htS hr, hη⟩
  let γ : ℝ → M := fun r => expMap (I := I) g p (show TangentSpace I p from r • x)
  have hγ r (hr : r ∈ uIcc (0 : ℝ) t) : ContMDiffAt 𝓘(ℝ, ℝ) I 1 γ r :=
    ((contMDiffAt_expMap (I := I) g p (hdom r hr)).comp r
      (contMDiff_id.smul (contMDiff_const : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun _ : ℝ => x))).contMDiffAt).of_le (WithTop.coe_le_coe.mpr le_top)
  have hJ (v : E) r (hr : r ∈ uIcc (0 : ℝ) t) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
        (fun s => (Bundle.TotalSpace.mk' E (γ s) (radialJacobiField (I := I) g p x v s) :
          TangentBundle I M)) r :=
    (contMDiffAt_radialJacobiField (I := I) g p x v (hdom r hr)).mdifferentiableAt (by simp)
  have hDJ (v : E) r (hr : r ∈ uIcc (0 : ℝ) t) :
      MDifferentiableAt 𝓘(ℝ, ℝ) I.tangent
        (fun s => (Bundle.TotalSpace.mk' E (γ s)
          (covDerivAlong (I := I) g γ (radialJacobiField (I := I) g p x v) s) :
            TangentBundle I M)) r :=
    (contMDiffAt_covDerivAlong (I := I) g (m := ⊤) (n := ⊤) (by simp)
      (contMDiffAt_radialJacobiField (I := I) g p x v (hdom r hr))).mdifferentiableAt (by simp)
  exact jacobiWronskian_eq_zero_of_isJacobiAt (I := I) g γ
    (radialJacobiField (I := I) g p x w) (radialJacobiField (I := I) g p x z)
    (convex_Icc _ _) hγ (hJ w) (hJ z) (hDJ w) (hDJ z)
    (fun r hr => isJacobiAt_radialJacobiField (I := I) g p x w (hdom r (interior_subset hr)))
    (fun r hr => isJacobiAt_radialJacobiField (I := I) g p x z (hdom r (interior_subset hr)))
    left_mem_uIcc right_mem_uIcc (radialJacobiField_zero (I := I) g p x w)
      (radialJacobiField_zero (I := I) g p x z)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
