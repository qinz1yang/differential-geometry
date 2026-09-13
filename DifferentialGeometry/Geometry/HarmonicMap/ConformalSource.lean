import DifferentialGeometry.Geometry.HarmonicMap.Coordinates
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Tactic.Module

noncomputable section
open Set Filter Bundle Manifold InnerProductSpace
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

private theorem complex_decompose (z : ℂ) :
    z = z.re • (1 : ℂ) + z.im • Complex.I := by
  simp [Complex.real_smul]

private theorem complex_mul_I_decompose (z : ℂ) :
    z * Complex.I = -z.im • (1 : ℂ) + z.re • Complex.I := by
  apply Complex.ext <;> simp [Complex.real_smul]

private theorem bilin_trace_mul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] V) (d : ℂ) :
    B d d + B (d * Complex.I) (d * Complex.I) =
      ‖d‖ ^ 2 • (B 1 1 + B Complex.I Complex.I) := by
  rw [complex_mul_I_decompose, complex_decompose d]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  simp only [← complex_decompose d, Complex.sq_norm, Complex.normSq_apply]
  module

private theorem real_deriv_apply {ψ : ℂ → ℂ} {z : ℂ}
    (hψ : DifferentiableAt ℂ ψ z) (v : ℂ) :
    fderiv ℝ ψ z v = deriv ψ z * v := by
  rw [(hψ.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [mul_comm]

private theorem bilin_trace_std {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] V) :
    (∑ i : Fin (Module.finrank ℝ ℂ), B (stdOrthonormalBasis ℝ ℂ i)
      (stdOrthonormalBasis ℝ ℂ i)) = B 1 1 + B Complex.I Complex.I := by
  calc
    _ = TensorProduct.lift B (canonicalCovariantTensor ℂ) := by
      rw [canonicalCovariantTensor_eq_sum ℂ (stdOrthonormalBasis ℝ ℂ)]
      simp
    _ = _ := by
      rw [canonicalCovariantTensor_eq_sum ℂ Complex.orthonormalBasisOneI]
      simp

private theorem laplacian_comp_complex {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {Y : ℂ → V} {ψ : ℂ → ℂ} {z : ℂ}
    (hY : ContDiffAt ℝ 2 Y (ψ z)) (hψ : ContDiffAt ℂ 2 ψ z) :
    Laplacian.laplacian (Y ∘ ψ) z = ‖deriv ψ z‖ ^ 2 • Laplacian.laplacian Y (ψ z) := by
  let B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] V := LinearMap.mk₂ ℝ
    (fun v w => fderiv ℝ (fderiv ℝ Y) (ψ z) (fderiv ℝ ψ z v) (fderiv ℝ ψ z w))
    (by intros; simp only [map_add, _root_.add_apply])
    (by intros; simp only [map_smul, _root_.smul_apply])
    (by intros; simp only [map_add]) (by intros; simp only [map_smul])
  have hsum := bilin_trace_std B
  have hrot := bilin_trace_mul (LinearMap.mk₂ ℝ
    (fun v w => fderiv ℝ (fderiv ℝ Y) (ψ z) v w)
    (by intros; simp only [map_add, _root_.add_apply])
    (by intros; simp only [map_smul, _root_.smul_apply])
    (by intros; simp only [map_add]) (by intros; simp only [map_smul])) (deriv ψ z)
  dsimp only [B, LinearMap.mk₂_apply] at hsum hrot
  rw [(hψ.restrict_scalars ℝ).laplacian_comp hY,
    hψ.harmonicAt.2.eq_of_nhds, Pi.zero_apply, map_zero, zero_add, hsum]
  simp only [real_deriv_apply (hψ.differentiableAt (by norm_num)), mul_one]
  rw [hrot, laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply]
  rfl

open Riemannian.Geodesic Riemannian.AlongCurve Riemannian.CovariantDerivativeAlong

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chart_planarTension [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U z) {a : M}
    (hsrc : U z ∈ (chartAt H a).source) :
    let X : ℂ → E := (extChartAt I a) ∘ U
    (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)
        (planarTension g U z) = Laplacian.laplacian X z +
      chartChristoffelContraction g a (fderiv ℝ X z 1) (fderiv ℝ X z 1) (X z) +
      chartChristoffelContraction g a (fderiv ℝ X z Complex.I)
        (fderiv ℝ X z Complex.I) (X z) := by
  obtain ⟨s, hs, hUs⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by norm_num)).mp hU
  obtain ⟨s', hsub, ho, hz⟩ := mem_nhds_iff.mp hs
  let r := s' ∩ U ⁻¹' (chartAt H a).source
  have hr : IsOpen r := (hUs.mono hsub).continuousOn.isOpen_inter_preimage ho
    (chartAt H a).open_source
  have hz' : z ∈ r := ⟨hz, hsrc⟩
  have hUr := (hUs.mono hsub).mono (show r ⊆ s' from inter_subset_left)
  let X : ℂ → E := (extChartAt I a) ∘ U
  have hX : ContDiffAt ℝ 2 X z :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) hsrc).comp z hU).contDiffAt
  have hpartial (v w : ℂ) : fderiv ℝ (fun q => fderiv ℝ X q w) z v =
      fderiv ℝ (fderiv ℝ X) z v w := by
    rw [fderiv_clm_apply ((hX.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp))
      (differentiableAt_const w)]
    simp
  have hpair (v : ℂ) :
      (trivializationAt E (TangentSpace I) a).continuousLinearMapAt ℝ (U z)
        (planarCovDeriv g U z v v) =
      fderiv ℝ (fun q => fderiv ℝ X q v) z v +
        chartChristoffelContraction g a (fderiv ℝ X z v) (fderiv ℝ X z v) (X z) := by
    have hh := chart_covDerivAlong_mfderiv_line g hr hUr (fun _ ht => ht.2) hz' v v
    dsimp only at hh
    erw [zero_smul, add_zero] at hh
    exact hh
  dsimp only
  rw [planarTension, map_add, hpair, hpair, hpartial, hpartial,
    laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, X]
  ac_rfl

private theorem christoffel_trace_mul (g : SmoothRiemannianMetric I M) (a : M)
    (D : ℂ →L[ℝ] E) (x : E) (d : ℂ) :
    chartChristoffelContraction g a (D d) (D d) x +
      chartChristoffelContraction g a (D (d * Complex.I)) (D (d * Complex.I)) x =
    ‖d‖ ^ 2 • (chartChristoffelContraction g a (D 1) (D 1) x +
      chartChristoffelContraction g a (D Complex.I) (D Complex.I) x) := by
  let B : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] E := LinearMap.mk₂ ℝ
    (fun v w => chartChristoffelContraction g a (D v) (D w) x)
    (by intros; rw [map_add, ChartChristoffel.contraction_add_left])
    (by intros; rw [map_smul, ChartChristoffel.contraction_smul_left])
    (by intros; rw [map_add, ChartChristoffel.contraction_add_right])
    (by intros; rw [map_smul, ChartChristoffel.contraction_smul_right])
  exact bilin_trace_mul B d

theorem planarTension_comp_holomorphic [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {U : ℂ → M} {ψ : ℂ → ℂ} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) I 2 U (ψ z)) (hψ : AnalyticAt ℂ ψ z) :
    planarTension g (U ∘ ψ) z = ‖deriv ψ z‖ ^ 2 • planarTension g U (ψ z) := by
  let a := U (ψ z)
  let X : ℂ → E := (extChartAt I a) ∘ U
  have hsrc : U (ψ z) ∈ (chartAt H a).source := mem_chart_source H a
  have hX : ContDiffAt ℝ 2 X (ψ z) :=
    ((contMDiffAt_extChartAt' (I := I) (n := 2) hsrc).comp (ψ z) hU).contDiffAt
  have hc : ContMDiffAt 𝓘(ℝ, ℂ) I 2 (U ∘ ψ) z :=
    hU.comp z (hψ.contDiffAt.restrict_scalars ℝ).contMDiffAt
  have hpull (v : ℂ) : fderiv ℝ (X ∘ ψ) z v =
      fderiv ℝ X (ψ z) (deriv ψ z * v) := by
    rw [fderiv_comp z (hX.differentiableAt (by norm_num))
      (hψ.differentiableAt.restrictScalars ℝ), ContinuousLinearMap.comp_apply,
      real_deriv_apply hψ.differentiableAt]
  have hT := chart_planarTension g hU hsrc
  have hTc := chart_planarTension g hc hsrc
  dsimp only at hT hTc
  simp only [Function.comp_apply] at hTc
  have hb : U (ψ z) ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hsrc
  apply (trivializationAt E (TangentSpace I) a).continuousLinearEquivAt ℝ (U (ψ z)) hb |>.injective
  simp only [Trivialization.coe_continuousLinearEquivAt_eq _ hb]
  rw [map_smul, hT, hTc]
  change Laplacian.laplacian (X ∘ ψ) z +
    chartChristoffelContraction g a (fderiv ℝ (X ∘ ψ) z 1) (fderiv ℝ (X ∘ ψ) z 1) (X (ψ z)) +
    chartChristoffelContraction g a (fderiv ℝ (X ∘ ψ) z Complex.I)
      (fderiv ℝ (X ∘ ψ) z Complex.I) (X (ψ z)) = _
  rw [laplacian_comp_complex hX hψ.contDiffAt, hpull, hpull]
  simp only [mul_one]
  rw [add_assoc, christoffel_trace_mul, smul_add, ← add_assoc]
  simp only [smul_add, X]

omit [FiniteDimensional ℝ E] in
theorem conformal_mfderiv_comp_complex (g : SmoothRiemannianMetric I M)
    {U : ℂ → M} {ψ : ℂ → ℂ} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) I U (ψ z)) (hψ : DifferentiableAt ℂ ψ z)
    (ho : g.inner (U (ψ z)) (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) Complex.I) = 0)
    (he : g.inner (U (ψ z)) (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) (1 : ℂ)) =
      g.inner (U (ψ z)) (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) Complex.I)
        (mfderiv 𝓘(ℝ, ℂ) I U (ψ z) Complex.I)) :
    g.inner ((U ∘ ψ) z) (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z Complex.I) = 0 ∧
      g.inner ((U ∘ ψ) z) (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z (1 : ℂ)) =
      g.inner ((U ∘ ψ) z) (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z Complex.I)
        (mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z Complex.I) := by
  have hD (v : ℂ) : mfderiv 𝓘(ℝ, ℂ) I (U ∘ ψ) z v =
      mfderiv 𝓘(ℝ, ℂ) I U (ψ z) (deriv ψ z * v) := by
    have hd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z v = deriv ψ z * v := by
      rw [mfderiv_eq_fderiv]
      exact real_deriv_apply hψ v
    exact (mfderiv_comp_apply z hU (hψ.restrictScalars ℝ).mdifferentiableAt v).trans
      (congrArg (mfderiv 𝓘(ℝ, ℂ) I U (ψ z)) hd)
  let D : ℂ →L[ℝ] E := mfderiv 𝓘(ℝ, ℂ) I U (ψ z)
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner (U (ψ z))
  have hsym : B (D Complex.I) (D 1) = B (D 1) (D Complex.I) := g.symm _ _ _
  change B (D 1) (D Complex.I) = 0 at ho
  change B (D 1) (D 1) = B (D Complex.I) (D Complex.I) at he
  simp only [hD, mul_one, Function.comp_apply]
  change B (D (deriv ψ z)) (D (deriv ψ z * Complex.I)) = 0 ∧
    B (D (deriv ψ z)) (D (deriv ψ z)) =
      B (D (deriv ψ z * Complex.I)) (D (deriv ψ z * Complex.I))
  rw [complex_mul_I_decompose, complex_decompose (deriv ψ z)]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  rw [hsym, ho, he]
  simp only [← complex_decompose (deriv ψ z)]
  constructor <;> ring

end DifferentialGeometry.Geometry
