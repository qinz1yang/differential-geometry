/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Analysis.Complex.FirstOrderSystems.BoundaryUniqueness
import DifferentialGeometry.Analysis.Complex.DiskBoundaryChart
import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientUniqueContinuation
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import Mathlib.Topology.Algebra.Group.Quotient

noncomputable section

open Set Metric Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

private theorem analyticAt_diskBoundaryChart (p : ℂ) (hp : ‖p‖ = 1)
    {z : ℂ} (hz : z ∈ (Complex.diskBoundaryChart p hp).source) :
    AnalyticAt ℂ (Complex.diskBoundaryChart p hp) z := by
  have hd : DifferentiableOn ℂ (Complex.diskBoundaryChart p hp)
      (Complex.diskBoundaryChart p hp).source := fun w hw =>
    (Complex.hasDerivAt_diskBoundaryChart p hp hw).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (Complex.diskBoundaryChart p hp).open_source z hz

private theorem eventually_boundaryChart_mem_arc {s t v : ℝ}
    (hv : v ∈ Ioo s t) (hp : ‖(diskBoundary (v : loopCircle) : ℂ)‖ = 1) :
    ∀ᶠ x : ℝ in 𝓝 0, ∃ r ∈ Ioo s t,
      Complex.diskBoundaryChart (diskBoundary (v : loopCircle) : ℂ) hp (x : ℂ) =
        (diskBoundary (r : loopCircle) : ℂ) := by
  let ψ := Complex.diskBoundaryChart (diskBoundary (v : loopCircle) : ℂ) hp
  have hsource (x : ℝ) : (x : ℂ) ∈ ψ.source := by
    change (x : ℂ) ≠ -Complex.I
    intro he
    have him := congrArg Complex.im he
    norm_num at him
  have hnorm (x : ℝ) : ‖ψ (x : ℂ)‖ = 1 :=
    (Complex.norm_diskBoundaryChart_eq_one_iff _ hp (hsource x)).mpr (by simp)
  let f : ℝ → Circle := fun x => ⟨ψ (x : ℂ), mem_sphere_zero_iff_norm.mpr (hnorm x)⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (ψ.toOpenPartialHomeomorph.continuousAt (hsource x)).comp
      Complex.continuous_ofReal.continuousAt
  let H : loopCircle ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  let J : Set loopCircle := ((↑) : ℝ → loopCircle) '' Ioo s t
  have hJ : IsOpen J := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hvJ : (v : loopCircle) ∈ J := ⟨v, hv, rfl⟩
  have hf0 : f 0 = H (v : loopCircle) := by
    apply Circle.ext
    change ψ 0 = (AddCircle.homeomorphCircle one_ne_zero (v : loopCircle) : ℂ)
    rw [AddCircle.homeomorphCircle_apply]
    exact Complex.diskBoundaryChart_zero _ hp
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, f x ∈ H '' J :=
    hf.continuousAt.tendsto.eventually
      ((H.isOpenMap J hJ).mem_nhds (hf0.symm ▸ mem_image_of_mem H hvJ))
  filter_upwards [hnear] with x hx
  rcases hx with ⟨θ, ⟨r, hr, rfl⟩, he⟩
  refine ⟨r, hr, ?_⟩
  have hec := congrArg (fun w : Circle => (w : ℂ)) he
  change (AddCircle.homeomorphCircle one_ne_zero (r : loopCircle) : ℂ) = ψ (x : ℂ) at hec
  rw [AddCircle.homeomorphCircle_apply] at hec
  exact hec.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem contDiffOn_chartGradient {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (p : M) (hsrc : ∀ z ∈ s, U z ∈ (chartAt E p).source) :
    ContDiffOn ℝ ∞ (fun z k => chartComplexGradient (E := E) p U k z) s := by
  let X : ℂ → E := extChartAt 𝓘(ℝ, E) p ∘ U
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞)
      (hsrc z hz)).comp z (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  apply contDiffOn_pi.mpr
  intro k
  let xk : ℂ → ℝ := fun z => chartCoordCLM E k (X z)
  have hxk : ContDiffOn ℝ ∞ xk s :=
    (chartCoordCLM E k).contDiff.comp_contDiffOn hX
  have hd := hxk.fderiv_of_isOpen (m := ∞) hs (by simp)
  have hd1 := hd.clm_apply (contDiffOn_const (c := (1 : ℂ)))
  have hdI := hd.clm_apply (contDiffOn_const (c := Complex.I))
  have hp := (hd1.mul (contDiffOn_const (c := (2 : ℝ)⁻¹))).prodMk
    (hdI.neg.mul (contDiffOn_const (c := (2 : ℝ)⁻¹)))
  refine (Complex.equivRealProdCLM.symm.contDiff.comp_contDiffOn hp).congr ?_
  intro z _
  change (⟨fderiv ℝ xk z 1 / 2, -fderiv ℝ xk z Complex.I / 2⟩ : ℂ) =
    Complex.equivRealProdCLM.symm
      (fderiv ℝ xk z 1 * (2 : ℝ)⁻¹, -fderiv ℝ xk z Complex.I * (2 : ℝ)⁻¹)
  apply Complex.ext <;> simp [Complex.equivRealProdCLM_symm_apply, div_eq_mul_inv]

private theorem chartGradient_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (p : M) (hsrc : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {z : ℂ} (hz : z ∈ s) (hτ : planarTension g U z = 0) :
    (1 / 2 : ℂ) •
      (fderiv ℝ (fun w k => chartComplexGradient p U k w) z 1 +
        Complex.I • fderiv ℝ (fun w k => chartComplexGradient p U k w) z Complex.I) =
      chartComplexGradientOperator g p U z (fun k => chartComplexGradient p U k z) := by
  let ξ : ℂ → (Fin (Module.finrank ℝ E) → ℂ) :=
    fun w k => chartComplexGradient p U k w
  have hξ := contDiffOn_chartGradient hs hU p hsrc
  have hd : DifferentiableAt ℝ ξ z :=
    (hξ.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)
  funext k
  have hcomponent (v : ℂ) :
      fderiv ℝ (chartComplexGradient p U k) z v = (fderiv ℝ ξ z v) k :=
    congrArg (fun L : ℂ →L[ℝ] ℂ => L v) (fderiv_apply hd k)
  have hk := chartComplexGradient_dbar_eq g
    ((hU.contMDiffAt (hs.mem_nhds hz)).of_le (by norm_num)) (hsrc z hz) hτ k
  change (1 / 2 : ℂ) *
    ((fderiv ℝ ξ z 1) k + Complex.I * (fderiv ℝ ξ z Complex.I) k) =
      chartComplexGradientOperator g p U z (ξ z) k
  rw [chartComplexGradientOperator_apply]
  calc
    (1 / 2 : ℂ) *
        ((fderiv ℝ ξ z 1) k + Complex.I * (fderiv ℝ ξ z Complex.I) k) =
        (fderiv ℝ (chartComplexGradient p U k) z 1 +
          Complex.I * fderiv ℝ (chartComplexGradient p U k) z Complex.I) / 2 := by
      rw [← hcomponent 1, ← hcomponent Complex.I]
      ring
    _ = _ := hk

omit [FiniteDimensional ℝ E] in
private theorem mfderiv_eq_zero_of_conformal_of_real_germ
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {z : ℂ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)
    (hconf : DiskMapConformalAt g U z) (hz : z.im = 0) (c : M)
    (hc : (fun x : ℝ => U (x : ℂ)) =ᶠ[𝓝 z.re] fun _ => c) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 := by
  have hzre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hz]
  have hcurve : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun x : ℝ => U (x : ℂ)) z.re = 0 := by
    rw [hc.mfderiv_eq, mfderiv_const, ContinuousLinearMap.comp_zero]
  have hUreal : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z.re : ℂ) := by
    simpa only [hzre] using hU
  have hchain := mfderiv_comp_apply z.re hUreal
    Complex.ofRealCLM.mdifferentiableAt (1 : ℝ)
  have hRealDeriv : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (Complex.ofReal : ℝ → ℂ) z.re Complex.ofRealCLM :=
    Complex.ofRealCLM.hasMFDerivAt
  have hReal : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (Complex.ofReal : ℝ → ℂ) z.re =
      Complex.ofRealCLM := hRealDeriv.mfderiv
  rw [hReal] at hchain
  change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun x : ℝ => U (x : ℂ)) z.re (1 : ℝ) =
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z.re : ℂ) (1 : ℂ) at hchain
  have hcurveOne : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun x : ℝ => U (x : ℂ)) z.re : ℝ →L[ℝ] E) (1 : ℝ) = 0 := by
    exact (congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hcurve).trans
      (show (0 : ℝ →L[ℝ] E) (1 : ℝ) = (0 : E) from rfl)
  have hOneReal : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z.re : ℂ) :
      ℂ →L[ℝ] E) (1 : ℂ) = 0 := hchain.symm.trans hcurveOne
  have hpoint : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (z.re : ℂ) : ℂ →L[ℝ] E) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z :=
    mfderiv_congr_point (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E)) (f := U) hzre
  have hOne : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ) = 0 :=
    (congrArg (fun L : ℂ →L[ℝ] E => L (1 : ℂ)) hpoint).symm.trans hOneReal
  have hI : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z Complex.I = 0 := by
    by_contra hne
    have hp := g.pos (U z) _ hne
    have he := hconf.2
    change g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ))
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z (1 : ℂ)) = _ at he
    rw [hOne, map_zero] at he
    exact (ne_of_gt hp) he.symm
  have hmodel (D : ℂ →L[ℝ] E) (hDOne : D (1 : ℂ) = 0)
      (hDI : D Complex.I = 0) : D = 0 := by
    apply ContinuousLinearMap.ext
    intro v
    change D v = (0 : E)
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      simpa only [Complex.real_smul, mul_one] using v.re_add_im.symm
    have hd := congrArg D hv
    simpa only [map_add, map_smul, hDOne, hDI, smul_zero, add_zero] using hd
  exact hmodel (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) hOne hI

private theorem not_constant_boundaryChart [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {a : C(closedDisk, M)} (ha : IsMorreyDisk g γ a)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {A : ℂ → M}
    (hA : SmoothDiskExtension (E := E) a A)
    (p : closedDisk) (hp : ‖(p : ℂ)‖ = 1) (c : M) :
    ¬ (∀ᶠ x : ℝ in 𝓝 0,
      A (Complex.diskBoundaryChart (p : ℂ) hp (x : ℂ)) = c) := by
  intro hc
  let ψ := Complex.diskBoundaryChart (p : ℂ) hp
  let U : ℂ → M := A ∘ ψ
  let v : M := a p
  obtain ⟨hAe, N, hN, hDN, hAN⟩ := hA
  have hA' : SmoothDiskExtension (E := E) a A := ⟨hAe, N, hN, hDN, hAN⟩
  have h0src : (0 : ℂ) ∈ ψ.source := by
    change (0 : ℂ) ≠ -Complex.I
    intro he
    have := congrArg Complex.im he
    norm_num at this
  have hψ0 : ψ 0 = (p : ℂ) := Complex.diskBoundaryChart_zero _ hp
  let S : Set ℂ := ψ.source ∩ ψ ⁻¹' N
  have hS : IsOpen S := ψ.contMDiffOn.continuousOn.isOpen_inter_preimage
    ψ.open_source hN
  have h0S : (0 : ℂ) ∈ S := by
    refine ⟨h0src, ?_⟩
    change ψ 0 ∈ N
    rw [hψ0]
    exact hDN p.property
  have hUS : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U S :=
    hAN.comp (ψ.contMDiffOn.mono inter_subset_left) (fun _ hz => hz.2)
  let T : Set ℂ := S ∩ U ⁻¹' (chartAt E v).source
  have hT : IsOpen T := hUS.continuousOn.isOpen_inter_preimage hS
    (chartAt E v).open_source
  have hU0 : U 0 = v := by
    change A (ψ 0) = a p
    rw [hψ0, hAe p]
  have h0T : (0 : ℂ) ∈ T := ⟨h0S, by
    change U 0 ∈ (chartAt E v).source
    rw [hU0]
    exact mem_chart_source E v⟩
  have hre0 : Tendsto Complex.re (𝓝 (0 : ℂ)) (𝓝 (0 : ℝ)) :=
    Complex.continuous_re.tendsto' (0 : ℂ) (0 : ℝ) Complex.zero_re
  have hcnear : ∀ᶠ z : ℂ in 𝓝 0, A (ψ (z.re : ℂ)) = c := hre0.eventually hc
  have hnear : T ∩ {z : ℂ | A (ψ (z.re : ℂ)) = c} ∈ 𝓝 (0 : ℂ) :=
    Filter.inter_mem (hT.mem_nhds h0T) hcnear
  obtain ⟨R, hR, hRsub⟩ := Metric.nhds_basis_ball.mem_iff.mp hnear
  have hRToT : ball (0 : ℂ) R ⊆ T := fun z hz => (hRsub hz).1
  have hsource (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) : z ∈ ψ.source :=
    (hRToT hz).1.1
  have hANat (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ A (ψ z) :=
    hAN.contMDiffAt (hN.mem_nhds (hRToT hz).1.2)
  have hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (ball (0 : ℂ) R) :=
    hUS.mono (hRToT.trans inter_subset_left)
  have hchart (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      U z ∈ (chartAt E v).source := (hRToT hz).2
  have hreal (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) (hi : z.im = 0) : U z = c := by
    have hzre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hval := (hRsub hz).2
    change A (ψ (z.re : ℂ)) = c at hval
    rw [hzre] at hval
    exact hval
  let ξ : ℂ → (Fin (Module.finrank ℝ E) → ℂ) :=
    fun z k => chartComplexGradient v U k z
  let B := chartComplexGradientOperator g v U
  have hB : ContDiffOn ℝ 1 B (ball (0 : ℂ) R) :=
    (contDiffOn_chartComplexGradientOperator g isOpen_ball hU v hchart).of_le (by simp)
  have hξ : ContDiffOn ℝ 1 ξ (ball (0 : ℂ) R) :=
    (contDiffOn_chartGradient isOpen_ball hU v hchart).of_le (by simp)
  have hDE : ∀ z ∈ ball (0 : ℂ) R, 0 < z.im →
      (1 / 2 : ℂ) • (fderiv ℝ ξ z 1 + Complex.I • fderiv ℝ ξ z Complex.I) =
        B z (ξ z) := by
    intro z hz hi
    apply chartGradient_equation g isOpen_ball hU v hchart hz
    have hin : ψ z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr
      ((Complex.norm_diskBoundaryChart_lt_one_iff _ hp (hsource z hz)).mpr hi)
    rw [show U = A ∘ ψ from rfl, planarTension_comp_holomorphic g
      ((hANat z hz).of_le (by norm_num))
      (analyticAt_diskBoundaryChart _ hp (hsource z hz))]
    have ht : planarTension g A (ψ z) = 0 := ha.tension_eq_zero_of_extension hA' _ hin
    rw [ht, smul_zero]
  have hzero : ∀ z ∈ ball (0 : ℂ) R, z.im = 0 → ξ z = 0 := by
    intro z hz hi
    have hclosed : ψ z ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.mpr
      ((Complex.norm_diskBoundaryChart_le_one_iff _ hp (hsource z hz)).mpr hi.ge)
    have hconfA := ha.conformal_of_extension_closedBall hA' (ψ z) hclosed
    have hconf : DiskMapConformalAt g U z :=
      conformal_mfderiv_comp_complex g ((hANat z hz).mdifferentiableAt (by simp))
        (Complex.hasDerivAt_diskBoundaryChart _ hp (hsource z hz)).differentiableAt
        hconfA.1 hconfA.2
    have hzre : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hline : (fun x : ℝ => U (x : ℂ)) =ᶠ[𝓝 z.re] fun _ => c := by
      have hnear : ∀ᶠ x : ℝ in 𝓝 z.re, (x : ℂ) ∈ ball (0 : ℂ) R :=
        Complex.continuous_ofReal.continuousAt.tendsto.eventually
          (isOpen_ball.mem_nhds (hzre.symm ▸ hz))
      filter_upwards [hnear] with x hx
      exact hreal (x : ℂ) hx (by simp)
    have hdU := mfderiv_eq_zero_of_conformal_of_real_germ g
      ((hU.contMDiffAt (isOpen_ball.mem_nhds hz)).mdifferentiableAt (by simp))
      hconf hi c hline
    funext k
    exact (chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
      ((hU.contMDiffAt (isOpen_ball.mem_nhds hz)).of_le (by simp)) (hchart z hz)).mpr hdU k
  obtain ⟨ρ, hρ, hρR, hξzero⟩ :=
    DifferentialGeometry.Analysis.exists_pos_radius_eq_zero_on_upperHalfBall
      hR B ξ hB hξ hDE hzero
  let z₀ : ℂ := (ρ / 2 : ℝ) • Complex.I
  have hz₀im : 0 < z₀.im := by
    simpa only [z₀, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, zero_add,
      add_zero] using half_pos hρ
  have hz₀ : z₀ ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff]
    simpa only [z₀, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hρ),
      Complex.norm_I, mul_one] using half_lt_self hρ
  have hρsub : ball (0 : ℂ) ρ ⊆ ball (0 : ℂ) R := ball_subset_ball hρR.le
  have hz₀source := hsource z₀ (hρsub hz₀)
  have hin : ψ z₀ ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr
    ((Complex.norm_diskBoundaryChart_lt_one_iff _ hp hz₀source).mpr hz₀im)
  have hzeroAcomp : ∀ᶠ z in 𝓝 z₀, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) A (ψ z) = 0 := by
    filter_upwards [isOpen_ball.mem_nhds hz₀,
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz₀im] with z hz hi
    have hzR := hρsub hz
    have hdU : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z = 0 :=
      (chartComplexGradient_eq_zero_iff_mfderiv_eq_zero
        ((hU.contMDiffAt (isOpen_ball.mem_nhds hzR)).of_le (by simp))
        (hchart z hzR)).mp (fun k => congrFun (hξzero z hz hi.le) k)
    have hsurj := ((ψ.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (hsource z hzR)).isInvertible_mfderiv (by simp)).surjective
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ))
      (I'' := 𝓘(ℝ, E)) z ((hANat z hzR).mdifferentiableAt (by simp))
      (ψ.mdifferentiableAt (by simp) (hsource z hzR))
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨v', hv'⟩ := hsurj w
    calc
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) A (ψ z) w =
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) A (ψ z) ∘L
            mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ψ z) v' := by
        rw [ContinuousLinearMap.comp_apply, hv']
      _ = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v' :=
        congrArg (fun L : ℂ →L[ℝ] E => L v') hchain.symm
      _ = 0 := by rw [hdU]; rfl
  have hzeroA : ∀ᶠ w in 𝓝 (ψ z₀), mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) A w = 0 :=
    (ψ.toOpenPartialHomeomorph.eventually_nhds _ hz₀source).mpr hzeroAcomp
  apply ha.not_eventually_mfderiv_eq_zero hγ hin
  filter_upwards [hzeroA, isOpen_ball.mem_nhds hin] with w hw hwin
  have heq := (hA'.eventuallyEq_diskExtension hwin).symm.mfderiv_eq
    (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
  rw [hw, ContinuousLinearMap.comp_zero] at heq
  exact heq

/-- The original Morrey disk cannot collapse any nonempty boundary parameter
interval. Its supplied smooth extension is an extension of this same disk;
no boundary rank, strict boundary phase, or replacement disk is assumed. -/
theorem IsMorreyDisk.not_constant_boundary_interval [T2Space M]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {a : C(closedDisk, M)} (ha : IsMorreyDisk g γ a)
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {A : ℂ → M}
    (hA : SmoothDiskExtension (E := E) a A)
    {s t : ℝ} (hst : s < t) (c : M) :
    ¬ (∀ r ∈ Ioo s t, diskTrace a (r : loopCircle) = c) := by
  intro hc
  obtain ⟨v, hsv, hvt⟩ := exists_between hst
  let p : closedDisk := diskBoundary (v : loopCircle)
  have hp : ‖(p : ℂ)‖ = 1 := Circle.norm_coe (AddCircle.toCircle (v : loopCircle))
  apply not_constant_boundaryChart ha hγ hA p hp c
  filter_upwards [eventually_boundaryChart_mem_arc ⟨hsv, hvt⟩ hp] with x hx
  obtain ⟨r, hr, he⟩ := hx
  rw [he, hA.1 (diskBoundary (r : loopCircle))]
  exact hc r hr

end DifferentialGeometry.Geometry
