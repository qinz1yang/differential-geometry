import DifferentialGeometry.Analysis.Sobolev.Tools.Mollification.WeakDerivative

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem convolution_fderiv_eq_convolution_weakPartial_of_support
    {u g : E → ℝ} {i : Fin d} {Ω : Set E}
    (hweak : DeGiorgi.HasWeakPartialDeriv i g u Ω)
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (x : E)
    (hsupport : ∀ y, x - y ∈ tsupport φ → y ∈ Ω) :
    ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
  classical
  let T : Homeomorph E E := (Homeomorph.neg E).trans (Homeomorph.addLeft x)
  let ψ : E → ℝ := φ ∘ T
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    let h : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      hφ_smooth.comp (contDiff_const.add contDiff_id.neg)
    exact h
  have hψ_compact : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp] using hφ_compact.comp_homeomorph T
  have hψsupport : tsupport ψ ⊆ Ω := by
    intro y hy
    apply hsupport y
    have hm := tsupport_comp_subset_preimage φ T.continuous hy
    simpa [T, sub_eq_add_neg] using hm
  have key := hweak ψ hψ_smooth hψ_compact hψsupport
  have hderiv :
      ∀ t,
        (fderiv ℝ ψ t) (EuclideanSpace.single i 1) =
          - (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) := by
    intro t
    have hraw :=
      (hφ_smooth.differentiable
        (show (((⊤ : ℕ∞) : WithTop ℕ∞)) ≠ 0 by simp) (x + -t)).hasFDerivAt.comp t
          ((hasFDerivAt_const x t).add (hasFDerivAt_id t).neg)
    have heq : ψ = φ ∘ ((fun _ : E => x) + -id) := by
      funext y
      simp [ψ, T]
    rw [← heq] at hraw
    rw [hraw.fderiv]
    simp
  have hkey :
      ∫ t, g t * ψ t ∂volume =
        ∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
    have hkey' :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, g t * ψ t ∂volume := by
      have hleft : (∫ t in Ω, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1)) =
          ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro t ht
        have hn : t ∉ tsupport ψ := fun h => ht (hψsupport h)
        rw [fderiv_of_notMem_tsupport ℝ hn]
        simp
      have hright : (∫ t in Ω, g t * ψ t) = ∫ t, g t * ψ t := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro t ht
        rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hψsupport h))]
        simp
      simpa only [hleft, hright] using key
    have hderiv_int :
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume =
          -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
      calc
        ∫ t, u t * (fderiv ℝ ψ t) (EuclideanSpace.single i 1) ∂volume
          = ∫ t, -(u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1)) ∂volume := by
              refine integral_congr_ae ?_
              filter_upwards with t
              rw [hderiv t]
              ring
        _ = -∫ t, u t * (fderiv ℝ φ (x + -t)) (EuclideanSpace.single i 1) ∂volume := by
              rw [integral_neg]
    linarith
  calc
      ((fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x
      = ∫ t, u t * (fderiv ℝ φ (x - t)) (EuclideanSpace.single i 1) ∂volume := by
          simpa [smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap
              (f := fun y => (fderiv ℝ φ y) (EuclideanSpace.single i 1)) (g := u) (x := x)
              (μ := volume))
    _ = ∫ t, g t * ψ t ∂volume := hkey.symm
    _ = (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x := by
          simpa [ψ, T, Function.comp, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
            smul_eq_mul, mul_comm] using
            (MeasureTheory.convolution_lsmul_swap (f := φ) (g := g) (x := x) (μ := volume)).symm

theorem mollifyEps_partial_eq_mollifyEps_weakPartial_of_closedBall_subset
    {ε : ℝ} (hε : 0 < ε)
    {u g : E → ℝ} {j : Fin d} {Ω : Set E}
    (hu_local : LocallyIntegrable u (volume : Measure E))
    (hweak : DeGiorgi.HasWeakPartialDeriv (d := d) j g u Ω) (x : E)
    (hball : closedBall x ε ⊆ Ω) :
    (fderiv ℝ (mollifyEps (d := d) hε u) x)
        (EuclideanSpace.single j 1) =
      mollifyEps (d := d) hε g x := by
  classical
  have hη_smooth : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have hη_C1 : ContDiff ℝ 1 (mollifierEps (d := d) hε) :=
    hη_smooth.of_le (by norm_cast)
  have hη_compact : HasCompactSupport (mollifierEps (d := d) hε) :=
    mollifierEps_compactSupport hε
  have hderiv : HasFDerivAt
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε)
      ((u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E,
        (volume : Measure E)] fderiv ℝ (mollifierEps (d := d) hε)) x) x :=
    hη_compact.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hu_local hη_C1 x
  have hpartial_uη :
      (fderiv ℝ (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) x) (EuclideanSpace.single j 1) =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun y => (fderiv ℝ (mollifierEps (d := d) hε) y)
          (EuclideanSpace.single j 1))) x := by
    rw [hderiv.fderiv]
    exact convolution_precompR_apply (𝕜 := ℝ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hu_local (hη_compact.fderiv ℝ)
      (hη_smooth.continuous_fderiv (by simp)) x
        (EuclideanSpace.single j 1)
  have hcomm : mollifyEps (d := d) hε u =
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        mollifierEps (d := d) hε) := by
    funext y
    exact mollifyEps_eq_convolution_swap hε u y
  rw [hcomm]
  rw [hpartial_uη]
  have h_swap_convergence : ∀ y : E,
      (u ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)]
        (fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))) y =
      ((fun z => (fderiv ℝ (mollifierEps (d := d) hε) z)
          (EuclideanSpace.single j 1))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (volume : Measure E)] u) y := by
    intro y
    rw [convolution_lsmul, convolution_lsmul_swap]
    refine integral_congr_ae ?_
    filter_upwards with t
    rw [smul_eq_mul, smul_eq_mul, mul_comm]
  rw [h_swap_convergence x]
  have hη_smooth' : ContDiff ℝ (⊤ : ℕ∞) (mollifierEps (d := d) hε) :=
    mollifierEps_smooth hε
  have h_ibp :=
    convolution_fderiv_eq_convolution_weakPartial_of_support
      (d := d) (i := j) (g := g) (u := u) hweak hη_smooth' hη_compact x (fun y hy => by
      apply hball
      rw [mem_closedBall, dist_eq_norm]
      have h := mollifierEps_tsupport_subset_closedBall_eps hε hy
      rw [mem_closedBall, dist_zero_right] at h
      simpa only [norm_sub_rev] using h)
  rw [h_ibp]
  rfl


theorem mollifyEps_second_partial_eq_mollifyEps_weakPartial_on
    {ε : ℝ} (hε : 0 < ε)
    {u du d2u : E → ℝ} {i j : Fin d} {Ω Ω' : Set E}
    (hu : LocallyIntegrable u volume) (hdu : LocallyIntegrable du volume)
    (hfirst : DeGiorgi.HasWeakPartialDeriv i du u Ω)
    (hsecond : DeGiorgi.HasWeakPartialDeriv j d2u du Ω)
    (hΩ' : IsOpen Ω') (hball : ∀ x ∈ Ω', closedBall x ε ⊆ Ω)
    {x : E} (hx : x ∈ Ω') :
    fderiv ℝ (fun y => fderiv ℝ (mollifyEps hε u) y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1) =
        mollifyEps hε d2u x := by
  have heq : (fun y => fderiv ℝ (mollifyEps hε u) y
      (EuclideanSpace.single i 1)) =ᶠ[𝓝 x] mollifyEps hε du := by
    filter_upwards [hΩ'.mem_nhds hx] with y hy
    exact mollifyEps_partial_eq_mollifyEps_weakPartial_of_closedBall_subset
      hε hu hfirst y (hball y hy)
  rw [heq.fderiv_eq]
  exact mollifyEps_partial_eq_mollifyEps_weakPartial_of_closedBall_subset
    hε hdu hsecond x (hball x hx)

theorem mollifyEps_eq_of_ae_eq_on
    {ε : ℝ} (hε : 0 < ε) {f g : E → ℝ} {Ω : Set E}
    (hΩ : MeasurableSet Ω) (hfg : f =ᵐ[volume.restrict Ω] g)
    (x : E) (hball : closedBall x ε ⊆ Ω) :
    mollifyEps hε f x = mollifyEps hε g x := by
  rw [mollifyEps_eq_convolution_swap, mollifyEps_eq_convolution_swap,
    convolution_lsmul, convolution_lsmul]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' hΩ).mp hfg] with y hy
  by_cases hyΩ : y ∈ Ω
  · rw [hy hyΩ]
  · have hzero : mollifierEps hε (x - y) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      apply hyΩ
      apply hball
      have h := mollifierEps_tsupport_subset_closedBall_eps hε hs
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_closedBall, dist_zero_right] at h
      simpa only [norm_sub_rev] using h
    simp only [hzero, smul_eq_mul, mul_zero]

end DifferentialGeometry.Analysis.Sobolev
