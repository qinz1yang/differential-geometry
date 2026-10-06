import DifferentialGeometry.Analysis.Elliptic.Planar.StreamFunction
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Mollification
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

open Set Filter Metric MeasureTheory Function
open scoped Topology ContDiff Convolution

namespace DifferentialGeometry.Analysis

local notation "V" => EuclideanSpace ℝ (Fin 2)

private theorem sum_fderiv_normed_convolution_eq_zero
    {Ω K : Set V} (hKΩ : K ⊆ Ω) {F G : V → V}
    (hG : LocallyIntegrable G volume) (hGF : EqOn G F K)
    (hdiv : DeGiorgi.HasWeakDiv 0 F Ω) (ρ : ContDiffBump (0 : V)) (x : V)
    (hbuffer : ∀ y, x - y ∈ tsupport (ρ.normed volume) → y ∈ K) :
    (∑ i : Fin 2, fderiv ℝ
      (fun z => (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z i)
        x (EuclideanSpace.single i 1)) = 0 := by
  let η : V → ℝ := ρ.normed volume
  let T : Homeomorph V V := (Homeomorph.neg V).trans (Homeomorph.addLeft x)
  let ψ : V → ℝ := fun y => η (x - y)
  have hη : ContDiff ℝ ∞ η := ρ.contDiff_normed
  have hηc : HasCompactSupport η := ρ.hasCompactSupport_normed
  have hψ : ContDiff ℝ ∞ ψ := hη.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := by
    simpa [ψ, T, Function.comp_def, sub_eq_add_neg] using hηc.comp_homeomorph T
  have hψK : tsupport ψ ⊆ K := by
    intro y hy
    apply hbuffer y
    have hm := tsupport_comp_subset_preimage η T.continuous
    have hyT : y ∈ tsupport (η ∘ T) := by
      simpa [ψ, T, Function.comp_def, sub_eq_add_neg] using hy
    simpa [T, sub_eq_add_neg] using hm hyT
  have hψΩ : tsupport ψ ⊆ Ω := hψK.trans hKΩ
  have hDψ (y : V) (i : Fin 2) :
      fderiv ℝ ψ y (EuclideanSpace.single i 1) =
        -fderiv ℝ η (x - y) (EuclideanSpace.single i 1) := by
    have hd := (hη.differentiable (by simp) (x - y)).hasFDerivAt.comp y
      ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    change HasFDerivAt ψ _ y at hd
    rw [hd.fderiv]
    simp
  have hweak := hdiv ψ hψ hψc hψΩ
  simp only [Pi.zero_apply, zero_mul, integral_zero, neg_zero] at hweak
  have hweakAmbient : (∫ y, ∑ i : Fin 2,
      F y i * fderiv ℝ ψ y (EuclideanSpace.single i 1)) = 0 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω) (fun y hy => ?_)]
    · exact hweak
    · rw [fderiv_of_notMem_tsupport ℝ (fun hyψ => hy (hψΩ hyψ))]
      simp
  have hGi (i : Fin 2) : LocallyIntegrable (fun y => G y i) volume :=
    fun z => (EuclideanSpace.proj i : V →L[ℝ] ℝ).integrableAtFilter_comp (hG z)
  have hderiv (i : Fin 2) : fderiv ℝ
      (fun z => (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) z i)
        x (EuclideanSpace.single i 1) =
      ∫ y, G y i * fderiv ℝ η (x - y) (EuclideanSpace.single i 1) := by
    rw [Sobolev.Euclidean.normed_convolution_coordinate ρ hG i]
    have hcomm : (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (fun y => G y i)) =
        ((fun y => G y i) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] η) := by
      funext z
      rw [convolution_lsmul, convolution_lsmul_swap]
      apply integral_congr_ae
      filter_upwards [] with t
      exact mul_comm _ _
    rw [hcomm, (hηc.hasFDerivAt_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hGi i) (hη.of_le (by simp)) x).fderiv,
      convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (hGi i) (hηc.fderiv ℝ) (hη.continuous_fderiv (by simp)) x]
    rfl
  have hi (i : Fin 2) : Integrable
      (fun y => G y i * fderiv ℝ η (x - y) (EuclideanSpace.single i 1)) :=
    (hηc.fderiv_apply ℝ (EuclideanSpace.single i 1)).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hGi i)
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const) x
  simp_rw [hderiv]
  rw [← integral_finsetSum _ (fun i _ => hi i)]
  have hpoint (y : V) : (∑ i : Fin 2,
      G y i * fderiv ℝ η (x - y) (EuclideanSpace.single i 1)) =
      -(∑ i : Fin 2, F y i * fderiv ℝ ψ y (EuclideanSpace.single i 1)) := by
    by_cases hy : y ∈ tsupport ψ
    · rw [hGF (hψK hy)]
      simp only [hDψ, mul_neg, Finset.sum_neg_distrib, neg_neg]
    · have hz := fderiv_of_notMem_tsupport ℝ hy
      have hηzero (i : Fin 2) :
          fderiv ℝ η (x - y) (EuclideanSpace.single i 1) = 0 := by
        have hh := hDψ y i
        rw [hz, zero_apply] at hh
        exact neg_eq_zero.mp hh.symm
      simp only [hηzero, hz, zero_apply, mul_zero, Finset.sum_const_zero, neg_zero]
  simp_rw [hpoint]
  rw [integral_neg, hweakAmbient, neg_zero]

private def planarFluxMap : V →L[ℝ] (V →L[ℝ] ℝ) :=
  -(EuclideanSpace.proj 1).smulRight (EuclideanSpace.proj 0) +
    (EuclideanSpace.proj 0).smulRight (EuclideanSpace.proj 1)

private theorem planarFluxMap_apply (F : V → V) (x : V) :
    planarFluxMap (F x) = planarFluxForm F x := by
  simp only [planarFluxMap, planarFluxForm, add_apply, neg_apply,
    ContinuousLinearMap.smulRight_apply, EuclideanSpace.coe_proj, neg_smul]

private theorem exists_stream_function_of_uniform_smooth_approximation
    (a : V) (r : ℝ) (hr : 0 < r) (F : V → V)
    (hF : ContinuousOn F (ball a r)) (Fseq : ℕ → V → V)
    (hseq : ∀ n, ContDiffOn ℝ ∞ (Fseq n) (ball a r))
    (hdiv : ∀ n, DeGiorgi.HasWeakDiv 0 (Fseq n) (ball a r))
    (hlim : TendstoUniformlyOn Fseq F atTop (ball a r)) :
    ∃ s : V → ℝ, ContDiffOn ℝ 1 s (ball a r) ∧ s a = 0 ∧
      ∀ x ∈ ball a r, HasFDerivAt s (planarFluxForm F x) x := by
  choose sseq hsseq hdsseq using fun n =>
    exists_stream_function_of_hasWeakDiv_zero isOpen_ball (convex_ball a r)
      (hseq n) (hdiv n)
  let t : ℕ → V → ℝ := fun n x => sseq n x - sseq n a
  have hdt (n : ℕ) (x : V) (hx : x ∈ ball a r) :
      HasFDerivAt (t n) (planarFluxForm (Fseq n) x) x :=
    (hdsseq n x hx).sub_const (sseq n a)
  have hωlim : TendstoUniformlyOn (fun n => planarFluxForm (Fseq n))
      (planarFluxForm F) atTop (ball a r) := by
    simpa only [Function.comp_def, planarFluxMap_apply] using
      planarFluxMap.uniformContinuous.comp_tendstoUniformlyOn hlim
  have hc0 : Cauchy (Filter.map (fun n => t n a) atTop) := by
    apply cauchy_map_iff_exists_tendsto.mpr
    exact ⟨0, by simpa only [t, sub_self] using (tendsto_const_nhds (x := (0 : ℝ)))⟩
  have hc : UniformCauchySeqOn t atTop (ball a r) :=
    uniformCauchySeqOn_ball_of_fderiv hωlim.uniformCauchySeqOn hdt hc0
  let s : V → ℝ := fun x => limUnder atTop (fun n => t n x)
  have hts (x : V) (hx : x ∈ ball a r) :
      Tendsto (fun n => t n x) atTop (𝓝 (s x)) :=
    CauchySeq.tendsto_limUnder (u := fun n => t n x) (hc.cauchy_map hx)
  have hds (x : V) (hx : x ∈ ball a r) :
      HasFDerivAt s (planarFluxForm F x) x :=
    hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hωlim hdt hts hx
  have hωc : ContinuousOn (planarFluxForm F) (ball a r) := by
    simpa only [Function.comp_def, planarFluxMap_apply] using
      planarFluxMap.continuous.comp_continuousOn hF
  have hC1 : ContDiffOn ℝ 1 s (ball a r) := by
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 0) isOpen_ball).mpr
    refine ⟨fun x hx => (hds x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact contDiffOn_zero.mpr (hωc.congr (fun x hx => (hds x hx).fderiv))
  refine ⟨s, hC1, ?_, hds⟩
  have hz : Tendsto (fun n => t n a) atTop (𝓝 (0 : ℝ)) := by
    simpa only [t, sub_self] using (tendsto_const_nhds (x := (0 : ℝ)))
  exact tendsto_nhds_unique (hts a (mem_ball_self hr)) hz

/-- A continuous weakly divergence-free planar flux admits a normalized C¹ stream
function on the concentric half-ball. Its derivative is the form of the original
flux, including at its zeroes. -/
theorem exists_contDiff_one_stream_function_of_continuousOn_hasWeakDiv_zero
    (a : V) (R : ℝ) (hR : 0 < R) {F : V → V}
    (hF : ContinuousOn F (ball a R)) (hdiv : DeGiorgi.HasWeakDiv 0 F (ball a R)) :
    ∃ s : V → ℝ, ContDiffOn ℝ 1 s (ball a (R / 2)) ∧ s a = 0 ∧
      ∀ x ∈ ball a (R / 2), HasFDerivAt s (planarFluxForm F x) x := by
  classical
  let K : Set V := closedBall a (3 * R / 4)
  have hK : IsCompact K := isCompact_closedBall a (3 * R / 4)
  have hKR : K ⊆ ball a R := closedBall_subset_ball (by linarith)
  have hFK : ContinuousOn F K := hF.mono hKR
  let G : V → V := K.indicator F
  have hG : Integrable G volume :=
    (integrable_indicator_iff hK.measurableSet).mpr (hFK.integrableOn_compact hK)
  have hGF : EqOn G F K := fun x hx => indicator_of_mem hx F
  let ε : ℕ → ℝ := fun n => (R / 4) * (1 / ((n : ℝ) + 1))
  have hεpos (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεle (n : ℕ) : ε n ≤ R / 4 := by
    have hn : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
    exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (mul_one _)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      (tendsto_const_nhds (x := R / 4)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  let ρ : ℕ → ContDiffBump (0 : V) := fun n => Sobolev.mollifierBumpEps (hεpos n)
  let Fseq : ℕ → V → V := fun n =>
    (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G
  have hseq (n : ℕ) : ContDiff ℝ ∞ (Fseq n) :=
    (ρ n).hasCompactSupport_normed.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (ρ n).contDiff_normed hG.locallyIntegrable
  have hxK {x : V} (hx : x ∈ ball a (R / 2)) : x ∈ K := by
    change dist x a ≤ 3 * R / 4
    have := mem_ball.mp hx
    linarith
  have hbuffer (n : ℕ) (x : V) (hx : x ∈ ball a (R / 2))
      (y : V) (hy : dist y x ≤ ε n) : y ∈ K := by
    change dist y a ≤ 3 * R / 4
    have hx' := mem_ball.mp hx
    have ht := dist_triangle y x a
    have hn := hεle n
    linarith
  have hdivseq (n : ℕ) : DeGiorgi.HasWeakDiv 0 (Fseq n) (ball a (R / 2)) := by
    have hsum (x : V) (hx : x ∈ ball a (R / 2)) :
        (∑ i : Fin 2, fderiv ℝ (fun z => Fseq n z i) x
          (EuclideanSpace.single i 1)) = 0 := by
      apply sum_fderiv_normed_convolution_eq_zero hKR hG.locallyIntegrable hGF hdiv (ρ n) x
      intro y hy
      apply hbuffer n x hx y
      have hy' : x - y ∈ closedBall (0 : V) (ρ n).rOut := by
        simpa only [(ρ n).tsupport_normed_eq] using hy
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, norm_sub_rev, ρ,
        Sobolev.mollifierBumpEps] using hy'
    have hclass := DeGiorgi.hasWeakDiv_of_contDiffOn
      (Ω := ball a (R / 2)) isOpen_ball
      (fun i : Fin 2 => ((contDiff_piLp_apply (p := 2) (i := i)).comp
        ((hseq n).of_le (by simp))).contDiffOn)
    intro φ hφ hc hs
    rw [hclass φ hφ hc hs]
    congr 1
    apply setIntegral_congr_fun isOpen_ball.measurableSet
    intro x hx
    change (∑ i : Fin 2, fderiv ℝ (fun z => Fseq n z i) x
      (EuclideanSpace.single i 1)) * φ x = 0 * φ x
    exact congrArg (fun t : ℝ => t * φ x) (hsum x hx)
  have hlim : TendstoUniformlyOn Fseq F atTop (ball a (R / 2)) := by
    have hFu : UniformContinuousOn F K := hK.uniformContinuousOn_of_continuous hFK
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro δ hδ
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp hFu (δ / 2) (half_pos hδ)
    filter_upwards [(tendsto_order.mp hεlim).2 η hη] with n hn x hx
    have hclose : ∀ y ∈ ball x (ρ n).rOut, dist (G y) (G x) ≤ δ / 2 := by
      intro y hy
      have hy' : dist y x < ε n := hy
      have hyK := hbuffer n x hx y hy'.le
      rw [hGF hyK, hGF (hxK hx)]
      exact (hmod y hyK x (hxK hx) (hy'.trans hn)).le
    have hh := (ρ n).dist_normed_convolution_le hG.aestronglyMeasurable hclose
    rw [hGF (hxK hx)] at hh
    have hbound : dist (F x) (Fseq n x) ≤ δ / 2 := by
      simpa only [Fseq, dist_comm] using hh
    exact hbound.trans_lt (half_lt_self hδ)
  exact exists_stream_function_of_uniform_smooth_approximation a (R / 2) (half_pos hR)
    F (hF.mono (ball_subset_ball (by linarith))) Fseq
    (fun n => (hseq n).contDiffOn) hdivseq hlim

end DifferentialGeometry.Analysis
