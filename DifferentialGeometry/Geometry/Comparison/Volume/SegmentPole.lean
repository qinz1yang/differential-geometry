import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicRatio
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set Matrix
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open CovariantDerivativeAlong
open Exponential
open Geodesic
open Variation
open BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

private lemma hypSn_div_tendsto (q : Real) :
    Tendsto (fun t => hypSn q t / t) (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hzero : hypSn q 0 = 0 := by
    by_cases hq : q = 0 <;> simp [hypSn, hq]
  have hval : hypSnDeriv q 0 = 1 := by
    by_cases hq : q = 0 <;> simp [hypSnDeriv, hq]
  have hderiv : HasDerivAt (hypSn q) (hypSnDeriv q 0) 0 := hasDerivAt_hypSn q 0
  have hslope := (hasDerivAt_iff_tendsto_slope).mp hderiv
  rw [hval] at hslope
  have hfun : slope (hypSn q) 0 = fun t => hypSn q t / t := by
    funext t
    rw [slope_def_field, hzero, sub_zero, sub_zero]
  rw [hfun] at hslope
  exact hslope.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))

private lemma hypDensity_div_tendsto (q : Real) (d : ℕ) :
    Tendsto (fun t => hypDensity q d t / t ^ d) (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hpow := (hypSn_div_tendsto q).pow d
  rw [one_pow] at hpow
  have hfun : (fun t : Real => hypDensity q d t / t ^ d)
      = fun t : Real => (hypSn q t / t) ^ d := by
    funext t
    simp only [hypDensity, div_pow]
  rw [hfun]
  exact hpow

private lemma clm_smul_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    (B : F →L[Real] F →L[Real] Real) (c : Real) (v w : F) :
    B (c • v) w = c * B v w := by
  have h := congrArg (fun L : F →L[Real] Real => L w) (B.map_smul c v)
  simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h

private lemma clm_sum_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
    {κ : Type*} [Fintype κ]
    (B : F →L[Real] F →L[Real] Real) (v : κ → F) (w : F) :
    B (∑ i, v i) w = ∑ i, B (v i) w := by
  rw [map_sum, ContinuousLinearMap.sum_apply]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
omit [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
lemma linIndep_of_ortho
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E - 1) → E)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    LinearIndependent Real e := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hpair := congrArg (fun z : E => g.inner x z (e j)) hc
  change g.inner x (∑ i, c i • e i) (e j) = g.inner x 0 (e j) at hpair
  rw [clm_sum_apply, map_zero, ContinuousLinearMap.zero_apply] at hpair
  rw [Finset.sum_eq_single j] at hpair
  · calc
      c j = c j * 1 := by rw [mul_one]
      _ = c j * g.inner x (e j) (e j) := by rw [hON j j, if_pos rfl]
      _ = g.inner x (c j • e j) (e j) :=
        (clm_smul_apply (g.inner x) (c j) (e j) (e j)).symm
      _ = 0 := hpair
  · intro i _ hij
    calc
      g.inner x (c i • e i) (e j) = c i * g.inner x (e i) (e j) :=
        clm_smul_apply (g.inner x) (c i) (e i) (e j)
      _ = c i * (if i = j then 1 else 0) := by rw [hON i j]
      _ = c i * 0 := by rw [if_neg (by simpa using hij)]
      _ = 0 := mul_zero _
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

theorem curveDensity_pole
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        t ^ (Module.finrank Real E - 1))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  classical
  have hv_li : LinearIndependent Real v := by
    simpa using linIndep_of_ortho (I := I) g p v hON
  obtain ⟨B, hBnone, hBsome⟩ := exists_perp_basis (I := I) g p u v hv_li hperp hu
  let ue : E := (u : E)
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h] at hu
    simp at hu
  have hue_ne : ue ≠ 0 := hu_ne
  have hunorm : 0 < ‖ue‖ := norm_pos_iff.mpr hue_ne
  set b₀ : Real := expMapC2Radius (I := I) g p / ‖ue‖ with hb₀_def
  have hb₀ : 0 < b₀ := div_pos (expMapC2Radius_pos (I := I) g p) hunorm
  have hrad : ∀ r ∈ Set.Ioo (0 : Real) b₀,
      ‖r • ue‖ < expMapC2Radius (I := I) g p := by
    intro r hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, ← lt_div_iff₀ hunorm]
    exact hr.2
  have hsrc : Set.MapsTo (fun r : Real => r • ue) (Set.Ioo (0 : Real) b₀)
      (expMapDiffeo (I := I) g p).source := by
    intro r hr
    change r • ue ∈ (expMapDiffeo (I := I) g p).source
    exact mem_expMapDiffeo_source_of_norm_lt_radius (I := I) g p (hrad r hr)
  have hBperp : ∀ i, g.inner p ue (B (some i)) = 0 := by
    intro i
    rw [hBsome i]
    exact hperp i
  have hONB : ∀ i j, g.inner p (B (some i)) (B (some j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hBsome i, hBsome j]
    exact hON i j
  obtain ⟨c, hc, hc_val, hdensity⟩ :=
    normalDensity_curve (I := I) g p ue B hBnone hBperp hsrc hrad
  have hzero_val :=
    normalChartDensity_zero_of_perpOrthonormal (I := I) g p ue B hBnone hBperp hONB
  have hc_eq_ncd0 : c = normalChartDensity (I := I) g p 0 := by
    rw [hc_val, hzero_val]
  have hcurveEq : ∀ᶠ t in 𝓝[>] (0 : Real),
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
        curveDensity (I := I) g (radialCurve (I := I) g p ue)
          (fun i => radialJacobiField (I := I) g p ue (B (some i))) t := by
    have hcurve : ∀ᶠ t in 𝓝[>] (0 : Real),
        intrinsicGeodesic (I := I) g hEnorm p u t =
          radialCurve (I := I) g p ue t := by
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p ue (0 : E)]
        with t ht using ht.1
    have hfields : ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
        (intrinsicJacobi (I := I) g hEnorm p u (v i) t : E) =
          (radialJacobiField (I := I) g p ue (B (some i)) t : E) := by
      refine Filter.eventually_all.2 (fun i => ?_)
      filter_upwards [intrJacobi_raw (I := I) g hEnorm p ue (v i : E)]
        with t ht
      rw [hBsome i]
      exact ht.2
    filter_upwards [hcurve, hfields] with t hct hft
    have hgram :
        curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
            (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
          curveGram (I := I) g (radialCurve (I := I) g p ue)
            (fun i => radialJacobiField (I := I) g p ue (B (some i))) t := by
      ext i j
      simp only [curveGram, Matrix.of_apply]
      rw [hct, hft i, hft j]
    simp only [curveDensity, hgram]
  have hratio : Filter.EventuallyEq (𝓝[>] (0 : Real))
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
            t ^ (Module.finrank Real E - 1))
      (fun t => normalChartDensity (I := I) g p (t • ue) / c) := by
    filter_upwards [hcurveEq, self_mem_nhdsWithin, Ioo_mem_nhdsGT hb₀]
      with t hcurvet htpos htwin
    have ht0 : 0 < t := htpos
    have hpow : 0 < t ^ (Module.finrank Real E - 1) := pow_pos ht0 _
    have hdens := hdensity t htwin
    rw [hcurvet]
    field_simp [hc.ne', hpow.ne']
    rw [mul_comm]
    rw [← hdens]
    rw [Fintype.card_fin]
  have hcontAt : ContinuousAt (normalChartDensity (I := I) g p) 0 := by
    have hcont : ContinuousOn (normalChartDensity (I := I) g p)
        (expMapDiffeo (I := I) g p).source := by
      simpa only [normalChartDensity] using
        paramDensity_contOn (I := I) g (expMapDiffeo (I := I) g p)
    exact hcont.continuousAt ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have htend : Tendsto (fun t : Real => t • ue) (𝓝[>] (0 : Real)) (𝓝 (0 : E)) := by
    have hcont : Continuous fun t : Real => t • ue := continuous_id.smul continuous_const
    have hzero : Tendsto (fun t : Real => t • ue) (𝓝 (0 : Real)) (𝓝 (0 : E)) := by
      simpa using (hcont.continuousAt (x := (0 : Real))).tendsto
    exact hzero.mono_left inf_le_left
  have hlim : Tendsto (fun t => normalChartDensity (I := I) g p (t • ue) / c)
      (𝓝[>] (0 : Real)) (𝓝 (normalChartDensity (I := I) g p 0 / c)) :=
    (hcontAt.tendsto.comp htend).div tendsto_const_nhds hc.ne'
  have hlim_one : Tendsto (fun t => normalChartDensity (I := I) g p (t • ue) / c)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
    rw [← (show normalChartDensity (I := I) g p 0 / c = 1 from by
      rw [← hc_eq_ncd0]
      exact div_self hc.ne')]
    exact hlim
  exact Filter.Tendsto.congr' hratio.symm hlim_one

theorem poleLimit
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (q : Real) (hq : 0 ≤ q)
    (hu : 0 < g.inner p u u)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        hypDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank Real E - 1) t)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hcd := curveDensity_pole (I := I) g hEnorm p u hu v hON hperp
  have hmd := hypDensity_div_tendsto (q * Real.sqrt (g.inner p u u))
    (Module.finrank Real E - 1)
  have hcombine := hcd.div hmd one_ne_zero
  rw [div_one] at hcombine
  refine hcombine.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : (0 : Real) < t := ht
  have hpow : (0 : Real) < t ^ (Module.finrank Real E - 1) := pow_pos ht0 _
  have hmdpos : 0 < hypDensity (q * Real.sqrt (g.inner p u u))
      (Module.finrank Real E - 1) t :=
    hypDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht0
  simp only [Pi.div_apply]
  field_simp [hpow.ne', hmdpos.ne']

theorem transDens_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (q b : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) b,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      (∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      let γ := intrinsicGeodesic (I := I) g hEnorm p u
      let V := fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
      let ell := Real.sqrt (g.inner p u u)
      ∀ t ∈ Set.Ioo (0 : Real) b,
        curveDensity (I := I) g γ V t ≤
          hypDensity (q * ell) (Module.finrank Real E - 1) t := by
  obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p u hu
  have hperp : ∀ i, g.inner p u (v i) = 0 := by
    intro i; rw [g.symm p u (v i)]; exact hperp' i
  have hanti := intrRatioOfFrame (I := I) g hEnorm p u q b hq hd hu v hON hperp hno hRic
  have hlim := poleLimit (I := I) g hEnorm p u q hq hu v hON hperp
  refine ⟨v, hON, hperp, ?_⟩
  intro γ V ell t ht
  have hpos : 0 < hypDensity (q * ell) (Module.finrank Real E - 1) t :=
    hypDensity_pos (mul_nonneg hq (Real.sqrt_nonneg _)) ht.1
  have hRatioLE :
      curveDensity (I := I) g γ V t /
        hypDensity (q * ell) (Module.finrank Real E - 1) t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : Real),
        curveDensity (I := I) g γ V t /
            hypDensity (q * ell) (Module.finrank Real E - 1) t ≤
          curveDensity (I := I) g γ V s /
            hypDensity (q * ell) (Module.finrank Real E - 1) s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsb : s ∈ Set.Ioo (0 : Real) b := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsb ht hs.2.le
    exact ge_of_tendsto hlim hev
  rwa [div_le_one hpos] at hRatioLE

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
