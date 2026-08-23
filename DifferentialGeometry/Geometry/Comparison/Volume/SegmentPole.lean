import DifferentialGeometry.Geometry.Comparison.Volume.IntrinsicRatio
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates

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

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem curveDensity_pole
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        t ^ (Module.finrank Real E - 1))
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  classical
  let C : Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E - 1)) Real :=
    fun k i => (chartModelBasis E).repr (v i) k
  let A : Real → Matrix (Fin (Module.finrank Real E - 1))
      (Fin (Module.finrank Real E - 1)) Real :=
    fun t => Cᵀ * normalGramMatrix (I := I) g p (t • (u : E)) * C
  have hv (i : Fin (Module.finrank Real E - 1)) :
      (v i : E) = ∑ k, C k i • (chartModelBasis E) k := by
    dsimp only [C]
    exact ((chartModelBasis E).sum_repr (v i)).symm
  have hG0 (k l : Fin (Module.finrank Real E)) :
      normalGramMatrix (I := I) g p (0 : E) k l =
        g.inner p ((chartModelBasis E) k) ((chartModelBasis E) l) := by
    rw [normalGram_apply, expMapDiffeo_zero]
    change
      g.inner p
          (mfderiv 𝓘(Real, E) I (normalChartAt (I := I) g p).symm (0 : E)
            ((chartModelBasis E) k))
          (mfderiv 𝓘(Real, E) I (normalChartAt (I := I) g p).symm (0 : E)
            ((chartModelBasis E) l)) =
        g.inner p ((chartModelBasis E) k) ((chartModelBasis E) l)
    exact normalChartAt_metric_pullback_at_origin (I := I) g p
      ((chartModelBasis E) k) ((chartModelBasis E) l)
  have hC0 :
      Cᵀ * normalGramMatrix (I := I) g p (0 : E) * C =
        (1 : Matrix (Fin (Module.finrank Real E - 1))
          (Fin (Module.finrank Real E - 1)) Real) := by
    have hbase0 :
        curveGram (I := I) g (fun _ : Real => p)
            (fun k (_ : Real) => (show TangentSpace I p from (chartModelBasis E) k)) 0 =
          normalGramMatrix (I := I) g p (0 : E) := by
      ext k l
      simpa only [curveGram, Matrix.of_apply] using (hG0 k l).symm
    have hrect0 :=
      curveGram_rect (I := I) g (fun _ : Real => p)
        (fun k (_ : Real) => (show TangentSpace I p from (chartModelBasis E) k))
        (fun i (_ : Real) => v i) 0 C hv
    rw [← hbase0, ← hrect0]
    ext i j
    simpa only [curveGram, Matrix.of_apply, Matrix.one_apply] using hON i j
  have hA0 :
      A 0 =
        (1 : Matrix (Fin (Module.finrank Real E - 1))
          (Fin (Module.finrank Real E - 1)) Real) := by
    simpa only [A, zero_smul] using hC0
  have htx :
      Tendsto (fun t : Real => t • (u : E)) (𝓝[>] (0 : Real)) (𝓝 (0 : E)) := by
    have hcont : Continuous fun t : Real => t • (u : E) :=
      continuous_id.smul continuous_const
    have hzero :
        Tendsto (fun t : Real => t • (u : E)) (𝓝 (0 : Real)) (𝓝 (0 : E)) := by
      simpa using (hcont.continuousAt (x := (0 : Real))).tendsto
    exact hzero.mono_left inf_le_left
  have hnormal :
      Tendsto
        (fun t : Real => normalGramMatrix (I := I) g p (t • (u : E)))
        (𝓝[>] (0 : Real))
        (𝓝 (normalGramMatrix (I := I) g p (0 : E))) :=
    (normalGram_contAt (I := I) g p).tendsto.comp htx
  have hA :
      Tendsto A (𝓝[>] (0 : Real))
        (𝓝 (1 : Matrix (Fin (Module.finrank Real E - 1))
          (Fin (Module.finrank Real E - 1)) Real)) := by
    rw [← hA0]
    have hmul : ContinuousAt
        (fun G : Matrix (Fin (Module.finrank Real E)) (Fin (Module.finrank Real E)) Real =>
          Cᵀ * G * C)
        (normalGramMatrix (I := I) g p (0 : E)) := by
      have hleft : Continuous
          (fun G : Matrix (Fin (Module.finrank Real E))
              (Fin (Module.finrank Real E)) Real => Cᵀ * G) :=
        continuous_const.matrix_mul continuous_id
      have hright : Continuous
          (fun G : Matrix (Fin (Module.finrank Real E))
              (Fin (Module.finrank Real E)) Real => C) :=
        continuous_const
      exact (hleft.matrix_mul hright).continuousAt
    simpa only [A, Function.comp_apply, zero_smul] using hmul.tendsto.comp hnormal
  have hsrc : ∀ᶠ t in 𝓝[>] (0 : Real),
      t • (u : E) ∈ (expMapDiffeo (I := I) g p).source :=
    htx.eventually ((expMapDiffeo (I := I) g p).open_source.mem_nhds
      (zero_mem_expMapDiffeo_source (I := I) g p))
  have hrad : ∀ᶠ t in 𝓝[>] (0 : Real),
      ‖(t • (u : E) : E)‖ < expMapC2Radius (I := I) g p := by
    have hball := htx.eventually
      (Metric.ball_mem_nhds (0 : E) (expMapC2Radius_pos (I := I) g p))
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hraw0 :=
    intrJacobi_raw (I := I) g hEnorm p (u : E) (0 : E)
  have hraw : ∀ᶠ t in 𝓝[>] (0 : Real), ∀ i,
      intrinsicGeodesic (I := I) g hEnorm p u t =
          radialCurve (I := I) g p (u : E) t ∧
        (intrinsicJacobi (I := I) g hEnorm p u (v i) t : E) =
          (radialJacobiField (I := I) g p (u : E) (v i : E) t : E) :=
    Filter.eventually_all.mpr fun i =>
      intrJacobi_raw (I := I) g hEnorm p (u : E) (v i : E)
  have hgram : ∀ᶠ t in 𝓝[>] (0 : Real),
      curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
        (t ^ 2) • A t := by
    filter_upwards [hraw0, hraw, hsrc, hrad] with t hraw0t hrawt hsrct hradt
    have hγ :
        intrinsicGeodesic (I := I) g hEnorm p u t =
          radialCurve (I := I) g p (u : E) t :=
      hraw0t.1
    have hrecomb (i : Fin (Module.finrank Real E - 1)) :
        radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1 =
          ∑ k, C k i • radialJacobiField (I := I) g p (t • (u : E))
            ((chartModelBasis E) k) 1 := by
      calc
        radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1 =
            radialJacobiField (I := I) g p (t • (u : E))
              (∑ k, C k i • (chartModelBasis E) k) 1 := by rw [hv i]
        _ = _ := radialJacobi_sum (I := I) g p (t • (u : E))
          (chartModelBasis E) (fun k => C k i) hradt
    have hbase :
        curveGram (I := I) g (radialCurve (I := I) g p (u : E))
            (fun k t => radialJacobiField (I := I) g p (t • (u : E))
              ((chartModelBasis E) k) 1) t =
          normalGramMatrix (I := I) g p (t • (u : E)) := by
      rw [normalGram_radialMat (I := I) g p hsrct hradt]
      rfl
    have hrect :
        curveGram (I := I) g (radialCurve (I := I) g p (u : E))
            (fun i t => radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1) t =
          A t := by
      rw [curveGram_rect (I := I) g (radialCurve (I := I) g p (u : E))
        (fun k t => radialJacobiField (I := I) g p (t • (u : E))
          ((chartModelBasis E) k) 1)
        (fun i t => radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1)
        t C hrecomb, hbase]
    calc
      curveGram (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t =
          (t ^ 2) •
            curveGram (I := I) g (radialCurve (I := I) g p (u : E))
              (fun i t => radialJacobiField (I := I) g p (t • (u : E))
                (v i : E) 1) t := by
        ext i j
        simp only [curveGram, Matrix.of_apply, Matrix.smul_apply]
        rw [hγ]
        change
          g.inner (radialCurve (I := I) g p (u : E) t)
              (intrinsicJacobi (I := I) g hEnorm p u (v i) t : E)
              (intrinsicJacobi (I := I) g hEnorm p u (v j) t : E) =
            t ^ 2 *
              g.inner (radialCurve (I := I) g p (u : E) t)
                (radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1)
                (radialJacobiField (I := I) g p (t • (u : E)) (v j : E) 1)
        have hi :
            radialJacobiField (I := I) g p (u : E) (v i : E) t =
              t • radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1 := by
          calc
            radialJacobiField (I := I) g p (u : E) (v i : E) t =
                radialJacobiField (I := I) g p (t • (u : E)) (t • (v i : E)) 1 :=
              radialJacobi_scale (I := I) g p (u : E) (v i : E) t
            _ = t • radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1 :=
              radialJacobi_one_smul (I := I) g p (t • (u : E)) (v i : E) t hradt
        have hj :
            radialJacobiField (I := I) g p (u : E) (v j : E) t =
              t • radialJacobiField (I := I) g p (t • (u : E)) (v j : E) 1 := by
          calc
            radialJacobiField (I := I) g p (u : E) (v j : E) t =
                radialJacobiField (I := I) g p (t • (u : E)) (t • (v j : E)) 1 :=
              radialJacobi_scale (I := I) g p (u : E) (v j : E) t
            _ = t • radialJacobiField (I := I) g p (t • (u : E)) (v j : E) 1 :=
              radialJacobi_one_smul (I := I) g p (t • (u : E)) (v j : E) t hradt
        rw [(hrawt i).2, (hrawt j).2, hi, hj]
        let β : E →L[Real] E →L[Real] Real :=
          g.inner (radialCurve (I := I) g p (u : E) t)
        let X : E :=
          (radialJacobiField (I := I) g p (t • (u : E)) (v i : E) 1 : E)
        let Y : E :=
          (radialJacobiField (I := I) g p (t • (u : E)) (v j : E) 1 : E)
        change β (t • X) (t • Y) = t ^ 2 * β X Y
        have hleft : β (t • X) (t • Y) = t * β X (t • Y) := by
          have h := congrArg (fun L : _ →L[Real] Real => L (t • Y)) (β.map_smul t X)
          simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using h
        have hright : β X (t • Y) = t * β X Y := by
          simpa only [smul_eq_mul] using (β X).map_smul t Y
        rw [hleft, hright, pow_two]
        ring
      _ = (t ^ 2) • A t := congrArg ((t ^ 2) • ·) hrect
  have hdet :
      Tendsto (fun t => (A t).det) (𝓝[>] (0 : Real)) (𝓝 1) := by
    simpa using (continuous_id.matrix_det.continuousAt.tendsto.comp hA)
  have hsqrt :
      Tendsto (fun t => Real.sqrt (A t).det) (𝓝[>] (0 : Real)) (𝓝 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hdet)
  refine hsqrt.congr' ?_
  filter_upwards [hgram, self_mem_nhdsWithin] with t hgramt ht
  have ht0 : (0 : Real) < t := ht
  have htpow : 0 < t ^ (Module.finrank Real E - 1) := pow_pos ht0 _
  simp only [curveDensity]
  rw [hgramt, Matrix.det_smul, Fintype.card_fin]
  have hpow :
      (t ^ 2) ^ (Module.finrank Real E - 1) =
        (t ^ (Module.finrank Real E - 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  rw [hpow, Real.sqrt_mul (sq_nonneg (t ^ (Module.finrank Real E - 1))),
    Real.sqrt_sq_eq_abs, abs_of_pos htpow,
    mul_div_cancel_left₀ _ htpow.ne']

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem poleLimit
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q : Real) (hq : 0 ≤ q)
    (v : Fin (Module.finrank Real E - 1) → TangentSpace I p)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    Tendsto
      (fun t => curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) t /
        hypDensity (q * Real.sqrt (g.inner p u u)) (Module.finrank Real E - 1) t)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  have hcd := curveDensity_pole (I := I) g hEnorm p u v hON
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

omit [CompleteSpace E] in
theorem transDens_le_hyp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
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
  have hlim := poleLimit (I := I) g hEnorm p u q hq v hON
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

omit [CompleteSpace E] in
theorem transDens_le_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : TangentSpace I p) (q : Real)
    (hq : 0 ≤ q)
    (hd : 0 < Module.finrank Real E - 1)
    (hu : 0 < g.inner p u u)
    (hno : ∀ t ∈ Set.Ioo (0 : Real) 1,
      ¬ IsConjVec (I := I) g hEnorm p
        ((t • u : TangentSpace I p) : E))
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2))) :
    ∃ v : Fin (Module.finrank Real E - 1) → TangentSpace I p,
      (∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) ∧
      (∀ i, g.inner p u (v i) = 0) ∧
      curveDensity (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm p u)
          (fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)) 1 ≤
        hypDensity (q * Real.sqrt (g.inner p u u))
          (Module.finrank Real E - 1) 1 := by
  obtain ⟨v, hON, hperp, hbound⟩ :=
    transDens_le_hyp (I := I) g hEnorm p u q 1 hq hd hu hno hRic
  refine ⟨v, hON, hperp, ?_⟩
  let γ : Real → M := intrinsicGeodesic (I := I) g hEnorm p u
  let V : Fin (Module.finrank Real E - 1) →
      ∀ t, TangentSpace I (γ t) :=
    fun i => intrinsicJacobi (I := I) g hEnorm p u (v i)
  let ell : Real := Real.sqrt (g.inner p u u)
  have hγ :
      ContMDiffAt 𝓘(Real, Real) I (1 : WithTop ℕ∞) γ 1 := by
    simpa only [γ] using
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p u).contMDiffAt
        Filter.univ_mem
  have hVdiff : ∀ i,
      DifferentiableAt Real (chartRepAt (I := I) γ (V i) 1) 1 := by
    intro i
    simpa only [γ, V] using
      (intrJacobi_diff (I := I) g hEnorm p u (v i) 1).1
  have hcurve :
      Tendsto (curveDensity (I := I) g γ V) (𝓝[<] (1 : Real))
        (𝓝 (curveDensity (I := I) g γ V 1)) :=
    (curveDensity_cont (I := I) (n := (1 : WithTop ℕ∞)) le_rfl
      g γ V 1 hγ hVdiff).tendsto.mono_left inf_le_left
  have hmodel :
      Tendsto (hypDensity (q * ell) (Module.finrank Real E - 1))
        (𝓝[<] (1 : Real))
        (𝓝 (hypDensity (q * ell) (Module.finrank Real E - 1) 1)) :=
    (hypDen_continuous (q * ell) (Module.finrank Real E - 1)).continuousAt.tendsto
      |>.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto hcurve hmodel
  filter_upwards [Ioo_mem_nhdsLT (show (0 : Real) < 1 by norm_num)] with t ht
  simpa only [γ, V, ell] using hbound t ht

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
theorem linIndep_of_ortho
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

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
