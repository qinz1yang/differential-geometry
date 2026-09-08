import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.CompactBall
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole
import DifferentialGeometry.Analysis.Integration.Measure.Lebesgue.RatioMonotonicity

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open Exponential
open NormalCoordinates
open Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [local instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance tangentSpaceNormedAddCommGroup
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

local notation "F₀" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [SigmaCompactSpace M]
    [T2Space (TangentBundle I M)] in
private lemma antitoneOn_radial_density_ratio_of_minimizing_endpoint
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) (q L : ℝ)
    (hq : 0 ≤ q) (hL : 0 < L)
    (hunit : g.inner p u u = 1)
    (hraw : L • u ∈ minimizingDomain (I := I) g p)
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t) ≤
        ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hyperbolicDensity q (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  have hLdom : (show TangentSpace I p from L • u) ∈ expDomain (I := I) g p :=
    minimizingDomain_subset_expDomain (I := I) g p hraw
  have hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p := by
    intro t ht
    have hfrac : t / L ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1 hL.le, (div_le_one hL).mpr ht.2⟩
    have hscale := Exponential.smul_mem_expDomain (I := I) (g := g) (p := p)
      (v := show TangentSpace I p from L • u) hLdom hfrac
    change (show TangentSpace I p from (t / L) • (L • u)) ∈
      expDomain (I := I) g p at hscale
    simpa only [smul_smul, div_mul_cancel₀ t hL.ne', one_smul] using hscale
  have hinj (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) L) :
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) (t • u)) := by
    have hfrac : t / L ∈ Ico (0 : ℝ) 1 :=
      ⟨div_nonneg ht.1.le hL.le, (div_lt_one hL).mpr ht.2⟩
    have h := injective_mfderiv_expMap_of_le_riemannianEDist (I := I) g hEnorm
      p (L • u) hLdom hraw.le hfrac
    have heq : ((t / L) • (L • u) : E) = t • u := by
      rw [smul_smul, div_mul_cancel₀ t hL.ne']
    exact (congrArg (fun x : E => Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) x)) heq).mp h
  have hu : u ≠ 0 := by
    intro hzero
    have huT : (show TangentSpace I p from u) = 0 := by
      rw [hzero]
      rfl
    rw [huT, map_zero] at hunit
    norm_num at hunit
  have hsqrt : Real.sqrt (g.inner p u u) = 1 := by
    rw [hunit, Real.sqrt_one]
  simpa only [Fintype.card_fin, hsqrt, mul_one] using
    antitoneOn_curveDensity_radialJacobiField_div_hyperbolicDensity
      (I := I) g p u hu v (by
        simpa only using!
          (linIndep_of_ortho (I := I) g p (fun i => show TangentSpace I p from v i) hON))
      hperp (Fintype.card_fin _)
      q L hq (fun t ht => hdom t ⟨ht.1.le, ht.2.le⟩) hinj hRic

omit [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private lemma euclideanNormalFrame_smul_mem_extendibleMinimizingDomain_inter_gBall_of_le
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) (A : ℝ)
    (u : Metric.sphere (0 : F₀) 1) {a b : Set.Ioi (0 : ℝ)}
    (hab : a ≤ b)
    (hb : (show E from euclideanNormalFrame (I := I) (E := E) g p (b.1 • u.1)) ∈
      extendibleMinimizingDomain (I := I) g p ∩ (show Set E from gBall (I := I) g p A)) :
    (show E from euclideanNormalFrame (I := I) (E := E) g p (a.1 • u.1)) ∈
      extendibleMinimizingDomain (I := I) g p ∩ (show Set E from gBall (I := I) g p A) := by
  let L : F₀ ≃L[ℝ] TangentSpace I p := euclideanNormalFrame (I := I) (E := E) g p
  let uT : E := show E from L u.1
  have hunorm : ‖u.1‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using u.2
  have hLa : (show E from L (a.1 • u.1)) = a.1 • uT := by
    exact L.map_smul a.1 u.1
  have hLb : (show E from L (b.1 • u.1)) = b.1 • uT := by
    exact L.map_smul b.1 u.1
  have hbInt : (show E from L (b.1 • u.1)) ∈ extendibleMinimizingDomain (I := I) g p := hb.1
  have hInt : (show E from L (a.1 • u.1)) ∈ extendibleMinimizingDomain (I := I) g p := by
    rw [hLa]
    exact smul_mem_extendibleMinimizingDomain_of_pos_of_le (I := I) g p a.2 hab (hLb ▸ hbInt)
  have hbA : b.1 < A := by
    have hbBall := hb.2
    change Real.sqrt (g.inner p
      (euclideanNormalFrame (I := I) (E := E) g p (b.1 • u.1))
      (euclideanNormalFrame (I := I) (E := E) g p (b.1 • u.1))) < A at hbBall
    simpa only [euclideanNormalFrame_sqrt, norm_smul, Real.norm_of_nonneg b.2.le,
      hunorm, mul_one] using hbBall
  refine ⟨?_, ?_⟩
  · exact hInt
  · change Real.sqrt (g.inner p
      (euclideanNormalFrame (I := I) (E := E) g p (a.1 • u.1))
      (euclideanNormalFrame (I := I) (E := E) g p (a.1 • u.1))) < A
    simpa only [euclideanNormalFrame_sqrt, norm_smul, Real.norm_of_nonneg a.2.le,
      hunorm, mul_one] using ((show a.1 ≤ b.1 from hab).trans_lt hbA)

theorem bishop_gromov_of_isCompact_closedEBall
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {q s R : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R)))
    (hRic : ∀ (y : M) (v : TangentSpace I y),
      riemannianEDist I p y < ENNReal.ofReal R →
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
            g.inner y v v ≤
          ricciTensor (I := I) g y v v) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal R} *
        ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) s) ≤
      ENNReal.ofReal (hyperbolicRadialVolume q (Module.finrank ℝ E - 1) R) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal s} := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl h =>
    let _ : Subsingleton H := I.injective.subsingleton
    let _ : DiscreteTopology M := ChartedSpace.discreteTopology H M
    have hdim : Module.finrank ℝ E = 0 := Module.finrank_zero_of_subsingleton
    have hball {t : ℝ} (ht : 0 < t) :
        {y : M | riemannianEDist I p y < ENNReal.ofReal t} = {p} := by
      ext y
      constructor
      · intro hy
        obtain ⟨γ, hγ0, hγ1, hγsmooth, _⟩ := exists_lt_of_riemannianEDist_lt hy
        have hpy : p = y := by
          rw [← hγ0, ← hγ1]
          exact isPreconnected_Icc.constant hγsmooth.continuousOn (by simp) (by simp)
        exact hpy.symm
      · intro hy
        rw [mem_singleton_iff] at hy
        subst y
        change riemannianEDist I p p < ENNReal.ofReal t
        rw [riemannianEDist_self]
        exact ENNReal.ofReal_pos.mpr ht
    have hmodel (t : ℝ) : hyperbolicRadialVolume q 0 t = t := by
      simp [hyperbolicRadialVolume, hyperbolicDensity]
    rw [hdim, Nat.zero_sub, hmodel, hmodel, hball hs, hball (hs.trans_le hsR)]
    rw [mul_comm (ENNReal.ofReal R)]
    exact mul_le_mul' le_rfl (ENNReal.ofReal_mono hsR)
  | inr h =>
    let _ : NeZero (Module.finrank ℝ E) := ⟨Nat.ne_of_gt Module.finrank_pos⟩
    let d : ℕ := Module.finrank ℝ E - 1
    let A : ℝ := R
    let L : F₀ → E := fun w =>
      show E from euclideanNormalFrame (I := I) (E := E) g p w
    let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
      normalBasis (I := I) g p
    let Dn : F₀ → ℝ := fun w =>
      curveDensity (I := I) g
        (radialCurve (I := I) g p
          (euclideanNormalFrame (I := I) (E := E) g p w))
        (fun i => radialJacobiField (I := I) g p
          (euclideanNormalFrame (I := I) (E := E) g p w)
          (normalBasis (I := I) g p i)) 1
    let T : Set F₀ := L ⁻¹' (extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A))
    let S : Metric.sphere (0 : F₀) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
      {r | r.1 • u.1 ∈ T}
    let F : Metric.sphere (0 : F₀) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
      (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
    let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
      ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1)
    have hR : 0 < R := hs.trans_le hsR
    have hsA : s ≤ A := hsR
    have hK : MeasurableSet (extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p A)) :=
      ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
        (measurableSet_gBall (I := I) g p A))
    have hL : Continuous L :=
      (euclideanNormalFrame (I := I) (E := E) g p).continuous
    have hT : MeasurableSet T := hK.preimage hL.measurable
    have hTdom : ∀ w ∈ T,
        euclideanNormalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p := by
      intro w hw
      change L w ∈ extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p A) at hw
      exact minimizingDomain_subset_expDomain (I := I) g p
        (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw.1)
    have hDn_cont : ContinuousOn Dn T := by
      exact (continuousOn_curveDensity_radialJacobiField_basis (I := I) g p
        (normalBasis (I := I) g p)).comp
          (euclideanNormalFrame (I := I) g p).continuous.continuousOn hTdom
    have hDn_nonneg (w : F₀) : 0 ≤ Dn w := by
      simp only [Dn, curveDensity]
      exact Real.sqrt_nonneg _
    have hS_meas (u : Metric.sphere (0 : F₀) 1) : MeasurableSet (S u) :=
      hT.preimage (continuous_subtype_val.smul continuous_const).measurable
    have hF_meas (u : Metric.sphere (0 : F₀) 1) :
        AEMeasurable (F u) (Measure.volumeIoiPow d) := by
      apply (aemeasurable_indicator_iff (hS_meas u)).mpr
      apply ENNReal.measurable_ofReal.comp_aemeasurable
      have hDnS : ContinuousOn (fun r : Set.Ioi (0 : ℝ) => Dn (r.1 • u.1)) (S u) :=
        hDn_cont.comp (continuous_subtype_val.smul continuous_const).continuousOn
          (fun r hr => hr)
      exact hDnS.aemeasurable (hS_meas u)
    have hG_meas : Measurable G := by
      have hscale (r : Set.Ioi (0 : ℝ)) :
          hyperbolicDensity (q * r.1) d 1 =
            hyperbolicDensity q d r.1 / r.1 ^ d := by
        apply (eq_div_iff (pow_ne_zero d r.2.ne')).2
        simpa only [mul_one, mul_comm] using
          hyperbolicDens_scale q r.1 d 1 r.2.ne'
      rw [show G = fun r : Set.Ioi (0 : ℝ) =>
          ENNReal.ofReal (hyperbolicDensity q d r.1 / r.1 ^ d) by
        funext r
        change ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1) =
          ENNReal.ofReal (hyperbolicDensity q d r.1 / r.1 ^ d)
        rw [hscale r]]
      exact ENNReal.measurable_ofReal.comp
        (((hyperbolicDen_continuous q d).measurable.comp measurable_subtype_coe).div
          (measurable_subtype_coe.pow_const d))
    have hS_down (u : Metric.sphere (0 : F₀) 1)
        {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) : a ∈ S u := by
      change L (b.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p A) at hb
      change L (a.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p A)
      simpa only [L] using euclideanNormalFrame_smul_mem_extendibleMinimizingDomain_inter_gBall_of_le (I := I) g p A u hab hb
    have hu_inner (u : Metric.sphere (0 : F₀) 1) :
        g.inner p (L u.1) (L u.1) = 1 := by
      have hunorm : ‖u.1‖ = 1 := by
        simpa only [mem_sphere_zero_iff_norm] using u.2
      dsimp only [L]
      rw [euclideanNormalFrame_inner, real_inner_self_eq_norm_sq, hunorm, one_pow]
    have hsingle (r : Set.Ioi (0 : ℝ)) :
        Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
      rw [Measure.volumeIoiPow]
      apply withDensity_absolutelyContinuous
      rw [comap_subtype_coe_apply measurableSet_Ioi]
      exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
        Set.subsingleton_singleton).image ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
    have hIio (r : Set.Ioi (0 : ℝ)) :
        Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r := Iio_ae_eq_Iic' (hsingle r)
    have hmodel {t : ℝ} (ht : 0 < t) :
        (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
            ∂Measure.volumeIoiPow d) =
          ENNReal.ofReal (hyperbolicRadialVolume q d t) := by
      calc
        (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
            ∂Measure.volumeIoiPow d) =
            ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
            ∂Measure.volumeIoiPow d := setLIntegral_congr (hIio ⟨t, ht⟩).symm
        _ = ∫⁻ r : Set.Ioi (0 : ℝ),
            (Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))).indicator G r ∂Measure.volumeIoiPow d :=
          (lintegral_indicator measurableSet_Iio G).symm
        _ = ENNReal.ofReal (hyperbolicRadialVolume q d t) := by
          simpa only [G] using
            lintegral_hyperbolicDensity_eq_hyperbolicRadialVolume q hq d ht
    have hpolar {t : ℝ} (ht : 0 < t) (htA : t ≤ A) :
        riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I p y < ENNReal.ofReal t} =
          ∫⁻ u : Metric.sphere (0 : F₀) 1,
            ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d ∂(volume : Measure F₀).toSphere := by
      calc
        _ = ∫⁻ u : Metric.sphere (0 : F₀) 1,
            ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)),
              T.indicator (fun w => ENNReal.ofReal (Dn w)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d ∂(volume : Measure F₀).toSphere :=
          riemannianVolumeMeasure_ball_eq_lintegral_polar_euclideanNormalFrame
            (I := I) g hEnorm p htA hcpt
        _ = _ := by
          apply lintegral_congr
          intro u
          rw [setLIntegral_congr (hIio ⟨t, ht⟩)]
          apply lintegral_congr
          intro r
          by_cases hr : r.1 • u.1 ∈ T <;> simp [F, S, hr]
    have hcross (u : Metric.sphere (0 : F₀) 1)
        {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) :
        F u b * G a ≤ F u a * G b := by
      by_cases hbS : b ∈ S u
      · have haS : a ∈ S u := hS_down u hab hbS
        have hbS' := hbS
        change L (b.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
          (show Set E from gBall (I := I) g p A) at hbS'
        have hbA : b.1 < A := by
          have hbBall := hbS'.2
          change Real.sqrt (g.inner p
            (euclideanNormalFrame (I := I) (E := E) g p (b.1 • u.1))
            (euclideanNormalFrame (I := I) (E := E) g p (b.1 • u.1))) < A at hbBall
          have hunorm : ‖u.1‖ = 1 := by
            simpa only [mem_sphere_zero_iff_norm] using u.2
          simpa only [euclideanNormalFrame_sqrt, norm_smul, Real.norm_of_nonneg b.2.le,
            hunorm, mul_one] using hbBall
        let uT : E := L u.1
        have huT_one : g.inner p uT uT = 1 := by
          simpa only [uT] using hu_inner u
        have huT_pos : 0 < g.inner p uT uT := by
          simpa only [huT_one] using one_pos
        have hrawIntB : b.1 • uT ∈ extendibleMinimizingDomain (I := I) g p := by
          have hLb : L (b.1 • u.1) = b.1 • uT := by
            exact (euclideanNormalFrame (I := I) (E := E) g p).map_smul b.1 u.1
          rw [← hLb]
          exact hbS'.1
        obtain ⟨c, hc, hcraw⟩ := hrawIntB
        have hc0 : 0 < c := one_pos.trans hc
        have hcb : b.1 < c * b.1 := lt_mul_of_one_lt_left b.2 hc
        let ell : ℝ := min ((c * b.1 + b.1) / 2) A
        have hbell : b.1 < ell := by
          apply lt_min
          · nlinarith
          · exact hbA
        have hellpos : 0 < ell := b.2.trans hbell
        have hellA : ell ≤ A := min_le_right _ _
        have hellcb : ell < c * b.1 := by
          calc
            ell ≤ (c * b.1 + b.1) / 2 := min_le_left _ _
            _ < c * b.1 := by nlinarith
        have hrawIntL : ell • uT ∈ extendibleMinimizingDomain (I := I) g p := by
          refine ⟨c * b.1 / ell, (lt_div_iff₀ hellpos).mpr (by
            simpa only [one_mul] using hellcb), ?_⟩
          simpa only [smul_smul, div_mul_cancel₀ (c * b.1) hellpos.ne'] using hcraw
        have hrawL : ell • uT ∈ minimizingDomain (I := I) g p :=
          extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hrawIntL
        have hdomB : ∀ t ∈ Set.Icc (0 : ℝ) b.1,
            (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p := by
          intro t ht
          have hfrac : t / ell ∈ Set.Icc (0 : ℝ) 1 :=
            ⟨div_nonneg ht.1 hellpos.le, (div_le_one hellpos).mpr (ht.2.trans hbell.le)⟩
          have hscale := Exponential.smul_mem_expDomain (I := I) (g := g) (p := p)
            (v := show TangentSpace I p from ell • uT)
            (minimizingDomain_subset_expDomain (I := I) g p hrawL) hfrac
          change (show TangentSpace I p from (t / ell) • (ell • uT)) ∈
            expDomain (I := I) g p at hscale
          simpa only [smul_smul, div_mul_cancel₀ t hellpos.ne', one_smul] using hscale
        have hRicRay : ∀ t ∈ Set.Ioo (0 : ℝ) ell,
            -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
                g.inner (radialCurve (I := I) g p uT t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p uT) t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p uT) t) ≤
              ricciTensor (I := I) g (radialCurve (I := I) g p uT t)
                (curveVelocity (I := I) (radialCurve (I := I) g p uT) t)
                (curveVelocity (I := I) (radialCurve (I := I) g p uT) t) := by
          intro t ht
          have hrawIntT : t • uT ∈ extendibleMinimizingDomain (I := I) g p :=
            smul_mem_extendibleMinimizingDomain_of_pos_of_le (I := I) g p ht.1 ht.2.le hrawIntL
          have hrawT := extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hrawIntT
          have hnormT : Real.sqrt (g.inner p (t • uT) (t • uT)) = t := by
            calc
              Real.sqrt (g.inner p (t • uT) (t • uT)) =
                  t * Real.sqrt (g.inner p uT uT) := by
                with_unfolding_all exact
                  sqrt_gInner_smul_self (I := I) g p ht.1.le uT
              _ = t := by rw [huT_one, Real.sqrt_one, mul_one]
          have hball : riemannianEDist I p (radialCurve (I := I) g p uT t) <
              ENNReal.ofReal R := by
            change ENNReal.ofReal (Real.sqrt (g.inner p (t • uT) (t • uT))) =
              riemannianEDist I p (radialCurve (I := I) g p uT t) at hrawT
            rw [← hrawT, hnormT]
            exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr (lt_of_lt_of_le ht.2 hellA)
          exact hRic _ _ hball
        obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p uT huT_pos
        have hperp : ∀ i, g.inner p uT (v i) = 0 := by
          intro i
          rw [g.symm p uT (v i)]
          exact hperp' i
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g (radialCurve (I := I) g p uT)
            (fun i => radialJacobiField (I := I) g p uT (v i)) t
        have hanti : AntitoneOn (fun t => Dt t / hyperbolicDensity q d t)
            (Set.Ioo (0 : ℝ) ell) := by
          simpa only [Dt, d, huT_one, Real.sqrt_one, mul_one] using
            antitoneOn_radial_density_ratio_of_minimizing_endpoint (I := I) g hEnorm p uT q ell hq hellpos huT_one hrawL
              v hON hperp hRicRay
        have haWin : a.1 ∈ Set.Ioo (0 : ℝ) ell :=
          ⟨a.2, (show a.1 ≤ b.1 from hab).trans_lt hbell⟩
        have hbWin : b.1 ∈ Set.Ioo (0 : ℝ) ell := ⟨b.2, hbell⟩
        have hratio := hanti haWin hbWin hab
        have hHa : 0 < hyperbolicDensity q d a.1 := hyperbolicDensity_pos hq a.2
        have hHb : 0 < hyperbolicDensity q d b.1 := hyperbolicDensity_pos hq b.2
        have htrans : Dt b.1 * hyperbolicDensity q d a.1 ≤
            Dt a.1 * hyperbolicDensity q d b.1 :=
          (div_le_div_iff₀ hHb hHa).1 hratio
        have hdomA : ∀ t ∈ Set.Icc (0 : ℝ) a.1,
            (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p :=
          fun t ht => hdomB t ⟨ht.1, ht.2.trans hab⟩
        let C : ℝ := |(chartModelBasis E).det B|
        let N : ℝ := paramDensity (I := I) g
          (fun x : E => expMap (I := I) g p (show TangentSpace I p from x)) 0
        have hCN : 0 ≤ C * N := by
          dsimp only [C, N]
          exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
        have hscale (r : ℝ) (hr : 0 < r)
            (hdom : ∀ t ∈ Set.Icc (0 : ℝ) r,
              (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p) :
            r ^ d * Dn (r • u.1) = (C * N) * Dt r := by
          have hLr : L (r • u.1) = r • uT := by
            exact (euclideanNormalFrame (I := I) (E := E) g p).map_smul r u.1
          have hDn : Dn (r • u.1) = C *
              curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                (fun i => radialJacobiField (I := I) g p (r • uT)
                  (chartModelBasis E i)) 1 := by
            dsimp only [Dn]
            have hNr : euclideanNormalFrame (I := I) (E := E) g p (r • u.1) =
                (show TangentSpace I p from r • uT) := by
              with_unfolding_all exact
                (euclideanNormalFrame (I := I) (E := E) g p).map_smul r u.1
            rw [hNr]
            have hbasis := curveDensity_radialJacobiField_basis
              (I := I) g p (r • uT)
              (hdom r ⟨hr.le, le_rfl⟩) (chartModelBasis E) B
            have hBval (i : Fin (Module.finrank ℝ E)) :
                normalBasis (I := I) g p i =
                  (show TangentSpace I p from B i) := by
              with_unfolding_all rfl
            simpa only [hBval, B, C] using hbasis
          have hrdom := hdom r ⟨hr.le, le_rfl⟩
          have hfac := paramDensity_expMap_smul_mul_pow_of_orthonormal
            (I := I) g p uT v hON hperp r hrdom
          rw [paramDensity_expMap_eq_curveDensity (I := I) g p (r • uT) hrdom,
            abs_of_pos hr] at hfac
          calc
            r ^ d * Dn (r • u.1) = C *
                (curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                  (fun i => radialJacobiField (I := I) g p (r • uT)
                    (chartModelBasis E i)) 1 * r ^ d) := by rw [hDn]; ring
            _ = C * (N * Dt r) := by simpa only [N] using congrArg (fun z => C * z) hfac
            _ = (C * N) * Dt r := by ring
        have hSa := hscale a.1 a.2 hdomA
        have hSb := hscale b.1 b.2 hdomB
        have hGa : a.1 ^ d * hyperbolicDensity (q * a.1) d 1 =
            hyperbolicDensity q d a.1 := by
          simpa only [mul_one] using hyperbolicDens_scale q a.1 d 1 a.2.ne'
        have hGb : b.1 ^ d * hyperbolicDensity (q * b.1) d 1 =
            hyperbolicDensity q d b.1 := by
          simpa only [mul_one] using hyperbolicDens_scale q b.1 d 1 b.2.ne'
        have hpowa : 0 < a.1 ^ d := pow_pos a.2 d
        have hpowb : 0 < b.1 ^ d := pow_pos b.2 d
        have hreal : Dn (b.1 • u.1) * hyperbolicDensity (q * a.1) d 1 ≤
            Dn (a.1 • u.1) * hyperbolicDensity (q * b.1) d 1 := by
          apply (mul_le_mul_iff_right₀ (mul_pos hpowa hpowb)).mp
          calc
            (a.1 ^ d * b.1 ^ d) *
                (Dn (b.1 • u.1) * hyperbolicDensity (q * a.1) d 1) =
                (b.1 ^ d * Dn (b.1 • u.1)) *
                  (a.1 ^ d * hyperbolicDensity (q * a.1) d 1) := by ring
            _ = (C * N) * (Dt b.1 * hyperbolicDensity q d a.1) := by
              rw [hSb, hGa]
              ring
            _ ≤ (C * N) * (Dt a.1 * hyperbolicDensity q d b.1) :=
              mul_le_mul_of_nonneg_left htrans hCN
            _ = (a.1 ^ d * Dn (a.1 • u.1)) *
                (b.1 ^ d * hyperbolicDensity (q * b.1) d 1) := by
              rw [hSa, hGb]
              ring
            _ = (a.1 ^ d * b.1 ^ d) *
                (Dn (a.1 • u.1) * hyperbolicDensity (q * b.1) d 1) := by ring
        simp only [F, G, Set.indicator_of_mem hbS, Set.indicator_of_mem haS]
        rw [← ENNReal.ofReal_mul (hDn_nonneg (b.1 • u.1)),
          ← ENNReal.ofReal_mul (hDn_nonneg (a.1 • u.1))]
        exact ENNReal.ofReal_le_ofReal hreal
      · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
    have hdir (u : Metric.sphere (0 : F₀) 1) :
        (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hyperbolicRadialVolume q d s) ≤
          (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
      have h := MeasureTheory.setLIntegral_Iic_mul_setLIntegral_Iic_le
        (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
        (hF_meas u).restrict hG_meas.aemeasurable.restrict
        (fun {_a _b} hab _ => hcross u hab)
        (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
      rw [hmodel hs, hmodel hR] at h
      exact h
    rw [show Module.finrank ℝ E - 1 = d by rfl]
    rw [hpolar hR le_rfl, hpolar hs hsA]
    rw [mul_comm (ENNReal.ofReal (hyperbolicRadialVolume q d R))
      (∫⁻ u : Metric.sphere (0 : F₀) 1,
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d ∂(volume : Measure F₀).toSphere)]
    rw [← lintegral_mul_const' (ENNReal.ofReal (hyperbolicRadialVolume q d s))
      (fun u : Metric.sphere (0 : F₀) 1 =>
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
    rw [← lintegral_mul_const' (ENNReal.ofReal (hyperbolicRadialVolume q d R))
      (fun u : Metric.sphere (0 : F₀) 1 =>
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
    exact lintegral_mono hdir

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
