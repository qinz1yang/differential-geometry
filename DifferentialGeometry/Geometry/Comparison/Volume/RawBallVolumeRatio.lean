import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Ball
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.PolarFramed
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.CompactBall
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole
import DifferentialGeometry.Geometry.Exponential.VolumeDensity
import DifferentialGeometry.Geometry.Comparison.Volume.RatioIntegral
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Ball.Measure

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
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

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private lemma gON_li
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {v : Fin (Module.finrank ℝ E - 1) → E}
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent ℝ v := by
  let vT : Fin (Module.finrank ℝ E - 1) → TangentSpace I p :=
    fun i => show TangentSpace I p from v i
  have hONT : ∀ i j, g.inner p (vT i) (vT j) = if i = j then 1 else 0 := by
    intro i j
    exact hON i j
  have hliT := linIndep_of_ortho (I := I) g p vT hONT
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) p
  have hliE := hliT.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hliE' : LinearIndependent ℝ (e.toLinearMap ∘ vT) := hliE
  have hev : (fun i => e (vT i)) = v := by
    funext i
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) p (vT i)
  change LinearIndependent ℝ (e.toLinearMap ∘ vT) at hliE'
  rw [show e.toLinearMap ∘ vT = v by
    funext i
    exact congrFun hev i] at hliE'
  exact hliE'

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma raw_min_seg
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : E) (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hraw : L • u ∈ minimizingDomain (I := I) g p) :
    ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g (radialCurve (I := I) g p u) 0 L ≤
        arcLength (I := I) g η 0 L := by
  intro η hη hη0 hηL
  have hradLen : arcLength (I := I) g
      (radialCurve (I := I) g p u) 0 L = L := by
    unfold arcLength
    calc
      ∫ t in (0 : ℝ)..L, Real.sqrt
          (g.inner (radialCurve (I := I) g p u t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) =
          ∫ _t in (0 : ℝ)..L, (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have ht' : t ∈ Icc (0 : ℝ) L := by
              simpa only [uIcc_of_le hL.le] using ht
            have hspeed : g.inner (radialCurve (I := I) g p u t)
                (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
                (curveVelocity (I := I) (radialCurve (I := I) g p u) t) =
                g.inner p u u := by
              simpa only [radialCurve] using!
                inner_curveVelocity_expMap_smul (I := I) g p u (hdom t ht')
            change Real.sqrt
                (g.inner (radialCurve (I := I) g p u t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
                  (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) = 1
            rw [hspeed, hunit, Real.sqrt_one]
      _ = L := by simp
  have hdist := Geodesic.riemannianEDist_le_arcLength
    (I := I) g hL.le hη (fun t _ =>
      hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))
  have hdist' : riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from L • u)) ≤
      ENNReal.ofReal (arcLength (I := I) g η 0 L) := by
    simpa only [hη0, hηL] using hdist
  have hnorm : Real.sqrt (g.inner p
      (show TangentSpace I p from L • u)
      (show TangentSpace I p from L • u)) = L := by
    change Real.sqrt (g.inner p
      (L • (show TangentSpace I p from u))
      (L • (show TangentSpace I p from u))) = L
    simpa only [hunit, Real.sqrt_one, mul_one] using
      sqrt_gInner_smul_self (I := I) g p hL.le
        (show TangentSpace I p from u)
  have hdistL : ENNReal.ofReal L ≤
      ENNReal.ofReal (arcLength (I := I) g η 0 L) := by
    change ENNReal.ofReal (Real.sqrt (g.inner p
      (show TangentSpace I p from L • u)
      (show TangentSpace I p from L • u))) =
        riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from L • u)) at hraw
    rw [hnorm] at hraw
    exact hraw.le.trans hdist'
  have harc : 0 ≤ arcLength (I := I) g η 0 L := by
    unfold arcLength
    apply intervalIntegral.integral_nonneg hL.le
    intro t _
    exact Real.sqrt_nonneg _
  rw [hradLen]
  exact (ENNReal.ofReal_le_ofReal_iff harc).mp hdistL

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem raw_ratio_anti_q
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (q a : ℝ) (hq : 0 ≤ q) (ha : 0 < a)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) = a ^ 2)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p
          (show TangentSpace I p from b) : M)) (t • u)))
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
        hyperbolicDensity (q * a) (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  classical
  have hv : LinearIndependent ℝ v := gON_li (I := I) g p hON
  let t : ℝ := L / 2
  have ht : t ∈ Ioo (0 : ℝ) L := by
    dsimp only [t]
    constructor <;> linarith
  have hu_inner : g.inner p u u = a ^ 2 := by
    rw [← hspeed t ht]
    exact (inner_curveVelocity_expMap_smul (I := I) g p u
      (hdom t ⟨ht.1.le, ht.2.le⟩)).symm
  have hu_pos : 0 < g.inner p (show TangentSpace I p from u)
      (show TangentSpace I p from u) := by
    change 0 < g.inner p u u
    rw [hu_inner]
    positivity
  have hu : u ≠ 0 := by
    intro hu
    have huT : (show TangentSpace I p from u) = 0 := by
      rw [hu]
      rfl
    rw [huT] at hu_pos
    simp only [map_zero, lt_self_iff_false] at hu_pos
  have hsqrt : Real.sqrt (g.inner p u u) = a := by
    rw [hu_inner, Real.sqrt_sq_eq_abs, abs_of_pos ha]
  simpa only [Fintype.card_fin, hsqrt] using
    antitoneOn_curveDensity_radialJacobiField_div_hyperbolicDensity
      (I := I) g p u hu v hv hperp (Fintype.card_fin _) q L hq
      (fun t ht => hdom t ⟨ht.1.le, ht.2.le⟩) hinj hRic

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma raw_ratio_ray
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
  have hspeed : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) = 1 ^ 2 := by
    intro t ht
    have heq : g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) =
        g.inner p u u := by
      simpa only [radialCurve] using!
        inner_curveVelocity_expMap_smul (I := I) g p u (hdom t ⟨ht.1.le, ht.2.le⟩)
    rw [heq, hunit]
    norm_num
  have hmin := raw_min_seg (I := I) g hEnorm p u hunit L hL hdom hraw
  simpa only [mul_one] using
    raw_ratio_anti_q (I := I) g p u q 1 hq one_pos L hL hdom hspeed
      (fun t ht => injective_mfderiv_expMap_of_minimising_geodesic
        (I := I) g p u hunit hLdom hmin ht)
      v hON hperp hRic

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma rawDn_cont
    (g : SmoothRiemannianMetric I M)
    (p : M) (T : Set E)
    (hTdom : ∀ w ∈ T,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p) :
    ContinuousOn (fun w : E =>
      curveDensity (I := I) g
        (radialCurve (I := I) g p
          (normalFrame (I := I) (E := E) g p w))
        (fun i => radialJacobiField (I := I) g p
          (normalFrame (I := I) (E := E) g p w)
          (normalBasis (I := I) g p i)) 1)
  T := by
  exact (continuousOn_curveDensity_radialJacobiField_basis (I := I) g p
    (normalBasis (I := I) g p)).comp
      (normalFrame (I := I) (E := E) g p).continuous.continuousOn hTdom

omit [NeZero (Module.finrank ℝ E)] in
private lemma rawBall_normal
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀)))
    (K : Set E)
    (hK : K = extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p R)) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹'
          K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (radialCurve (I := I) g p
              (normalFrame (I := I) (E := E) g p w))
            (fun i => radialJacobiField (I := I) g p
              (normalFrame (I := I) (E := E) g p w)
              (normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure E) := by
  classical
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  have hKmeas : MeasurableSet K := by
    rw [hK]
    exact ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p R))
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    rw [hK] at hv
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1)
  have hcptR : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R)) := by
    let : TopologicalSpace M := PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
    exact hcpt.of_isClosed_subset Metric.isClosed_closedEBall
      (Metric.closedEBall_subset_closedEBall (ENNReal.ofReal_mono hRR₀.le))
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
        ∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g F v)
          ∂(modelHaar (E := E)) := by
      rw [hK]
      exact riemannianVolumeMeasure_ball_eq_lintegral_paramDensity_expMap
        (I := I) g hEnorm p R hcptR
    _ = _ := lintegral_paramDensity_expMap_eq_lintegral_curveDensity
      (I := I) g p hKmeas hKdom

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private lemma rawSegInt_ray_down
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (p : M) (A : ℝ)
    (u : Metric.sphere (0 : E) 1) {a b : Set.Ioi (0 : ℝ)}
    (hab : a ≤ b)
    (hb : (show E from normalFrame (I := I) (E := E) g p (b.1 • u.1)) ∈
      extendibleMinimizingDomain (I := I) g p ∩ (show Set E from gBall (I := I) g p A)) :
    (show E from normalFrame (I := I) (E := E) g p (a.1 • u.1)) ∈
      extendibleMinimizingDomain (I := I) g p ∩ (show Set E from gBall (I := I) g p A) := by
  let L : E ≃L[ℝ] TangentSpace I p := normalFrame (I := I) (E := E) g p
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
      (normalFrame (I := I) (E := E) g p (b.1 • u.1))
      (normalFrame (I := I) (E := E) g p (b.1 • u.1))) < A at hbBall
    simpa only [normalFrame_sqrt, norm_smul, Real.norm_of_nonneg b.2.le,
      hunorm, mul_one] using hbBall
  refine ⟨?_, ?_⟩
  · exact hInt
  · change Real.sqrt (g.inner p
      (normalFrame (I := I) (E := E) g p (a.1 • u.1))
      (normalFrame (I := I) (E := E) g p (a.1 • u.1))) < A
    simpa only [normalFrame_sqrt, norm_smul, Real.norm_of_nonneg a.2.le,
      hunorm, mul_one] using ((show a.1 ≤ b.1 from hab).trans_lt hbA)

private lemma rawBall_polar
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {t A A₀ : ℝ} (ht : 0 < t) (htA : t < A) (hAA₀ : A < A₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal A₀))) :
  let L : E → E := fun w =>
    show E from normalFrame (I := I) (E := E) g p w
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (radialCurve (I := I) g p
        (normalFrame (I := I) (E := E) g p w))
      (fun i => radialJacobiField (I := I) g p
        (normalFrame (I := I) (E := E) g p w)
        (normalBasis (I := I) g p i)) 1
  let T : Set E := L ⁻¹' (extendibleMinimizingDomain (I := I) g p ∩
    (show Set E from gBall (I := I) g p A))
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | r.1 • u.1 ∈ T}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
        ∂(volume : Measure E).toSphere := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  let L : E → E := fun w =>
    show E from normalFrame (I := I) (E := E) g p w
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (radialCurve (I := I) g p
        (normalFrame (I := I) (E := E) g p w))
      (fun i => radialJacobiField (I := I) g p
        (normalFrame (I := I) (E := E) g p w)
        (normalBasis (I := I) g p i)) 1
  let Kt : Set E := extendibleMinimizingDomain (I := I) g p ∩
    (show Set E from gBall (I := I) g p t)
  let Ka : Set E := extendibleMinimizingDomain (I := I) g p ∩
    (show Set E from gBall (I := I) g p A)
  let T : Set E := L ⁻¹' Ka
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | r.1 • u.1 ∈ T}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  have hA : 0 < A := ht.trans htA
  have htA₀ : t < A₀ := htA.trans hAA₀
  have hKa : MeasurableSet Ka := by
    simpa only [Ka] using ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p A))
  have hL : Continuous L :=
    (normalFrame (I := I) (E := E) g p).continuous
  have hT : MeasurableSet T := hKa.preimage hL.measurable
  have hTdom : ∀ w ∈ T,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p := by
    intro w hw
    change L w ∈ extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A) at hw
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw.1)
  have hDn : ContinuousOn Dn T := by
    simpa only [Dn] using rawDn_cont (I := I) g p T hTdom
  have hS (u : Metric.sphere (0 : E) 1) : MeasurableSet (S u) :=
    hT.preimage (continuous_subtype_val.smul continuous_const).measurable
  have hF (u : Metric.sphere (0 : E) 1) :
      AEMeasurable (F u) (Measure.volumeIoiPow d) := by
    apply (aemeasurable_indicator_iff (hS u)).mpr
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    have hDnS : ContinuousOn (fun r : Set.Ioi (0 : ℝ) => Dn (r.1 • u.1)) (S u) :=
      hDn.comp (continuous_subtype_val.smul continuous_const).continuousOn
        (fun r hr => hr)
    exact hDnS.aemeasurable (hS u)
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r :=
    Iio_ae_eq_Iic' (hsingle r)
  have hLt : L ⁻¹' (show Set E from gBall (I := I) g p t) =
      Metric.ball (0 : E) t := by
    with_unfolding_all exact preimage_gBall (I := I) (E := E) g p t
  have hLA : L ⁻¹' (show Set E from gBall (I := I) g p A) =
      Metric.ball (0 : E) A := by
    with_unfolding_all exact preimage_gBall (I := I) (E := E) g p A
  have hpre : (normalFrame (I := I) (E := E) g p) ⁻¹' Kt =
      T ∩ Metric.ball (0 : E) t := by
    ext w
    have hLt_w :
        L w ∈ (show Set E from gBall (I := I) g p t) ↔
          w ∈ Metric.ball (0 : E) t := Set.ext_iff.mp hLt w
    have hLA_w :
        L w ∈ (show Set E from gBall (I := I) g p A) ↔
          w ∈ Metric.ball (0 : E) A := Set.ext_iff.mp hLA w
    change ((show E from normalFrame (I := I) (E := E) g p w) ∈
          extendibleMinimizingDomain (I := I) g p ∧
        (show E from normalFrame (I := I) (E := E) g p w) ∈
          (show Set E from gBall (I := I) g p t)) ↔
      ((L w ∈ extendibleMinimizingDomain (I := I) g p ∧
          L w ∈ (show Set E from gBall (I := I) g p A)) ∧
        w ∈ Metric.ball (0 : E) t)
    constructor
    · rintro ⟨hw, hwt⟩
      have hwt' := hLt_w.mp hwt
      exact ⟨⟨hw, hLA_w.mpr (Metric.ball_subset_ball htA.le hwt')⟩, hwt'⟩
    · rintro ⟨⟨hw, _⟩, hwt⟩
      exact ⟨hw, hLt_w.mpr hwt⟩
  have hset : MeasurableSet (T ∩ Metric.ball (0 : E) t) :=
    hT.inter measurableSet_ball
  have hind : AEMeasurable
      ((T ∩ Metric.ball (0 : E) t).indicator fun w => ENNReal.ofReal (Dn w))
      (volume : Measure E) := by
    apply (aemeasurable_indicator_iff hset).mpr
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    exact (hDn.mono Set.inter_subset_left).aemeasurable hset
  have hnormal := rawBall_normal (I := I) g hEnorm p htA₀ hcpt Kt rfl
  have hpolar :
      riemannianVolumeMeasure (I := I) (M := M) g
          {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
          ∫⁻ w in (normalFrame (I := I) (E := E) g p) ⁻¹' Kt,
            ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
        simpa only [Dn] using hnormal
      _ = ∫⁻ w in T ∩ Metric.ball (0 : E) t,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by rw [hpre]
      _ = ∫⁻ w : E,
          (T ∩ Metric.ball (0 : E) t).indicator (fun z => ENNReal.ofReal (Dn z)) w
          ∂(volume : Measure E) := (lintegral_indicator hset _).symm
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ),
            (T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        let _ : Nontrivial E :=
          Module.nontrivial_of_finrank_pos
            (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
        simpa only [d] using lintegral_polar (volume : Measure E) _ hind
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        apply lintegral_congr
        intro u
        have hu : ‖u.1‖ = 1 := by
          simpa only [mem_sphere_zero_iff_norm] using u.2
        have hball (r : Set.Ioi (0 : ℝ)) :
            r.1 • u.1 ∈ Metric.ball (0 : E) t ↔
              r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)) := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_of_nonneg r.2.le, hu, mul_one]
          rfl
        calc
          (∫⁻ r : Set.Ioi (0 : ℝ),
              (T ∩ Metric.ball (0 : E) t).indicator
                (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d) =
              ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
                ∂Measure.volumeIoiPow d := by
            rw [← lintegral_indicator measurableSet_Iio]
            apply lintegral_congr
            intro r
            have hseg : r ∈ S u ↔ r.1 • u.1 ∈ T := Iff.rfl
            dsimp only [F]
            by_cases hrS : r ∈ S u
            · by_cases hrt : r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · have hmem : r.1 • u.1 ∈ T ∩ Metric.ball (0 : E) t :=
                  ⟨hseg.mp hrS, (hball r).mpr hrt⟩
                rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hrt,
                  Set.indicator_of_mem hrS]
              · rw [Set.indicator_of_notMem (fun h => hrt ((hball r).mp h.2)),
                  Set.indicator_of_notMem hrt]
            · rw [Set.indicator_of_notMem (fun h => hrS (hseg.mpr h.1))]
              by_cases hrt : r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · rw [Set.indicator_of_mem hrt, Set.indicator_of_notMem hrS]
              · rw [Set.indicator_of_notMem hrt]
          _ = ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d := setLIntegral_congr (hIio ⟨t, ht⟩)
  simpa only [d, L, Dn, T, S, F] using hpolar

theorem rawBall_vol_rel
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {q s R R₀ : ℝ} (hq : 0 ≤ q) (hs : 0 < s) (hsR : s ≤ R)
    (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀)))
    (hRic : ∀ (y : M) (v : TangentSpace I y),
      riemannianEDist I p y < ENNReal.ofReal R₀ →
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
  let d : ℕ := Module.finrank ℝ E - 1
  let A : ℝ := (R + R₀) / 2
  let L : E → E := fun w =>
    show E from normalFrame (I := I) (E := E) g p w
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g p
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (radialCurve (I := I) g p
        (normalFrame (I := I) (E := E) g p w))
      (fun i => radialJacobiField (I := I) g p
        (normalFrame (I := I) (E := E) g p w)
        (normalBasis (I := I) g p i)) 1
  let T : Set E := L ⁻¹' (extendibleMinimizingDomain (I := I) g p ∩
    (show Set E from gBall (I := I) g p A))
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | r.1 • u.1 ∈ T}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (hyperbolicDensity (q * r.1) d 1)
  have hR : 0 < R := hs.trans_le hsR
  have hA : 0 < A := by
    dsimp only [A]
    linarith
  have hRA : R < A := by
    dsimp only [A]
    linarith
  have hAA₀ : A < R₀ := by
    dsimp only [A]
    linarith
  have hsA : s < A := hsR.trans_lt hRA
  have hK : MeasurableSet (extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A)) :=
    ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p A))
  have hL : Continuous L :=
    (normalFrame (I := I) (E := E) g p).continuous
  have hT : MeasurableSet T := hK.preimage hL.measurable
  have hTdom : ∀ w ∈ T,
      normalFrame (I := I) (E := E) g p w ∈ expDomain (I := I) g p := by
    intro w hw
    change L w ∈ extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A) at hw
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw.1)
  have hDn_cont : ContinuousOn Dn T := by
    simpa only [Dn] using rawDn_cont (I := I) g p T hTdom
  have hDn_nonneg (w : E) : 0 ≤ Dn w := by
    simp only [Dn, curveDensity]
    exact Real.sqrt_nonneg _
  have hS_meas (u : Metric.sphere (0 : E) 1) : MeasurableSet (S u) :=
    hT.preimage (continuous_subtype_val.smul continuous_const).measurable
  have hF_meas (u : Metric.sphere (0 : E) 1) :
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
  have hS_down (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) : a ∈ S u := by
    change L (b.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A) at hb
    change L (a.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p A)
    simpa only [L] using rawSegInt_ray_down (I := I) g p A u hab hb
  have hu_inner (u : Metric.sphere (0 : E) 1) :
      g.inner p (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    dsimp only [L]
    rw [normalFrame_inner, real_inner_self_eq_norm_sq, hunorm, one_pow]
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
  have hpolar {t : ℝ} (ht : 0 < t) (htA : t < A) :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I p y < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d ∂(volume : Measure E).toSphere := by
    simpa only [d, L, Dn, T, S, F] using
      rawBall_polar (I := I) g hEnorm p ht htA hAA₀ hcpt
  have hcross (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b)
      (hbR : b ≤ (⟨R, hR⟩ : Set.Ioi (0 : ℝ))) :
      F u b * G a ≤ F u a * G b := by
    by_cases hbS : b ∈ S u
    · have haS : a ∈ S u := hS_down u hab hbS
      have hbS' := hbS
      change L (b.1 • u.1) ∈ extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p A) at hbS'
      let uT : E := L u.1
      have huT_one : g.inner p uT uT = 1 := by
        simpa only [uT] using hu_inner u
      have huT_pos : 0 < g.inner p uT uT := by
        simpa only [huT_one] using one_pos
      have hrawIntB : b.1 • uT ∈ extendibleMinimizingDomain (I := I) g p := by
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          exact (normalFrame (I := I) (E := E) g p).map_smul b.1 u.1
        rw [← hLb]
        exact hbS'.1
      obtain ⟨c, hc, hcraw⟩ := hrawIntB
      have hc0 : 0 < c := one_pos.trans hc
      have hcb : b.1 < c * b.1 := lt_mul_of_one_lt_left b.2 hc
      let ell : ℝ := min ((c * b.1 + b.1) / 2) A
      have hbell : b.1 < ell := by
        apply lt_min
        · nlinarith
        · exact (show b.1 ≤ R from hbR).trans_lt hRA
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
            ENNReal.ofReal R₀ := by
          change ENNReal.ofReal (Real.sqrt (g.inner p (t • uT) (t • uT))) =
            riemannianEDist I p (radialCurve (I := I) g p uT t) at hrawT
          rw [← hrawT, hnormT]
          exact (ENNReal.ofReal_lt_ofReal_iff (hA.trans hAA₀)).mpr
            (lt_trans (lt_of_lt_of_le ht.2 hellA) hAA₀)
        exact hRic _ _ hball
      by_cases hd : 0 < d
      · obtain ⟨v, hON, hperp'⟩ := exists_perp_pos (I := I) g p uT huT_pos
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
            raw_ratio_ray (I := I) g hEnorm p uT q ell hq hellpos huT_one hrawL
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
            exact (normalFrame (I := I) (E := E) g p).map_smul r u.1
          have hDn : Dn (r • u.1) = C *
              curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                (fun i => radialJacobiField (I := I) g p (r • uT)
                  (chartModelBasis E i)) 1 := by
            dsimp only [Dn]
            have hNr : normalFrame (I := I) (E := E) g p (r • u.1) =
                (show TangentSpace I p from r • uT) := by
              with_unfolding_all exact
                (normalFrame (I := I) (E := E) g p).map_smul r u.1
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
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        let v : Fin d → E := fun i => isEmptyElim (hd0 ▸ i)
        have hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hperp : ∀ i, g.inner p uT (v i) = 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g (radialCurve (I := I) g p uT)
            (fun i => radialJacobiField (I := I) g p uT (v i)) t
        have hDt (t : ℝ) : Dt t = 1 := by
          have hgram : curveGram (I := I) g (radialCurve (I := I) g p uT)
              (fun i => radialJacobiField (I := I) g p uT (v i)) t = 1 := by
            ext i
            exact isEmptyElim (hd0 ▸ i)
          simp only [Dt, curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
        have hdomA : ∀ t ∈ Set.Icc (0 : ℝ) a.1,
            (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p :=
          fun t ht => hdomB t ⟨ht.1, ht.2.trans hab⟩
        let C : ℝ := |(chartModelBasis E).det B|
        let N : ℝ := paramDensity (I := I) g
          (fun x : E => expMap (I := I) g p (show TangentSpace I p from x)) 0
        have hscale (r : ℝ) (hr : 0 < r)
            (hdom : ∀ t ∈ Set.Icc (0 : ℝ) r,
              (show TangentSpace I p from t • uT) ∈ expDomain (I := I) g p) :
            r ^ d * Dn (r • u.1) = (C * N) * Dt r := by
          have hLr : L (r • u.1) = r • uT := by
            exact (normalFrame (I := I) (E := E) g p).map_smul r u.1
          have hDn : Dn (r • u.1) = C *
              curveDensity (I := I) g (radialCurve (I := I) g p (r • uT))
                (fun i => radialJacobiField (I := I) g p (r • uT)
                  (chartModelBasis E i)) 1 := by
            dsimp only [Dn]
            have hNr : normalFrame (I := I) (E := E) g p (r • u.1) =
                (show TangentSpace I p from r • uT) := by
              with_unfolding_all exact
                (normalFrame (I := I) (E := E) g p).map_smul r u.1
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
        have hDa : Dn (a.1 • u.1) = C * N := by
          have h := hscale a.1 a.2 hdomA
          simpa only [hd0, pow_zero, one_mul, mul_one, hDt] using h
        have hDb : Dn (b.1 • u.1) = C * N := by
          have h := hscale b.1 b.2 hdomB
          simpa only [hd0, pow_zero, one_mul, mul_one, hDt] using h
        have hGa : hyperbolicDensity (q * a.1) d 1 = 1 := by
          simp only [hd0, hyperbolicDensity, pow_zero]
        have hGb : hyperbolicDensity (q * b.1) d 1 = 1 := by
          simp only [hd0, hyperbolicDensity, pow_zero]
        simp only [F, G, Set.indicator_of_mem hbS, Set.indicator_of_mem haS,
          hDa, hDb, hGa, hGb, ENNReal.ofReal_one, mul_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
  have hdir (u : Metric.sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hyperbolicRadialVolume q d s) ≤
        (∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) * ENNReal.ofReal (hyperbolicRadialVolume q d R) := by
    have h := lintegral_Iic_cross
      (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
      (hF_meas u).restrict hG_meas.aemeasurable.restrict
      (fun {_a _b} hab hbR => hcross u hab hbR)
      (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
    rw [hmodel hs, hmodel hR] at h
    exact h
  rw [show Module.finrank ℝ E - 1 = d by rfl]
  rw [hpolar hR hRA, hpolar hs hsA]
  rw [mul_comm (ENNReal.ofReal (hyperbolicRadialVolume q d R))
    (∫⁻ u : Metric.sphere (0 : E) 1,
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d ∂(volume : Measure E).toSphere)]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hyperbolicRadialVolume q d s))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const' (ENNReal.ofReal (hyperbolicRadialVolume q d R))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d) ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
