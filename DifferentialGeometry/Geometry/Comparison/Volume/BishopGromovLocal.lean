import DifferentialGeometry.Geometry.Comparison.Volume.BishopGromovNonpositiveLocal

open DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold MeasureTheory Metric
open scoped Topology Manifold ContDiff ENNReal

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Volume
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance instMeasTangent (x : M) : MeasurableSpace (TangentSpace I x) :=
  borel _
private local instance instBorelTangent (x : M) : BorelSpace (TangentSpace I x) :=
  ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem modelRadialVolume_cross_of_ricciBoundedBelowOn
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K s R R₀ : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hconj : 0 < K → R < Real.pi / Real.sqrt K)
    (hRR₀ : R < R₀)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal R₀}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K)) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (modelRadialVolume K (Module.finrank ℝ E - 1) s)
      ≤ ENNReal.ofReal (modelRadialVolume K (Module.finrank ℝ E - 1) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  classical
  let : Nontrivial E :=
    Module.nontrivial_of_finrank_pos
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let d : ℕ := Module.finrank ℝ E - 1
  let L : E ≃L[ℝ] TangentSpace I x :=
    normalFrame (I := I) (E := E) g x
  let B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    normalBasis (I := I) g x
  let Dn : E → ℝ := fun w =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x (L w))
      (fun i t =>
        intrinsicJacobi (I := I) g hEnorm x (L w) (B i) t)
      1
  let T : Set E :=
    L ⁻¹' SegmentInt (I := I) g hEnorm x
  let S : Metric.sphere (0 : E) 1 → Set (Set.Ioi (0 : ℝ)) := fun u =>
    {r | L (r.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x}
  let F : Metric.sphere (0 : E) 1 → Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    (S u).indicator fun r => ENNReal.ofReal (Dn (r.1 • u.1))
  let G : Set.Ioi (0 : ℝ) → ℝ≥0∞ := fun r =>
    ENNReal.ofReal (modelDensity K d r.1 / r.1 ^ d)
  have hDn_eq (w : E) :
      Dn w =
        |(chartModelBasis E).det B| *
          expJacobianDensity (I := I) g hEnorm x (L w) := by
    with_unfolding_all exact
      (jacobianDens_basis (I := I) g hEnorm x (L w) (chartModelBasis E) B)
  have hDn_cont : Continuous Dn := by
    rw [show Dn = fun w =>
        |(chartModelBasis E).det B| *
          expJacobianDensity (I := I) g hEnorm x (L w) by
      funext w
      exact hDn_eq w]
    exact continuous_const.mul
      ((expJacobian_continuous (I := I) g hEnorm x).comp L.continuous)
  have hDn_nonneg (w : E) : 0 ≤ Dn w := by
    simp only [Dn, curveDensity]
    exact Real.sqrt_nonneg _
  have hT_meas : MeasurableSet T :=
    (measurableSet_segmentInt (I := I) g hEnorm x).preimage
      L.continuous.measurable
  have hS_meas (u : Metric.sphere (0 : E) 1) :
      MeasurableSet (S u) := by
    exact (measurableSet_segmentInt (I := I) g hEnorm x).preimage
      (L.continuous.comp
        (continuous_subtype_val.smul continuous_const)).measurable
  have hF_meas (u : Metric.sphere (0 : E) 1) :
      Measurable (F u) := by
    exact (ENNReal.measurable_ofReal.comp
      (hDn_cont.measurable.comp
        (continuous_subtype_val.smul continuous_const).measurable)).indicator
          (hS_meas u)
  have hG_meas : Measurable G := by
    exact ENNReal.measurable_ofReal.comp
      (((modelDensity_continuous K d).measurable.comp measurable_subtype_coe).div
        (measurable_subtype_coe.pow_const d))
  have hS_down (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b) (hb : b ∈ S u) :
      a ∈ S u := by
    change L (b.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x at hb
    change L (a.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x
    have hab' : a.1 ≤ b.1 := hab
    have hratio0 : 0 ≤ a.1 / b.1 :=
      div_nonneg a.2.le b.2.le
    have hratio1 : a.1 / b.1 ≤ 1 :=
      (div_le_one b.2).2 hab'
    have hscaled :=
      segmentInt_smul (I := I) g hEnorm hb hratio0 hratio1
    simpa only [map_smul, smul_smul,
      div_mul_cancel₀ a.1 b.2.ne'] using hscaled
  have hu_inner (u : Metric.sphere (0 : E) 1) :
      g.inner x (L u.1) (L u.1) = 1 := by
    have hunorm : ‖u.1‖ = 1 := by
      simpa only [mem_sphere_zero_iff_norm] using u.2
    simp only [L, normalFrame_inner, real_inner_self_eq_norm_sq,
      hunorm, one_pow]
  have hsingle (r : Set.Ioi (0 : ℝ)) :
      Measure.volumeIoiPow d ({r} : Set (Set.Ioi (0 : ℝ))) = 0 := by
    rw [Measure.volumeIoiPow]
    apply withDensity_absolutelyContinuous
    rw [comap_subtype_coe_apply measurableSet_Ioi]
    exact ((show ({r} : Set (Set.Ioi (0 : ℝ))).Subsingleton from
      Set.subsingleton_singleton).image
        ((↑) : Set.Ioi (0 : ℝ) → ℝ)).measure_zero volume
  have hIio_Iic (r : Set.Ioi (0 : ℝ)) :
      Set.Iio r =ᵐ[Measure.volumeIoiPow d] Set.Iic r :=
    Iio_ae_eq_Iic' (hsingle r)
  have hR : 0 < R := hs.trans_le hsR
  have hmodel {t : ℝ} (ht : 0 < t) (htR : t ≤ R) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), G r
          ∂Measure.volumeIoiPow d) =
        ENNReal.ofReal (modelRadialVolume K d t) := by
    simpa only [G] using modelRadial_lintegral K d ht
      ⟨ht.le, fun hK => (htR.trans_lt (hconj hK)).le⟩
  have hpolar {t : ℝ} (ht : 0 < t) :
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
        ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
    let K : Set E :=
      SegmentInt (I := I) g hEnorm x ∩ gBall (I := I) g x t
    have hpre :
        L ⁻¹' K = T ∩ Metric.ball (0 : E) t := by
      dsimp only [K]
      change
        (L ⁻¹' SegmentInt (I := I) g hEnorm x) ∩
            (L ⁻¹' gBall (I := I) g x t) =
          T ∩ Metric.ball (0 : E) t
      rw [preimage_gBall (I := I) (E := E) g x t]
    have hset : MeasurableSet (T ∩ Metric.ball (0 : E) t) :=
      hT_meas.inter measurableSet_ball
    have hfun : Measurable (fun w : E => ENNReal.ofReal (Dn w)) :=
      ENNReal.measurable_ofReal.comp hDn_cont.measurable
    have hind :
        Measurable ((T ∩ Metric.ball (0 : E) t).indicator
          (fun w : E => ENNReal.ofReal (Dn w))) :=
      hfun.indicator hset
    calc
      riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal t} =
          ∫⁻ v in K,
            ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
            ∂(modelHaar (E := E)) := by
        simpa only [K] using segmentBall_area_eq (I := I) g hEnorm x ht
      _ = ∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn w)
          ∂(volume : Measure E) := by
        simpa only [Dn, L, B] using
          expJacobian_normal_int (I := I) (E := E) g hEnorm x K
      _ = ∫⁻ w in T ∩ Metric.ball (0 : E) t,
          ENNReal.ofReal (Dn w) ∂(volume : Measure E) := by
        rw [hpre]
      _ = ∫⁻ w : E,
          (T ∩ Metric.ball (0 : E) t).indicator
            (fun z => ENNReal.ofReal (Dn z)) w
          ∂(volume : Measure E) :=
        (lintegral_indicator hset _).symm
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ),
            (T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        simpa only [d] using
          lintegral_polar (volume : Measure E)
            ((T ∩ Metric.ball (0 : E) t).indicator
              (fun z => ENNReal.ofReal (Dn z))) hind.aemeasurable
      _ = ∫⁻ u : Metric.sphere (0 : E) 1,
          ∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d
          ∂(volume : Measure E).toSphere := by
        apply lintegral_congr
        intro u
        have hunorm : ‖u.1‖ = 1 := by
          simpa only [mem_sphere_zero_iff_norm] using u.2
        have hball (r : Set.Ioi (0 : ℝ)) :
            r.1 • u.1 ∈ Metric.ball (0 : E) t ↔
              r ∈ Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)) := by
          rw [Metric.mem_ball, dist_zero_right, norm_smul,
            Real.norm_of_nonneg r.2.le, hunorm, mul_one]
          rfl
        calc
          (∫⁻ r : Set.Ioi (0 : ℝ),
              (T ∩ Metric.ball (0 : E) t).indicator
                (fun z => ENNReal.ofReal (Dn z)) (r.1 • u.1)
              ∂Measure.volumeIoiPow d) =
              ∫⁻ r : Set.Ioi (0 : ℝ) in
                Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
                ∂Measure.volumeIoiPow d := by
            rw [← lintegral_indicator measurableSet_Iio]
            apply lintegral_congr
            intro r
            have hseg : r ∈ S u ↔ r.1 • u.1 ∈ T := Iff.rfl
            dsimp only [F]
            by_cases hrS : r ∈ S u
            · by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · have hmem :
                    r.1 • u.1 ∈ T ∩ Metric.ball (0 : E) t :=
                  ⟨hseg.mp hrS, (hball r).mpr hrt⟩
                rw [Set.indicator_of_mem hmem,
                  Set.indicator_of_mem hrt,
                  Set.indicator_of_mem hrS]
              · rw [Set.indicator_of_notMem
                    (fun h => hrt ((hball r).mp h.2)),
                  Set.indicator_of_notMem hrt]
            · rw [Set.indicator_of_notMem
                  (fun h => hrS (hseg.mpr h.1))]
              by_cases hrt : r ∈
                  Set.Iio (⟨t, ht⟩ : Set.Ioi (0 : ℝ))
              · rw [Set.indicator_of_mem hrt,
                  Set.indicator_of_notMem hrS]
              · rw [Set.indicator_of_notMem hrt]
          _ = ∫⁻ r : Set.Ioi (0 : ℝ) in
              Set.Iic (⟨t, ht⟩ : Set.Ioi (0 : ℝ)), F u r
              ∂Measure.volumeIoiPow d :=
            setLIntegral_congr (hIio_Iic ⟨t, ht⟩)
  have hcross (u : Metric.sphere (0 : E) 1)
      {a b : Set.Ioi (0 : ℝ)} (hab : a ≤ b)
      (hbR : b ≤ (⟨R, hR⟩ : Set.Ioi (0 : ℝ))) :
      F u b * G a ≤ F u a * G b := by
    by_cases hbS : b ∈ S u
    · have haS : a ∈ S u := hS_down u hab hbS
      have hbS' := hbS
      change L (b.1 • u.1) ∈ SegmentInt (I := I) g hEnorm x at hbS'
      obtain ⟨c, hc, hcb⟩ := hbS'
      let uT : TangentSpace I x := L u.1
      have huT_pos : 0 < g.inner x uT uT := by
        simpa only [uT, hu_inner u] using one_pos
      have huT0 : uT ≠ 0 := by
        intro hu0
        rw [hu0] at huT_pos
        simp only [map_zero, lt_self_iff_false] at huT_pos
      have hc0 : 0 < c := one_pos.trans hc
      have hcb_pos : 0 < c * b.1 := mul_pos hc0 b.2
      have hcbD :
          (c * b.1) • uT ∈ SegmentDom (I := I) g hEnorm x := by
        simpa only [uT, map_smul, smul_smul] using hcb
      have hcb0 : (c * b.1) • uT ≠ 0 :=
        smul_ne_zero hcb_pos.ne' huT0
      have hno :
          ∀ t ∈ Set.Ioo (0 : ℝ) (c * b.1),
            ¬ IsConjVec (I := I) g hEnorm x
              ((t • uT : TangentSpace I x) : E) := by
        intro t ht
        have hratio :
            t / (c * b.1) ∈ Set.Ioo (0 : ℝ) 1 := by
          exact ⟨div_pos ht.1 hcb_pos,
            (div_lt_one hcb_pos).2 ht.2⟩
        have hraw :=
          segmentDom_no_conj (I := I) g hEnorm hcbD hcb0
            (t / (c * b.1)) hratio
        simpa only [smul_smul,
          div_mul_cancel₀ t hcb_pos.ne'] using hraw
      have hb_lt : b.1 < c * b.1 :=
        lt_mul_of_one_lt_left b.2 hc
      have hbR' : b.1 ≤ R := hbR
      let modelCut : ℝ :=
        if 0 < K then (b.1 + Real.pi / Real.sqrt K) / 2 else b.1 + 1
      have hbmid : b.1 < (b.1 + R₀) / 2 := by
        linarith
      have hb_modelCut : b.1 < modelCut := by
        by_cases hK : 0 < K
        · have hbconj : b.1 < Real.pi / Real.sqrt K :=
            hbR'.trans_lt (hconj hK)
          simp only [modelCut, if_pos hK]
          linarith
        · simp only [modelCut, if_neg hK]
          linarith
      let bcut : ℝ :=
        min (c * b.1) (min ((b.1 + R₀) / 2) modelCut)
      have hb_bcut : b.1 < bcut := by
        exact lt_min hb_lt (lt_min hbmid hb_modelCut)
      have hbcut_cb : bcut ≤ c * b.1 := min_le_left _ _
      have hbcut_R₀ : bcut < R₀ := by
        calc
          bcut ≤ min ((b.1 + R₀) / 2) modelCut := min_le_right _ _
          _ ≤ (b.1 + R₀) / 2 := min_le_left _ _
          _ < R₀ := by linarith
      have hbcut_modelCut : bcut ≤ modelCut := by
        exact (min_le_right _ _).trans (min_le_right _ _)
      have hadmCut :
          ∀ t ∈ Set.Ioo (0 : ℝ) bcut, modelRadiusAdmissible K t := by
        intro t ht
        refine ⟨ht.1, ?_⟩
        intro hK
        have hbconj : b.1 < Real.pi / Real.sqrt K :=
          hbR'.trans_lt (hconj hK)
        have hmodelCut : modelCut < Real.pi / Real.sqrt K := by
          simp only [modelCut, if_pos hK]
          linarith
        exact (ht.2.trans_le hbcut_modelCut).trans hmodelCut
      have haWin : a.1 ∈ Set.Ioo (0 : ℝ) bcut :=
        ⟨a.2, (show a.1 ≤ b.1 from hab).trans_lt hb_bcut⟩
      have hbWin : b.1 ∈ Set.Ioo (0 : ℝ) bcut :=
        ⟨b.2, hb_bcut⟩
      by_cases hd : 0 < d
      · obtain ⟨v, hON, hperp'⟩ :=
          exists_perp_pos (I := I) g x uT huT_pos
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          rw [g.symm x uT (v i)]
          exact hperp' i
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have huT_one : g.inner x uT uT = 1 := by
          simpa only [uT] using hu_inner u
        have hnoCut :
            ∀ t ∈ Set.Ioo (0 : ℝ) bcut,
              ¬ IsConjVec (I := I) g hEnorm x
                ((t • uT : TangentSpace I x) : E) := by
          intro t ht
          exact hno t ⟨ht.1, ht.2.trans_le hbcut_cb⟩
        have hRicCut :
            let γ := intrinsicGeodesic (I := I) g hEnorm x uT
            ∀ t ∈ Set.Ioo (0 : ℝ) bcut,
              (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K) *
                    g.inner (γ t) (curveVelocity (I := I) γ t)
                      (curveVelocity (I := I) γ t) ≤
                ricciTensor (I := I) g (γ t)
                  (curveVelocity (I := I) γ t)
                  (curveVelocity (I := I) γ t) := by
          dsimp only
          intro t ht
          apply ricciBoundedBelowOn_apply hRic
          exact intrinsicGeodesic_mem_ball_of_lt (I := I) g hEnorm x uT
            huT_one ht.1.le (ht.2.trans hbcut_R₀)
        have hanti :
            AntitoneOn
              (fun t => Dt t / modelDensity K d t)
              (Set.Ioo (0 : ℝ) bcut) := by
          simpa only [Dt, d] using
            intrModelRatioOfFrame_on (I := I) g hEnorm x uT K bcut
              huT_one hd hadmCut v hON hperp hnoCut hRicCut
        have hratio :=
          hanti haWin hbWin (show a.1 ≤ b.1 from hab)
        have hHa : 0 < modelDensity K d a.1 :=
          modelDensity_pos (hadmCut a.1 haWin)
        have hHb : 0 < modelDensity K d b.1 :=
          modelDensity_pos (hadmCut b.1 hbWin)
        have htrans :
            Dt b.1 * modelDensity K d a.1 ≤
              Dt a.1 * modelDensity K d b.1 :=
          (div_le_div_iff₀ hHb hHa).1 hratio
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa :
            a.1 ^ d * Dn (a.1 • u.1) = Dt a.1 := by
          rw [hDnA]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
        have hDb :
            b.1 ^ d * Dn (b.1 • u.1) = Dt b.1 := by
          rw [hDnB]
          simpa only [d, Dt] using
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
        have hGa :
            a.1 ^ d * (modelDensity K d a.1 / a.1 ^ d) =
              modelDensity K d a.1 := by
          exact mul_div_cancel₀ _ (pow_ne_zero d a.2.ne')
        have hGb :
            b.1 ^ d * (modelDensity K d b.1 / b.1 ^ d) =
              modelDensity K d b.1 := by
          exact mul_div_cancel₀ _ (pow_ne_zero d b.2.ne')
        have hpowa : 0 < a.1 ^ d := pow_pos a.2 d
        have hpowb : 0 < b.1 ^ d := pow_pos b.2 d
        have hreal :
            Dn (b.1 • u.1) * (modelDensity K d a.1 / a.1 ^ d) ≤
              Dn (a.1 • u.1) * (modelDensity K d b.1 / b.1 ^ d) := by
          apply (mul_le_mul_iff_right₀ (mul_pos hpowa hpowb)).mp
          calc
            (a.1 ^ d * b.1 ^ d) *
                (Dn (b.1 • u.1) * (modelDensity K d a.1 / a.1 ^ d)) =
                (b.1 ^ d * Dn (b.1 • u.1)) *
                  (a.1 ^ d * (modelDensity K d a.1 / a.1 ^ d)) := by ring
            _ = Dt b.1 * modelDensity K d a.1 := by
              rw [hDb, hGa]
            _ ≤ Dt a.1 * modelDensity K d b.1 := htrans
            _ = (a.1 ^ d * Dn (a.1 • u.1)) *
                (b.1 ^ d * (modelDensity K d b.1 / b.1 ^ d)) := by
              rw [hDa, hGb]
            _ = (a.1 ^ d * b.1 ^ d) *
                (Dn (a.1 • u.1) *
                  (modelDensity K d b.1 / b.1 ^ d)) := by ring
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS]
        rw [← ENNReal.ofReal_mul (hDn_nonneg (b.1 • u.1)),
          ← ENNReal.ofReal_mul (hDn_nonneg (a.1 • u.1))]
        exact ENNReal.ofReal_le_ofReal hreal
      · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
        let v : Fin d → TangentSpace I x := fun i =>
          isEmptyElim (hd0 ▸ i)
        have hON :
            ∀ i j, g.inner x (v i) (v j) =
              if i = j then 1 else 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hperp : ∀ i, g.inner x uT (v i) = 0 := by
          intro i
          exact isEmptyElim (hd0 ▸ i)
        have hB :
            ∀ i j, g.inner x (B i) (B j) =
              if i = j then 1 else 0 := by
          simpa only [B] using normalBasis_inner (I := I) g x
        let Dt : ℝ → ℝ := fun t =>
          curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x uT)
            (fun i => intrinsicJacobi (I := I) g hEnorm x uT (v i)) t
        have hDt (t : ℝ) : Dt t = 1 := by
          have hgram :
              curveGram (I := I) g
                  (intrinsicGeodesic (I := I) g hEnorm x uT)
                  (fun i =>
                    intrinsicJacobi (I := I) g hEnorm x uT (v i)) t =
                1 := by
            ext i
            exact isEmptyElim (hd0 ▸ i)
          simp only [Dt, curveDensity, hgram, Matrix.det_one, Real.sqrt_one]
        have hLa : L (a.1 • u.1) = a.1 • uT := by
          simpa only [uT] using L.map_smul a.1 u.1
        have hLb : L (b.1 • u.1) = b.1 • uT := by
          simpa only [uT] using L.map_smul b.1 u.1
        have hDnA :
            Dn (a.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (a.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (a.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLa]
        have hDnB :
            Dn (b.1 • u.1) =
              curveDensity (I := I) g
                (intrinsicGeodesic (I := I) g hEnorm x (b.1 • uT))
                (fun i t =>
                  intrinsicJacobi (I := I) g hEnorm x
                    (b.1 • uT) (B i) t) 1 := by
          dsimp only [Dn]
          rw [hLb]
        have hDa : Dn (a.1 • u.1) = 1 := by
          rw [hDnA]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp a.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hDb : Dn (b.1 • u.1) = 1 := by
          rw [hDnB]
          have hscale :=
            expDens_scale (I := I) g hEnorm x uT huT_pos
              B hB v hON hperp b.2
          simpa only [d, hd0, pow_zero, one_mul, Dt, hDt] using hscale
        have hGa : modelDensity K d a.1 / a.1 ^ d = 1 := by
          simp only [hd0, modelDensity, pow_zero, div_one]
        have hGb : modelDensity K d b.1 / b.1 ^ d = 1 := by
          simp only [hd0, modelDensity, pow_zero, div_one]
        simp only [F, G, Set.indicator_of_mem hbS,
          Set.indicator_of_mem haS, hDa, hDb, hGa, hGb,
          ENNReal.ofReal_one, mul_one, le_refl]
    · simp only [F, Set.indicator_of_notMem hbS, zero_mul, zero_le]
  have hdir (u : Metric.sphere (0 : E) 1) :
      (∫⁻ r : Set.Ioi (0 : ℝ) in
          Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
          ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (modelRadialVolume K d s) ≤
        (∫⁻ r : Set.Ioi (0 : ℝ) in
            Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
            ∂Measure.volumeIoiPow d) *
          ENNReal.ofReal (modelRadialVolume K d R) := by
    have h :=
      setLIntegral_Iic_mul_setLIntegral_Iic_le
        (μ := Measure.volumeIoiPow d) (f := F u) (g := G)
        (hF_meas u).aemeasurable.restrict
        hG_meas.aemeasurable.restrict
        (fun {_a _b} hab hbR => hcross u hab hbR)
        (show (⟨s, hs⟩ : Set.Ioi (0 : ℝ)) ≤ ⟨R, hR⟩ from hsR)
    rw [hmodel hs hsR, hmodel hR le_rfl] at h
    exact h
  rw [show Module.finrank ℝ E - 1 = d by rfl]
  rw [hpolar hR, hpolar hs]
  rw [mul_comm
    (ENNReal.ofReal (modelRadialVolume K d R))
    (∫⁻ u : Metric.sphere (0 : E) 1,
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d
      ∂(volume : Measure E).toSphere)]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (modelRadialVolume K d s))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨R, hR⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  rw [← lintegral_mul_const'
    (ENNReal.ofReal (modelRadialVolume K d R))
    (fun u : Metric.sphere (0 : E) 1 =>
      ∫⁻ r : Set.Ioi (0 : ℝ) in
        Set.Iic (⟨s, hs⟩ : Set.Ioi (0 : ℝ)), F u r
        ∂Measure.volumeIoiPow d)
    ENNReal.ofReal_ne_top]
  exact lintegral_mono hdir

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem modelVolume_cross_of_ricciBoundedBelowOn
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K s R R₀ : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hconj : 0 < K → R < Real.pi / Real.sqrt K)
    (hRR₀ : R < R₀)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal R₀}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K)) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s)
      ≤ ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  let n : ℕ := Module.finrank ℝ E
  have hn : 1 ≤ n := by
    exact Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hfactor : 0 ≤ (n : ℝ) * euclideanUnitBallVolume n :=
    mul_nonneg (Nat.cast_nonneg n) (euclideanUnitBallVolume_pos n).le
  have hrad := modelRadialVolume_cross_of_ricciBoundedBelowOn
    (I := I) g hEnorm x hs hsR hconj hRR₀ hRic
  have hscaled := mul_le_mul_right
    hrad (ENNReal.ofReal ((n : ℝ) * euclideanUnitBallVolume n))
  rw [show Module.finrank ℝ E = n by rfl,
    modelVolume_eq_sphereFactor_mul_radialVolume K n s,
    modelVolume_eq_sphereFactor_mul_radialVolume K n R,
    ENNReal.ofReal_mul hfactor, ENNReal.ofReal_mul hfactor]
  simpa only [n, mul_assoc, mul_left_comm, mul_comm] using hscaled

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem modelVolume_cross_endpoint_of_ricciBoundedBelowOn
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {K s R : ℝ} (hs : 0 < s) (hsR : s ≤ R)
    (hconj : 0 < K → R ≤ Real.pi / Real.sqrt K)
    (hRic : ricciBoundedBelowOn (I := I) g
      {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * K)) :
    riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        * ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s)
      ≤ ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) R)
        * riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal s} := by
  rcases hsR.lt_or_eq with hsR' | rfl
  · let n : ℕ := Module.finrank ℝ E
    let ballVolume : ℝ → ℝ≥0∞ := fun r =>
      riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal r}
    let modelVolumeENN : ℝ → ℝ≥0∞ := fun r =>
      ENNReal.ofReal (modelVolume K n r)
    let ρ : ℕ → ℝ := fun m =>
      R - (R - s) * (1 / 2 : ℝ) ^ m
    let A : ℕ → Set M := fun m =>
      {y : M | riemannianEDist I x y < ENNReal.ofReal (ρ m)}
    have hn : 1 ≤ n := by
      exact Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
    have hR : 0 < R := hs.trans hsR'
    have hδ : 0 < R - s := sub_pos.2 hsR'
    have hρ_ge (m : ℕ) : s ≤ ρ m := by
      have hp : (1 / 2 : ℝ) ^ m ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      have hmul := mul_le_mul_of_nonneg_left hp hδ.le
      dsimp only [ρ]
      linarith
    have hρ_lt (m : ℕ) : ρ m < R := by
      have hp : 0 < (1 / 2 : ℝ) ^ m := pow_pos (by norm_num) m
      have hmul : 0 < (R - s) * (1 / 2 : ℝ) ^ m := mul_pos hδ hp
      dsimp only [ρ]
      linarith
    have hρ_mono : Monotone ρ := by
      intro i j hij
      have hp : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hij
      have hmul := mul_le_mul_of_nonneg_left hp hδ.le
      dsimp only [ρ]
      linarith
    have hpow : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hρ_tendsto : Tendsto ρ atTop (𝓝 R) := by
      simpa only [ρ, mul_zero, sub_zero] using
        tendsto_const_nhds.sub (tendsto_const_nhds.mul hpow)
    have hA_mono : Monotone A := by
      intro i j hij y hy
      exact hy.trans_le (ENNReal.ofReal_le_ofReal (hρ_mono hij))
    have hA_union :
        (⋃ m, A m) =
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
      ext y
      constructor
      · intro hy
        obtain ⟨m, hym⟩ := Set.mem_iUnion.mp hy
        exact hym.trans
          ((ENNReal.ofReal_lt_ofReal_iff hR).2 (hρ_lt m))
      · intro hy
        have hofReal : Tendsto (fun m => ENNReal.ofReal (ρ m)) atTop
            (𝓝 (ENNReal.ofReal R)) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp hρ_tendsto
        obtain ⟨m, hm⟩ :=
          (hofReal.eventually (Ioi_mem_nhds hy)).exists
        exact Set.mem_iUnion.mpr ⟨m, hm⟩
    have hball_tendsto : Tendsto (fun m => ballVolume (ρ m)) atTop
        (𝓝 (ballVolume R)) := by
      have hmeasure := MeasureTheory.tendsto_measure_iUnion_atTop
        (μ := riemannianVolumeMeasure (I := I) (M := M) g) hA_mono
      rw [hA_union] at hmeasure
      simpa only [Function.comp_def, ballVolume, A] using hmeasure
    have hmodel_tendsto : Tendsto (fun m => modelVolumeENN (ρ m)) atTop
        (𝓝 (modelVolumeENN R)) := by
      exact ((ENNReal.continuous_ofReal.comp (modelVolume_continuous K n))
        |>.continuousAt.tendsto).comp hρ_tendsto
    have hleft : Tendsto
        (fun m => ballVolume (ρ m) * modelVolumeENN s) atTop
        (𝓝 (ballVolume R * modelVolumeENN s)) := by
      exact ENNReal.Tendsto.mul_const hball_tendsto
        (Or.inr ENNReal.ofReal_ne_top)
    have hmodelR_pos : 0 < modelVolumeENN R := by
      exact ENNReal.ofReal_pos.2
        (modelVolume_pos hn hR ⟨hR.le, hconj⟩)
    have hright : Tendsto
        (fun m => modelVolumeENN (ρ m) * ballVolume s) atTop
        (𝓝 (modelVolumeENN R * ballVolume s)) := by
      exact ENNReal.Tendsto.mul_const hmodel_tendsto
        (Or.inl hmodelR_pos.ne')
    have hcross : ∀ m,
        ballVolume (ρ m) * modelVolumeENN s ≤
          modelVolumeENN (ρ m) * ballVolume s := by
      intro m
      simpa only [ballVolume, modelVolumeENN, n] using
        modelVolume_cross_of_ricciBoundedBelowOn (I := I) g hEnorm x
          hs (hρ_ge m) (fun hK => (hρ_lt m).trans_le (hconj hK))
          (hρ_lt m) hRic
    simpa only [ballVolume, modelVolumeENN, n] using
      le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hcross)
  · simpa only [mul_comm] using
      le_refl (ENNReal.ofReal (modelVolume K (Module.finrank ℝ E) s) *
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal s})

end Poincare.Geometry.Riemannian.VolumeComparison
