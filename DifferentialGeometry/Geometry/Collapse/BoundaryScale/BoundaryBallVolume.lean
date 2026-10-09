import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryChartMeasure
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryChartDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryHalfBallMeasure
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.FirstScaleInterior

/-!
# Small boundary balls on an actual compact carrier

Metric-normalized half-space slices in a genuine boundary chart give the boundary
half-ball lower coefficient. Chart paths and chart density are controlled locally.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem exists_boundary_chart_control (g : SmoothRiemannianMetric I M) (p : M)
    {K a : ℝ} (hK : 1 < K) (ha : a < 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : E, ‖y - extChartAt I p p‖ < δ → y ∈ range I →
      y ∈ (extChartAt I p).target ∧
      a * chartDensity g p p ≤ chartDensity g p ((extChartAt I p).symm y) ∧
      ∀ v : TangentSpace I p,
        let e := trivializationAt E (TangentSpace I) p
        let x := (extChartAt I p).symm y
        Real.sqrt (g.inner x (e.symmL ℝ x (e.continuousLinearMapAt ℝ p v))
          (e.symmL ℝ x (e.continuousLinearMapAt ℝ p v))) ≤
            K * Real.sqrt (g.inner p v v) := by
  let e := extChartAt I p
  have hdp : 0 < chartDensity g p p :=
    chartDensity_pos g p (mem_baseSet_trivializationAt E (TangentSpace I) p)
  have hdc : ContinuousAt (chartDensity g p) p :=
    (chartDensity_continuousOn g p).continuousAt
      (show (trivializationAt E (TangentSpace I) p).baseSet ∈ 𝓝 p from
        chart_source_mem_nhds H p)
  have hdnear : ∀ᶠ x in 𝓝 p, a * chartDensity g p p < chartDensity g p x :=
    hdc.eventually (Ioi_mem_nhds (mul_lt_of_lt_one_left hdp ha))
  have hp : e p ∈ e.target := e.map_source (mem_extChartAt_source p)
  have hinv : Tendsto e.symm (𝓝[range I] (e p)) (𝓝 p) := by
    rw [← nhdsWithin_extChartAt_target_eq (I := I) p]
    have hh := continuousOn_extChartAt_symm (I := I) p (e p) hp
    change Tendsto e.symm (𝓝[e.target] (e p)) (𝓝 (e.symm (e p))) at hh
    rw [e.left_inv (mem_extChartAt_source p)] at hh
    exact hh
  have htnear : ∀ᶠ y in 𝓝[range I] (e p), y ∈ e.target := by
    rw [← nhdsWithin_extChartAt_target_eq (I := I) p]
    exact self_mem_nhdsWithin
  have hnear := htnear.and (hinv.eventually (hdnear.and
    (eventually_tangent_transport_le g p hK)))
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyr
  have h := hsub ⟨by simpa only [Metric.mem_ball, dist_eq_norm] using hy, hyr⟩
  exact ⟨h.1, h.2.1.le, h.2.2.2.2⟩

theorem normalizedChart_compact_volume_lower [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (p : M)
    {S : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))} (hS : IsCompact S)
    {a : ℝ} (ha : 0 ≤ a)
    (hSt : ∀ v ∈ S, extChartAt I p p + (metricChartEuclideanEquiv g p).symm v ∈
      (extChartAt I p).target)
    (hdens : ∀ v ∈ S, a * chartDensity g p p ≤ chartDensity g p
      ((extChartAt I p).symm (extChartAt I p p +
        (metricChartEuclideanEquiv g p).symm v))) :
    ENNReal.ofReal a * (volume : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) S ≤
        riemannianVolumeMeasure (I := I) (M := M) g
          ((fun v => (extChartAt I p).symm (extChartAt I p p +
            (metricChartEuclideanEquiv g p).symm v)) '' S) := by
  let A := metricChartEuclideanEquiv g p
  let cp := extChartAt I p p
  let f : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E := fun v => cp + A.symm v
  let T := f '' S
  have hT : IsCompact T := hS.image (continuous_const.add A.symm.continuous)
  have hTt : T ⊆ (extChartAt I p).target := by
    rintro y ⟨v, hv, rfl⟩
    exact hSt v hv
  have hμ : ENNReal.ofReal (chartDensity g p p) * modelHaar (E := E) T = volume S := by
    have hm := congrArg (fun μ : Measure
      (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) => μ S)
        (map_metricChartEuclideanEquiv_density_haar g p)
    rw [Measure.map_apply A.continuous.measurable hS.measurableSet,
      Measure.smul_apply, smul_eq_mul] at hm
    have hpre : A ⁻¹' S = A.symm '' S := by
      ext y
      constructor
      · intro hy
        exact ⟨A y, hy, A.symm_apply_apply y⟩
      · rintro ⟨v, hv, rfl⟩
        simpa only [mem_preimage, A.apply_symm_apply] using hv
    have ht : T = (fun y : E => -cp + y) ⁻¹' (A.symm '' S) := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, by simp only [f, neg_add_cancel_left]⟩
      · rintro ⟨v, hv, heq⟩
        refine ⟨v, hv, ?_⟩
        change cp + A.symm v = y
        rw [heq]
        simp only [add_neg_cancel_left]
    rw [ht, measure_preimage_add, ← hpre]
    exact hm
  have hlow : ENNReal.ofReal (a * chartDensity g p p) * modelHaar (E := E) T ≤
      ∫⁻ y in T, ENNReal.ofReal (chartDensity g p ((extChartAt I p).symm y))
        ∂modelHaar (E := E) := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hT.measurableSet] with y hy
    rcases hy with ⟨v, hv, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hdens v hv)
  rw [ENNReal.ofReal_mul ha, mul_assoc, hμ] at hlow
  have himage : ((extChartAt I p).symm '' T) =
      (fun v => (extChartAt I p).symm (cp + A.symm v)) '' S := by
    ext x
    constructor
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨f v, ⟨v, hv, rfl⟩, rfl⟩
  rw [← volume_inverseChart_compact_image g p hT hTt, himage] at hlow
  exact hlow

end DifferentialGeometry.Geometry.Metric

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Metric

private theorem exists_half_volume_coeff {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ a L : ℝ, 0 < a ∧ a < 1 ∧ 1 < L ∧ 1 - ε < a / L ^ 3 := by
  let a := 1 - ε / 2
  have ha : 0 < a := by dsimp only [a]; linarith
  have ha1 : a < 1 := by dsimp only [a]; linarith
  have hlim : ContinuousAt (fun L : ℝ => a / L ^ 3) 1 :=
    continuousAt_const.div (continuousAt_id.pow 3) (by norm_num)
  have he : 1 - ε < a / (1 : ℝ) ^ 3 := by dsimp only [a]; norm_num; linarith
  have hn : ∀ᶠ L in 𝓝 (1 : ℝ), 1 - ε < a / L ^ 3 :=
    continuousAt_const.eventually_lt hlim he
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨a, 1 + δ / 2, ha, ha1, by linarith, ?_⟩
  apply hsub
  rw [Metric.mem_ball, Real.dist_eq]
  have hh : 1 + δ / 2 - 1 = δ / 2 := by ring
  rw [hh, abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ

private abbrev BoundaryEuStd := EuclideanSpace ℝ
  (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))

section HalfSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [CompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem halfSpace_chart_ratio
    (g : SmoothRiemannianMetric (𝓡∂ 3) M) (p : M)
    (hp : (𝓡∂ 3).IsBoundaryPoint p) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ENNReal.ofReal ((1 - ε) * (euclideanThreeUnitBallVolume / 2) * r ^ 3) ≤
        ballVolume g p r := by
  let A := metricChartEuclideanEquiv g p
  let cp := extChartAt (𝓡∂ 3) p p
  let ell := ((ContinuousLinearMap.proj (0 : Fin 3)).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap).comp
      A.symm.toContinuousLinearMap
  have hell : ell ≠ 0 := by
    intro h
    have hh := DFunLike.congr_fun h (A (EuclideanSpace.single (0 : Fin 3) 1))
    simp only [ell, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      A.symm_apply_apply, ContinuousLinearMap.proj_apply, zero_apply] at hh
    change (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0 = 0 at hh
    simp at hh
  have hcp : cp 0 = 0 := by
    have hh : cp ∈ frontier (range (𝓡∂ 3)) := hp
    rw [frontier_range_modelWithCornersEuclideanHalfSpace] at hh
    exact hh.symm
  obtain ⟨a, L, ha, ha1, hL, hcoeff⟩ := exists_half_volume_coeff hε hε1
  let K := (1 + L) / 2
  have hK : 1 < K := by dsimp only [K]; linarith
  have hKL : K < L := by dsimp only [K]; linarith
  have hL0 : 0 < L := zero_lt_one.trans hL
  have hK0 : 0 < K := zero_lt_one.trans hK
  obtain ⟨δ, hδ, hcontrol⟩ := exists_boundary_chart_control g p hK ha1
  let B := ‖A.symm.toContinuousLinearMap‖
  let ρ := δ / (B + 1)
  have hB : 0 ≤ B := norm_nonneg _
  have hρ : 0 < ρ := div_pos hδ (by linarith)
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ
  let R := r / L
  have hR : 0 < R := div_pos hr hL0
  have hRr : R < r := (div_lt_self hr hL)
  have hRρ : R < ρ := hRr.trans hrρ
  let Q := Metric.closedBall (0 : BoundaryEuStd) R ∩ {v | 0 ≤ ell v}
  have hQ : IsCompact Q := (isCompact_closedBall (0 : BoundaryEuStd) R).inter_right
      (isClosed_le continuous_const ell.continuous)
  have hpoint (v : BoundaryEuStd) (hv : v ∈ Q)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      cp + t • A.symm v ∈ (extChartAt (𝓡∂ 3) p).target ∧
      a * chartDensity g p p ≤ chartDensity g p
        ((extChartAt (𝓡∂ 3) p).symm (cp + t • A.symm v)) ∧
      ∀ u : TangentSpace (𝓡∂ 3) p,
        let e := trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡∂ 3)) p
        let x := (extChartAt (𝓡∂ 3) p).symm (cp + t • A.symm v)
        Real.sqrt (g.inner x (e.symmL ℝ x (e.continuousLinearMapAt ℝ p u))
          (e.symmL ℝ x (e.continuousLinearMapAt ℝ p u))) ≤
            K * Real.sqrt (g.inner p u u) := by
    have hvn : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv.1
    have hn : ‖A.symm v‖ < δ := by
      have hh := A.symm.toContinuousLinearMap.le_opNorm v
      have hlt : (B + 1) * ‖v‖ < δ := by
        have hh' := mul_lt_mul_of_pos_left (hvn.trans_lt hRρ) (by linarith : 0 < B + 1)
        have heq : (B + 1) * ρ = δ := by dsimp only [ρ]; field_simp
        rwa [heq] at hh'
      exact hh.trans_lt ((mul_le_mul_of_nonneg_right (by linarith : B ≤ B + 1)
        (norm_nonneg v)).trans_lt hlt)
    apply hcontrol
    · have htn : ‖t • A.symm v‖ ≤ ‖A.symm v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2
      simpa only [cp, add_sub_cancel_left] using htn.trans_lt hn
    · rw [range_modelWithCornersEuclideanHalfSpace]
      change 0 ≤ cp 0 + t * (A.symm v) 0
      rw [hcp, zero_add]
      exact mul_nonneg ht.1 hv.2
  have hSt : ∀ v ∈ Q, cp + A.symm v ∈ (extChartAt (𝓡∂ 3) p).target := by
    intro v hv
    simpa only [one_smul] using (hpoint v hv 1 ⟨by norm_num, le_rfl⟩).1
  have hdens : ∀ v ∈ Q, a * chartDensity g p p ≤ chartDensity g p
      ((extChartAt (𝓡∂ 3) p).symm (cp + A.symm v)) := by
    intro v hv
    simpa only [one_smul] using (hpoint v hv 1 ⟨by norm_num, le_rfl⟩).2.1
  have hsub : (fun v => (extChartAt (𝓡∂ 3) p).symm (cp + A.symm v)) '' Q ⊆
      riemannianBallOf g p r := by
    rintro x ⟨v, hv, rfl⟩
    have hd := riemannianEDistOf_chart_segment_le g p (A.symm v)
      (fun t ht => (hpoint v hv t ht).1) (fun t ht => (hpoint v hv t ht).2.2)
    have hvn : ‖v‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv.1
    have hKr : K * ‖v‖ < r := by
      calc
        K * ‖v‖ ≤ K * R := mul_le_mul_of_nonneg_left hvn hK0.le
        _ < L * R := mul_lt_mul_of_pos_right hKL hR
        _ = r := by dsimp only [R]; field_simp
    apply hd.trans_lt
    rw [A.apply_symm_apply]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hKr
  have hvlow := normalizedChart_compact_volume_lower g p hQ ha.le hSt hdens
  have hballlow := hvlow.trans (measure_mono hsub)
  change ENNReal.ofReal a * volume Q ≤ ballVolume g p r at hballlow
  have hhalf : (volume : Measure BoundaryEuStd)
      (Metric.ball 0 R ∩ {v | 0 ≤ ell v}) =
        ENNReal.ofReal ((euclideanThreeUnitBallVolume / 2) * R ^ 3) := by
    rw [Geometry.Measure.measure_ball_inter_nonnegative_halfspace volume ell hell,
      Measure.addHaar_ball volume 0 hR.le]
    simp only [finrank_euclideanSpace_fin] at *
    have hunit : (volume : Measure BoundaryEuStd) (Metric.ball 0 1) =
        ENNReal.ofReal (euclideanUnitBallVolume 3) := by
      rw [InnerProductSpace.volume_ball]
      simp [euclideanUnitBallVolume, BoundaryEuStd]
    rw [hunit]
    rw [euclideanUnitBallVolume_three_eq]
    rw [← ENNReal.ofReal_mul (pow_nonneg hR.le 3)]
    have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
    rw [htwo]
    rw [← ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [euclideanThreeUnitBallVolume]
    ring
  have hhalfQ : (volume : Measure BoundaryEuStd)
      (Metric.ball 0 R ∩ {v | 0 ≤ ell v}) ≤ volume Q :=
    measure_mono (inter_subset_inter Metric.ball_subset_closedBall Subset.rfl)
  have hω : 0 < euclideanThreeUnitBallVolume := by
    change 0 < 4 * Real.pi / 3
    positivity
  calc
    ENNReal.ofReal ((1 - ε) * (euclideanThreeUnitBallVolume / 2) * r ^ 3) ≤
        ENNReal.ofReal (a * ((euclideanThreeUnitBallVolume / 2) * R ^ 3)) := by
      apply ENNReal.ofReal_le_ofReal
      have hc := mul_le_mul_of_nonneg_right hcoeff.le
        (mul_nonneg (half_pos hω).le (pow_pos hr 3).le)
      dsimp only [R]
      convert hc using 1 <;> field_simp
    _ = ENNReal.ofReal a * ENNReal.ofReal
        ((euclideanThreeUnitBallVolume / 2) * R ^ 3) := ENNReal.ofReal_mul ha.le
    _ ≤ ENNReal.ofReal a * volume Q := by rw [← hhalf]; exact mul_le_mul_right hhalfQ _
    _ ≤ ballVolume g p r := hballlow

end HalfSpace

theorem exists_ballVolume_boundary_ratio
    (W : CompactCarrier) (g : SmoothRiemannianMetric W.model W.Carrier)
    (p : W.Carrier) (hp : p ∈ W.model.boundary W.Carrier)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ r : ℝ, 0 < r → r < ρ →
      ENNReal.ofReal ((1 - ε) * (euclideanThreeUnitBallVolume / 2) * r ^ 3) ≤
        ballVolume g p r := by
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      exact False.elim (by rw [hh] at hp; exact hp)
    | withBoundary => exact halfSpace_chart_ratio g p hp ε hε hε1

end DifferentialGeometry.Geometry.Collapse
