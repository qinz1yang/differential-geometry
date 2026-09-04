import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Equality

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJacobian_lt_of_ricci
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {v : TangentSpace I x}
    (hv : v ∈ SegmentDom (I := I) g hEnorm x) (hvne : v ≠ 0)
    (q : ℝ) (hq : 0 ≤ q) (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hne : ricciTensor (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x v t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x v) t)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm x v) t) ≠
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
        (q * Real.sqrt (g.inner x v v)) ^ 2)) :
    expJacobianDensity (I := I) g hEnorm x (v : E) <
      normalChartDensity (I := I) g x 0 *
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := by
  have hle := expJacobianDensity_le (I := I) g hEnorm x hv hvne q hq hd hRic
  refine lt_of_le_of_ne hle ?_
  intro heq
  obtain ⟨w, hON, hperp'⟩ :=
    exists_perp_pos (I := I) g x v (g.pos x v hvne)
  have hperp : ∀ i, g.inner x v (w i) = 0 := by
    intro i
    rw [← g.symm x (w i) v]
    exact hperp' i
  have hncd : 0 < normalChartDensity (I := I) g x 0 := by
    simpa only [normalChartDensity] using
      paramDensity_pos (I := I) g (expMapDiffeo (I := I) g x)
        (zero_mem_expMapDiffeo_source (I := I) g x)
  have htrans :
      curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
          (fun i ↦ intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 =
        hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := by
    apply mul_left_cancel₀ hncd.ne'
    calc
      normalChartDensity (I := I) g x 0 *
          curveDensity (I := I) g (intrinsicGeodesic (I := I) g hEnorm x v)
            (fun i ↦ intrinsicJacobi (I := I) g hEnorm x v (w i)) 1 =
          expJacobianDensity (I := I) g hEnorm x (v : E) :=
        (expJacobianDensity_eq_ncd0_mul_transverse (I := I) g hEnorm x hvne w hON hperp).symm
      _ = normalChartDensity (I := I) g x 0 *
          hyperbolicDensity (q * Real.sqrt (g.inner x v v)) (Module.finrank ℝ E - 1) 1 := heq
  have hsat := (transDens_eq_rigid (I := I) g hEnorm x hv hvne w hON hperp
    q hq hd hRic htrans).2 t ht
  exact hne hsat.1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentBall_vol_lt
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (y : M) ↦ TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : ℝ} (hR : 0 < R)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRicPos : ∀ (y : M) (u : TangentSpace I y), u ≠ 0 →
      0 < ricciTensor (I := I) g y u u) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
      < (∫⁻ θ : Metric.sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
        * ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) R) := by
  classical
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let : Measure.IsAddHaarMeasure (modelHaar (E := E)) :=
    DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure
  have hRic : RicciBoundedBelow (I := I) g 0 := by
    intro y u
    by_cases hu : u = 0
    · subst u
      simp
    · simpa only [zero_mul] using (hRicPos y u hu).le
  let K : Set E :=
    {v : E | (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x} ∩
      closedGBall (I := I) g x R
  let F : E → ℝ := fun v => normalChartDensity (I := I) g x 0 *
    hyperbolicDensity (0 * Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v))) (Module.finrank ℝ E - 1) 1
  have hV := segmentBall_vol_le_int (I := I) g hEnorm x R
  have hncd : 0 < normalChartDensity (I := I) g x 0 := by
    simpa only [normalChartDensity] using
      paramDensity_pos (I := I) g (expMapDiffeo (I := I) g x)
        (zero_mem_expMapDiffeo_source (I := I) g x)
  have hpoint : ∀ v : E, v ∈ K → v ≠ 0 →
      expJacobianDensity (I := I) g hEnorm x v < F v := by
    intro v hv hvne
    let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm x
      (show TangentSpace I x from v)
    have hvel : curveVelocity (I := I) γ (1 / 2 : ℝ) ≠ 0 := by
      simpa only [γ, curveVelocity] using
        intrinsicGeo_velocity_ne (I := I) g hEnorm x (show TangentSpace I x from v) hvne (1 / 2 : ℝ)
    have hne : ricciTensor (I := I) g (γ (1 / 2 : ℝ))
        (curveVelocity (I := I) γ (1 / 2 : ℝ))
        (curveVelocity (I := I) γ (1 / 2 : ℝ)) ≠
        -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
          (0 * Real.sqrt (g.inner x v v)) ^ 2) := by
      simpa using
        (hRicPos (γ (1 / 2 : ℝ)) (curveVelocity (I := I) γ (1 / 2 : ℝ)) hvel).ne'
    exact expJacobian_lt_of_ricci (I := I) g hEnorm x hv.1 hvne 0 (by positivity) hd
      (by simpa using hRic) (t := 1 / 2) (by norm_num) (by simpa only [γ] using hne)
  have hFpos (v : E) : 0 < F v := by
    simpa [F, hyperbolicDensity, hyperbolicSn] using hncd
  have hKcomp : IsCompact K := by
    have hclosed : IsClosed {v : E | (show TangentSpace I x from v) ∈
        SegmentDom (I := I) g hEnorm x} := by
      with_unfolding_all exact
        (isClosed_segmentDom (I := I) g hEnorm x).preimage continuous_id
    exact (isCompact_closedGBall (I := I) g x R).of_isClosed_subset
      (hclosed.inter (isClosed_closedGBall (I := I) g x R))
      (Set.inter_subset_right : K ⊆ closedGBall (I := I) g x R)
  have hKmeas : MeasurableSet K := hKcomp.measurableSet
  obtain ⟨ρ, hρ, hradial⟩ := riemannianEDist_expMapIntrinsic_eq_norm_of_small (I := I) g hEnorm x
  let δ : ℝ := min ρ R / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith [lt_min hρ hR]
  have hδρ : δ < ρ := by
    dsimp only [δ]
    linarith [lt_min hρ hR, min_le_left ρ R]
  have hδR : δ < R := by
    dsimp only [δ]
    linarith [lt_min hρ hR, min_le_right ρ R]
  have hsmall : gBall (I := I) g x δ ⊆ K := by
    intro v hv
    change Real.sqrt (g.inner x v v) < δ at hv
    have hvρ : Real.sqrt (g.inner x v v) < ρ := hv.trans hδρ
    have hvseg : (show TangentSpace I x from v) ∈ SegmentDom (I := I) g hEnorm x := by
      rw [mem_segmentDom, hradial hvρ,
        ENNReal.toReal_ofReal (Real.sqrt_nonneg (g.inner x v v))]
    refine ⟨hvseg, ?_⟩
    change Real.sqrt (g.inner x v v) ≤ R
    exact (hv.trans hδR).le
  have hsmall_ne : (gBall (I := I) g x δ).Nonempty := by
    refine ⟨0, ?_⟩
    change Real.sqrt (g.inner x (0 : E) 0) < δ
    simpa using hδ
  have hsmall_ne0 : (modelHaar (E := E)) (gBall (I := I) g x δ) ≠ 0 :=
    (DifferentialGeometry.Integral.Measure.modelHaar_isAddHaarMeasure
      (E := E)).toIsOpenPosMeasure.open_pos _
        (isOpen_gBall (I := I) g x δ) hsmall_ne
  have hsmall_pos : 0 < (modelHaar (E := E)) (gBall (I := I) g x δ) :=
    hsmall_ne0.bot_lt
  have hKne : (modelHaar (E := E)) K ≠ 0 :=
    (hsmall_pos.trans_le (measure_mono hsmall)).ne'
  have hGmeas : Measurable (fun v : E => ENNReal.ofReal (F v)) := by
    have hfun : (fun v : E => ENNReal.ofReal (F v)) =
      fun _ : E => ENNReal.ofReal (normalChartDensity (I := I) g x 0) := by
      funext v
      simp [F, hyperbolicDensity, hyperbolicSn]
    rw [hfun]
    fun_prop
  have hmono : (∫⁻ v in K,
      ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)))
      ≤ ∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := by
    apply setLIntegral_mono_ae' hKmeas
    filter_upwards [Measure.ae_ne (modelHaar (E := E)) (0 : E)] with v hvne hvK
    exact ENNReal.ofReal_le_ofReal (hpoint v hvK hvne).le
  have hFfin : (∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E))) < ⊤ := by
    have hfun : (fun v : E => ENNReal.ofReal (F v)) =
      fun _ : E => ENNReal.ofReal (normalChartDensity (I := I) g x 0) := by
      funext v
      simp [F, hyperbolicDensity, hyperbolicSn]
    rw [hfun, setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKcomp.measure_lt_top
  have hfin : (∫⁻ v in K,
      ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E))) ≠ ⊤ :=
    (hmono.trans_lt hFfin).ne
  have hstrict : (∫⁻ v in K,
      ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) ∂(modelHaar (E := E)))
      < ∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := by
    apply setLIntegral_strict_mono hKmeas hKne hGmeas hfin
    filter_upwards [Measure.ae_ne (modelHaar (E := E)) (0 : E)] with v hvne hvK
    exact (ENNReal.ofReal_lt_ofReal_iff (hFpos v)).2 (hpoint v hvK hvne)
  have hmodel := gBall_model_int (I := I) g x 0 R (by positivity) hR
  calc
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R}
        ≤ ∫⁻ v in K, ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
            ∂(modelHaar (E := E)) := by
          simpa only [K] using hV
    _ < ∫⁻ v in K, ENNReal.ofReal (F v) ∂(modelHaar (E := E)) := hstrict
    _ ≤ ∫⁻ v in closedGBall (I := I) g x R,
          ENNReal.ofReal (F v) ∂(modelHaar (E := E)) :=
      lintegral_mono_set (Set.inter_subset_right : K ⊆ closedGBall (I := I) g x R)
    _ = (∫⁻ θ : Metric.sphere (0 : E) 1,
          ENNReal.ofReal (normalChartDensity (I := I) g x 0 *
            (Real.sqrt (g.inner x θ.1 θ.1) ^ (Module.finrank ℝ E))⁻¹)
          ∂(modelHaar (E := E)).toSphere)
        * ENNReal.ofReal (hyperbolicRadialVolume 0 (Module.finrank ℝ E - 1) R) := by
      simpa only [F] using hmodel

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
