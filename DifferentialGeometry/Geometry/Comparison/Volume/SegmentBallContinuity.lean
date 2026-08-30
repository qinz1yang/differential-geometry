import DifferentialGeometry.Geometry.Comparison.Volume.SegmentPolar

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
  [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segBall_vol_cont [RiemannianBundle (fun x : M => TangentSpace I x)]
    [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) {R : Real} (hR : 0 < R) :
    ContinuousAt (fun r : Real =>
      riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal r}) R := by
  classical
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E)))
  let q : E → Real := fun v =>
    Real.sqrt (g.inner x (show TangentSpace I x from v)
      (show TangentSpace I x from v))
  let S : Set E := SegInt (I := I) g hEnorm x
  let A : Real → Set E := fun r => S ∩ {v | q v < r}
  let D : E → ENNReal := fun v =>
    ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
  let F : Real → E → ENNReal := fun r => (A r).indicator D
  have hq_cont : Continuous q := by
    have hquad := (continuous_gInner_self (I := I) g x).comp
      (tangentSpaceModelContinuousLinearEquiv
        (I := I) x).symm.continuous
    have hsqrt := Real.continuous_sqrt.comp hquad
    have hfun :
        (Real.sqrt ∘ (fun v : TangentSpace I x ↦ g.inner x v v) ∘
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm) = q := by
      funext v
      rfl
    rw [hfun] at hsqrt
    exact hsqrt
  have hA_meas (r : Real) : MeasurableSet (A r) := by
    exact (measurableSet_segInt (I := I) g hEnorm x).inter
      (isOpen_lt hq_cont continuous_const).measurableSet
  have hD_meas : Measurable D := by
    exact ENNReal.continuous_ofReal.comp
      (expJacDensity_continuous (I := I) g hEnorm x) |>.measurable
  have hF_meas (r : Real) : Measurable (F r) :=
    hD_meas.indicator (hA_meas r)
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g x
  let level : Set E := {v | q v = R}
  have hlevel_meas : MeasurableSet level :=
    (isClosed_eq hq_cont continuous_const).measurableSet
  have hlevel_eq : level = L '' sphere (0 : E) R := by
    ext v
    constructor
    · intro hv
      refine ⟨L.symm v, ?_, L.apply_symm_apply v⟩
      rw [mem_sphere_zero_iff_norm]
      have hqv : q v = R := hv
      have hsqrt : q v = ‖L.symm v‖ := by
        have hs := normalFrame_sqrt (I := I) g x (L.symm v)
        change q (L (L.symm v)) = ‖L.symm v‖ at hs
        simpa only [L.apply_symm_apply] using hs
      exact hsqrt.symm.trans hqv
    · rintro ⟨w, hw, rfl⟩
      have hnorm : ‖w‖ = R := by
        simpa only [mem_sphere_zero_iff_norm] using hw
      change q (L w) = R
      have hs := normalFrame_sqrt (I := I) g x w
      change q (L w) = ‖w‖ at hs
      exact hs.trans hnorm
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    b.map L.toLinearEquiv
  have hmap : Measure.map L (modelHaar (E := E)) = b'.addHaar := by
    simpa only [b, b', modelHaar] using Module.Basis.map_addHaar b L
  have hlevel_map : b'.addHaar level = 0 := by
    rw [← hmap, Measure.map_apply_of_aemeasurable
      L.continuous.measurable.aemeasurable hlevel_meas, hlevel_eq,
      L.injective.preimage_image]
    exact Measure.addHaar_sphere (modelHaar (E := E)) (0 : E) R
  have hlevel_zero : (modelHaar (E := E)) level = 0 := by
    change b.addHaar level = 0
    rw [← Module.Basis.det_smul_addHaar b b', Measure.smul_apply,
      hlevel_map, smul_zero]
  let G : E → ENNReal := (A (R + 1)).indicator D
  have hbound : ∀ᶠ r in 𝓝 R,
      ∀ᵐ v ∂modelHaar (E := E), F r v ≤ G v := by
    filter_upwards [Iio_mem_nhds (lt_add_one R)] with r hr
    apply ae_of_all
    intro v
    by_cases hv : v ∈ A r
    · change v ∈ S ∧ q v < r at hv
      have hvr : v ∈ A r := by
        change v ∈ S ∧ q v < r
        exact hv
      have hv' : v ∈ A (R + 1) := by
        change v ∈ S ∧ q v < R + 1
        exact ⟨hv.1, hv.2.trans hr⟩
      simp only [F, G, indicator_of_mem hvr, indicator_of_mem hv']
      exact le_rfl
    · simp only [F, indicator_of_notMem hv, zero_le]
  have hR1 : 0 < R + 1 := hR.trans (lt_add_one R)
  have hfin : ∫⁻ v, G v ∂modelHaar (E := E) ≠ (⊤ : ENNReal) := by
    rw [show (∫⁻ v, G v ∂modelHaar (E := E)) =
        ∫⁻ v in A (R + 1), D v ∂modelHaar (E := E) by
      exact lintegral_indicator (hA_meas (R + 1)) D]
    have harea := segBall_area_eq (I := I) g hEnorm x hR1
    have hvol_fin := segBall_vol_fin (I := I) g hEnorm x (R := R + 1)
    have hset : A (R + 1) =
        SegInt (I := I) g hEnorm x ∩ gBall (I := I) g x (R + 1) := by
      rfl
    rw [hset]
    apply ne_of_lt
    calc
      (∫⁻ v in SegInt (I := I) g hEnorm x ∩
          gBall (I := I) g x (R + 1), D v ∂modelHaar (E := E)) =
          riemannianVolumeMeasure (I := I) (M := M) g
            {y : M | riemannianEDist I x y < ENNReal.ofReal (R + 1)} := by
        dsimp only [D]
        with_unfolding_all exact harea.symm
      _ < (⊤ : ENNReal) := hvol_fin
  have hlim : ∀ᵐ v ∂modelHaar (E := E),
      Tendsto (fun r : Real => F r v) (𝓝 R) (𝓝 (F R v)) := by
    filter_upwards [(measure_eq_zero_iff_ae_notMem.mp hlevel_zero)] with v hv
    have hq_ne : q v ≠ R := by
      simpa only [level, mem_ofPred_eq] using hv
    rcases lt_or_gt_of_ne hq_ne with hlt | hgt
    · have hev : (fun r : Real => F r v) =ᶠ[𝓝 R] fun _ => F R v := by
        filter_upwards [Ioi_mem_nhds hlt] with r hr
        by_cases hvS : v ∈ S
        · have hvr : v ∈ A r := by
            change v ∈ S ∧ q v < r
            exact ⟨hvS, hr⟩
          have hvR : v ∈ A R := by
            change v ∈ S ∧ q v < R
            exact ⟨hvS, hlt⟩
          simp only [F, indicator_of_mem hvr, indicator_of_mem hvR]
        · have hvAr : v ∉ A r := fun h => hvS h.1
          have hvAR : v ∉ A R := fun h => hvS h.1
          simp only [F, indicator_of_notMem hvAr, indicator_of_notMem hvAR]
      exact tendsto_const_nhds.congr' hev.symm
    · have hev : (fun r : Real => F r v) =ᶠ[𝓝 R] fun _ => F R v := by
        filter_upwards [Iio_mem_nhds hgt] with r hr
        have hvAr : v ∉ A r := by
          intro h
          change v ∈ S ∧ q v < r at h
          exact (not_lt_of_ge hr.le) h.2
        have hvAR : v ∉ A R := by
          intro h
          change v ∈ S ∧ q v < R at h
          exact (not_lt_of_ge hgt.le) h.2
        simp only [F, indicator_of_notMem hvAr, indicator_of_notMem hvAR]
      exact tendsto_const_nhds.congr' hev.symm
  have hDCT : Tendsto (fun r : Real =>
      ∫⁻ v, F r v ∂modelHaar (E := E)) (𝓝 R)
      (𝓝 (∫⁻ v, F R v ∂modelHaar (E := E))) :=
    tendsto_lintegral_filter_of_dominated_convergence G
      (Eventually.of_forall hF_meas) hbound hfin hlim
  have hR_integral :
      (∫⁻ v, F R v ∂modelHaar (E := E)) =
        riemannianVolumeMeasure (I := I) (M := M) g
          {y : M | riemannianEDist I x y < ENNReal.ofReal R} := by
    rw [lintegral_indicator (hA_meas R)]
    have harea := segBall_area_eq (I := I) g hEnorm x hR
    dsimp only [F, A, D, q, S]
    with_unfolding_all exact harea.symm
  rw [hR_integral] at hDCT
  apply hDCT.congr'
  filter_upwards [Ioi_mem_nhds hR] with r hr
  rw [lintegral_indicator (hA_meas r)]
  have harea := segBall_area_eq (I := I) g hEnorm x hr
  dsimp only [F, A, D, q, S]
  with_unfolding_all exact harea.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
