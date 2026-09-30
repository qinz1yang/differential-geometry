import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.GaussianBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.Measurability
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaInequality

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Integral.Measure
open scoped Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature (metricScalarAt)

universe u

private local instance (P : OrientedThreeStage.{u}) : MeasurableSpace P.Carrier :=
  borel P.Carrier

private local instance (P : OrientedThreeStage.{u}) : BorelSpace P.Carrier := ⟨rfl⟩

private local instance : MeasurableSpace ThreeSpace := borel ThreeSpace

private local instance : BorelSpace ThreeSpace := ⟨rfl⟩

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {T B v : ℝ}
  {p : (H.stage last).Carrier}

theorem lintegral_image_historyMinDomain_tail_le {hle : first ≤ last}
    (hfloor : ∀ j, ∀ t ∈ H.stageDomain j, ∀ x : (H.stage j).Carrier,
      -B ≤ metricScalarAt (H.stageMetric j t) x)
    (hT : T ∈ Ico (H.time last) (H.stageEndTime last)) (hv : 0 < v) (R : ℝ) :
    ∫⁻ q in H.historyLExp hle T v p '' (Subtype.val ⁻¹' (H.historyMinDomain hle T B v p ∩
        {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)})),
        H.regularizedDensity first last hle T B v p q
        ∂riemannianVolumeMeasure ThreeModel (H.stage first).Carrier
          (H.stageMetric first (T - v ^ 2)) ≤
      ∫⁻ Z : ThreeSpace in {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)},
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ * H.historyLSourceDensity T p *
          Real.exp (-(H.stageMetric last T).inner p Z Z)) ∂(modelHaar (E := ThreeSpace)) := by
  classical
  rcases (H.historyMinDomain hle T B v p).eq_empty_or_nonempty with hK0 | ⟨Z₀, hZ₀⟩
  · have hempty : Subtype.val ⁻¹' (H.historyMinDomain hle T B v p ∩
        {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)}) =
        (∅ : Set (H.historyLExpDomain hle T v p)) := by
      ext Z
      refine iff_of_false (fun hZ => ?_) (notMem_empty Z)
      have h1 : Z.1 ∈ H.historyMinDomain hle T B v p := hZ.1
      rw [hK0] at h1
      exact h1
    rw [hempty, image_empty, Measure.restrict_empty, lintegral_zero_measure]
    exact bot_le
  set Tail : Set ThreeSpace := {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)}
    with hTail
  set K : Set ThreeSpace := H.historyMinDomain hle T B v p ∩ Tail with hKdef
  have hZ₀d : Z₀ ∈ H.historyLExpDomain hle T v p := historyMinDomain_subset_historyLExpDomain hZ₀
  obtain ⟨U, hU, hMU, hUd, ⟨f, hf, hfeq⟩, -⟩ :=
    exists_isOpen_superset_historyMinDomain_subset_historyLExpDomain (hle := hle) (p := p)
      hv hT hfloor (H.historyLExp hle T v p ⟨Z₀, hZ₀d⟩)
  have hKU : K ⊆ U := fun Z hZ => hMU hZ.1
  have hTailo : IsOpen Tail := by
    have hc : Continuous fun Z : ThreeSpace => (H.stageMetric last T).inner p Z Z :=
      (H.stageMetric last T).inner p |>.continuous₂.comp (continuous_id.prodMk continuous_id)
    exact isOpen_lt continuous_const (Real.continuous_sqrt.comp hc)
  have hKm : MeasurableSet K :=
    (measurableSet_historyMinDomain hv hT hfloor).inter hTailo.measurableSet
  have himg : H.historyLExp hle T v p '' (Subtype.val ⁻¹' K) = f '' K := by
    ext q
    constructor
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨Z.1, hZ, hfeq Z.1 Z.2⟩
    · rintro ⟨Z, hZ, rfl⟩
      exact ⟨⟨Z, historyMinDomain_subset_historyLExpDomain hZ.1⟩, hZ,
        (hfeq Z (historyMinDomain_subset_historyLExpDomain hZ.1)).symm⟩
  have hpt : ∀ Z ∈ K,
      ENNReal.ofReal (paramDensity (H.stageMetric first (T - v ^ 2)) f Z) *
          H.regularizedDensity first last hle T B v p (f Z) ≤
        ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ * H.historyLSourceDensity T p *
          Real.exp (-(H.stageMetric last T).inner p Z Z)) := by
    intro Z hZ
    have hZd : Z ∈ H.historyLExpDomain hle T v p := hUd (hKU hZ)
    have hJ : paramDensity (H.stageMetric first (T - v ^ 2)) f Z =
        H.historyLJacobianDensity hle T v p ⟨Z, hZd⟩ ⟨first, le_rfl, hle⟩ v := by
      refine paramDensity_eq_historyLJacobianDensity_of_eventuallyEq (Z₀ := ⟨Z, hZd⟩)
        ⟨first, le_rfl, hle⟩ v ?_
      filter_upwards [hU.mem_nhds (hKU hZ)] with W hW
      rw [hfeq W (hUd hW), historyLCurveMap_of_mem _ _ (hUd hW)]
      rfl
    have hsrc := H.historyLSourceDensity_pos (T := T) (p := p)
    have e := ofReal_historyReducedJacobian_eq hfloor hv (Z₀ := ⟨Z, hZd⟩) hZ.1
    have hG := historyReducedJacobian_le_gaussian hfloor hv ⟨Z, hZd⟩ hZ.1
    have key : ENNReal.ofReal (H.historyLJacobianDensity hle T v p ⟨Z, hZd⟩
          ⟨first, le_rfl, hle⟩ v) * H.regularizedDensity first last hle T B v p
            (H.historyLExp hle T v p ⟨Z, hZd⟩) =
        ENNReal.ofReal (H.historyLSourceDensity T p) *
          ENNReal.ofReal (H.historyReducedJacobian hle T v p ⟨Z, hZd⟩) := by
      rw [e, ← mul_assoc, ← ENNReal.ofReal_mul hsrc.le, mul_div_cancel₀ _ hsrc.ne']
    rw [hJ, hfeq Z hZd, key, ← ENNReal.ofReal_mul hsrc.le]
    refine ENNReal.ofReal_le_ofReal ?_
    calc H.historyLSourceDensity T p * H.historyReducedJacobian hle T v p ⟨Z, hZd⟩ ≤
          H.historyLSourceDensity T p * ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ *
            Real.exp (-(H.stageMetric last T).inner p Z Z)) :=
        mul_le_mul_of_nonneg_left hG hsrc.le
      _ = _ := by ring
  rw [show H.historyLExp hle T v p '' (Subtype.val ⁻¹' (H.historyMinDomain hle T B v p ∩
      {Z | R < Real.sqrt ((H.stageMetric last T).inner p Z Z)})) = f '' K from himg]
  calc _ ≤ ∫⁻ Z in K, ENNReal.ofReal (paramDensity (H.stageMetric first (T - v ^ 2)) f Z) *
          H.regularizedDensity first last hle T B v p (f Z) ∂(modelHaar (E := ThreeSpace)) :=
        lintegral_image_le_lintegral_paramDensity_mul _ hU hKm hKU hf _
    _ ≤ ∫⁻ Z in K, ENNReal.ofReal ((Real.pi ^ ((3 : ℝ) / 2))⁻¹ * H.historyLSourceDensity T p *
          Real.exp (-(H.stageMetric last T).inner p Z Z)) ∂(modelHaar (E := ThreeSpace)) :=
        setLIntegral_mono' hKm hpt
    _ ≤ _ := lintegral_mono_set inter_subset_right

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
