import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspVolumeTransfer
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspCollarVolume

/-!
# Volume of a height window of a cusp of a finite-volume hyperbolic model (S26)

For `T : HyperbolicTruncation H` and a cusp `i`, the window `{a < z < b}` (`0 ≤ a ≤ b`) of the
half-collar `T.cuspMap i` has volume at most `A e^{-a} (b - a)`, `A` the area of the cusp torus.

Proof: the exact isometry `T.cuspIsometry` and the model formula give
`paramDensity H.metric (T.cuspMap i ∘ cuspAngleParam) v ≤ c e^{-v₂} ρ_T(u)` at positive heights
(the `δ = 0` case of `CuspEmbedding.paramDensity_cuspAngle_bounds`); the area formula on the
angle set and `setLIntegral_cuspAngleSet_eq` bound the volume by the cusp measure, which is
`≤ A e^{-a} (b - a)`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Function
open DifferentialGeometry DifferentialGeometry.Integral.Measure GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff ENNReal Real

namespace GC.LongTime.Ch12

local notation "E₂" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

private local instance instMeasE₃_S26 : MeasurableSpace E₃ := borel E₃
private local instance instBorelE₃_S26 : BorelSpace E₃ := ⟨rfl⟩

universe u

/-- The cusp measure of a set of heights in `(a, b)` is at most `Area · e^{-a} · (b - a)`. -/
theorem cusp_measure_le_torusArea_exp_mul_S26 (Hc : HyperbolicCusp) {S : Set (Torus × ℝ)}
    {a b : ℝ} (hS : ∀ q ∈ S, a < q.2 ∧ q.2 < b) :
    (@Measure.prod Torus ℝ (borel Torus) _
        (riemannianVolumeMeasure torusModel Torus Hc.torusMetric) volume).withDensity
          (fun q => ENNReal.ofReal (Real.exp (-q.2))) S ≤
      riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ *
        ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (b - a) := by
  let : MeasurableSpace Torus := borel Torus
  set μ₀ := (riemannianVolumeMeasure torusModel Torus Hc.torusMetric).prod
    (volume : Measure ℝ) with hμ₀
  set T : Set (Torus × ℝ) := univ ×ˢ Ioo a b with hT
  have hTm : MeasurableSet T := MeasurableSet.univ.prod measurableSet_Ioo
  have hST : S ⊆ T := fun q hq => ⟨mem_univ _, (hS q hq).1, (hS q hq).2⟩
  calc μ₀.withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) S
      ≤ μ₀.withDensity (fun q => ENNReal.ofReal (Real.exp (-q.2))) T := measure_mono hST
    _ = ∫⁻ q in T, ENNReal.ofReal (Real.exp (-q.2)) ∂μ₀ := withDensity_apply _ hTm
    _ ≤ ∫⁻ _ in T, ENNReal.ofReal (Real.exp (-a)) ∂μ₀ := by
        refine setLIntegral_mono' hTm fun q hq => ?_
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith [hq.2.1]))
    _ = ENNReal.ofReal (Real.exp (-a)) * μ₀ T := by rw [setLIntegral_const]
    _ ≤ ENNReal.ofReal (Real.exp (-a)) *
          (riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ * volume (Ioo a b)) := by
        gcongr
        exact Measure.prod_prod_le _ _
    _ = riemannianVolumeMeasure torusModel Torus Hc.torusMetric univ *
          ENNReal.ofReal (Real.exp (-a)) * ENNReal.ofReal (b - a) := by
        rw [Real.volume_Ioo]
        ring

variable {H : FiniteVolumeHyperbolicModel.{u}} (T : HyperbolicTruncation H) (i : Fin T.count)

/-- **Density along the angle parametrisation of a cusp (exact isometry).** -/
theorem paramDensity_cuspMap_cuspAngle_le_S26 {v : E₃} (hv0 : 0 < v 2) :
    paramDensity H.metric (T.cuspMap i ∘ cuspAngleParam) v ≤
      cuspAngleConstant * (Real.exp (-v 2) *
        paramDensity (T.cusp i).torusMetric torusAngleParam (cuspCoordEquiv v).1) := by
  set gT := (T.cusp i).torusMetric
  set u := (cuspCoordEquiv v).1
  set B : LinearMap.BilinForm ℝ E₃ :=
    (cuspModelForm gT u (v 2)).compl₁₂ cuspCoordEquiv.toLinearMap cuspCoordEquiv.toLinearMap
    with hB
  have hBapp : ∀ x y : E₃, B x y = cuspModelForm gT u (v 2) (cuspCoordEquiv x) (cuspCoordEquiv y) :=
    fun x y => rfl
  have hsqrt : Real.sqrt (LinearMap.BilinForm.toMatrix
      (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E₃) B).det =
      cuspAngleConstant * (Real.exp (-v 2) * paramDensity gT torusAngleParam u) :=
    sqrt_det_toMatrix_cuspModelForm_comp gT u (v 2)
  have hsymm : ∀ x y, B x y = B y x := by
    intro x y
    rw [hBapp, hBapp, cuspModelForm_apply, cuspModelForm_apply, gT.symm]
    ring
  have hparam : MDifferentiableAt 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v :=
    (hasMFDerivAt_cuspAngleParam hv0).mdifferentiableAt
  have hmap : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) (cuspAngleParam v) :=
    (T.cuspEmbedding i).contMDiff.mdifferentiableAt (by simp)
  have hchain : ∀ x : E₃, mfderiv 𝓘(ℝ, E₃) (𝓡 3) (T.cuspMap i ∘ cuspAngleParam) v x =
      mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (cuspAngleParam v)
        (mfderiv 𝓘(ℝ, E₃) halfCollarModel cuspAngleParam v x) := by
    intro x
    rw [mfderiv_comp v hmap hparam]
    rfl
  have h := paramDensity_le_rpow_mul_sqrt_det H.metric (T.cuspMap i ∘ cuspAngleParam) v hsymm
    (zero_le_one : (0 : ℝ) ≤ 1) (fun x => by
      rw [hchain, one_mul]
      refine le_of_eq ?_
      change H.metric.inner (T.cuspMap i (cuspAngleParam v)) _ _ = _
      rw [T.cuspIsometry i]
      exact metric_inner_mfderiv_cuspAngleParam (T.cusp i) hv0 x x)
  rwa [Real.one_rpow, one_mul, hsqrt] at h

/-- **Volume of the image of a set of positive heights** is at most its cusp measure. -/
theorem volume_cuspMap_image_le_S26 {S : Set (Torus × ℝ)}
    (hS : MeasurableSet[borel (Torus × ℝ)] S) (hSd : ∀ p ∈ S, 0 < p.2) :
    riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (T.cuspMap i '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S)) ≤
      (@Measure.prod Torus ℝ (borel Torus) _
          (riemannianVolumeMeasure torusModel Torus (T.cusp i).torusMetric) volume).withDensity
            (fun p => ENNReal.ofReal (Real.exp (-p.2))) S := by
  set KS := cuspAngleSet S with hKSdef
  set U : Set E₃ := {v | 0 < v 2} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const (by fun_prop : Continuous fun v : E₃ => v 2)
  have hKU : KS ⊆ U := fun v hv => hSd _ hv.2
  have hKm : MeasurableSet KS := measurableSet_cuspAngleSet hS
  have hΨ : ContMDiffOn 𝓘(ℝ, E₃) (𝓡 3) 1 (T.cuspMap i ∘ cuspAngleParam) U :=
    ((T.cuspEmbedding i).contMDiff.of_le (by exact_mod_cast le_top)).comp_contMDiffOn
      ((contMDiffOn_cuspAngleParam.mono fun v (hv : 0 < v 2) => hv.le).of_le
        (by exact_mod_cast le_top))
  have hinj : InjOn (T.cuspMap i ∘ cuspAngleParam) KS := by
    intro v hv v' hv' h
    exact injOn_cuspAngleParam ⟨hv.1, (hKU hv).le⟩ ⟨hv'.1, (hKU hv').le⟩
      ((T.cuspEmbedding i).isEmbedding.injective h)
  have hT : T.cuspMap i '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S) =
      (T.cuspMap i ∘ cuspAngleParam) '' KS := by
    rw [image_lift_eq_image_cuspAngleSet, image_comp]
  rw [hT, riemannianVolumeMeasure_image_eq H.metric hUo hKm hKU hΨ hinj,
    ← setLIntegral_cuspAngleSet_eq (T.cusp i).torusMetric hS]
  refine setLIntegral_mono' hKm fun v hv => ?_
  exact ENNReal.ofReal_le_ofReal (paramDensity_cuspMap_cuspAngle_le_S26 T i (hKU hv))

/-- **Volume of a cusp window.** -/
theorem cusp_window_volume_le_S26 : ∃ A : ℝ, 0 ≤ A ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b →
    riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
      (T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0 ∧ q.2.val 0 < b}) ≤
      ENNReal.ofReal (A * Real.exp (-a) * (b - a)) := by
  set gT := (T.cusp i).torusMetric
  have hfin : riemannianVolumeMeasure torusModel Torus gT univ ≠ ⊤ := by
    let : MeasurableSpace Torus := borel Torus
    have : IsFiniteMeasure (riemannianVolumeMeasure torusModel Torus gT) :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := torusModel) (M := Torus) gT
    exact measure_ne_top _ _
  refine ⟨(riemannianVolumeMeasure torusModel Torus gT univ).toReal, ENNReal.toReal_nonneg,
    fun a b ha _ => ?_⟩
  set S : Set (Torus × ℝ) := Prod.snd ⁻¹' Ioo a b with hS
  have hSm : MeasurableSet[borel (Torus × ℝ)] S := by
    have hA : MeasurableSet[borel ℝ] (Ioo a b) := by
      rw [← BorelSpace.measurable_eq]
      exact measurableSet_Ioo
    exact continuous_snd.borel_measurable hA
  have hsub : T.cuspMap i '' {q : CuspHalfSpace | a < q.2.val 0 ∧ q.2.val 0 < b} ⊆
      T.cuspMap i '' ((fun p : Torus × ℝ => (p.1, halfSpaceOneLift p.2)) '' S) := by
    rintro _ ⟨q, ⟨hq1, hq2⟩, rfl⟩
    refine ⟨q, ⟨(q.1, q.2.val 0), ⟨hq1, hq2⟩, ?_⟩, rfl⟩
    exact Prod.ext rfl (halfSpaceOneLift_val_zero_self q.2)
  have hvol := volume_cuspMap_image_le_S26 T i hSm fun p hp => lt_of_le_of_lt ha hp.1
  have hμ := cusp_measure_le_torusArea_exp_mul_S26 (T.cusp i) (S := S) (a := a) (b := b)
    fun q hq => hq
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := hvol
    _ ≤ _ := hμ
    _ = ENNReal.ofReal ((riemannianVolumeMeasure torusModel Torus gT univ).toReal *
          Real.exp (-a) * (b - a)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le),
          ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin]

end GC.LongTime.Ch12
