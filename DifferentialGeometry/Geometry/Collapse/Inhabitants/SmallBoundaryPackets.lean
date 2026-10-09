import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarAlternative
import DifferentialGeometry.Geometry.Collapse.Inhabitants.CompactDerivativeControl
import DifferentialGeometry.Geometry.Collapse.Inhabitants.CuspMetric
import DifferentialGeometry.Geometry.Metric.Distance.CompactImage
import DifferentialGeometry.Geometry.Collapse.CutPieceBalls
import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspProfile
import DifferentialGeometry.Geometry.Metric.WarpedProduct.FiberVolume
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspCurvature
import DifferentialGeometry.Geometry.Collapse.Inhabitants.DoubleCuspInterior
import DifferentialGeometry.Geometry.Collapse.Inhabitants.SmallBoundaryGeometry
import DifferentialGeometry.Geometry.Collapse.Inhabitants.BoundaryComponentCount

/-!
The actual compact double-cusp metric supplies small-threshold boundary packets on both ends.
The volume test uses a genuine interior curvature floor and the total volume of that same metric.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory DifferentialGeometry GC.Endpoint
open DifferentialGeometry.Geometry.Collapse
open GC.Seifert
open scoped ENNReal Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local instance smallBoundaryCompact : CompactSpace (productSet.{u} 2) :=
  annulusCircleCarrier.{u}.compact
local instance smallBoundaryConnected : ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)
local instance smallBoundarySigma : SigmaCompactSpace (productSet.{u} 2) :=
  CompactSpace.sigmaCompact

private theorem smallBoundaryVolume_of_total (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {w R : ℝ} (hw : 0 < w) (hR : 0 < R)
    (hfloor : ∀ p, ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g p →
      ENNReal.ofReal R ≤ curvatureRadius g p)
    (hvolume : (Integral.Measure.riemannianVolumeMeasure W.model W.Carrier g) univ ≤
      ENNReal.ofReal (w * R ^ 3)) : boundaryVolumeCollapsed W g w := by
  intro p hp r hr hrad
  have hf := hfloor p hp
  rw [hrad] at hf
  have hRr := ENNReal.toReal_mono (by simp) hf
  rw [ENNReal.toReal_ofReal hR.le, ENNReal.toReal_ofReal hr.le] at hRr
  have hpow := pow_le_pow_left₀ hR.le hRr 3
  exact (measure_mono (subset_univ _)).trans (hvolume.trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpow hw.le)))

private theorem smallBoundary_scale (D V R w : ℝ) (hD : 0 ≤ D) (hV : 0 ≤ V)
    (hR : 0 < R) (hw : 0 < w) :
    ∃ a : ℝ, 0 < a ∧ a * D ≤ w ∧ a ^ 2 * V ≤ w * R ^ 3 := by
  let a := min 1 (min (w / (D + 1)) (w * R ^ 3 / (V + 1)))
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  have ha1 : a ≤ 1 := min_le_left _ _
  have haD : a ≤ w / (D + 1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have haV : a ≤ w * R ^ 3 / (V + 1) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have haDw := (le_div_iff₀ (by positivity : 0 < D + 1)).mp haD
  have haVw := (le_div_iff₀ (by positivity : 0 < V + 1)).mp haV
  refine ⟨a, ha, by nlinarith, ?_⟩
  have hs : a ^ 2 ≤ a := by nlinarith
  have hv := mul_le_mul_of_nonneg_right hs hV
  nlinarith

private theorem smallBoundary_torus_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ x y : Torus,
      riemannianEDistOf standardCuspTorusMetric x y ≤ ENNReal.ofReal D := by
  obtain ⟨D, hD, hd⟩ := exists_uniform_riemannianEDistOf_bound_of_compact_preconnected
    standardCuspTorusMetric (ContinuousMap.id Torus) (1, 1)
  refine ⟨D + D + 1, by linarith, ?_⟩
  intro x y
  have hy : riemannianEDistOf standardCuspTorusMetric (1, 1) y ≤ ENNReal.ofReal D := by
    rw [riemannianEDistOf_comm]
    exact hd y
  refine (riemannianEDistOf_triangle standardCuspTorusMetric x (1, 1) y).trans
    ((add_le_add (hd x) hy).trans ?_)
  rw [← ENNReal.ofReal_add hD hD]
  exact ENNReal.ofReal_le_ofReal (by linarith)

private theorem smallBoundary_curvature_floor (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {C : ℝ} (hC : 0 < C)
    (hsec : ∀ q ∈ W.model.interior W.Carrier,
      Geometry.Riemannian.SectionalBoundedBelowAt g q (-C)) :
    ∀ p, ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g p →
      ENNReal.ofReal (1 / (C + 1)) ≤ curvatureRadius g p := by
  let R := 1 / (C + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : R ≤ 1 := by
    dsimp [R]
    apply (div_le_one (by positivity : 0 < C + 1)).2
    linarith
  have hCR : C * R ≤ 1 := by
    dsimp [R]
    rw [← mul_div_assoc, mul_one]
    exact (div_le_one (by positivity : 0 < C + 1)).2 (by linarith)
  have hCRR : C * R ^ 2 ≤ 1 := by
    have hs : R ^ 2 ≤ R := by nlinarith
    exact (mul_le_mul_of_nonneg_left hs hC.le).trans hCR
  have hCI : C ≤ (R ^ 2)⁻¹ := by
    rw [← one_div]
    exact (le_div_iff₀ (pow_pos hR 2)).2 hCRR
  intro p hp
  refine ofReal_le_curvatureRadius g hR ?_
  intro q hq
  have hb : ENNReal.ofReal R ≤ distanceToBoundary W g p :=
    (ENNReal.ofReal_le_ofReal (hR1.trans (by norm_num [boundaryBufferDistance]))).trans hp.le
  exact (hsec q (riemannianBallOf_subset_interior W g hb hq)).mono (neg_le_neg hCI)

private theorem smallBoundary_volume (a : ℝ) (ha : 0 < a) :
    Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
      (doubleCuspMetric.{u} a ha) =
      ENNReal.ofReal (a ^ 2) • Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3)
        (productSet.{u} 2) (doubleCuspMetric.{u} 1 zero_lt_one) := by
  let w : ℝ → ℝ := fun r => Real.exp (doubleCuspLogProfile r)
  have hw : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ w :=
    (Real.contDiff_exp.comp doubleCuspLogProfile_smooth).contMDiff
  have hp (r : ℝ) : 0 < w r := Real.exp_pos _
  have he : (DifferentialGeometry.euclideanMetric (E := ℝ)).warpedProduct
      standardCuspTorusMetric w hw hp =
      doubleCuspRealMetric 1 zero_lt_one := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v z
    rw [SmoothRiemannianMetric.warpedProduct_inner]
    rw [doubleCuspRealMetric, SmoothRiemannianMetric.warpedProduct_inner]
    simp only [doubleCuspWarp, one_mul]
    rfl
  have h := Integral.Measure.volume_warped_fiber_scale_pullback
    (I := 𝓡∂ 3) (J := torusModel) (M := productSet.{u} 2) (N := Torus)
    (by simp : Module.finrank ℝ
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2)
    (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3)
    standardCuspTorusMetric w hw hp
    doubleCuspCoordinate.{u} doubleCuspCoordinate_smooth.{u}
    doubleCuspCoordinate_immersion.{u} a ha
  change Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
    ((doubleCuspRealMetric a ha).pullback doubleCuspCoordinate.{u}
      doubleCuspCoordinate_smooth.{u} doubleCuspCoordinate_immersion.{u}) = _ at h
  rw [he] at h
  exact h

private theorem smallBoundary_volume_bound :
    ∃ V : ℝ, 0 < V ∧ ∀ (a : ℝ) (ha : 0 < a),
      Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
        (doubleCuspMetric.{u} a ha) univ ≤ ENNReal.ofReal (a ^ 2 * V) := by
  let μ := Integral.Measure.riemannianVolumeMeasure (𝓡∂ 3) (productSet.{u} 2)
    (doubleCuspMetric.{u} 1 zero_lt_one)
  let smallBoundaryFinite : IsFiniteMeasure μ :=
    Integral.Measure.riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace _
  refine ⟨(μ univ).toReal + 1, by positivity, fun a ha => ?_⟩
  rw [smallBoundary_volume a ha, Measure.smul_apply, smul_eq_mul]
  change ENNReal.ofReal (a ^ 2) * μ univ ≤ _
  rw [ENNReal.ofReal_mul (sq_nonneg _)]
  apply mul_le_mul_right
  calc
    μ univ = ENNReal.ofReal (μ univ).toReal :=
      (ENNReal.ofReal_toReal (measure_lt_top μ univ).ne).symm
    _ ≤ ENNReal.ofReal ((μ univ).toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)

theorem exists_doubleCuspBoundaryExport (K : ℕ) (hK : 2 ≤ K) (w₀ ε : ℝ)
    (hw₀ : 0 < w₀) (hw₀small : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1000) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryExportPacket annulusCircleCarrier.{u}
        (doubleCuspMetric.{u} a ha) K A w₀ ε, P.cusp.count = 2 := by
  obtain ⟨C, hC, hsec⟩ := exists_doubleCuspRealMetric_sectionalBound
  obtain ⟨V, hV, hvol⟩ := smallBoundary_volume_bound.{u}
  obtain ⟨D, hD, hdiam⟩ := smallBoundary_torus_bound
  let R : ℝ := 1 / (C + 1)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨a, ha, haD, haV⟩ := smallBoundary_scale D V R w₀ hD.le hV.le hR hw₀
  let g := doubleCuspMetric.{u} a ha
  have hfloor : ∀ p, ENNReal.ofReal boundaryBufferDistance <
      distanceToBoundary annulusCircleCarrier.{u} g p →
      ENNReal.ofReal R ≤ curvatureRadius g p :=
    smallBoundary_curvature_floor annulusCircleCarrier.{u} g hC
      (fun p hp => doubleCuspMetric_sectional_interior a ha C (hsec a ha) p hp)
  have hvolume : boundaryVolumeCollapsed annulusCircleCarrier.{u} g w₀ :=
    smallBoundaryVolume_of_total annulusCircleCarrier.{u} g hw₀ hR hfloor
      ((hvol a ha).trans (ENNReal.ofReal_le_ofReal haV))
  obtain ⟨A, hA, hderiv⟩ := exists_compact_curvatureDerivativeControl
    annulusCircleCarrier.{u} g K hw₀
  let B := doubleCuspNearlyCuspidalBoundaryAt.{u} a ha D hD.le hdiam K w₀ haD
  let P₀ : BoundaryCollapsePremises annulusCircleCarrier.{u} g K A w₀ :=
    ⟨B, hvolume, hderiv⟩
  let P := BoundaryExportPacket.ofCollarPacket
    (BoundaryCollarPacket.ofPremises P₀ hK hw₀small hε (by linarith)) (by omega) hεsmall
  exact ⟨a, ha, A, hA, P, P.cusp.count_eq_two_of_annulus⟩

theorem exists_doubleCuspBoundaryCollar (K : ℕ) (hK : 2 ≤ K) (w₀ ε : ℝ)
    (hw₀ : 0 < w₀) (hw₀small : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 1000) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryCollarPacket annulusCircleCarrier.{u}
        (doubleCuspMetric.{u} a ha) K A w₀ ε, P.cusp.count = 2 := by
  obtain ⟨a, ha, A, hA, P, hc⟩ :=
    exists_doubleCuspBoundaryExport.{u} K hK w₀ ε hw₀ hw₀small hε hεsmall
  exact ⟨a, ha, A, hA, P.toBoundaryCollarPacket, hc⟩

end DifferentialGeometry.Geometry.Collapse
