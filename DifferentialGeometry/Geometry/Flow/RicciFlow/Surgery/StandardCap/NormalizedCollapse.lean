import DifferentialGeometry.Geometry.Neck.InsertionChart
import DifferentialGeometry.Geometry.Metric.DistancePullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.CollapseDomination

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped Manifold ContDiff Topology ENNReal NNReal
namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private abbrev EC := EuclideanSpace ℝ (Fin 2) × ℝ
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance (d : normalizedDatum g x₀ δ k) : RegularSpace d.controlledImage :=
  d.controlledChart.symm.toHomeomorph.isEmbedding.isInducing.regularSpace

def positiveSideCollapseMetric (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    SmoothRiemannianMetric (𝓡 3) (insertionBall δ⁻¹) :=
  scaleMetric (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos)
    (insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric)

theorem positiveSideCollapseMetric_normalization (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    scaleMetric (metricScalarAt g x₀) d.scalar_pos (d.positiveSideCollapseMetric hA hAB) =
      insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro p v w
  simp only [positiveSideCollapseMetric, scaleMetric_inner]
  rw [← mul_assoc, mul_inv_cancel₀ d.scalar_pos.ne', one_mul]

def positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) : d.controlledImage → insertionBall δ⁻¹ :=
  collapseMap hA hAB ∘ d.controlledChart.symm

theorem positiveSideCollapseMap_controlledMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹) :
    d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ = collapseMap hA hAB q := by
  simp only [positiveSideCollapseMap, Function.comp_apply, controlledChart_symm_controlledMap]

theorem positiveSideCollapseMap_retained (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹) (hq : 0 ≤ q.val.2) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) =
        (transitionEnd + q.val.2) • (q.val.1 : E3) := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_retained hA hAB q hq

theorem positiveSideCollapseMap_collapsed (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : q.val.2 ≤ collapseTip A) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) = 0 := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_collapsed hA hAB q hq

theorem positiveSideCollapseMap_radial (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (q : openCylinder δ⁻¹)
    (hq : collapseTip A ≤ q.val.2) :
    (d.positiveSideCollapseMap hA hAB
      ⟨d.controlledMap q, d.controlledMap_mem_controlledImage q⟩ : E3) =
        collapseRadius A q.val.2 • (q.val.1 : E3) := by
  rw [positiveSideCollapseMap_controlledMap]
  exact collapseMap_radial hA hAB q hq

theorem continuous_positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) : Continuous (d.positiveSideCollapseMap hA hAB) :=
  (continuous_collapseMap hA hAB).comp d.controlledChart.symm.contMDiff.continuous

private theorem controlledChart_symm_edist (d : normalizedDatum g x₀ δ k)
    (p q : d.controlledImage) :
    riemannianEDistOf d.controlledMetric (d.controlledChart.symm p) (d.controlledChart.symm q) =
      ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)) *
        riemannianEDistOf (g.restrictOpen d.controlledImage) p q := by
  rw [controlledMetric_eq_pullback_controlledChart, edistOf_pullbackMetricCross,
    d.controlledChart.apply_symm_apply, d.controlledChart.apply_symm_apply, edistOf_scale]

theorem positiveSideCollapseMap_local_intrinsic_bound (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (p : d.controlledImage) :
    ∃ L : ℝ≥0, ∃ t ∈ 𝓝 p, ∀ x ∈ t, ∀ y ∈ t,
      riemannianEDistOf (d.positiveSideCollapseMetric hA hAB)
        (d.positiveSideCollapseMap hA hAB x) (d.positiveSideCollapseMap hA hAB y) ≤
          L * riemannianEDistOf (g.restrictOpen d.controlledImage) x y := by
  obtain ⟨L, t, ht, hL⟩ := collapseMap_local_intrinsic_bound hA hAB d.controlledMetric
    (d.positiveSideCollapseMetric hA hAB) (d.controlledChart.symm p)
  refine ⟨L * Real.toNNReal (Real.sqrt (metricScalarAt g x₀)), d.controlledChart.symm ⁻¹' t,
    d.controlledChart.symm.contMDiff.continuous.continuousAt.preimage_mem_nhds ht, ?_⟩
  intro x hx y hy
  have hb := hL (d.controlledChart.symm x) hx (d.controlledChart.symm y) hy
  rw [controlledChart_symm_edist] at hb
  simpa only [positiveSideCollapseMap, Function.comp_apply, ENNReal.coe_mul,
    ENNReal.ofReal, mul_assoc] using hb

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem locallyLipschitz_positiveSideCollapseMap (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) :
    (let s := g.restrictOpen d.controlledImage
     let cs := s.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
       ⟨cs.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideCollapseMetric hA hAB
     let ch := h.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       ⟨ch.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall δ⁻¹) := .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
     LocallyLipschitz (d.positiveSideCollapseMap hA hAB)) :=
  (locallyLipschitz_iff_local_riemannianEDistOf_le (g.restrictOpen d.controlledImage)
    (d.positiveSideCollapseMetric hA hAB) (d.positiveSideCollapseMap hA hAB)).mpr
      (d.positiveSideCollapseMap_local_intrinsic_bound hA hAB)

private theorem eVariationOn_eq_mul_of_edist
    {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]
    (f : ℝ → X) (h : ℝ → Y) (s : Set ℝ) (c : ℝ≥0∞)
    (he : ∀ t u, edist (f t) (f u) = c * edist (h t) (h u)) :
    eVariationOn f s = c * eVariationOn h s := by
  simp only [eVariationOn, he, ← Finset.mul_sum, ENNReal.mul_iSup]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem positiveSideCollapseMap_eVariationOn_le (d : normalizedDatum g x₀ δ k) {A : ℝ}
    (hA : 0 < A) (hAB : 2 * A < δ⁻¹) (γ : ℝ → d.controlledImage)
    (a b : ℝ) (hγ : ContinuousOn γ (Icc a b)) :
    (let s := g.restrictOpen d.controlledImage
     let cs := s.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
       ⟨cs.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace d.controlledImage := .ofRiemannianMetric I d.controlledImage
     let h := d.positiveSideCollapseMetric hA hAB
     let ch := h.toContinuousRiemannianMetric
     letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       ⟨ch.toRiemannianMetric⟩
     letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
       inferInstance
     letI : PseudoEMetricSpace (insertionBall δ⁻¹) := .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
     eVariationOn (d.positiveSideCollapseMap hA hAB ∘ γ) (Icc a b) ≤ eVariationOn γ (Icc a b)) := by
  let s := g.restrictOpen d.controlledImage
  let n := insertedMetric hA hAB d.controlledMetric_cylinder_lower.1 d.controlledMetric
  let h := d.positiveSideCollapseMetric hA hAB
  let mi : PseudoEMetricSpace d.controlledImage := by
    let cs := s.toContinuousRiemannianMetric
    letI : RiemannianBundle (TangentSpace I : d.controlledImage → Type _) :=
      ⟨cs.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (TangentSpace I : d.controlledImage → Type _) :=
      inferInstance
    exact .ofRiemannianMetric I d.controlledImage
  let mc : PseudoEMetricSpace (openCylinder δ⁻¹) := by
    let cc := d.controlledMetric.toContinuousRiemannianMetric
    letI : RiemannianBundle (TangentSpace IC : openCylinder δ⁻¹ → Type _) :=
      ⟨cc.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle EC (TangentSpace IC : openCylinder δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric IC (openCylinder δ⁻¹)
  let mn : PseudoEMetricSpace (insertionBall δ⁻¹) := by
    let cn := n.toContinuousRiemannianMetric
    letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      ⟨cn.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
  let mh : PseudoEMetricSpace (insertionBall δ⁻¹) := by
    let ch := h.toContinuousRiemannianMetric
    letI : RiemannianBundle (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      ⟨ch.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E3 (TangentSpace (𝓡 3) : insertionBall δ⁻¹ → Type _) :=
      inferInstance
    exact .ofRiemannianMetric (𝓡 3) (insertionBall δ⁻¹)
  let α := ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀))
  let β := ENNReal.ofReal (Real.sqrt (metricScalarAt g x₀)⁻¹)
  let ζ := d.controlledChart.symm ∘ γ
  have hζ : ContinuousOn ζ (Icc a b) :=
    d.controlledChart.symm.contMDiff.continuous.comp_continuousOn hγ
  have hc := collapseMap_eVariationOn_le_of_cylinder_lower hA hAB
    d.controlledMetric_cylinder_lower.1 d.controlledMetric
    d.controlledMetric_cylinder_lower.2 ζ a b hζ
  change @eVariationOn ℝ _ (insertionBall δ⁻¹) mn (collapseMap hA hAB ∘ ζ) (Icc a b) ≤
    @eVariationOn ℝ _ (openCylinder δ⁻¹) mc ζ (Icc a b) at hc
  have hs : @eVariationOn ℝ _ (openCylinder δ⁻¹) mc ζ (Icc a b) =
      α * @eVariationOn ℝ _ d.controlledImage mi γ (Icc a b) := by
    apply @eVariationOn_eq_mul_of_edist _ _ mc mi ζ γ (Icc a b) α
    intro t u
    exact controlledChart_symm_edist d (γ t) (γ u)
  have ht : @eVariationOn ℝ _ (insertionBall δ⁻¹) mh
      (d.positiveSideCollapseMap hA hAB ∘ γ) (Icc a b) =
      β * @eVariationOn ℝ _ (insertionBall δ⁻¹) mn (collapseMap hA hAB ∘ ζ) (Icc a b) := by
    apply @eVariationOn_eq_mul_of_edist _ _ mh mn
      (d.positiveSideCollapseMap hA hAB ∘ γ) (collapseMap hA hAB ∘ ζ) (Icc a b) β
    intro t u
    exact edistOf_scale (metricScalarAt g x₀)⁻¹ (inv_pos.mpr d.scalar_pos) n
      (collapseMap hA hAB (ζ t)) (collapseMap hA hAB (ζ u))
  have hscale : β * α = 1 := by
    dsimp only [α, β]
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (inv_pos.mpr d.scalar_pos).le,
      inv_mul_cancel₀ d.scalar_pos.ne', Real.sqrt_one, ENNReal.ofReal_one]
  change @eVariationOn ℝ _ (insertionBall δ⁻¹) mh
    (d.positiveSideCollapseMap hA hAB ∘ γ) (Icc a b) ≤
      @eVariationOn ℝ _ d.controlledImage mi γ (Icc a b)
  rw [ht]
  exact (mul_right_mono hc).trans_eq (by
    dsimp only
    rw [hs, ← mul_assoc, hscale, one_mul])

end DifferentialGeometry.Geometry.Neck.normalizedDatum
