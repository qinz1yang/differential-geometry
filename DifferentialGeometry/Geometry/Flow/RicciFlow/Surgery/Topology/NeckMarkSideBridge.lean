import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Neck.NormalizedDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.EndNeckDatum
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalDiffeomorphEmbedding
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Arity
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion

set_option autoImplicit false
noncomputable section

open Set Function
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Neck (bufferedCylinder referenceMetric normalizedDatum
  spherePoint cylinderCenter)

universe u

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {h : SmoothRiemannianMetric ThreeModel M} {δ : ℝ} {k : ℕ}

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_of_chart_eq_of_center_eq {N₁ N₂ : NormalizedNeck h δ k}
    (hchart : N₁.chart = N₂.chart) (hcenter : N₁.center = N₂.center) :
    N₁.sphereMark = N₂.sphereMark := by
  have h₁ : N₂.chart ⟨(N₁.sphereMark, 0), by
      have := inv_pos.mpr N₁.delta_pos
      constructor <;> linarith⟩ = N₂.center := by
    rw [← hchart, ← hcenter]
    exact N₁.marked
  have h₂ : N₂.chart ⟨(N₂.sphereMark, 0), by
      have := inv_pos.mpr N₂.delta_pos
      constructor <;> linarith⟩ = N₂.center := N₂.marked
  have h₃ := N₂.chart_smooth.isEmbedding.injective (h₁.trans h₂.symm)
  have h₄ := congrArg (fun x : neckBuffer δ => ((x : Sphere 2 × ℝ).1)) h₃
  simpa using h₄

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_spherePoint_iff_chart_cylinderCenter
    (N : NormalizedNeck h δ k) :
    N.sphereMark = spherePoint ↔
      N.chart (cylinderCenter δ N.delta_pos : neckBuffer δ) = N.center := by
  constructor
  · intro hmark
    have hp : (cylinderCenter δ N.delta_pos : neckBuffer δ) =
        ⟨(N.sphereMark, 0), by
          have := inv_pos.mpr N.delta_pos
          constructor <;> linarith⟩ := by
      apply Subtype.ext
      simp only [cylinderCenter, hmark]
    rw [hp]
    exact N.marked
  · intro hcenter
    have h₁ : N.chart ⟨(N.sphereMark, 0), by
        have := inv_pos.mpr N.delta_pos
        constructor <;> linarith⟩ = N.center := N.marked
    have h₃ := N.chart_smooth.isEmbedding.injective (h₁.trans hcenter.symm)
    have h₄ := congrArg (fun x : neckBuffer δ => ((x : Sphere 2 × ℝ).1)) h₃
    have h₅ : ((cylinderCenter δ N.delta_pos : neckBuffer δ) : Sphere 2 × ℝ) =
        (spherePoint, 0) :=
      rfl
    rw [h₅] at h₄
    simpa using h₄

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.sphereMark_eq_spherePoint_of_datum (N : NormalizedNeck h δ k)
    (d : normalizedDatum h N.center δ k)
    (hchart : ∀ x : bufferedCylinder δ, d.map x = N.chart x) : N.sphereMark = spherePoint := by
  rw [N.sphereMark_eq_spherePoint_iff_chart_cylinderCenter]
  exact (hchart _).symm.trans ((rfl : d.map (cylinderCenter δ N.delta_pos : bufferedCylinder δ) =
    d.map (cylinderCenter δ d.precision_pos)).trans d.center_eq)

omit [SigmaCompactSpace M] in
theorem NormalizedNeck.not_exists_datum_of_sphereMark_ne (N : NormalizedNeck h δ k)
    (hne : N.sphereMark ≠ spherePoint) :
    ¬ ∃ d : normalizedDatum h N.center δ k,
        ∀ x : bufferedCylinder δ, d.map x = N.chart x := by
  rintro ⟨d, hchart⟩
  exact hne (N.sphereMark_eq_spherePoint_of_datum d hchart)

omit [T2Space M] [SigmaCompactSpace M] in
theorem NormalizedNeck.exists_sphereMark_ne_of_scalar_eq (N : NormalizedNeck h δ k)
    (y : Sphere 2) (hy : y ≠ N.sphereMark) (hmem : (y, 0) ∈ neckBuffer δ)
    (hscalar : metricScalarAt h (N.chart ⟨(y, 0), hmem⟩) = N.scale) :
    ∃ N' : NormalizedNeck h δ k, N'.sphereMark ≠ N.sphereMark ∧ N'.chart = N.chart ∧
      N'.normalizedMetric = N.normalizedMetric := by
  exact ⟨{ N with
    sphereMark := y
    center := N.chart ⟨(y, 0), hmem⟩
    marked := congrArg (fun q : neckBuffer δ => N.chart q) (Subtype.ext rfl)
    scale_scalar := hscalar.symm }, hy, rfl, rfl⟩

open DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (localDiffeomorphAt_isImmersionAtOfComplement)
open DifferentialGeometry.CheegerGromovCompactness

private local instance : Fact (Module.finrank ℝ ThreeSpace = 3) := ⟨by simp [ThreeSpace]⟩

theorem referenceMetric_eq_roundCylinderMetric_neckBuffer (δ : ℝ) :
    referenceMetric δ = roundCylinderMetric.restrictOpen (neckBuffer δ) := by
  rw [referenceMetric, roundCylinderMetric_eq_geometry]
  rfl

private theorem metricDerivNormSupOn_self_neckClosedTest (δ : ℝ) (k : ℕ)
    (g : SmoothRiemannianMetric NeckCylinderModel (neckBuffer δ)) :
    metricDerivNormSupOn (neckClosedTest δ) k g g g = 0 := by
  refine le_antisymm ?_ ?_
  · refine Real.sSup_le (fun r hr => ?_) le_rfl
    obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
    exact le_of_eq (metricDerivNorm_self a g g x)
  · exact Real.sSup_nonneg (fun r hr => by
      obtain ⟨a, _ha, x, _hx, rfl⟩ := hr
      rw [metricDerivNorm_self])

private theorem endNeckMarker_mem (y : Sphere 2) {δ : ℝ} (hδ : 0 < δ) :
    ((y, 0) : Sphere 2 × ℝ) ∈ neckBuffer δ := by
  change -δ⁻¹ - 1 < (0 : ℝ) ∧ (0 : ℝ) < δ⁻¹ + 1
  have hi := inv_pos.mpr hδ
  constructor <;> linarith

private theorem endNeckMap_marker (r δ : ℝ) (hδ : 0 < δ) (y : Sphere 2) :
    endNeckMap r δ ⟨(y, 0), endNeckMarker_mem y hδ⟩ = r • (y : ThreeSpace) := by
  rw [endNeckMap_apply]
  simp only [add_zero]

private theorem metricScalarAt_endNeckMap_marker (r δ : ℝ) (hδ : 0 < δ)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (y : Sphere 2) :
    metricScalarAt metric (r • (y : ThreeSpace)) = 1 := by
  rw [← endNeckMap_marker r δ hδ y]
  exact endNeckMap_scalar hr _

private theorem metricScalarAt_endNeckMap_center (r δ : ℝ) (hδ : 0 < δ)
    (hr : transitionEnd + δ⁻¹ + 1 < r) :
    metricScalarAt metric (r • (spherePoint : ThreeSpace)) = 1 :=
  metricScalarAt_endNeckMap_marker r δ hδ hr spherePoint

private theorem endNeckMap_isImmersion (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    Manifold.IsImmersion NeckCylinderModel ThreeModel ∞
      (fun z : neckBuffer δ => endNeckMap r δ z) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp
  have hloc : IsLocalDiffeomorph NeckCylinderModel (𝓡 3) ∞ (endNeckMap r δ) :=
    isLocalDiffeomorph_of_injective_mfderiv (endNeckMap r δ)
      (endNeckDatum r δ hδ hδ1 hr k false).smooth
      (endNeckDatum r δ hδ hδ1 hr k false).immersion hdim
  have h : Manifold.IsImmersion NeckCylinderModel (𝓡 3) ∞ (endNeckMap r δ) :=
    Manifold.IsImmersionOfComplement.isImmersion fun z =>
      localDiffeomorphAt_isImmersionAtOfComplement (hloc z)
  exact h

private theorem endNeckMap_isEmbedding (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    Topology.IsEmbedding (fun z : neckBuffer δ => endNeckMap r δ z) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) =
      Module.finrank ℝ ThreeSpace := by
    simp
  have h : _root_.Topology.IsOpenEmbedding (endNeckMap r δ) :=
    isOpenEmbedding_of_injective_immersion (endNeckMap r δ)
      (endNeckDatum r δ hδ hδ1 hr k false).smooth
      (endNeckDatum r δ hδ hδ1 hr k false).injective
      (endNeckDatum r δ hδ hδ1 hr k false).immersion hdim
  exact h.toIsEmbedding

def endNeckNormalizedNeck (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    NormalizedNeck metric δ k where
  delta_pos := hδ
  delta_lt_one := hδ1
  sphereMark := y
  center := r • (y : ThreeSpace)
  chart := ⟨fun z : neckBuffer δ => endNeckMap r δ z,
    (endNeckDatum r δ hδ hδ1 hr k false).smooth.continuous⟩
  chart_smooth := ⟨endNeckMap_isImmersion r δ hδ hδ1 hr k,
    endNeckMap_isEmbedding r δ hδ hδ1 hr k⟩
  marked := endNeckMap_marker r δ hδ y
  scale := 1
  scale_pos := one_pos
  scale_scalar := (metricScalarAt_endNeckMap_marker r δ hδ hr y).symm
  normalizedMetric := (endNeckDatum r δ hδ hδ1 hr k false).normalizedMetric
  normalized_inner := by
    intro x V W
    have h := (endNeckDatum r δ hδ hδ1 hr k false).normalizedMetric_inner x V W
    rw [metricScalarAt_endNeckMap_center r δ hδ hr, one_mul] at h
    have h' : ((endNeckDatum r δ hδ hδ1 hr k false).normalizedMetric.inner x V W) =
        metric.inner ((fun z : neckBuffer δ => endNeckMap r δ z) x)
          (mfderiv NeckCylinderModel ThreeModel (fun z : neckBuffer δ => endNeckMap r δ z) x V)
          (mfderiv NeckCylinderModel ThreeModel
            (fun z : neckBuffer δ => endNeckMap r δ z) x W) := h
    rw [one_mul]
    exact h'
  closeness := by
    rw [endNeckDatum_normalizedMetric, referenceMetric_eq_roundCylinderMetric_neckBuffer,
      metricDerivNormSupOn_self_neckClosedTest]
    exact hδ

theorem endNeckNormalizedNeck_sphereMark (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).sphereMark = y := rfl

theorem endNeckNormalizedNeck_center (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).center = r • (y : ThreeSpace) := rfl

theorem endNeckNormalizedNeck_chart (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    ((endNeckNormalizedNeck r δ hδ hδ1 hr k y).chart : neckBuffer δ → ThreeSpace) =
      fun z : neckBuffer δ => endNeckMap r δ z := rfl

theorem endNeckNormalizedNeck_normalizedMetric (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) (y : Sphere 2) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k y).normalizedMetric = referenceMetric δ :=
  endNeckDatum_normalizedMetric r δ hδ hδ1 hr k false

theorem neg_spherePoint_ne_spherePoint : (-spherePoint : Sphere 2) ≠ spherePoint :=
  fun h => ne_neg_of_mem_unit_sphere ℝ spherePoint h.symm

theorem endNeckNormalizedNeck_sphereMark_countermodel (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).sphereMark ≠
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).sphereMark ∧
      (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).chart =
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).chart ∧
      (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).normalizedMetric =
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).normalizedMetric :=
  ⟨neg_spherePoint_ne_spherePoint, rfl, rfl⟩

theorem endNeckNormalizedNeck_exists_datum (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    ∃ d : normalizedDatum metric
        (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).center δ k,
      ∀ x : bufferedCylinder δ,
        d.map x = (endNeckNormalizedNeck r δ hδ hδ1 hr k spherePoint).chart x :=
  ⟨endNeckDatum r δ hδ hδ1 hr k false, fun _ => rfl⟩

theorem endNeckNormalizedNeck_not_exists_datum_neg (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    ¬ ∃ d : normalizedDatum metric
        (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).center δ k,
      ∀ x : bufferedCylinder δ,
        d.map x = (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)).chart x := by
  refine NormalizedNeck.not_exists_datum_of_sphereMark_ne
    (endNeckNormalizedNeck r δ hδ hδ1 hr k (-spherePoint)) ?_
  rw [endNeckNormalizedNeck_sphereMark]
  exact neg_spherePoint_ne_spherePoint

theorem endNeckDatum_retainedSide_countermodel (r δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hr : transitionEnd + δ⁻¹ + 1 < r) (k : ℕ) :
    (endNeckDatum r δ hδ hδ1 hr k false).retainedSign ≠
        (endNeckDatum r δ hδ hδ1 hr k true).retainedSign ∧
      (endNeckDatum r δ hδ hδ1 hr k false).map =
        (endNeckDatum r δ hδ hδ1 hr k true).map ∧
      (endNeckDatum r δ hδ hδ1 hr k false).normalizedMetric =
        (endNeckDatum r δ hδ hδ1 hr k true).normalizedMetric := by
  refine ⟨?_, rfl, ?_⟩
  · rw [normalizedDatum.retainedSign, normalizedDatum.retainedSign,
      endNeckDatum_retainedSide, endNeckDatum_retainedSide]
    norm_num
  · rw [endNeckDatum_normalizedMetric, endNeckDatum_normalizedMetric]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace DifferentialGeometry.Geometry.Neck

open scoped ContDiff ENNReal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3) :=
  ⟨by simp⟩

def normalizedDatum.withRetainedSide (d : normalizedDatum g x₀ δ k) (b : Bool) :
    normalizedDatum g x₀ δ k :=
  { d with retainedSide := b }

theorem normalizedDatum.withRetainedSide_retainedSide (d : normalizedDatum g x₀ δ k) (b : Bool) :
    (d.withRetainedSide b).retainedSide = b := rfl

theorem normalizedDatum.withRetainedSide_geometric_eq (d : normalizedDatum g x₀ δ k) (b : Bool) :
    (d.withRetainedSide b).map = d.map ∧ (d.withRetainedSide b).smooth = d.smooth ∧
      (d.withRetainedSide b).center_eq = d.center_eq ∧
      (d.withRetainedSide b).normalizedMetric = d.normalizedMetric ∧
      (d.withRetainedSide b).error_lt = d.error_lt :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem normalizedDatum.withRetainedSide_ne (d : normalizedDatum g x₀ δ k) (b : Bool)
    (hb : b ≠ d.retainedSide) : d.withRetainedSide b ≠ d := by
  intro h
  exact hb (by rw [← h, d.withRetainedSide_retainedSide])

theorem roundCylinderDatum_retainedSide_countermodel (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) :
    (roundCylinderDatum δ hδ hδ1 k false).retainedSign ≠
        (roundCylinderDatum δ hδ hδ1 k true).retainedSign ∧
      (roundCylinderDatum δ hδ hδ1 k false).map =
        (roundCylinderDatum δ hδ hδ1 k true).map := by
  refine ⟨?_, rfl⟩
  · rw [normalizedDatum.retainedSign, normalizedDatum.retainedSign,
      roundCylinderDatum_retainedSide, roundCylinderDatum_retainedSide]
    norm_num

end DifferentialGeometry.Geometry.Neck


namespace DifferentialGeometry.Geometry.Neck.normalizedDatum

open DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology.Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
variable {g : SmoothRiemannianMetric ThreeModel M} {x₀ : M} {δ : ℝ} {k : ℕ}

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

def toNormalizedNeck (d : normalizedDatum g x₀ δ k) :
    NormalizedNeck g δ k := by
  refine ⟨d.precision_pos, d.precision_lt_one, spherePoint, x₀,
    ⟨d.map, d.smooth.continuous⟩, ?_, ?_, metricScalarAt g x₀, d.scalar_pos, rfl,
    d.normalizedMetric, ?_, ?_⟩
  · exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv
      d.smooth d.injective d.immersion (by simp [ThreeSpace])
  · exact d.center_eq
  · exact d.normalizedMetric_inner
  · have hE := d.error_lt
    change metricDerivENormSupOn (controlledCylinder δ) k d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ at hE
    rw [metricDerivENormSupOn_eq_ofReal_of_isCompact
      (isCompact_controlledCylinder δ) k d.normalizedMetric (referenceMetric δ) (referenceMetric δ)] at hE
    have hnorm : metricDerivNormSupOn (controlledCylinder δ) k d.normalizedMetric
        (referenceMetric δ) (referenceMetric δ) < δ :=
      (ENNReal.ofReal_lt_ofReal_iff d.precision_pos).mp hE
    have hset : controlledCylinder δ = neckClosedTest δ := by
      ext x
      rfl
    rw [hset] at hnorm
    rw [← referenceMetric_eq_roundCylinderMetric_neckBuffer δ]
    exact hnorm

@[simp] theorem toNormalizedNeck_chart (d : normalizedDatum g x₀ δ k) :
    (d.toNormalizedNeck.chart : neckBuffer δ → M) = d.map := by
  rfl

@[simp] theorem toNormalizedNeck_center (d : normalizedDatum g x₀ δ k) :
    d.toNormalizedNeck.center = x₀ := rfl

@[simp] theorem toNormalizedNeck_sphereMark (d : normalizedDatum g x₀ δ k) :
    d.toNormalizedNeck.sphereMark = spherePoint := rfl

end DifferentialGeometry.Geometry.Neck.normalizedDatum
