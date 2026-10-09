import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Curvature.ScalarRoundCylinder
import DifferentialGeometry.Geometry.Curvature.RoundCylinder
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Neck

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def spherePoint : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩

def bufferedCylinder (δ : ℝ) : Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ Ioo (-δ⁻¹ - 1) (δ⁻¹ + 1)}, isOpen_Ioo.preimage continuous_snd⟩

def controlledCylinder (δ : ℝ) : Set (bufferedCylinder δ) :=
  {q | q.val.2 ∈ Icc (-δ⁻¹) δ⁻¹}

def cylinderCenter (δ : ℝ) (hδ : 0 < δ) : bufferedCylinder δ :=
  ⟨(spherePoint, 0), by
    change -δ⁻¹ - 1 < 0 ∧ (0 : ℝ) < δ⁻¹ + 1
    have hi := inv_pos.mpr hδ
    constructor <;> linarith⟩

def referenceMetric (δ : ℝ) : SmoothRiemannianMetric IC (bufferedCylinder δ) :=
  (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (bufferedCylinder δ)

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
private theorem cylinder_dimension_eq :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E := by
  rw [show Module.finrank ℝ E = 3 from Fact.out]
  simp

structure normalizedDatum (g : SmoothRiemannianMetric I M) (x₀ : M) (δ : ℝ) (k : ℕ) where
  precision_pos : 0 < δ
  precision_lt_one : δ < 1
  map : bufferedCylinder δ → M
  smooth : ContMDiff IC I ∞ map
  injective : Injective map
  immersion : ∀ x, Injective (mfderiv IC I map x)
  center_eq : map (cylinderCenter δ precision_pos) = x₀
  scalar_pos : 0 < metricScalarAt g x₀
  error_lt : metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric (metricScalarAt g x₀) scalar_pos g) map
      (isLocalDiffeomorph_of_injective_mfderiv map smooth immersion cylinder_dimension_eq)
      injective) (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  retainedSide : Bool

namespace normalizedDatum

variable {g : SmoothRiemannianMetric I M} {x₀ : M} {δ : ℝ} {k : ℕ}

theorem isOpenEmbedding_map (d : normalizedDatum g x₀ δ k) :
    _root_.Topology.IsOpenEmbedding d.map :=
  isOpenEmbedding_of_injective_immersion d.map d.smooth d.injective d.immersion
    cylinder_dimension_eq

def normalizedMetric (d : normalizedDatum g x₀ δ k) :
    SmoothRiemannianMetric IC (bufferedCylinder δ) :=
  pullbackMetricOfInjectiveLocalDiffeomorph
    (scaleMetric (metricScalarAt g x₀) d.scalar_pos g) d.map
    (isLocalDiffeomorph_of_injective_mfderiv d.map d.smooth d.immersion cylinder_dimension_eq)
    d.injective

theorem normalizedMetric_inner (d : normalizedDatum g x₀ δ k)
    (x : bufferedCylinder δ) (v w : TangentSpace IC x) :
    d.normalizedMetric.inner x v w = metricScalarAt g x₀ *
      g.inner (d.map x) (mfderiv IC I d.map x v) (mfderiv IC I d.map x w) := by
  rw [normalizedMetric, pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner]

theorem normalizedMetric_error_lt (d : normalizedDatum g x₀ δ k) :
    metricDerivENormSupOn (controlledCylinder δ) k d.normalizedMetric
      (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ := d.error_lt

def retainedSign (d : normalizedDatum g x₀ δ k) : ℝ := if d.retainedSide then 1 else -1

theorem retainedSign_sq (d : normalizedDatum g x₀ δ k) : d.retainedSign ^ 2 = 1 := by
  unfold retainedSign
  split_ifs <;> norm_num

end normalizedDatum
end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance : Fact
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3) := ⟨by simp⟩

def roundCylinderDatum (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (k : ℕ)
    (side : Bool) : normalizedDatum (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) δ k := by
  let φ : bufferedCylinder δ → S2 × ℝ := Subtype.val
  have hs : ContMDiff IC IC ∞ φ := contMDiff_subtype_val
  have hi : Injective φ := Subtype.val_injective
  have hm : ∀ x, Injective (mfderiv IC IC φ x) := by
    intro x v w hvw
    simpa only [φ, mfderiv_subtype_val, ContinuousLinearMap.id_apply] using! hvw
  have hscalar : metricScalarAt (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) = 1 := by
    rw [metricScalarAt_roundCylinder]
    norm_num
  have hp : 0 < metricScalarAt (roundCylinderMetric (E := E3) (n := 2))
      (spherePoint, 0) := by rw [hscalar]; norm_num
  have hloc := isLocalDiffeomorph_of_injective_mfderiv φ hs hm (by rfl)
  have he : pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (roundCylinderMetric (E := E3) (n := 2))) φ hloc hi =
        referenceMetric δ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, hscalar,
      one_mul, mfderiv_subtype_val]
    rfl
  refine
    { precision_pos := hδ
      precision_lt_one := hδ1
      map := φ
      smooth := hs
      injective := hi
      immersion := hm
      center_eq := rfl
      scalar_pos := hp
      retainedSide := side
      error_lt := ?_ }
  change metricDerivENormSupOn (controlledCylinder δ) k
    (pullbackMetricOfInjectiveLocalDiffeomorph
      (scaleMetric _ hp (roundCylinderMetric (E := E3) (n := 2))) φ hloc hi)
        (referenceMetric δ) (referenceMetric δ) < ENNReal.ofReal δ
  rw [he, metricDerivENormSupOn_self]
  exact ENNReal.ofReal_pos.mpr hδ

theorem roundCylinderDatum_map (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (k : ℕ)
    (side : Bool) (x : bufferedCylinder δ) :
    (roundCylinderDatum δ hδ hδ1 k side).map x = x.val := rfl

theorem roundCylinderDatum_retainedSide (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (k : ℕ) (side : Bool) :
    (roundCylinderDatum δ hδ hδ1 k side).retainedSide = side := rfl

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Fact (Module.finrank ℝ F = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]

structure datumIsometry {g : SmoothRiemannianMetric I M}
    {g' : SmoothRiemannianMetric J N} {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
    (d : normalizedDatum g x₀ δ k) (d' : normalizedDatum g' x₀' δ k) where
  source : Opens M
  target : Opens N
  image_source : ∀ z, d.map z ∈ source
  image_target : ∀ z, d'.map z ∈ target
  equiv : source ≃ₘ⟮I, J⟯ target
  metric_eq : Diffeomorph.pullbackMetricCross (g'.restrictOpen target) equiv =
    g.restrictOpen source
  chart_eq : ∀ z, (equiv ⟨d.map z, image_source z⟩ : N) = d'.map z
  scalar_eq : metricScalarAt g' x₀' = metricScalarAt g x₀
  retainedSide_eq : d'.retainedSide = d.retainedSide

namespace datumIsometry

variable {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

theorem center_mem_source (F : datumIsometry d d') : x₀ ∈ F.source := by
  simpa only [d.center_eq] using F.image_source (cylinderCenter δ d.precision_pos)

theorem center_mem_target (F : datumIsometry d d') : x₀' ∈ F.target := by
  simpa only [d'.center_eq] using F.image_target (cylinderCenter δ d'.precision_pos)

theorem center_eq (F : datumIsometry d d') :
    (F.equiv ⟨x₀, F.center_mem_source⟩ : N) = x₀' := by
  simpa only [d.center_eq, d'.center_eq] using
    F.chart_eq (cylinderCenter δ d.precision_pos)

def refl (d : normalizedDatum g x₀ δ k) : datumIsometry d d where
  source := ⊤
  target := ⊤
  image_source := fun _ => Set.mem_univ _
  image_target := fun _ => Set.mem_univ _
  equiv := Diffeomorph.refl I (⊤ : Opens M) ∞
  metric_eq := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    change (g.restrictOpen ⊤).inner x (mfderiv I I id x v) (mfderiv I I id x w) = _
    rw [mfderiv_id]
    rfl
  chart_eq := fun _ => rfl
  scalar_eq := rfl
  retainedSide_eq := rfl

end datumIsometry
end DifferentialGeometry.Geometry.Neck

namespace DifferentialGeometry.Geometry.Neck

theorem isCompact_controlledCylinder (δ : ℝ) : IsCompact (controlledCylinder δ) := by
  rw [Subtype.isCompact_iff]
  have he : (Subtype.val : bufferedCylinder δ → S2 × ℝ) '' controlledCylinder δ =
      (univ : Set S2) ×ˢ Icc (-δ⁻¹) δ⁻¹ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨mem_univ _, hx⟩
    · intro hq
      have hb : q ∈ bufferedCylinder δ := by
        change -δ⁻¹ - 1 < q.2 ∧ q.2 < δ⁻¹ + 1
        constructor <;> linarith [hq.2.1, hq.2.2]
      exact ⟨⟨q, hb⟩, hq.2, rfl⟩
  rw [he]
  exact isCompact_univ.prod isCompact_Icc

theorem cylinderCenter_mem_controlledCylinder (δ : ℝ) (hδ : 0 < δ) :
    cylinderCenter δ hδ ∈ controlledCylinder δ := by
  change -δ⁻¹ ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ δ⁻¹
  constructor <;> have hi := inv_pos.mpr hδ <;> linarith

end DifferentialGeometry.Geometry.Neck
