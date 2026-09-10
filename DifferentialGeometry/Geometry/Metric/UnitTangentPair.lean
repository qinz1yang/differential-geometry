import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry

namespace DifferentialGeometry.Geometry.Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


abbrev SameBaseUnitTangentPair (g : SmoothRiemannianMetric I M) :=
  {p : MetricUnitTangent g × MetricUnitTangent g //
    MetricUnitTangent.base p.1 = MetricUnitTangent.base p.2}

namespace SameBaseUnitTangentPair

variable (g : SmoothRiemannianMetric I M)


def base (p : SameBaseUnitTangentPair g) : M := MetricUnitTangent.base p.val.1


def first (p : SameBaseUnitTangentPair g) : TangentSpace I (base g p) :=
  MetricUnitTangent.vec p.val.1


def second (p : SameBaseUnitTangentPair g) : TangentSpace I (base g p) :=
  (MetricUnitTangent.vec p.val.2 : E)

omit [FiniteDimensional ℝ E] in
theorem continuous_base : Continuous (base g) :=
  (FiberBundle.continuous_proj E (TangentSpace I)).comp
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))

omit [FiniteDimensional ℝ E] in
theorem continuous_first : Continuous (fun p : SameBaseUnitTangentPair g =>
    (⟨base g p, first g p⟩ : TangentBundle I M)) :=
  continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)

omit [FiniteDimensional ℝ E] in
theorem continuous_second : Continuous (fun p : SameBaseUnitTangentPair g =>
    (⟨base g p, second g p⟩ : TangentBundle I M)) := by
  have h := continuous_subtype_val.comp (continuous_snd.comp
    (continuous_subtype_val : Continuous (Subtype.val : SameBaseUnitTangentPair g → _)))
  apply h.congr
  intro p
  apply TotalSpace.ext
  · exact p.property.symm
  · rfl

omit [FiniteDimensional ℝ E] in
theorem unit (p : SameBaseUnitTangentPair g) :
    g.inner (base g p) (first g p) (first g p) = 1 ∧
      g.inner (base g p) (second g p) (second g p) = 1 := by
  refine ⟨p.val.1.property, ?_⟩
  have h := p.val.2.property
  change g.inner (MetricUnitTangent.base p.val.2)
    (MetricUnitTangent.vec p.val.2) (MetricUnitTangent.vec p.val.2) = 1 at h
  unfold base second
  erw [p.property]
  exact h

theorem compactSpace [T2Space M] [CompactSpace M] : CompactSpace (SameBaseUnitTangentPair g) := by
  let : CompactSpace (MetricUnitTangent g) :=
    isCompact_univ_iff.mp (metricUnit_compact g)
  have hb : Continuous (MetricUnitTangent.base (g := g)) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).comp continuous_subtype_val
  exact isCompact_iff_compactSpace.mp
    (isClosed_eq (hb.comp continuous_fst) (hb.comp continuous_snd)).isCompact

omit [FiniteDimensional ℝ E] in
theorem continuous_inner : Continuous (fun p : SameBaseUnitTangentPair g =>
    g.inner (base g p) (first g p) (second g p)) := by
  have h := Continuous.clm_bundle_apply₂ (𝕜 := ℝ) (E₃ := fun _ : M => ℝ) (F₁ := E) (F₂ := E) (F₃ := ℝ)
    (g.contMDiff.continuous.comp (continuous_base g)) (continuous_first g) (continuous_second g)
  exact (continuous_snd.comp (Bundle.Trivial.homeomorphProd M ℝ).continuous).comp h

end SameBaseUnitTangentPair

abbrev OrthonormalTangentPair (g : SmoothRiemannianMetric I M) :=
  {p : SameBaseUnitTangentPair g //
    g.inner (SameBaseUnitTangentPair.base g p)
      (SameBaseUnitTangentPair.first g p) (SameBaseUnitTangentPair.second g p) = 0}


theorem orthonormalTangentPair_compactSpace [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) : CompactSpace (OrthonormalTangentPair g) := by
  let := SameBaseUnitTangentPair.compactSpace g
  exact isCompact_iff_compactSpace.mp
    (isClosed_eq (SameBaseUnitTangentPair.continuous_inner g) continuous_const).isCompact

end DifferentialGeometry.Geometry.Riemannian
