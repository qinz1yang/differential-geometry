import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Topology.SphereSeparation.ComplementPair

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

open DifferentialGeometry.Topology.SphereSeparation

variable {E H M A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [TopologicalSpace A]

theorem exists_minimizing_segment_across_open_embedding_sides
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M) (E : A ≃ₜ U)
    {S : Set A} (d : ComplementPair S) (o : M) (a b : A)
    (ha : a ∈ d.left) (hb : b ∈ d.right) {R : ℝ} (hR : 0 ≤ R)
    (hdistA : riemannianEDistOf g o (E a) ≤ ENNReal.ofReal R)
    (hdistB : riemannianEDistOf g o (E b) ≤ ENNReal.ofReal R)
    (hcompact : IsCompact (riemannianClosedBallOf g o (3 * R + 1)))
    (hcapture : riemannianClosedBallOf g o (3 * R) ⊆ U) :
    ∃ gamma : ℝ → M,
      let length := (riemannianEDistOf g (E a) (E b)).toReal
      gamma 0 = E a ∧ gamma length = E b ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma (Icc 0 length) ∧
      (∀ t ∈ Icc 0 length, gamma t ∈ riemannianClosedBallOf g o (3 * R)) ∧
      (∀ t ∈ Icc 0 length, ∀ u ∈ Icc 0 length,
        riemannianEDistOf g (gamma t) (gamma u) = ENNReal.ofReal |t - u|) ∧
      ∃ t ∈ Icc 0 length, gamma t ∈ (fun z => (E z : M)) '' S := by
  obtain ⟨gamma, hstart, hend, hsmooth, hmem, hmin⟩ :=
    exists_distance_parametrized_minimizer_in_closedBall g o (E a) (E b)
      hR hdistA hdistB hcompact
  refine ⟨gamma, hstart, hend, hsmooth, hmem, hmin, ?_⟩
  let length := (riemannianEDistOf g (E a) (E b)).toReal
  have hlength : 0 ≤ length := ENNReal.toReal_nonneg
  let G : ℝ → U := fun t =>
    ⟨gamma (projIcc 0 length hlength t),
      hcapture (hmem _ (projIcc 0 length hlength t).property)⟩
  let lifted : ℝ → A := fun t => E.symm (G t)
  have hGc : Continuous G :=
    ((hsmooth.continuousOn.domRestrict.comp continuous_projIcc).subtype_mk _)
  have hcont : Continuous lifted := E.symm.continuous.comp hGc
  have hround (t : ℝ) (ht : t ∈ Icc 0 length) : (E (lifted t) : M) = gamma t := by
    have hh := congrArg Subtype.val (E.apply_symm_apply (G t))
    change (E (lifted t) : M) = gamma (projIcc 0 length hlength t) at hh
    simpa only [projIcc_of_mem hlength ht] using hh
  have hstartLift : lifted 0 = a := E.injective (Subtype.ext
    ((hround 0 ⟨le_rfl, hlength⟩).trans hstart))
  have hendLift : lifted length = b := E.injective (Subtype.ext
    ((hround length ⟨hlength, le_rfl⟩).trans hend))
  have hcross : ∃ t ∈ Icc 0 length, lifted t ∈ S := by
    by_contra hnone
    have havoid : lifted '' Icc 0 length ⊆ Sᶜ := by
      rintro z ⟨t, ht, rfl⟩ hS
      exact hnone ⟨t, ht, hS⟩
    rcases d.subset_left_or_subset_right
      (isPreconnected_Icc.image lifted hcont.continuousOn) havoid with hl | hr
    · exact disjoint_left.mp d.disjoint
        (hendLift ▸ hl ⟨length, ⟨hlength, le_rfl⟩, rfl⟩) hb
    · exact disjoint_left.mp d.disjoint ha
        (hstartLift ▸ hr ⟨0, ⟨le_rfl, hlength⟩, rfl⟩)
  obtain ⟨t, ht, htS⟩ := hcross
  exact ⟨t, ht, lifted t, htS, hround t ht⟩

end DifferentialGeometry.Geometry.Riemannian
