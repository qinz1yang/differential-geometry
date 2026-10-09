import DifferentialGeometry.Geometry.Neck.ScalarCutCore
import DifferentialGeometry.Topology.RelativeOpenInterior
import DifferentialGeometry.Topology.Connected.CoverBySides
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

set_option autoImplicit false
noncomputable section

open Set Function TopologicalSpace Manifold
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.ThreeManifold.Surgery

variable {M : Type*} [TopologicalSpace M] {ι : Type*} {δ : ι → ℝ}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

def scalarSublevelComponents
    (U : Opens M) (g : SmoothRiemannianMetric I U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (K : ℝ) :
    Set (ConnectedComponents (cutCore f)) :=
  {c | ∃ x : U, metricScalarAt g x ≤ K ∧
    ∃ hx : x.val ∈ cutCore f, ConnectedComponents.mk (⟨x.val, hx⟩ : cutCore f) = c}

omit [Fact (Module.finrank ℝ E = 3)] [I.Boundaryless] [T2Space M] in
theorem retainedCore_component_meets_scalar_sublevel_of_image_subset
    (U : Opens M) (g : SmoothRiemannianMetric I U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (K : ℝ)
    {S : Set M} (R : Set S) (hS : cutCore f ⊆ S)
    (hR : (Subtype.val : S → M) '' R ⊆ (Subtype.val : cutCore f → M) ''
      retainedCore f (scalarSublevelComponents U g f K)) :
    ∀ c : ConnectedComponents S,
      (∃ p : S, ConnectedComponents.mk p = c ∧ p ∈ R) →
      ∃ x : U, ∃ hx : x.val ∈ S,
        ConnectedComponents.mk ⟨x.val, hx⟩ = c ∧ metricScalarAt g x ≤ K := by
  intro c ⟨p, hpc, hp⟩
  obtain ⟨q, hq, hqp⟩ := hR ⟨p, hp, rfl⟩
  obtain ⟨x, hxscalar, hxcut, hxcomponent⟩ := hq
  refine ⟨x, hS hxcut, ?_, hxscalar⟩
  have heq := congrArg (continuous_inclusion hS).connectedComponentsMap hxcomponent
  change ConnectedComponents.mk (Set.inclusion hS ⟨x.val, hxcut⟩) =
    ConnectedComponents.mk (Set.inclusion hS q) at heq
  have hqp' : Set.inclusion hS q = p := Subtype.ext hqp
  rw [hqp'] at heq
  exact heq.trans hpc


theorem scalarSublevelComponents_protected [Finite ι]
    (U : Opens M) (g : SmoothRiemannianMetric I U)
    (x₀ : ι → U) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum g (x₀ i) (δ i) (order i))
    (horder : ∀ i, 2 ≤ order i) (hδ : ∀ i, δ i ≤ 1 / 2)
    (hdisj : Pairwise fun i j => Disjoint (range (neckAmbientMap U (d i)))
      (range (neckAmbientMap U (d j))))
    (K : ℝ) (hhigh : ∀ i, K < (1 - 4323 * δ i) * metricScalarAt g (x₀ i)) :
    let f := fun i => neckAmbientMap U (d i)
    let R := scalarSublevelComponents U g f K
    (∀ x : U, metricScalarAt g x ≤ K →
      x.val ∈ interior ((Subtype.val : cutCore f → M) '' retainedCore f R)) ∧
    (∀ c : ConnectedComponents (cutCore f),
      (∃ x : cutCore f, ConnectedComponents.mk x = c ∧ x ∈ retainedCore f R) →
      ∃ x : U, metricScalarAt g x ≤ K ∧
        ∃ hx : x.val ∈ cutCore f, ConnectedComponents.mk (⟨x.val, hx⟩ : cutCore f) = c) := by
  intro f R
  let : LocallyPathConnectedSpace M :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  have hopen := (isClopen_retained_discardedCore (fun i => (d i).precision_pos) f
    (fun i => isOpenEmbedding_neckAmbientMap U (d i)) hdisj R).1.isOpen
  constructor
  · intro x hx
    have hint := scalar_sublevel_mem_interior_cutCore U g x₀ order d horder hδ K hhigh x hx
    let p : cutCore f := ⟨x.val, interior_subset hint⟩
    have hmem : p ∈ retainedCore f R := ⟨x, hx, p.property, rfl⟩
    exact DifferentialGeometry.Topology.mem_interior_image_val_of_isOpen hopen hmem hint
  · intro c hc
    obtain ⟨p, hp, hr⟩ := hc
    change ConnectedComponents.mk p ∈ R at hr
    rw [hp] at hr
    exact hr


theorem scalarSublevelComponents_protected_of_common_radius [Finite ι]
    (U : Opens M) (g : SmoothRiemannianMetric I U)
    (x₀ : ι → U) (order : ι → ℕ)
    (d : ∀ i, normalizedDatum g (x₀ i) (δ i) (order i))
    (horder : ∀ i, 2 ≤ order i) (hδ : ∀ i, δ i ≤ 1 / 8646)
    (hdisj : Pairwise fun i j => Disjoint (range (neckAmbientMap U (d i)))
      (range (neckAmbientMap U (d j))))
    (h ρ : ℝ) (hh : 0 < h) (hρ : 0 < ρ) (hhρ : 2 * h ≤ ρ)
    (hscale : ∀ i, metricScalarAt g (x₀ i) = (h ^ 2)⁻¹) :
    let f := fun i => neckAmbientMap U (d i)
    let R := scalarSublevelComponents U g f (ρ ^ 2)⁻¹
    (∀ x : U, metricScalarAt g x ≤ (ρ ^ 2)⁻¹ →
      x.val ∈ interior ((Subtype.val : cutCore f → M) '' retainedCore f R)) ∧
    (∀ c : ConnectedComponents (cutCore f),
      (∃ x : cutCore f, ConnectedComponents.mk x = c ∧ x ∈ retainedCore f R) →
      ∃ x : U, metricScalarAt g x ≤ (ρ ^ 2)⁻¹ ∧
        ∃ hx : x.val ∈ cutCore f, ConnectedComponents.mk (⟨x.val, hx⟩ : cutCore f) = c) := by
  apply scalarSublevelComponents_protected U g x₀ order d horder
    (fun i => (hδ i).trans (by norm_num)) hdisj (ρ ^ 2)⁻¹
  intro i
  rw [hscale i]
  have hsq : 2 * h ^ 2 < ρ ^ 2 := by nlinarith [sq_pos_of_pos hh]
  have hi : (ρ ^ 2)⁻¹ < (2 * h ^ 2)⁻¹ :=
    (inv_lt_inv₀ (sq_pos_of_pos hρ) (by positivity)).mpr hsq
  have heq : (2 * h ^ 2)⁻¹ = (1 / 2 : ℝ) * (h ^ 2)⁻¹ := by
    rw [mul_inv_rev]
    ring
  rw [heq] at hi
  refine hi.trans_le (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (sq_nonneg h)))
  linarith [hδ i]

omit [Fact (Module.finrank ℝ E = 3)] [I.Boundaryless] [T2Space M] in
theorem scalarSublevelComponents_retained_subset_of_frontier_removed
    (U : Opens M) (g : SmoothRiemannianMetric I U)
    (f : ∀ i, bufferedCylinder (δ i) → M) (a : ℝ) (K : Set M)
    (hlow : ∀ x : U, metricScalarAt g x ≤ a → x.val ∈ K)
    (hfront : frontier K ⊆ ⋃ i, removedSlab (f i)) :
    (Subtype.val : cutCore f → M) '' retainedCore f (scalarSublevelComponents U g f a) ⊆
      interior K := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hqc, hcomp⟩ := hp
  let C : Set M := (Subtype.val : cutCore f → M) '' connectedComponent p
  have hC : IsPreconnected C :=
    isPreconnected_connectedComponent.image Subtype.val continuous_subtype_val.continuousOn
  have hqcomp : (⟨q.val, hqc⟩ : cutCore f) ∈ connectedComponent p :=
    ConnectedComponents.coe_eq_coe'.mp hcomp
  have hmeet : (C ∩ K).Nonempty := ⟨q.val, ⟨⟨q.val, hqc⟩, hqcomp, rfl⟩, hlow q hq⟩
  have hdisj : Disjoint C (frontier K) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨r, hr, rfl⟩ hy
    exact r.property (hfront hy)
  exact DifferentialGeometry.Topology.isPreconnected_subset_interior_of_meets_of_disjoint_frontier
    hC hmeet hdisj ⟨p, mem_connectedComponent, rfl⟩

end DifferentialGeometry.Topology.ThreeManifold.Surgery
