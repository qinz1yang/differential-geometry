import DifferentialGeometry.Topology.Engulfing.Local.Charts.LocalOptimalApproximation

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology

variable {E M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
theorem exists_chart_source_neighborhood
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (f : C(K.space, M))
    (e : OpenPartialHomeomorph M F) (c : F) {r R : ℝ}
    (hrR : r < R) (hR : closedBall c R ⊆ e.target) :
    ∃ A U : Set E, IsCompact A ∧ A ⊆ K.space ∧ IsOpen U ∧ A ⊆ U ∧
      (∀ x : K.space, x.val ∈ A ↔ f x ∈ e.symm '' closedBall c r) ∧
      (∀ x : K.space, x.val ∈ U ↔ f x ∈ e.source ∧ e (f x) ∈ ball c R) := by
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (isCompact_space_of_finite_faces K hK)
  have hr : closedBall c r ⊆ e.target := (closedBall_subset_closedBall hrR.le).trans hR
  have hcompact : IsCompact (e.symm '' closedBall c r) :=
    (isCompact_closedBall c r).image_of_continuousOn (e.continuousOn_symm.mono hr)
  let S : Set K.space := f ⁻¹' (e.symm '' closedBall c r)
  let V : Set K.space := f ⁻¹' (e.source ∩ e ⁻¹' ball c R)
  have hS : IsCompact S := (hcompact.isClosed.preimage f.continuous).isCompact
  have hV : IsOpen V := (e.isOpen_inter_preimage isOpen_ball).preimage f.continuous
  obtain ⟨U, hU, hUV⟩ := isOpen_induced_iff.mp hV
  let A : Set E := Subtype.val '' S
  have hAmem (x : K.space) : x.val ∈ A ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, he⟩
      exact (Subtype.ext he : y = x) ▸ hy
    · exact fun hx => ⟨x, hx, rfl⟩
  refine ⟨A, U, hS.image continuous_subtype_val, ?_, hU, ?_, hAmem, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact x.property
  · rintro _ ⟨x, hx, rfl⟩
    have hxV : x ∈ V := by
      obtain ⟨y, hy, he⟩ := hx
      refine ⟨he ▸ e.map_target (hr hy), ?_⟩
      change e (f x) ∈ ball c R
      rw [← he, e.right_inv (hr hy)]
      exact closedBall_subset_ball hrR hy
    exact show x ∈ Subtype.val ⁻¹' U from hUV.symm.subset hxV
  · intro x
    exact Set.ext_iff.mp hUV x

end DifferentialGeometry.Topology.Engulfing
