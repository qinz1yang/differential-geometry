import DifferentialGeometry.Topology.Engulfing.Newman.Step.NewmanLocalStep
import DifferentialGeometry.Topology.Engulfing.Newman.Data.NewmanLocalData

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology

variable {Z M : Type*} [TopologicalSpace Z] [PseudoMetricSpace M]

theorem exists_protected_image_tolerance
    (f : C(Z, M)) {A : Set Z} (hA : IsCompact A)
    {V S : Set M} (hV : IsOpen V) (hS : IsClosed S) (hSV : S ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : Z → M,
      (∀ x ∈ A, dist (g x) (f x) < δ) →
      EqOn g f (A ∩ f ⁻¹' V) → (g '' A) ∩ S = (f '' A) ∩ S := by
  have hcompact : IsCompact (A \ f ⁻¹' V) :=
    hA.inter_right (hV.preimage f.continuous).isClosed_compl
  have havoid : Disjoint (f '' (A \ f ⁻¹' V)) S := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hy
    exact hx.2 (hSV hy)
  obtain ⟨δ, hδ, hcontrol⟩ := exists_perturbation_control f hcompact isOpen_univ hS
    (subset_univ _) havoid
  refine ⟨δ, hδ, fun g hnear hfix => ?_⟩
  exact image_inter_eq_of_eqOn_and_avoid hfix havoid
    (hcontrol g (fun x hx => hnear x hx.1)).2

omit [TopologicalSpace Z] [PseudoMetricSpace M] in
theorem image_inter_subset_of_protected_stability
    {f g : Z → M} {A : Set Z} {S R : Set M}
    (hstable : (g '' A) ∩ S = (f '' A) ∩ S)
    (hbound : (f '' A) ∩ S ⊆ R) : (g '' A) ∩ S ⊆ R :=
  hstable.subset.trans hbound

end DifferentialGeometry.Topology.Engulfing
