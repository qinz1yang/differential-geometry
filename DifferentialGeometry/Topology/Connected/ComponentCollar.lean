import DifferentialGeometry.Topology.Connected.RegularClosedComponents
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.Topology

theorem connectedComponentIn_interval_side
    {X Z : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {K : Set X} {x : X} {r : ℝ} (f : Z → ℝ → X)
    (hcontinuous : ∀ z, ContinuousOn (f z) (Ioo (-r) r))
    (hside : ∀ z, ∀ t ∈ Ioo (-r) r, f z t ∈ K ↔ t ≤ 0)
    (hinterior : ∀ z, ∀ t ∈ Ioo (-r) r, f z t ∈ interior K ↔ t < 0)
    (hzero : ∀ z, f z 0 ∈ connectedComponentIn K x) :
    (∀ z, ∀ t ∈ Ioo (-r) r,
      f z t ∈ connectedComponentIn K x ↔ t ≤ 0) ∧
    ∀ z, ∀ t ∈ Ioo (-r) r,
      f z t ∈ interior (connectedComponentIn K x) ↔ t < 0 := by
  have hmem : ∀ z, ∀ t ∈ Ioo (-r) r,
      f z t ∈ connectedComponentIn K x ↔ t ≤ 0 := by
    intro z t ht
    constructor
    · intro h
      exact (hside z t ht).mp (connectedComponentIn_subset K x h)
    · intro ht0
      let γ : ℝ → X := f z
      have hr : 0 < r := neg_lt_zero.mp (ht.1.trans_le ht0)
      have hI : Icc t 0 ⊆ Ioo (-r) r := by
        intro s hs
        exact ⟨ht.1.trans_le hs.1, hs.2.trans_lt hr⟩
      have hγ : ContinuousOn γ (Icc t 0) := (hcontinuous z).mono hI
      have hsub : γ '' Icc t 0 ⊆ K := by
        rintro w ⟨s, hs, rfl⟩
        exact (hside z s (hI hs)).mpr hs.2
      have hzero' : γ 0 ∈ connectedComponentIn K x := by
        simpa only [γ] using hzero z
      rw [connectedComponentIn_eq hzero']
      exact (isPreconnected_Icc.image γ hγ).subset_connectedComponentIn
        (mem_image_of_mem γ ⟨ht0, le_rfl⟩) hsub (mem_image_of_mem γ ⟨le_rfl, ht0⟩)
  refine ⟨hmem, ?_⟩
  intro z t ht
  constructor
  · intro h
    exact (hinterior z t ht).mp (interior_mono (connectedComponentIn_subset K x) h)
  · intro ht0
    apply (mem_interior_iff_notMem_frontier ((hmem z t ht).mpr ht0.le)).mpr
    intro hf
    exact (frontier_connectedComponentIn_subset K x hf).2
      ((hinterior z t ht).mpr ht0)

end DifferentialGeometry.Topology
