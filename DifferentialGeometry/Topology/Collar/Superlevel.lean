import DifferentialGeometry.Topology.Collar.Rescaling
import DifferentialGeometry.Topology.Order.IntervalPush

set_option autoImplicit false
noncomputable section
open Set Function Topology
namespace Poincare.Topology.Collar
variable {B X : Type*} [TopologicalSpace B] [TopologicalSpace X] {ε a : ℝ}


theorem range_rescale_intervalPush_eq_superlevel
    (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c) (haε : 2 * a ≤ ε)
    {r : X → ℝ} (hheight : ∀ q, r (c q) = (q.2 : ℝ))
    (houtside : ∀ x ∉ range c, a ≤ r x) :
    range (rescale c hc (intervalPush a haε)) = {x | a ≤ r x} := by
  rw [range_rescale c hc _ (range_intervalPush haε)]
  ext x
  constructor
  · rintro (hx | ⟨q,hq,rfl⟩)
    · exact houtside x hx
    · change a ≤ r (c q)
      rw [hheight]
      exact hq
  · intro hx
    by_cases hxc : x ∈ range c
    · obtain ⟨q,rfl⟩ := hxc
      have hq : a ≤ (q.2 : ℝ) := (hheight q) ▸ (show a ≤ r (c q) from hx)
      exact Or.inr ⟨q,hq,rfl⟩
    · exact Or.inl hxc

variable [CompactSpace B] [T2Space X]


theorem exists_homeomorph_superlevel_of_collar
    (c : B × Icc (0 : ℝ) ε → X) (hc : IsEmbedding c) {δ : ℝ}
    (haδ : 2 * a < δ) (hδε : δ ≤ ε)
    (hopen : IsOpen (c '' {q | (q.2 : ℝ) < δ}))
    {r : X → ℝ} (hheight : ∀ q, r (c q) = (q.2 : ℝ))
    (houtside : ∀ x ∉ range c, a ≤ r x) :
    ∃ h : X ≃ₜ {x | a ≤ r x}, ∀ x,
      (h x : X) = rescale c hc (intervalPush a (haδ.le.trans hδε)) x := by
  let σ := intervalPush a (haδ.le.trans hδε)
  have hj : IsClosedEmbedding (rescale c hc σ) := isClosedEmbedding_rescale c hc σ
    (strictMono_intervalPush a _).injective haδ hopen (intervalPush_fixed a _)
  have hrange : range (rescale c hc σ) = {x | a ≤ r x} :=
    range_rescale_intervalPush_eq_superlevel c hc _ hheight houtside
  exact ⟨hj.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange),fun _ => rfl⟩

end Poincare.Topology.Collar
