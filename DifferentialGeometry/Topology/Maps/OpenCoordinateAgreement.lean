import DifferentialGeometry.Topology.Compactness.EventualLocality
import Mathlib.Topology.Sets.Opens

section

noncomputable section
open Set Filter
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E Q α : Type*} [TopologicalSpace E] [LocallyCompactSpace E]
  [TopologicalSpace Q] {M : α → Type*} {l : Filter α}

theorem eventually_mem_of_compact_agreement_in_open_coordinates
    (U : TopologicalSpace.Opens E) (inc : U → Q)
    (hinj : Function.Injective inc) (hinc : Continuous inc)
    (V : Set Q) (hV : IsOpen V)
    (W : U → Set E) (hW : ∀ a, IsOpen (W a)) (hcenter : ∀ a : U, (a : E) ∈ W a)
    (f : U → ∀ k, E → M k) (b : ∀ k, M k) (F : ∀ k, Q → M k)
    (T : ∀ k, Set (M k))
    (hmem : ∀ a (K : Set E), IsCompact K → K ⊆ W a →
      ∀ᶠ k in l, MapsTo (f a k) K (T k))
    (hagree : ∀ a (L : Set Q), IsCompact L →
      L ⊆ V ∩ (inc '' (Subtype.val ⁻¹' W a)) →
      ∀ᶠ k in l, EqOn (F k)
        (Function.extend inc (fun z : U => f a k z) (fun _ => b k)) L)
    (K : Set E) (hK : IsCompact K) (hKD : K ⊆ Subtype.val '' (inc ⁻¹' V)) :
    ∀ᶠ k in l, ∀ (z : E) (hz : z ∈ U), z ∈ K → F k (inc ⟨z, hz⟩) ∈ T k := by
  classical
  have hD : IsOpen (Subtype.val '' (inc ⁻¹' V)) :=
    U.isOpen.isOpenMap_subtype_val _ (hV.preimage hinc)
  have htail : ∀ᶠ k in l, ∀ z ∈ K, ∀ hz : z ∈ U, F k (inc ⟨z, hz⟩) ∈ T k := by
    apply hK.eventually_forall_of_locally_eventually_on_compacts
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hKD hx
    refine ⟨(Subtype.val '' (inc ⁻¹' V)) ∩ W a,
      (hD.inter (hW a)).mem_nhds ⟨⟨a, ha, rfl⟩, hcenter a⟩, ?_⟩
    intro L hLD hL
    have hLU : L ⊆ (U : Set E) := by
      intro z hz
      obtain ⟨y, _, hy⟩ := (hLD hz).1
      exact hy ▸ y.property
    have hLsub : IsCompact ((Subtype.val : U → E) ⁻¹' L) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hL (by simpa using hLU)
    have himage : inc '' ((Subtype.val : U → E) ⁻¹' L) ⊆
        V ∩ (inc '' (Subtype.val ⁻¹' W a)) := by
      rintro q ⟨z, hz, rfl⟩
      obtain ⟨y, hy, heq⟩ := (hLD hz).1
      have hyz : y = z := Subtype.ext heq
      exact ⟨hyz ▸ hy, z, (hLD hz).2, rfl⟩
    filter_upwards [hagree a _ (hLsub.image hinc) himage,
      hmem a L hL (fun z hz => (hLD hz).2)] with k hk hm z hz hzU
    rw [hk ⟨⟨z, hzU⟩, hz, rfl⟩, hinj.extend_apply]
    exact hm hz
  exact htail.mono fun k hk z hz hzK => hk z hzK hz

end DifferentialGeometry.Topology

end

end
