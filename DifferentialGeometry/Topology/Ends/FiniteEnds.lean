import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false

open Set Function

namespace DifferentialGeometry.Geometry.Topology

def HasAtLeastEnds (X : Type*) [TopologicalSpace X] (k : ℕ) : Prop :=
  ∃ K : Set X, IsCompact K ∧ ∃ x : Fin k → X,
    (∀ i, x i ∉ K) ∧ Injective (fun i => connectedComponentIn Kᶜ (x i)) ∧
      ∀ i, ¬ IsCompact (closure (connectedComponentIn Kᶜ (x i)))


def HasExactlyEnds (X : Type*) [TopologicalSpace X] (k : ℕ) : Prop :=
  HasAtLeastEnds X k ∧ ¬ HasAtLeastEnds X (k + 1)


def HasAtMostTwoEnds (X : Type*) [TopologicalSpace X] : Prop :=
  ¬ HasAtLeastEnds X 3

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]


theorem HasAtLeastEnds.mono {k l : ℕ} (h : HasAtLeastEnds X l) (hkl : k ≤ l) :
    HasAtLeastEnds X k := by
  obtain ⟨K, hK, x, hx, hinj, hnc⟩ := h
  exact ⟨K, hK, x ∘ Fin.castLE hkl, fun i => hx (Fin.castLE hkl i),
    hinj.comp (Fin.castLE_injective hkl), fun i => hnc (Fin.castLE hkl i)⟩

private theorem hasAtLeastEnds_map (e : X ≃ₜ Y) {k : ℕ} (h : HasAtLeastEnds X k) :
    HasAtLeastEnds Y k := by
  obtain ⟨K, hK, x, hx, hinj, hnc⟩ := h
  have hc (i : Fin k) : e '' connectedComponentIn Kᶜ (x i) =
      connectedComponentIn (e '' K)ᶜ (e (x i)) := by
    simpa only [image_compl_eq e.bijective] using
      e.image_connectedComponentIn (s := Kᶜ) (x := x i) (hx i)
  refine ⟨e '' K, hK.image e.continuous, e ∘ x, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨a, ha, heq⟩ := hi
    exact hx i (e.injective heq ▸ ha)
  · intro i j hij
    apply hinj
    apply (Set.image_injective.mpr e.injective)
    rw [hc i, hc j]
    exact hij
  · intro i hi
    apply hnc i
    apply e.isCompact_image.mp
    rw [e.image_closure, hc i]
    exact hi

theorem hasAtLeastEnds_homeomorph_iff (e : X ≃ₜ Y) (k : ℕ) :
    HasAtLeastEnds X k ↔ HasAtLeastEnds Y k :=
  ⟨hasAtLeastEnds_map e, hasAtLeastEnds_map e.symm⟩


theorem hasExactlyEnds_homeomorph_iff (e : X ≃ₜ Y) (k : ℕ) :
    HasExactlyEnds X k ↔ HasExactlyEnds Y k := by
  simp only [HasExactlyEnds, hasAtLeastEnds_homeomorph_iff e]


theorem hasAtMostTwoEnds_homeomorph_iff (e : X ≃ₜ Y) :
    HasAtMostTwoEnds X ↔ HasAtMostTwoEnds Y := by
  simp only [HasAtMostTwoEnds, hasAtLeastEnds_homeomorph_iff e]


theorem not_hasAtLeastEnds_of_compact [CompactSpace X] {k : ℕ} (hk : 0 < k) :
    ¬ HasAtLeastEnds X k := by
  rintro ⟨K, _, x, _, _, hnc⟩
  exact hnc ⟨0, hk⟩ isClosed_closure.isCompact

theorem hasAtMostTwoEnds_of_not_hasAtLeastEnds_two (h : ¬ HasAtLeastEnds X 2) :
    HasAtMostTwoEnds X := fun hthree => h (hthree.mono (by decide))

end DifferentialGeometry.Geometry.Topology
