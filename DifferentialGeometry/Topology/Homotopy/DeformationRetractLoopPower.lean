import DifferentialGeometry.Topology.FundamentalGroup.LoopPower
import DifferentialGeometry.Topology.Homotopy.DeformationRetractPath

namespace DifferentialGeometry.Topology.Homotopy

universe u

open ContinuousMap
open unitInterval

namespace StrongDeformationRetract

variable {X : Type u} [TopologicalSpace X] {A : Set X}

noncomputable def retractLoopSubtype (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) : Path (⟨x, hx⟩ : A) ⟨x, hx⟩ where
  toFun s := r.retraction (ℓ s)
  continuous_toFun := (map_continuous r.retraction).comp (map_continuous ℓ)
  source' := by
    have h0 : ℓ 0 = x := ℓ.source
    change r.retraction (ℓ 0) = _
    rw [h0]
    exact Subtype.ext (r.retraction_eq hx)
  target' := by
    have h1 : ℓ 1 = x := ℓ.target
    change r.retraction (ℓ 1) = _
    rw [h1]
    exact Subtype.ext (r.retraction_eq hx)

theorem map_retractLoopSubtype (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (ℓ : Path x x) :
    (r.retractLoopSubtype hx ℓ).map continuous_subtype_val = r.retractLoop hx ℓ := rfl

end StrongDeformationRetract

theorem exists_homotopic_loopZPow_of_strongDeformationRetract {X : Type u} [TopologicalSpace X]
    {A : Set X} (r : StrongDeformationRetract A) {x : X} (hx : x ∈ A)
    (p : Path (⟨x, hx⟩ : A) ⟨x, hx⟩)
    (hgen : ∀ ℓ : Path (⟨x, hx⟩ : A) ⟨x, hx⟩, ∃ k : ℤ, ℓ.Homotopic (loopZPow p k))
    (m : Path x x) :
    ∃ k : ℤ, m.Homotopic (loopZPow (p.map continuous_subtype_val) k) := by
  obtain ⟨k, hk⟩ := hgen (r.retractLoopSubtype hx m)
  have hmap := hk.map (⟨((↑) : A → X), continuous_subtype_val⟩ : C(A, X))
  rw [loopZPow_map] at hmap
  exact ⟨k, (r.homotopic_retractLoop hx m).trans hmap⟩

end DifferentialGeometry.Topology.Homotopy
