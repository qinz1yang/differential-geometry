import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BicollarComplementComponents
import Mathlib.Topology.Algebra.Group.Basic

set_option autoImplicit false

noncomputable section

open Set Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions


def bicollarLowerSide {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ) : Set M :=
  connectedComponentIn (range (fun y => φ (y, c)))ᶜ (φ (a, c - 1))


def bicollarUpperSide {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ) : Set M :=
  connectedComponentIn (range (fun y => φ (y, c)))ᶜ (φ (a, c + 1))

theorem bicollar_slice_components
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ) (a : A) (c : ℝ) :
    IsConnected (bicollarLowerSide φ a c) ∧ IsConnected (bicollarUpperSide φ a c) ∧
      IsOpen (bicollarLowerSide φ a c) ∧ IsOpen (bicollarUpperSide φ a c) ∧
      Disjoint (bicollarLowerSide φ a c) (bicollarUpperSide φ a c) ∧
      bicollarLowerSide φ a c ∪ bicollarUpperSide φ a c =
        (range (fun y => φ (y, c)))ᶜ ∧
      frontier (bicollarLowerSide φ a c) = range (fun y => φ (y, c)) ∧
      frontier (bicollarUpperSide φ a c) = range (fun y => φ (y, c)) ∧
      closure (bicollarLowerSide φ a c) =
        bicollarLowerSide φ a c ∪ range (fun y => φ (y, c)) ∧
      closure (bicollarUpperSide φ a c) =
        bicollarUpperSide φ a c ∪ range (fun y => φ (y, c)) ∧
      (∀ y z, z < c → φ (y, z) ∈ bicollarLowerSide φ a c) ∧
      (∀ y z, c < z → φ (y, z) ∈ bicollarUpperSide φ a c) := by
  let τ : A × ℝ ≃ₜ A × ℝ := (Homeomorph.refl A).prodCongr (Homeomorph.addRight c)
  let ψ : A × ℝ → M := fun p => φ (p.1, p.2 + c)
  have hψ : IsOpenEmbedding ψ := hφ.comp τ.isOpenEmbedding
  obtain ⟨B, E, hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hcomponents, hneg, hpos⟩ := bicollar_complement_components ψ hψ
  have hcenter : range (fun y => ψ (y, 0)) = range (fun y => φ (y, c)) := by
    simp only [ψ, zero_add]
  rw [hcenter] at hcover hBfr hEfr hBcl hEcl hcomponents
  have hnegative (y : A) (z : ℝ) (hz : z < c) : φ (y, z) ∈ B := by
    have h := hneg y (z - c) (sub_neg.mpr hz)
    simpa only [ψ, sub_add_cancel] using h
  have hpositive (y : A) (z : ℝ) (hz : c < z) : φ (y, z) ∈ E := by
    have h := hpos y (z - c) (sub_pos.mpr hz)
    simpa only [ψ, sub_add_cancel] using h
  have hBlo : φ (a, c - 1) ∈ B := hnegative a (c - 1) (by linarith)
  have hEhi : φ (a, c + 1) ∈ E := hpositive a (c + 1) (by linarith)
  have hloAvoid : φ (a, c - 1) ∈ (range (fun y => φ (y, c)))ᶜ := by
    rw [← hcover]
    exact Or.inl hBlo
  have hhiAvoid : φ (a, c + 1) ∈ (range (fun y => φ (y, c)))ᶜ := by
    rw [← hcover]
    exact Or.inr hEhi
  have hlower : bicollarLowerSide φ a c = B := by
    rcases hcomponents _ hloAvoid with hcomp | hcomp
    · exact hcomp
    · have hmem := mem_connectedComponentIn hloAvoid
      rw [hcomp] at hmem
      exact False.elim (Set.disjoint_left.mp hBE hBlo hmem)
  have hupper : bicollarUpperSide φ a c = E := by
    rcases hcomponents _ hhiAvoid with hcomp | hcomp
    · have hmem := mem_connectedComponentIn hhiAvoid
      rw [hcomp] at hmem
      exact False.elim (Set.disjoint_left.mp hBE hmem hEhi)
    · exact hcomp
  rw [hlower, hupper]
  exact ⟨hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hnegative, hpositive⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
