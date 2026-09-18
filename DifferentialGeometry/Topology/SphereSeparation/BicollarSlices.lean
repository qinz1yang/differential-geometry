import DifferentialGeometry.Topology.SphereSeparation.BicollarComponents
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

private theorem bicollar_slice_components_of_sides
    {A M : Type*} [TopologicalSpace M]
    (φ : A × ℝ → M) (a : A) (c : ℝ)
    (B E : Set M)
    (hB : IsConnected B) (hE : IsConnected E) (hBop : IsOpen B) (hEop : IsOpen E)
    (hBE : Disjoint B E) (hcover : B ∪ E = (range (fun y => φ (y, c)))ᶜ)
    (hBfr : frontier B = range (fun y => φ (y, c)))
    (hEfr : frontier E = range (fun y => φ (y, c)))
    (hBcl : closure B = B ∪ range (fun y => φ (y, c)))
    (hEcl : closure E = E ∪ range (fun y => φ (y, c)))
    (hcomponents : ∀ x ∈ (range (fun y => φ (y, c)))ᶜ,
      connectedComponentIn (range (fun y => φ (y, c)))ᶜ x = B ∨
      connectedComponentIn (range (fun y => φ (y, c)))ᶜ x = E)
    (hnegative : ∀ y z, z < c → φ (y, z) ∈ B)
    (hpositive : ∀ y z, c < z → φ (y, z) ∈ E) :
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
  exact bicollar_slice_components_of_sides φ a c B E hB hE hBop hEop hBE hcover
    hBfr hEfr hBcl hEcl hcomponents hnegative hpositive

theorem bicollar_slice_components_of_homotopic_disjoint
    {A M : Type*} [TopologicalSpace A] [T2Space A] [CompactSpace A] [ConnectedSpace A]
    [TopologicalSpace M] [T2Space M] [ConnectedSpace M] [LocallyConnectedSpace M]
    (φ : A × ℝ → M) (hφ : IsOpenEmbedding φ)
    (r : C(M, M)) (hr : ContinuousMap.Homotopic r (ContinuousMap.id M))
    (hdisjoint : Disjoint (range r) (range (fun y => φ (y, 0)))) (a : A) (c : ℝ) :
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
  obtain ⟨B, E, hB, hE, hBop, hEop, hBE, hcover, hBfr, hEfr, hBcl, hEcl,
    hcomponents, hnegative, hpositive⟩ :=
      bicollar_slice_complement_components_of_homotopic_disjoint φ hφ r hr hdisjoint c
  exact bicollar_slice_components_of_sides φ a c B E hB hE hBop hEop hBE hcover
    hBfr hEfr hBcl hEcl hcomponents hnegative hpositive

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
