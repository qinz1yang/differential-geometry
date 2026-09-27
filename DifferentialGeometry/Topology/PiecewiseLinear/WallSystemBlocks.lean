/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlock

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

def HasStableCrossingBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM Q : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (m : ℕ) (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ))
      (r tlo : Fin m → ℝ) (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2)))
      (a b : Fin m → ℝ × ℝ → ℝ) (La Lb : Fin m → ℝ),
      doublePointSet f S ∩ Q ⊆ ⋃ i, innerChartBlock ec (A i) (r i) (tlo i) ∧
        ∀ i, IsStableCrossingBlock f S ec ℓ BdM (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i)
          (La i) (Lb i) η

def wallSystemCells (Q : Geometry.SimplicialComplex ℝ Ea) : Set (Finset Ea) :=
  {s | s ∈ Q.faces ∧ s.card = 4}

def wallSystemWalls (Q : Geometry.SimplicialComplex ℝ Ea) : Set (Finset Ea) :=
  {s | s ∈ Q.faces ∧ s.card = 3}

def wallSystemCell (ρ : M → Ea) (s : Finset Ea) : Set M :=
  ρ ⁻¹' convexHull ℝ (s : Set Ea)

def wallSystemCellInt (ρ : M → Ea) (s : Finset Ea) : Set M :=
  ρ ⁻¹' openSimplex s

def wallSystemSkeleton (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) : Set M :=
  ⋃ s ∈ {s : Finset Ea | s ∈ Q.faces ∧ s.card ≤ 2}, wallSystemCell ρ s

structure IsCommonWallSystem (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea)
    (Cf Bf : Set (Finset Ea)) (BdM C : Set M) {ι : Type}
    (ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb Eb' : ι → Set M) : Prop where
  finiteFaces : Q.faces.Finite
  dimLe : ∀ s ∈ Q.faces, s.card ≤ 4
  memCell : ∀ s ∈ Q.faces, ∃ c ∈ wallSystemCells Q, s ⊆ c
  continuous : Continuous ρ
  injective : Function.Injective ρ
  rangeEq : Set.range ρ = Q.space
  facesC : Cf ⊆ wallSystemCells Q
  facesBd : Bf ⊆ wallSystemWalls Q
  eqC : C = ⋃ c ∈ Cf, wallSystemCell ρ c
  eqBd : BdM = ⋃ w ∈ Bf, wallSystemCell ρ w
  wallSides : ∀ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q,
    ∃ cp ∈ wallSystemCells Q, cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
      ∀ c ∈ wallSystemCells Q, w ⊆ c → c = cm ∨ c = cp
  boundarySides : ∀ w ∈ Bf, ∃ c ∈ Cf, w ⊆ c ∧ ∀ c' ∈ Cf, w ⊆ c' → c' = c
  starLayer : ∀ i, ∀ c ∈ wallSystemCells Q, (wallSystemCell ρ c ∩ Eb i).Nonempty →
    wallSystemCell ρ c ⊆ Eb' i
  layerSubset : ∀ i, Eb i ⊆ Eb' i
  layerCompact : ∀ i, IsCompact (Eb' i)
  layerSource : ∀ i, Eb' i ⊆ (ec i).source
  chartAtlas : ∀ i, ec i ∈ (plGroupoid 3).maximalAtlas M
  normalNe : ∀ i, ℓ i ≠ 0
  chartC : ∀ i, ∀ x ∈ (ec i).source, x ∈ C ↔ 0 ≤ ℓ i (ec i x)
  chartBd : ∀ i, ∀ x ∈ (ec i).source, x ∈ BdM ↔ ℓ i (ec i x) = 0
  chartAffine : ∀ i, ∀ s ∈ Q.faces, wallSystemCell ρ s ⊆ Eb' i →
    ∃ A : Ea →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3), ∀ x ∈ wallSystemCell ρ s, ec i x = A (ρ x)

def WallProductBlock (f : EuclideanSpace ℝ (Fin 2) → M) (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM C : Set M)
    (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η ∧
    Disjoint (chartBlock ec A r tlo) (wallSystemSkeleton Q ρ) ∧
    ((∃ c ∈ wallSystemCells Q, tlo = -r ∧
        chartBlock ec A r tlo ⊆ wallSystemCellInt ρ c) ∨
      (∃ w ∈ wallSystemWalls Q, ∃ cm ∈ wallSystemCells Q, ∃ cp ∈ wallSystemCells Q,
        tlo = -r ∧ cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
          chartBlock ec A r tlo ⊆ wallSystemCell ρ cm ∪ wallSystemCell ρ cp ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ cm).Nonempty ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ cp).Nonempty ∧
          (∀ w' ∈ wallSystemWalls Q,
            chartBlock ec A r tlo ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w) ∧
          (∀ x ∈ chartBlock ec A r tlo, x ∈ wallSystemCell ρ w ↔ (A (ec x)).2.2 = 0) ∧
          (∀ x ∈ chartBlock ec A r tlo ∩ wallSystemCell ρ cm, (A (ec x)).2.2 ≤ 0) ∧
          ∀ x ∈ chartBlock ec A r tlo ∩ wallSystemCell ρ cp, 0 ≤ (A (ec x)).2.2) ∨
      (∃ c ∈ wallSystemCells Q, ∃ w ∈ wallSystemWalls Q, tlo = 0 ∧ w ⊆ c ∧
        (∀ z, (A z).2.2 = ℓ z) ∧ chartBlock ec A r tlo ∩ C ⊆ wallSystemCell ρ c ∧
          (chartBlock ec A r tlo ∩ wallSystemCellInt ρ c).Nonempty ∧
          chartBlock ec A r tlo ∩ BdM ⊆ wallSystemCell ρ w ∧
          ∀ w' ∈ wallSystemWalls Q,
            chartBlock ec A r tlo ∩ wallSystemCell ρ w' ⊆ wallSystemCell ρ w))

def HasWallProductBlocks (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2))) {ι : Type}
    (ec : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : ι → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)) (Eb : ι → Set M) (BdM C : Set M)
    (Q : Geometry.SimplicialComplex ℝ Ea) (ρ : M → Ea) (Z : Set M) (η : ℝ) : Prop :=
  0 < η ∧ ∃ (N : Set M) (m : ℕ) (j : Fin m → ι)
      (A : Fin m → (EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ)) (r tlo : Fin m → ℝ)
      (SA SB : Fin m → Set (EuclideanSpace ℝ (Fin 2))) (a b : Fin m → ℝ × ℝ → ℝ)
      (La Lb : Fin m → ℝ),
      IsOpen N ∧ Z ⊆ N ∧
        doublePointSet f S ∩ N ⊆ ⋃ i, innerChartBlock (ec (j i)) (A i) (r i) (tlo i) ∧
        (∀ i, chartBlock (ec (j i)) (A i) (r i) (tlo i) ⊆ Eb (j i)) ∧
        ∀ i, WallProductBlock f S (ec (j i)) (ℓ (j i)) BdM C Q ρ
          (A i) (r i) (tlo i) (SA i) (SB i) (a i) (b i) (La i) (Lb i) η

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
