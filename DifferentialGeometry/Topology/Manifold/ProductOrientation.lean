import DifferentialGeometry.Topology.Manifold.Orientation
import Mathlib.LinearAlgebra.Basis.Prod

noncomputable section

open Manifold Module
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F H')
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

def tangentProdEquiv (p : M × N) :
    TangentSpace (I.prod J) p ≃ₗ[ℝ] TangentSpace I p.1 × TangentSpace J p.2 := by
  change (E × F) ≃ₗ[ℝ] (E × F)
  exact LinearEquiv.refl ℝ (E × F)

def productTangentBasis {m n : ℕ} {x : M} {y : N}
    (b : Basis (Fin m) ℝ (TangentSpace I x))
    (c : Basis (Fin n) ℝ (TangentSpace J y)) :
    Basis (Fin (m + n)) ℝ (TangentSpace (I.prod J) (x, y)) :=
  ((b.prod c).reindex finSumFinEquiv).map (tangentProdEquiv I J (x, y)).symm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

theorem exists_unique_product_orientation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    ∃! o : ManifoldOrientation (I.prod J) (M × N) (m + n),
      ∀ x y, ∀ b : Basis (Fin m) ℝ (TangentSpace I x),
        ∀ c : Basis (Fin n) ℝ (TangentSpace J y),
          b.orientation = oM.orientation x → c.orientation = oN.orientation y →
            (productTangentBasis I J b c).orientation = o.orientation (x, y) := by
  sorry

def productOrientation {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n) :
    ManifoldOrientation (I.prod J) (M × N) (m + n) :=
  (exists_unique_product_orientation I J hm hn oM oN).exists.choose

theorem productOrientation_characterization {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n)
    (x : M) (y : N) (b : Basis (Fin m) ℝ (TangentSpace I x))
    (c : Basis (Fin n) ℝ (TangentSpace J y))
    (hb : b.orientation = oM.orientation x) (hc : c.orientation = oN.orientation y) :
    (productTangentBasis I J b c).orientation =
      (productOrientation I J hm hn oM oN).orientation (x, y) :=
  (exists_unique_product_orientation I J hm hn oM oN).exists.choose_spec x y b c hb hc

theorem productOrientation_unique {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (oM : ManifoldOrientation I M m) (oN : ManifoldOrientation J N n)
    (o : ManifoldOrientation (I.prod J) (M × N) (m + n))
    (ho : ∀ x y, ∀ b : Basis (Fin m) ℝ (TangentSpace I x),
      ∀ c : Basis (Fin n) ℝ (TangentSpace J y),
        b.orientation = oM.orientation x → c.orientation = oN.orientation y →
          (productTangentBasis I J b c).orientation = o.orientation (x, y)) :
    o = productOrientation I J hm hn oM oN :=
  (exists_unique_product_orientation I J hm hn oM oN).unique ho
    (productOrientation_characterization I J hm hn oM oN)

end DifferentialGeometry
