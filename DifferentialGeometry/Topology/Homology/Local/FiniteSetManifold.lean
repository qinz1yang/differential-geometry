import DifferentialGeometry.Topology.Homology.Local.FiniteSetEuler
import DifferentialGeometry.Topology.Homology.Local.Graded

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set
open scoped Manifold
namespace DifferentialGeometry.Homology
variable {k : Type} [Ring k] (R : ModuleCat k)
section Interior
variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
  (Z : Set M) (hZ : Z.Finite) (hI : ∀ p ∈ Z, I.IsInteriorPoint p)
include hZ hI


theorem isZero_finitePunctureManifold_interior_of_gt (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) Zᶜ R q) :=
  isZero_relativeHomology_finitePuncture (TopCat.of M) Z R hZ q
    (fun p => isZero_localManifold_interior_of_gt R I p.val (hI p.val p.property) q hq)

variable (k : Type) [Field k]

theorem finiteHomologyType_finitePunctureManifold_interior :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) Zᶜ (ModuleCat.of k k)) :=
  finiteHomologyType_finitePuncture (TopCat.of M) Z hZ k
    (fun p => finiteHomologyType_localManifold_interior k I p.val (hI p.val p.property))


theorem relativeEulerChar_finitePunctureManifold_interior :
    relativeEulerChar (TopCat.of M) Zᶜ k = (Nat.card Z : ℤ) * (-1 : ℤ)^n := by
  let := hZ.fintype
  rw [relativeEulerChar_finitePuncture (TopCat.of M) Z hZ k
    (fun p => finiteHomologyType_localManifold_interior k I p.val (hI p.val p.property))]
  rw [finsum_eq_sum_of_fintype]
  calc
    _ = ∑ _ : Z, (-1 : ℤ)^n := Finset.sum_congr rfl (fun p _ =>
      relativeEulerChar_localManifold_interior k I p.val (hI p.val p.property))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
end Interior
section Boundary
variable {n : ℕ} [hn : NeZero n] {M : Type} [TopologicalSpace M]
  [hM : ChartedSpace (EuclideanHalfSpace n) M] [T2Space M]
  (Z : Set M) (hZ : Z.Finite)
include hZ hM hn


theorem isZero_finitePunctureManifold_of_gt (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) Zᶜ R q) :=
  isZero_relativeHomology_finitePuncture (TopCat.of M) Z R hZ q
    (fun p => isZero_localManifold_of_gt R p.val q hq)

variable (k : Type) [Field k]

theorem finiteHomologyType_finitePunctureManifold :
    DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) Zᶜ (ModuleCat.of k k)) := by
  apply finiteHomologyType_finitePuncture (TopCat.of M) Z hZ k
  intro p
  rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint p.val with hi | hb
  · exact finiteHomologyType_localManifold_interior k (𝓡∂ n) p.val hi
  · exact finiteHomologyType_localManifold_boundary k p.val hb

open Classical in
theorem relativeEulerChar_finitePunctureManifold :
    relativeEulerChar (TopCat.of M) Zᶜ k =
      ∑ᶠ p : Z, if (𝓡∂ n).IsInteriorPoint p.val then (-1 : ℤ)^n else 0 := by
  classical
  have hlocal (p : Z) : DifferentialGeometry.HomologicalComplex.finiteHomologyType
      (relativeChainComplex (TopCat.of M) ({p.val}ᶜ : Set M) (ModuleCat.of k k)) := by
    rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint p.val with hi | hb
    · exact finiteHomologyType_localManifold_interior k (𝓡∂ n) p.val hi
    · exact finiteHomologyType_localManifold_boundary k p.val hb
  rw [relativeEulerChar_finitePuncture (TopCat.of M) Z hZ k hlocal]
  apply finsum_congr
  intro p
  by_cases hi : (𝓡∂ n).IsInteriorPoint p.val
  · rw [if_pos hi]
    exact relativeEulerChar_localManifold_interior k (𝓡∂ n) p.val hi
  · rw [if_neg hi]
    exact relativeEulerChar_localManifold_boundary k p.val
      (((𝓡∂ n).isBoundaryPoint_iff_not_isInteriorPoint p.val).mpr hi)
end Boundary
end DifferentialGeometry.Homology
