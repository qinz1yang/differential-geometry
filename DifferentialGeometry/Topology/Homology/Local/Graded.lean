import DifferentialGeometry.Topology.Homology.Local.Manifold
import DifferentialGeometry.Topology.Homology.Relative.Reduced
import DifferentialGeometry.Topology.LocalDegree.SphereGenerator
import DifferentialGeometry.Topology.LocalDegree.SphereVanishing

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits Set Metric
open scoped Manifold

namespace Poincare.Homology

variable {k : Type} [Ring k] (R : ModuleCat k)

def localEuclideanSphereHomologyIso (n q : ℕ) :
    relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R (q + 1) ≅
        reducedSingularHomology R
          (TopCat.of (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) q :=
  relativeReducedConnectingIso _ _ R q ≪≫
    reducedSingularHomologyIso R (puncturedSpaceSphereHomotopyEquiv _) q

theorem isZero_localEuclidean_succ (n q : ℕ) (h : q + 1 ≠ n) :
    IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R (q + 1)) := by
  apply IsZero.of_iso _ (localEuclideanSphereHomologyIso R n q)
  cases n with
  | zero => exact isZero_reducedSingularHomology_of_isEmpty R _ q
  | succ n => exact Poincare.LocalDegree.isZero_euclideanSphere_reducedHomology R n q (by omega)


theorem isZero_localEuclidean_of_gt (n q : ℕ) (h : n < q) :
    IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R q) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact isZero_localEuclidean_succ R n q (by omega)

theorem not_isZero_localEuclidean_top (n : ℕ) :
    ¬IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) (ModuleCat.of ℤ ℤ) (n + 1)) := by
  intro h
  have hz := h.of_iso (localEuclideanSphereHomologyIso (ModuleCat.of ℤ ℤ) (n + 1) n).symm
  have := ModuleCat.isZero_iff_subsingleton.mp hz
  exact Poincare.LocalDegree.euclideanSphereTopGenerator_ne_zero n
    (Subsingleton.elim _ _)


theorem isZero_localEuclidean_at_of_gt (n q : ℕ) (p : EuclideanSpace ℝ (Fin n)) (h : n < q) :
    IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin n)))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin n))) R q) := by
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have he : e p = 0 := sub_self p
  have hi := chartLocalHomologyIso (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e p (mem_univ p) R q
  rw [he] at hi
  exact (isZero_localEuclidean_of_gt R n q h).of_iso hi


theorem not_isZero_localEuclidean_at_top (n : ℕ) (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ¬IsZero (relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
      ({p}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) (ModuleCat.of ℤ ℤ) (n + 1)) := by
  intro h
  let e := (Homeomorph.subRight p).toOpenPartialHomeomorph
  have he : e p = 0 := sub_self p
  have hi := chartLocalHomologyIso (X := TopCat.of (EuclideanSpace ℝ (Fin (n + 1))))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin (n + 1)))) e p (mem_univ p) (ModuleCat.of ℤ ℤ) (n + 1)
  rw [he] at hi
  exact not_isZero_localEuclidean_top n (h.of_iso hi.symm)

theorem isZero_localHalfSpace_succ {n : ℕ} [NeZero n] (p : EuclideanHalfSpace n)
    (hp : p.val 0 = 0) (q : ℕ) :
    IsZero (relativeHomology (TopCat.of (EuclideanHalfSpace n))
      ({p}ᶜ : Set (EuclideanHalfSpace n)) R (q + 1)) := by
  let := contractibleSpace_euclideanHalfSpace (n := n)
  let := contractibleSpace_puncturedHalfSpace p hp
  exact (isZero_reducedSingularHomology_of_contractible R _ q).of_iso
    (relativeReducedConnectingIso _ _ R q)

section Manifold
variable {n : ℕ} {H M : Type} [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M] [T1Space M] (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H)
  (x : M)

theorem isZero_localManifold_interior_of_gt (hx : I.IsInteriorPoint x) (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R q) := by
  let e := (Poincare.Manifold.interiorChart I 0 x).toOpenPartialHomeomorph
  have he : x ∈ e.source := (Poincare.Manifold.mem_interiorChart_source_iff I 0 x).mpr hx
  exact (isZero_localEuclidean_at_of_gt R n q (e x) hq).of_iso
    (chartLocalHomologyIso (X := TopCat.of M)
      (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) e x he R q)

end Manifold

section Boundary
variable {n : ℕ} [NeZero n] {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M] [T1Space M] (x : M)

theorem isZero_localManifold_boundary_succ (hx : (𝓡∂ n).IsBoundaryPoint x) (q : ℕ) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R (q + 1)) := by
  let : T1Space (EuclideanHalfSpace n) := inferInstanceAs
    (T1Space {v : EuclideanSpace ℝ (Fin n) // 0 ≤ v 0})
  exact (isZero_localHalfSpace_succ R (chartAt (EuclideanHalfSpace n) x x)
    (chartAt_boundary_normal_eq_zero x hx) q).of_iso
    (chartLocalHomologyIso (X := TopCat.of M) (Y := TopCat.of (EuclideanHalfSpace n))
      (chartAt (EuclideanHalfSpace n) x) x (mem_chart_source _ x) R (q + 1))

theorem isZero_localManifold_of_gt (q : ℕ) (hq : n < q) :
    IsZero (relativeHomology (TopCat.of M) ({x}ᶜ : Set M) R q) := by
  rcases (𝓡∂ n).isInteriorPoint_or_isBoundaryPoint x with hx | hx
  · exact isZero_localManifold_interior_of_gt R (𝓡∂ n) x hx q hq
  · obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact isZero_localManifold_boundary_succ R x hx q

end Boundary

end Poincare.Homology
