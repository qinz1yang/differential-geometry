import DifferentialGeometry.Topology.Simplex.BallCoordinates
import DifferentialGeometry.Topology.Simplex.RelativeHomology
import DifferentialGeometry.Topology.Homology.RelativeHomeomorphism

noncomputable section

namespace DifferentialGeometry.Topology

universe u

open Set
open scoped BigOperators

def simplexCoordinateInclusion (n : ℕ) :
    C(stdSimplex ℝ (Fin (n + 1)), Fin n → ℝ) :=
  ⟨fun p i => p.val i.succ, by
      exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)⟩

theorem simplexCoordinateInclusion_injective (n : ℕ) :
    Function.Injective (simplexCoordinateInclusion n) := by
  intro p q h
  apply (Simplex.stdSimplexCoordinateHomeomorph n).injective
  exact Subtype.ext h

private theorem simplexCoordinateInclusion_mem_interior_iff (n : ℕ)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    simplexCoordinateInclusion n p ∈ interior (Simplex.coordinateSimplex n) ↔
      p ∈ Simplex.openCell (Fin (n + 1)) := by
  rw [Simplex.interior_coordinateSimplex]
  change ((∀ i : Fin n, 0 < p.val i.succ) ∧ ∑ i : Fin n, p.val i.succ < 1) ↔
    ∀ i, 0 < p.val i
  have hs := p.property.2
  rw [Fin.sum_univ_succ] at hs
  constructor
  · rintro ⟨hp, hsum⟩ i
    exact Fin.cases (by linarith) hp i
  · intro hp
    exact ⟨fun i => hp i.succ, by linarith [hp 0]⟩

private def simplexOpenCellCoordinateHomeomorph (n : ℕ) :
    Simplex.openCell (Fin (n + 1)) ≃ₜ interior (Simplex.coordinateSimplex n) where
  toFun p := ⟨simplexCoordinateInclusion n p,
    (simplexCoordinateInclusion_mem_interior_iff n p).mpr p.property⟩
  invFun x := ⟨(Simplex.stdSimplexCoordinateHomeomorph n).symm
      ⟨x.val, interior_subset x.property⟩,
    (simplexCoordinateInclusion_mem_interior_iff n _).mp x.property⟩
  left_inv p := by
    apply Subtype.ext
    exact (Simplex.stdSimplexCoordinateHomeomorph n).symm_apply_apply p.val
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Simplex.stdSimplexCoordinateHomeomorph n).symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)

theorem simplexCoordinateInclusion_mapsTo_pointComplement (n : ℕ)
    (p : stdSimplex ℝ (Fin (n + 1))) :
    MapsTo (simplexCoordinateInclusion n) ({p}ᶜ : Set (stdSimplex ℝ (Fin (n + 1))))
      ({simplexCoordinateInclusion n p}ᶜ : Set (Fin n → ℝ)) :=
  fun _ hp => (simplexCoordinateInclusion_injective n).ne hp

theorem integralRelativeHomologyMap_simplexCoordinateInclusion_bijective
    (n k : ℕ) (p : stdSimplex ℝ (Fin (n + 1)))
    (hp : p ∈ Simplex.openCell (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (simplexCoordinateInclusion n)
      (simplexCoordinateInclusion_mapsTo_pointComplement n p)) := by
  let f := simplexCoordinateInclusion n
  let e := simplexOpenCellCoordinateHomeomorph n
  have hUV : MapsTo f (Simplex.openCell (Fin (n + 1)))
      (interior (Simplex.coordinateSimplex n)) :=
    fun p hp => (simplexCoordinateInclusion_mem_interior_iff n p).mpr hp
  let Jx := integralLocalHomologyNeighborhoodIso k p (Simplex.openCell (Fin (n + 1)))
    Simplex.isOpen_openCell hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p)
    (interior (Simplex.coordinateSimplex n)) isOpen_interior (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e
    (⟨p, hp⟩ : Simplex.openCell (Fin (n + 1)))
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (simplexCoordinateInclusion_mapsTo_pointComplement n p)
    (Simplex.openCell (Fin (n + 1))) (interior (Simplex.coordinateSimplex n))
    Simplex.isOpen_openCell isOpen_interior hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (simplexCoordinateInclusion_mapsTo_pointComplement n p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp

def liftedSimplexCoordinateInclusion (n : ℕ) :
    C(ULift.{u} (stdSimplex ℝ (Fin (n + 1))), ULift.{u} (Fin n → ℝ)) :=
  ⟨fun p => ULift.up (simplexCoordinateInclusion n p.down), by fun_prop⟩

theorem liftedSimplexCoordinateInclusion_injective (n : ℕ) :
    Function.Injective (liftedSimplexCoordinateInclusion.{u} n) := by
  intro p q h
  apply ULift.ext
  exact simplexCoordinateInclusion_injective n (congrArg ULift.down h)

theorem liftedSimplexCoordinateInclusion_mapsTo_pointComplement (n : ℕ)
    (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :
    MapsTo (liftedSimplexCoordinateInclusion n)
      ({p}ᶜ : Set (ULift.{u} (stdSimplex ℝ (Fin (n + 1)))))
      ({liftedSimplexCoordinateInclusion n p}ᶜ : Set (ULift.{u} (Fin n → ℝ))) :=
  fun _ hp => (liftedSimplexCoordinateInclusion_injective n).ne hp

private def liftedSimplexOpenCell (n : ℕ) :
    Set (ULift.{u} (stdSimplex ℝ (Fin (n + 1)))) :=
  {p | p.down ∈ Simplex.openCell (Fin (n + 1))}

private def liftedCoordinateSimplexInterior (n : ℕ) : Set (ULift.{u} (Fin n → ℝ)) :=
  {x | x.down ∈ interior (Simplex.coordinateSimplex n)}

private theorem isOpen_liftedSimplexOpenCell (n : ℕ) :
    IsOpen (liftedSimplexOpenCell.{u} n) :=
  Simplex.isOpen_openCell.preimage continuous_uliftDown

private theorem isOpen_liftedCoordinateSimplexInterior (n : ℕ) :
    IsOpen (liftedCoordinateSimplexInterior.{u} n) :=
  isOpen_interior.preimage continuous_uliftDown

private def liftedSimplexOpenCellCoordinateHomeomorph (n : ℕ) :
    liftedSimplexOpenCell.{u} n ≃ₜ liftedCoordinateSimplexInterior.{u} n where
  toFun p := ⟨liftedSimplexCoordinateInclusion n p,
    (simplexCoordinateInclusion_mem_interior_iff n p.val.down).mpr p.property⟩
  invFun x := ⟨ULift.up ((simplexOpenCellCoordinateHomeomorph n).symm
    ⟨x.val.down, x.property⟩).val,
    ((simplexOpenCellCoordinateHomeomorph n).symm ⟨x.val.down, x.property⟩).property⟩
  left_inv p := by
    apply Subtype.ext
    apply ULift.ext
    exact congrArg Subtype.val ((simplexOpenCellCoordinateHomeomorph n).symm_apply_apply
      ⟨p.val.down, p.property⟩)
  right_inv x := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_uliftUp.comp
    apply continuous_subtype_val.comp
    exact (simplexOpenCellCoordinateHomeomorph n).symm.continuous.comp
      ((continuous_uliftDown.comp continuous_subtype_val).subtype_mk _)

theorem integralRelativeHomologyMap_liftedSimplexCoordinateInclusion_bijective
    (n k : ℕ) (p : ULift.{u} (stdSimplex ℝ (Fin (n + 1))))
    (hp : p.down ∈ Simplex.openCell (Fin (n + 1))) :
    Function.Bijective (integralRelativeHomologyMap k (liftedSimplexCoordinateInclusion n)
      (liftedSimplexCoordinateInclusion_mapsTo_pointComplement n p)) := by
  let f := liftedSimplexCoordinateInclusion n
  let e := liftedSimplexOpenCellCoordinateHomeomorph.{u} n
  have hUV : MapsTo f (liftedSimplexOpenCell n) (liftedCoordinateSimplexInterior n) :=
    fun p hp => (simplexCoordinateInclusion_mem_interior_iff n p.down).mpr hp
  let Jx := integralLocalHomologyNeighborhoodIso k p (liftedSimplexOpenCell n)
    (isOpen_liftedSimplexOpenCell n) hp
  let Jy := integralLocalHomologyNeighborhoodIso k (f p) (liftedCoordinateSimplexInterior n)
    (isOpen_liftedCoordinateSimplexInterior n) (hUV hp)
  let L := integralLocalHomologyHomeomorphIso k e (⟨p, hp⟩ : liftedSimplexOpenCell n)
  have h := integralLocalHomologyNeighborhoodIso_map k f p
    (liftedSimplexCoordinateInclusion_mapsTo_pointComplement n p)
    (liftedSimplexOpenCell n) (liftedCoordinateSimplexInterior n)
    (isOpen_liftedSimplexOpenCell n) (isOpen_liftedCoordinateSimplexInterior n) hUV hp
  change (integralRelativeHomologyMap k f _).comp Jx.hom.hom =
    Jy.hom.hom.comp L.hom.hom at h
  have hcomp : Function.Bijective ((integralRelativeHomologyMap k f
      (liftedSimplexCoordinateInclusion_mapsTo_pointComplement n p)).comp Jx.hom.hom) := by
    rw [h]
    exact Jy.toLinearEquiv.bijective.comp L.toLinearEquiv.bijective
  exact (Function.Bijective.of_comp_iff _ Jx.toLinearEquiv.bijective).mp hcomp

end DifferentialGeometry.Topology
