import DifferentialGeometry.Topology.Manifold.AddCircle.CircleSimpHGI
import DifferentialGeometry.Topology.Diffeomorph.FiniteProduct
import DifferentialGeometry.Topology.Diffeomorph.Product
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.AddCircle.PiQuotient
import DifferentialGeometry.Topology.Quotient.LatticeCoordinates
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped ContDiff Manifold

namespace DifferentialGeometry

theorem exists_torus_diffeomorph_of_lattice_fibers {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
    {S : Type*} [TopologicalSpace S] [ChartedSpace H S]
    (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin 2))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (q : EuclideanSpace ℝ (Fin 2) → S)
    (hq : IsLocalDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) J ∞ q)
    (hs : Function.Surjective q) (hf : ∀ x y, q x = q y ↔ x - y ∈ Λ) :
    ∃ b : Module.Basis (Fin 2) ℤ Λ,
      ∃ D : Diffeomorph ((𝓡 1).prod (𝓡 1)) J (Circle × Circle) S ∞,
        (∀ t : Fin 2 → ℝ,
          D (Circle.exp (2 * Real.pi * t 0), Circle.exp (2 * Real.pi * t 1)) =
            q ((b.ofZLatticeBasis ℝ Λ).equivFunL.symm t)) ∧
        (∀ x, D.symm (q x) =
          (Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ Λ).equivFunL x 0),
            Circle.exp (2 * Real.pi * (b.ofZLatticeBasis ℝ Λ).equivFunL x 1))) := by
  let b : Module.Basis (Fin 2) ℤ Λ :=
    Module.finBasisOfFinrankEq ℤ Λ ((ZLattice.rank ℝ Λ).trans (by simp))
  let B := b.ofZLatticeBasis ℝ Λ
  let L := B.equivFunL.symm
  have hqL : IsLocalDiffeomorph 𝓘(ℝ, Fin 2 → ℝ) J ∞ (fun t => q (L t)) := by
    intro t
    exact (L.toDiffeomorph.isLocalDiffeomorph t).comp (K := J) (P := S) (hq (L t))
  have hsL : Function.Surjective (fun t => q (L t)) := hs.comp L.surjective
  have hfL (x y : Fin 2 → ℝ) : q (L x) = q (L y) ↔
      (fun i => (x i : AddCircle (1 : ℝ))) =
        (fun i => (y i : AddCircle (1 : ℝ))) := by
    rw [hf]
    have h := B.sub_mem_span_int_iff_coe_repr_eq (L x) (L y)
    rw [b.ofZLatticeBasis_span ℝ] at h
    have hx (i : Fin 2) : B.repr (L x) i = x i :=
      congrFun (B.equivFunL.apply_symm_apply x) i
    have hy (i : Fin 2) : B.repr (L y) i = y i :=
      congrFun (B.equivFunL.apply_symm_apply y) i
    simpa only [hx, hy] using h
  obtain ⟨D, hD, hDi⟩ :=
    AddCircle.exists_pi_diffeomorph_of_fibers (fun t => q (L t)) hqL hsL hfL
  let C : Diffeomorph (ModelWithCorners.pi (fun _ : Fin 2 => 𝓘(ℝ, ℝ)))
      ((𝓡 1).prod (𝓡 1)) (Fin 2 → AddCircle (1 : ℝ)) (Circle × Circle) ∞ :=
    (Diffeomorph.piFinTwo (fun _ : Fin 2 => 𝓘(ℝ, ℝ))
      (fun _ => AddCircle (1 : ℝ)) ∞).trans
      (Diffeomorph.prodCongrCross (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 1)
        (J := 𝓘(ℝ, ℝ)) (J' := 𝓡 1)
        AddCircle.diffeomorphCircle AddCircle.diffeomorphCircle)
  have hC (t : Fin 2 → ℝ) : C (fun i => (t i : AddCircle (1 : ℝ))) =
      (Circle.exp (2 * Real.pi * t 0), Circle.exp (2 * Real.pi * t 1)) := by
    change (AddCircle.diffeomorphCircle (t 0 : AddCircle (1 : ℝ)),
      AddCircle.diffeomorphCircle (t 1 : AddCircle (1 : ℝ))) = _
    simp only [AddCircle.diffeomorphCircle_apply_coe]
  refine ⟨b, C.symm.trans D, ?_, ?_⟩
  · intro t
    change D (C.symm _) = q (L t)
    rw [← hC t, C.symm_apply_apply]
    exact hD t
  · intro x
    change C (D.symm (q x)) = _
    have h := hDi (B.equivFunL x)
    have hx : L (B.equivFunL x) = x := B.equivFunL.symm_apply_apply x
    rw [hx] at h
    rw [h]
    exact hC (B.equivFunL x)

end DifferentialGeometry
