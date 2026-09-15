import DifferentialGeometry.Analysis.Calculus.MapConvergence.Composition

set_option autoImplicit false

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Set
open scoped ContDiff

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace Real E']

theorem mapCInfConvergence_mul {U : Set E'} (hU : IsOpen U)
    {u v : Nat → E' → Real} {uinf vinf : E' → Real}
    (hu : MapCInfConvergenceOnCompacts U u uinf) (hv : MapCInfConvergenceOnCompacts U v vinf)
    (huc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U)
    (hvc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (v k) U)
    (hvinfc : ContDiffOn Real (∞ : WithTop ℕ∞) vinf U) :
    MapCInfConvergenceOnCompacts U (fun k x => u k x * v k x) (fun x => uinf x * vinf x) := by
  have hpair := mapCInfConvergence_prodMk hU hu hv huc huinfc hvc hvinfc
  have hmulc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (fun q : Real × Real => q.1 * q.2) Set.univ :=
    contDiff_mul.contDiffOn
  have hcomp := MapCInfConvergenceOnCompacts.comp hU isOpen_univ hpair
    (mapCInfConvergence_const (U := (Set.univ : Set (Real × Real)))
      (fun q : Real × Real => q.1 * q.2))
    (fun k => (huc k).prodMk (hvc k)) (huinfc.prodMk hvinfc)
    (fun _ => hmulc) hmulc (Set.mapsTo_univ _ _) (fun _ => Set.mapsTo_univ _ _)
  exact hcomp

theorem mapCInfConvergence_inv {U : Set E'} (hU : IsOpen U)
    {u : Nat → E' → Real} {uinf : E' → Real} {δ : Real} (hδ : 0 < δ)
    (hu : MapCInfConvergenceOnCompacts U u uinf)
    (huc : ∀ k, ContDiffOn Real (∞ : WithTop ℕ∞) (u k) U)
    (huinfc : ContDiffOn Real (∞ : WithTop ℕ∞) uinf U)
    (hlow : ∀ k, ∀ y ∈ U, δ < u k y)
    (hlowinf : ∀ y ∈ U, δ < uinf y) :
    MapCInfConvergenceOnCompacts U (fun k y => (u k y)⁻¹) (fun y => (uinf y)⁻¹) := by
  have hinvc : ContDiffOn Real (∞ : WithTop ℕ∞)
      (Inv.inv : Real → Real) (Set.Ioi δ) :=
    ContDiffOn.mono (contDiffOn_inv Real)
      (fun t ht => Set.mem_compl_singleton_iff.mpr (ne_of_gt (lt_trans hδ ht)))
  have hcomp := MapCInfConvergenceOnCompacts.comp hU isOpen_Ioi hu
    (mapCInfConvergence_const (U := Set.Ioi δ) (Inv.inv : Real → Real))
    huc huinfc (fun _ => hinvc) hinvc
    (fun y hy => hlowinf y hy) (fun k y hy => hlow k y hy)
  exact hcomp

end CheegerGromovCompactness
end DifferentialGeometry

noncomputable section
open Set

namespace DifferentialGeometry.CheegerGromovCompactness

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem MapCInfConvergenceOnCompacts.const_add {U : Set P}
    {f : ℕ → P → E} {fInf : P → E}
    (h : MapCInfConvergenceOnCompacts U f fInf) (a : E) :
    MapCInfConvergenceOnCompacts U (fun k z => a + f k z) (fun z => a + fInf z) := by
  intro K hK hKU p ε hε
  obtain ⟨N, hN⟩ := h K hK hKU p ε hε
  refine ⟨N, fun k hk j hj z hz => ?_⟩
  simpa only [mapDerivNorm, add_sub_add_left_eq_sub] using hN k hk j hj z hz

end DifferentialGeometry.CheegerGromovCompactness
end
