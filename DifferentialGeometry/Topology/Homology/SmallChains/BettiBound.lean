import DifferentialGeometry.Topology.Homology.BettiNumber
import DifferentialGeometry.Topology.Homology.SmallChains.FiniteType
import DifferentialGeometry.Topology.Homology.SmallChains.QuasiIso
import Mathlib.Algebra.Category.ModuleCat.Biproducts

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace DifferentialGeometry.Homology

universe u

theorem bettiNumber_union_le (k : Type u) [Field k] (X : TopCat.{u}) (s t : Set X)
    (hs : IsOpen s) (ht : IsOpen t) (hcover : s ∪ t = Set.univ)
    (hfs : finiteHomologyType k (TopCat.of s)) (hft : finiteHomologyType k (TopCat.of t))
    (hfI : finiteHomologyType k (TopCat.of (s ∩ t : Set X))) (n : ℕ) :
    bettiNumber k X (n + 1) ≤ bettiNumber k (TopCat.of s) (n + 1) +
      bettiNumber k (TopCat.of t) (n + 1) + bettiNumber k (TopCat.of (s ∩ t : Set X)) n := by
  let S := subspaceSmallShortComplex X s t (ModuleCat.of k k)
  have hS := subspaceSmallShortExact X s t (ModuleCat.of k k)
  have hB := DifferentialGeometry.HomologicalComplex.finiteHomologyType_biprod _ _ hfs hft
  have hU := finiteHomologyType_twoSetSmall X s t k hfs hft hfI
  let _ : FiniteDimensional k (S.X₁.homology n) := hfI.1 n
  let _ : FiniteDimensional k (S.X₂.homology (n + 1)) := hB.1 (n + 1)
  let _ : FiniteDimensional k (S.X₃.homology (n + 1)) := hU.1 (n + 1)
  let _ : FiniteDimensional k
      (((TopCat.toSSet.obj (TopCat.of s)).chainComplex (ModuleCat.of k k)).homology (n + 1)) :=
    hfs.1 (n + 1)
  let _ : FiniteDimensional k
      (((TopCat.toSSet.obj (TopCat.of t)).chainComplex (ModuleCat.of k k)).homology (n + 1)) :=
    hft.1 (n + 1)
  have hopen : ∀ b, IsOpen (twoSetFamily X s t b) := by
    intro b
    cases b
    · exact ht
    · exact hs
  have hcov : ∀ x : X, ∃ b, x ∈ twoSetFamily X s t b := by
    intro x
    have hx : x ∈ s ∪ t := hcover.symm ▸ Set.mem_univ x
    rcases hx with hx | hx
    · exact ⟨true, hx⟩
    · exact ⟨false, hx⟩
  have he := (smallChainHomologyIso X (twoSetFamily X s t) (ModuleCat.of k k)
    hopen hcov (n + 1)).toLinearEquiv.finrank_eq
  change Module.finrank k (S.X₃.homology (n + 1)) = bettiNumber k X (n + 1) at he
  have hr := DifferentialGeometry.ShortComplex.finrank_eq_range_add_range _
    (hS.homology_exact₃ (n + 1) n rfl)
  have hle : Module.finrank k (S.X₃.homology (n + 1)) ≤
      Module.finrank k (S.X₂.homology (n + 1)) + Module.finrank k (S.X₁.homology n) := by
    rw [hr]
    exact add_le_add (LinearMap.finrank_range_le _) (Submodule.finrank_le _)
  have hb := ((DifferentialGeometry.HomologicalComplex.homologyBiprodIso
    ((TopCat.toSSet.obj (TopCat.of s)).chainComplex (ModuleCat.of k k))
    ((TopCat.toSSet.obj (TopCat.of t)).chainComplex (ModuleCat.of k k)) (n + 1)) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at hb
  change Module.finrank k (S.X₂.homology (n + 1)) =
    bettiNumber k (TopCat.of s) (n + 1) + bettiNumber k (TopCat.of t) (n + 1) at hb
  rwa [he, hb] at hle

end DifferentialGeometry.Homology
