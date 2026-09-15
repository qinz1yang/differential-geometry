import DifferentialGeometry.Topology.Homology.ManifoldCompactHomology
import Mathlib.Topology.Sets.Compacts

noncomputable section

open Set TopologicalSpace Module

universe u

namespace DifferentialGeometry.Topology

theorem exists_unique_compact_homology_family_of_locally_realized_family
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) (μ : ∀ x : X, integralLocalHomology n x)
    (hlocal : ∀ x : X, ∃ L : Set X, IsCompact L ∧ x ∈ interior L ∧
      ∃ a : integralRelativeHomology n Lᶜ, ∀ y (hy : y ∈ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show Lᶜ ⊆ ({y}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hy)) a = μ y) :
    ∃! c : ∀ K : Compacts X, integralRelativeHomology n (K : Set X)ᶜ,
      (∀ (K L : Compacts X) (h : K ≤ L),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr h) (c L) = c K) ∧
      ∀ (K : Compacts X) (x : X) (hx : x ∈ K),
        integralRelativeHomologyMap n (ContinuousMap.id X)
          (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
            compl_subset_compl.mpr (singleton_subset_iff.mpr hx)) (c K) = μ x := by
  have hex (K : Compacts X) := exists_unique_compact_class_of_locally_realized_family
    (E := E) n hn (K : Set X) K.isCompact μ (fun x _ => by
      obtain ⟨L, hL, hx, a, ha⟩ := hlocal x
      exact ⟨L, hL, hx, a, fun y hy => ha y hy.2⟩)
  choose c hc huniq using hex
  refine ⟨c, ⟨?_, hc⟩, ?_⟩
  · intro K L hKL
    apply huniq K
    intro x hx
    have hcomp := LinearMap.congr_fun (integralRelativeHomologyMap_comp n
      (ContinuousMap.id X) (ContinuousMap.id X)
      (show (L : Set X)ᶜ ⊆ (K : Set X)ᶜ from compl_subset_compl.mpr hKL)
      (show (K : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from
        compl_subset_compl.mpr (singleton_subset_iff.mpr hx))) (c L)
    exact hcomp.symm.trans (hc L x (hKL hx))
  · intro d hd
    funext K
    exact huniq K (d K) (hd.2 K)

end DifferentialGeometry.Topology
