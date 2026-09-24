import DifferentialGeometry.Topology.Homology.ManifoldCompactHomology
import DifferentialGeometry.Topology.Homology.RelativeEmpty

noncomputable section
open Set Module
open scoped Topology
universe u
namespace DifferentialGeometry.Topology

theorem integralAbsoluteToRelative_family_injective
    {E X : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [T2Space X] [ChartedSpace E X] [CompactSpace X]
    (n : ℕ) (hn : finrank ℝ E ≤ n) :
    Function.Injective (fun a : integralSingularHomology n X =>
      fun x : X => integralAbsoluteToRelative n ({x}ᶜ : Set X) a) := by
  intro a b hab
  apply (integralAbsoluteToRelativeEmptyEquiv n X).injective
  change integralAbsoluteToRelative n (∅ : Set X) a =
    integralAbsoluteToRelative n (∅ : Set X) b
  rw [← compl_univ]
  apply integralRelativeHomology_eq_of_local_restrictions (E := E) n hn univ isCompact_univ
  intro x hx
  have hnat := integralAbsoluteToRelative_natural n (ContinuousMap.id X)
    (show (univ : Set X)ᶜ ⊆ ({x}ᶜ : Set X) from compl_subset_compl.mpr (subset_univ {x}))
  have ha := LinearMap.congr_fun hnat a
  have hb := LinearMap.congr_fun hnat b
  simp only [LinearMap.comp_apply, integralSingularHomologyMap_id, LinearMap.id_apply] at ha hb
  rw [← ha, ← hb]
  exact congrFun hab x

end DifferentialGeometry.Topology
