import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.VanKampen.SimplyConnectedUnion
import Mathlib.Topology.Constructions

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Topology

universe u v

theorem injective_fundamentalGroup_sigmaMk
    {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)]
    (i : I) (x₀ : X i) :
    Function.Injective (FundamentalGroup.map
      (⟨Sigma.mk i, continuous_sigmaMk⟩ : C(X i, Σ j, X j)) x₀) := by
  classical
  let r : C((Σ j, X j), X i) :=
    { toFun := fun p => if h : p.fst = i then h ▸ p.snd else x₀
      continuous_toFun := by
        apply continuous_sigma
        intro j
        by_cases h : j = i
        · subst j
          simp only
          exact continuous_id
        · simp only [dif_neg h]
          exact continuous_const }
  apply injective_fundamentalGroup_map_of_leftInverse _ r _ x₀
  intro x
  simp [r]

theorem simplyConnectedSpace_sigma_fiber_of_subsingleton_fundamentalGroup
    {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)]
    (i : I) [PathConnectedSpace (X i)]
    (h : ∀ p : Σ j, X j, Subsingleton (FundamentalGroup (Σ j, X j) p)) :
    SimplyConnectedSpace (X i) := by
  let x₀ : X i := Classical.choice inferInstance
  let := h ⟨i, x₀⟩
  exact (VanKampen.simplyConnectedSpace_iff_fundamentalGroup_subsingleton (X i) x₀).mpr
    (injective_fundamentalGroup_sigmaMk X i x₀).subsingleton

end DifferentialGeometry.Topology
