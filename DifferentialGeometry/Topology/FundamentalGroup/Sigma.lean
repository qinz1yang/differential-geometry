import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.FundamentalGroup.SimplyConnected
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
        · simp only [dite_eq_right h]
          exact continuous_const }
  apply injective_fundamentalGroup_map_of_leftInverse _ r _ x₀
  intro x
  simp [r]

theorem simplyConnectedSpace_sigma_fiber_of_subsingleton_fundamentalGroup
    {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)]
    (i : I) [PathConnectedSpace (X i)] (x₀ : X i)
    (h : Subsingleton (FundamentalGroup (Σ j, X j) ⟨i, x₀⟩)) :
    SimplyConnectedSpace (X i) := by
  let _ := h
  have hsub : Subsingleton (FundamentalGroup (X i) x₀) :=
    (injective_fundamentalGroup_sigmaMk X i x₀).subsingleton
  exact (simplyConnectedSpace_iff_fundamentalGroup_eq_one x₀).mpr
    (fun g => hsub.elim g 1)

end DifferentialGeometry.Topology
