import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

noncomputable section

open Set Metric

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a : ℝ}

def annulusSphereProductHomeomorph (ha : 0 ≤ a) :
    {x : E // a < ‖x‖ ∧ ‖x‖ < 1} ≃ₜ sphere (0 : E) 1 × Ioo a 1 := by
  let S : Set E := {x | a < ‖x‖ ∧ ‖x‖ < 1}
  let T : Set (Ioi (0 : ℝ)) := {r | a < r.val ∧ r.val < 1}
  have hS : S ⊆ Set.range (Subtype.val : ({0}ᶜ : Set E) → E) := by
    intro x hx
    exact ⟨⟨x, norm_pos_iff.mp (ha.trans_lt hx.1)⟩, rfl⟩
  have hT : Ioo a 1 ⊆ Set.range (Subtype.val : Ioi (0 : ℝ) → ℝ) := by
    intro r hr
    exact ⟨⟨r, ha.trans_lt hr.1⟩, rfl⟩
  let e₁ : S ≃ₜ {x : ({0}ᶜ : Set E) // a < ‖x.val‖ ∧ ‖x.val‖ < 1} :=
    (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hS).symm
  let e₂ : {x : ({0}ᶜ : Set E) // a < ‖x.val‖ ∧ ‖x.val‖ < 1} ≃ₜ
      ((Set.univ : Set (sphere (0 : E) 1)) ×ˢ T) :=
    (homeomorphUnitSphereProd E).subtype (by
      intro x
      simp only [Set.mem_prod, Set.mem_univ, true_and, T, Set.mem_ofPred_eq,
        homeomorphUnitSphereProd_apply_snd_coe])
  let e₃ : T ≃ₜ Ioo a 1 :=
    Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hT
  exact e₁.trans (e₂.trans ((Homeomorph.Set.prod Set.univ T).trans
    ((Homeomorph.Set.univ _).prodCongr e₃)))

theorem simplyConnectedSpace_annulus (ha : 0 ≤ a) (ha₁ : a < 1)
    [SimplyConnectedSpace (sphere (0 : E) 1)] :
    SimplyConnectedSpace {x : E // a < ‖x‖ ∧ ‖x‖ < 1} := by
  have hp : a < (a + 1) / 2 ∧ (a + 1) / 2 < 1 := by constructor <;> linarith
  let : ContractibleSpace (Ioo a (1 : ℝ)) := (convex_Ioo a 1).contractibleSpace ⟨_, hp⟩
  let e : ContinuousMap.HomotopyEquiv (sphere (0 : E) 1 × Ioo a (1 : ℝ))
      (sphere (0 : E) 1) :=
    ((ContinuousMap.HomotopyEquiv.refl (sphere (0 : E) 1)).prodCongr
      (ContractibleSpace.hequiv_unit (Ioo a (1 : ℝ))).some).trans
        (Homeomorph.prodUnique (sphere (0 : E) 1) Unit).toHomotopyEquiv
  exact ((annulusSphereProductHomeomorph (E := E) ha).toHomotopyEquiv.trans e).simplyConnectedSpace

end DifferentialGeometry.Topology
