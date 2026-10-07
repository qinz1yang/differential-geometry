import DifferentialGeometry.Analysis.NormedRing.Zassenhaus
import DifferentialGeometry.Geometry.Metric.Isometry.SmallDisplacement
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.DiscreteSubset

namespace MulAction

open scoped Topology

variable {A G X : Type*} [SeminormedRing A] [Group G] [TopologicalSpace G]
  [PseudoMetricSpace X] [MulAction G X] [IsIsometricSMul G X]

theorem margulis_lemma (ρ : G →* Aˣ) (hρ : Topology.IsEmbedding ρ) (x : X)
    (hK : IsCompact {g : G | dist (g • x) x ≤ 1}) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ (Γ : Subgroup G) [DiscreteTopology Γ],
      let L := Subgroup.closure {g : Γ | dist ((g : G) • x) x < ε}
      ∃ H : Subgroup L, Group.IsNilpotent H ∧ ENat.card (L ⧸ H) ≤ (N : ℕ∞) := by
  have : IsTopologicalGroup G := Topology.IsInducing.isTopologicalGroup ρ hρ.isInducing
  obtain ⟨δ, hδ, hZ⟩ := Units.zassenhaus_lemma (A := A)
  let U : Set G := {g | ‖((ρ g : Aˣ) : A) - 1‖ < δ}
  have hUopen : IsOpen U :=
    isOpen_lt (((Units.continuous_val.comp hρ.continuous).sub continuous_const).norm)
      continuous_const
  have hU : U ∈ 𝓝 (1 : G) := hUopen.mem_nhds (by simpa [U] using hδ)
  obtain ⟨ε, hε, N, hindex⟩ := exists_index_bound_small_displacement x hK hU
  refine ⟨ε, hε, N, ?_⟩
  intro Γ _
  let L := Subgroup.closure {g : Γ | dist ((g : G) • x) x < ε}
  let H : Subgroup L := Subgroup.closure {g : L | ((g : Γ) : G) ∈ U}
  refine ⟨H, ?_, hindex Γ⟩
  let Γ' : Subgroup Aˣ := Γ.map ρ
  have hΓ : IsDiscrete (Γ : Set G) :=
    SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance
  have : DiscreteTopology Γ' := SetLike.isDiscrete_iff_discreteTopology.mp (by
    simpa only [Γ', Subgroup.coe_map] using hΓ.image hρ.isInducing)
  let T : Set Γ' := {g | ‖((g : Aˣ) : A) - 1‖ < δ}
  let K : Subgroup Γ' := Subgroup.closure T
  have : Group.IsNilpotent K := hZ Γ'
  let ψ : L →* Γ' := (ρ.subgroupMap Γ).comp L.subtype
  have hψ : Function.Injective ψ :=
    (ρ.subgroupMap_injective Γ hρ.injective).comp Subtype.val_injective
  have hHK : H ≤ K.comap ψ := ψ.closure_preimage_le T
  let f : H →* K := (ψ.comp H.subtype).codRestrict K (fun h => hHK h.property)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hψ
    exact congrArg Subtype.val hab
  exact (Group.isNilpotent_congr (MonoidHom.ofInjective hf)).mpr inferInstance

end MulAction
