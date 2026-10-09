import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometryTopology
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Proper
import DifferentialGeometry.Geometry.Metric.Isometry.Compactness
import DifferentialGeometry.Geometry.Metric.Isometry.Margulis
import Mathlib.Topology.Algebra.Group.Basic

namespace DifferentialGeometry.Hyperboloid

private theorem enat_card_quotient_map_equiv {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') (H : Subgroup G) :
    ENat.card (G' ⧸ H.map e.toMonoidHom) = ENat.card (G ⧸ H) := by
  symm
  apply ENat.card_congr
  apply Quotient.congr e.toEquiv
  intro a b
  simp only [QuotientGroup.leftRel_apply]
  change a⁻¹ * b ∈ H ↔ (e a)⁻¹ * e b ∈ H.map e.toMonoidHom
  simp only [Subgroup.mem_map_equiv, map_mul, map_inv, MulEquiv.symm_apply_apply]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem margulis_lemma :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (Γ : Subgroup (Hyperboloid E ≃ᵢ Hyperboloid E)) [DiscreteTopology Γ]
        (x : Hyperboloid E),
        let L := Subgroup.closure
          {g : Γ | dist ((g : Hyperboloid E ≃ᵢ Hyperboloid E) x) x < ε}
        ∃ H : Subgroup L, Group.IsNilpotent H ∧ ENat.card (L ⧸ H) ≤ (N : ℕ∞) := by
  let G := Hyperboloid E ≃ᵢ Hyperboloid E
  let _ : MulAction G (Hyperboloid E) :=
    { smul := fun g x => g x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  let _ : IsIsometricSMul G (Hyperboloid E) :=
    ⟨fun g => g.isometry⟩
  obtain ⟨ε, hε, N, hN⟩ := MulAction.margulis_lemma (lorentzRepresentation (E := E))
    isEmbedding_lorentzRepresentation (origin : Hyperboloid E)
    (IsometryEquiv.isCompact_setOf_dist_apply_le origin 1)
  refine ⟨ε, hε, N, ?_⟩
  intro Γ _ x
  let b := boost x
  let c : G ≃* G := MulAut.conj b.symm
  let Γ' : Subgroup G := Γ.map c.toMonoidHom
  let e : Γ ≃* Γ' := c.subgroupMap Γ
  let eh : Γ ≃ₜ Γ' :=
    { toEquiv := e.toEquiv
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (IsTopologicalGroup.continuous_conj b.symm).comp continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        change Continuous (fun g : Γ' => b.symm⁻¹ * (g : G) * b.symm)
        simpa only [inv_inv, Function.comp_def] using
          (IsTopologicalGroup.continuous_conj b.symm⁻¹).comp continuous_subtype_val }
  let _ : DiscreteTopology Γ' := eh.symm.isEmbedding.discreteTopology
  let S : Set Γ := {g | dist ((g : G) x) x < ε}
  let S' : Set Γ' := {g | dist ((g : G) origin) origin < ε}
  let L := Subgroup.closure S
  let L' := Subgroup.closure S'
  have hdisp (g : Γ) : dist ((e g : G) origin) origin = dist ((g : G) x) x := by
    change dist (b.symm ((g : G) (b origin))) origin = dist ((g : G) x) x
    have hb : b origin = x := boost_origin x
    have hb' : b.symm x = origin := by rw [← hb, b.symm_apply_apply]
    rw [hb, ← hb', b.symm.dist_eq]
  have himage : e '' S = S' := by
    ext g
    constructor
    · rintro ⟨h, hh, rfl⟩
      change dist ((e h : G) origin) origin < ε
      rw [hdisp]
      exact hh
    · intro hg
      refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
      change dist (((e.symm g : Γ) : G) x) x < ε
      rw [← hdisp, e.apply_symm_apply]
      exact hg
  have hL : L.map e.toMonoidHom = L' := by
    rw [MonoidHom.map_closure]
    change Subgroup.closure (e '' S) = Subgroup.closure S'
    rw [himage]
  let eL : L ≃* L' := (e.subgroupMap L).trans (MulEquiv.subgroupCongr hL)
  obtain ⟨H', hH', hindex⟩ := hN Γ'
  let H : Subgroup L := H'.map eL.symm.toMonoidHom
  refine ⟨H, ?_, ?_⟩
  · exact (Group.isNilpotent_congr (eL.symm.subgroupMap H')).mp hH'
  · exact (enat_card_quotient_map_equiv eL.symm H').trans_le hindex

end DifferentialGeometry.Hyperboloid
