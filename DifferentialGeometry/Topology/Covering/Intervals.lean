import DifferentialGeometry.Topology.Covering.Lifting

noncomputable section
open scoped unitInterval
namespace DifferentialGeometry.Topology.Covering

theorem exists_unique_Icc_lift {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} (hp : IsCoveringMap p) {a b : ℝ} (hab : a ≤ b)
    (γ : C(Set.Icc a b, B)) (e : E) (he : p e = γ ⟨a, le_rfl, hab⟩) :
    ∃! Γ : C(Set.Icc a b, E), p ∘ Γ = γ ∧ Γ ⟨a, le_rfl, hab⟩ = e := by
  rcases lt_or_eq_of_le hab with hlt | rfl
  · let q := iccHomeoI a b hlt
    have hz : q.symm 0 = ⟨a, le_rfl, hab⟩ := by
      apply Subtype.ext
      simp [q, iccHomeoI_symm_apply_coe]
    obtain ⟨F, hF, huniq⟩ := exists_unique_path_lift hp
      (γ.comp ⟨q.symm, q.symm.continuous⟩) e (by simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hz] using he)
    refine ⟨F.comp ⟨q, q.continuous⟩, ⟨?_, ?_⟩, ?_⟩
    · funext t
      simpa using congrFun hF.1 (q t)
    · have hq : q ⟨a, le_rfl, hab⟩ = 0 := by rw [← hz, q.apply_symm_apply]
      simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hq] using hF.2
    · intro G hG
      have hg : G.comp ⟨q.symm, q.symm.continuous⟩ = F := huniq _ ⟨by
          funext t
          exact congrFun hG.1 (q.symm t), by
          simpa only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, hz] using hG.2⟩
      ext t
      simpa using DFunLike.congr_fun hg (q t)
  · have hall (t : Set.Icc a a) : t = ⟨a, le_rfl, le_rfl⟩ :=
      Subtype.ext (le_antisymm t.property.2 t.property.1)
    refine ⟨.const _ e, ⟨?_, rfl⟩, ?_⟩
    · funext t
      rw [hall t]
      exact he
    · intro G hG
      ext t
      rw [hall t]
      exact hG.2

end DifferentialGeometry.Topology.Covering
