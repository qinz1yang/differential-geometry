import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.inter_image_eq_of_model_conjugacy {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ψ : M ≃ₜ M) (hφP : φ '' P = P) (hconj : ∀ x ∈ P, ψ (u x) = u (φ x))
    {A B : Set M} (hAP : A ⊆ u '' P) :
    A ∩ ψ '' B = u '' ((Function.invFunOn u P '' A) ∩ φ '' (P ∩ u ⁻¹' B)) := by
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hφmap : MapsTo φ P P := fun _ hx => hφP ▸ mem_image_of_mem φ hx
  have hψP : ψ '' (u '' P) = u '' P := by
    rw [image_image]
    calc
      (ψ ∘ u) '' P = (u ∘ φ) '' P := image_congr hconj
      _ = u '' P := by rw [image_comp, hφP]
  ext x
  constructor
  · rintro ⟨hxA, y, hyB, hyx⟩
    have hyP : y ∈ u '' P := by
      obtain ⟨z, hz, hzx⟩ := hψP.symm ▸ hAP hxA
      exact (ψ.injective (hzx.trans hyx.symm)) ▸ hz
    obtain ⟨z, hz, rfl⟩ := hyP
    have hzx : u (φ z) = x := (hconj z hz).symm.trans hyx
    refine ⟨φ z, ⟨?_, ⟨z, ⟨hz, hyB⟩, rfl⟩⟩, hzx⟩
    exact ⟨x, hxA, by rw [← hzx]; exact hleft (hφmap hz)⟩
  · rintro ⟨y, ⟨⟨a, ha, hay⟩, ⟨z, hz, hzy⟩⟩, rfl⟩
    have hya : u y = a := hay ▸ hright (hAP ha)
    refine ⟨hya.symm ▸ ha, u z, hz.2, ?_⟩
    exact (hconj z hz.1).trans (congrArg u hzy)

end DifferentialGeometry.Topology.PiecewiseLinear
