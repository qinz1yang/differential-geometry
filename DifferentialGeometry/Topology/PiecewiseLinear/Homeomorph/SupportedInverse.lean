import DifferentialGeometry.Topology.PiecewiseLinear.Section34ModelMotionTransport
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSupportedModification

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLHomeomorphInto.isPLOn_symm_of_supported_homeomorph {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M}
    (hu : IsPLHomeomorphInto 3 u P) (hP : IsPLBall 3 P) (ψ : M ≃ₜ M) {K : Set M}
    (hK : IsClosed K) (hKP : K ⊆ interior (u '' P)) (hfix : EqOn ψ id Kᶜ)
    (hψ : IsPLOn 3 3 ψ (interior (u '' P))) : IsPLOn 3 3 ψ.symm (interior (u '' P)) := by
  obtain ⟨r, hr⟩ := hP
  have hψu := hu.postcomp_of_supported_isPLOn (isPLCellOn_id_of_isPLBall hr) ψ hψ
    isOpen_interior hK hKP hfix
  have hψP : ψ '' (u '' P) = u '' P :=
    image_eq_of_homeomorph_eqOn_compl_of_subset ψ hfix (hKP.trans interior_subset)
  let τ := Function.invFunOn u P
  have hleft : LeftInvOn τ u P := hu.injOn.leftInvOn_invFunOn
  have hright : RightInvOn τ u (u '' P) := hu.injOn.bijOn_image.invOn_invFunOn.2
  have hψsP : MapsTo ψ.symm (u '' P) (u '' P) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hψP.symm.subset hx
    rw [← hyx, ψ.symm_apply_apply]
    exact hy
  have hgleft : LeftInvOn (τ ∘ ψ.symm) (ψ ∘ u) P := by
    intro x hx
    change τ (ψ.symm (ψ (u x))) = x
    rw [ψ.symm_apply_apply]
    exact hleft hx
  have hg : IsPLOn 3 3 (τ ∘ ψ.symm) (u '' P) := by
    have hg := hψu.isPLOn_inverse hgleft
    rwa [image_comp, hψP] at hg
  have hmap : MapsTo (τ ∘ ψ.symm) (u '' P) P :=
    hu.injOn.bijOn_image.surjOn.mapsTo_invFunOn.comp hψsP
  have hinv : IsPLOn 3 3 ψ.symm (u '' P) := (hu.isPLOn.comp_of_mapsTo hg hmap).congr
    (fun x hx => (hright (hψsP hx)).symm)
  exact hinv.mono_of_isOpen isOpen_interior interior_subset

end DifferentialGeometry.Topology.PiecewiseLinear
