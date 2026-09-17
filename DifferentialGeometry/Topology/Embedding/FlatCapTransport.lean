import DifferentialGeometry.Topology.Homeomorph.CylinderCap

open Set Metric

namespace Homeomorph

theorem exists_cylinderCap_replacement_flattening
    {X Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [ProperSpace E] {e f g : X → Y} (Ψ : (E × ℝ) ≃ₜ Y)
    {a b R : ℝ} (ha : a ≠ 0) (hab : |a| < b) (hR : 1 < R)
    {D : Set X} (χ : E → X) (hχD : χ '' closedBall (0 : E) 1 = D)
    (hcap : ∀ x ∈ closedBall (0 : E) 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap a x))
    (hflat : ∀ x ∈ closedBall (0 : E) 1, g (χ x) = Ψ (x, 0))
    (hfix : EqOn f e Dᶜ) (hgfix : EqOn g e Dᶜ)
    (hside : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Dᶜ → ‖p.1‖ = 1 ∧ 0 ≤ a * p.2) :
    ∃ Φ : Y ≃ₜ Y, Φ ∘ f = g ∧ EqOn Φ id (e '' Dᶜ) ∧
      ∃ C : Set Y, IsCompact C ∧ C ⊆ Ψ '' (ball (0 : E) R ×ˢ Ioo (-b) b) ∧
        EqOn Φ id Cᶜ ∧ EqOn Φ.symm id Cᶜ := by
  classical
  obtain ⟨H, hHcap, hHwall, C, hC, hCU, hHfix, hHifix⟩ :=
    exists_cylinderCap_flattening (E := E) ha hab hR
  let Φ := Ψ.symm.trans (H.trans Ψ)
  have hretained : EqOn Φ id (e '' Dᶜ) := by
    rintro z ⟨x, hx, rfl⟩
    let p := Ψ.symm (e x)
    have hHp : H p = p := by
      by_cases hp : p ∈ C
      · have hs := hside p (hCU hp) ⟨x, hx, (Ψ.apply_symm_apply (e x)).symm⟩
        exact hHwall p hs.1 hs.2
      · exact hHfix hp
    change Ψ (H p) = e x
    rw [hHp]
    exact Ψ.apply_symm_apply (e x)
  refine ⟨Φ, ?_, hretained, Ψ '' C, hC.image Ψ.continuous, image_mono hCU, ?_, ?_⟩
  · funext x
    by_cases hx : x ∈ D
    · obtain ⟨y, hy, rfl⟩ := hχD.symm.subset hx
      change Ψ (H (Ψ.symm (f (χ y)))) = g (χ y)
      rw [hcap y hy, Ψ.symm_apply_apply, hHcap y hy, hflat y hy]
    · change Φ (f x) = g x
      rw [hfix hx, hgfix hx]
      exact hretained (mem_image_of_mem e hx)
  · intro y hy
    have hp : Ψ.symm y ∉ C := fun hp => hy ⟨Ψ.symm y, hp, Ψ.apply_symm_apply y⟩
    change Ψ (H (Ψ.symm y)) = y
    rw [hHfix hp, id_eq, Ψ.apply_symm_apply]
  · intro y hy
    have hp : Ψ.symm y ∉ C := fun hp => hy ⟨Ψ.symm y, hp, Ψ.apply_symm_apply y⟩
    change Ψ (H.symm (Ψ.symm y)) = y
    rw [hHifix hp, id_eq, Ψ.apply_symm_apply]

end Homeomorph
