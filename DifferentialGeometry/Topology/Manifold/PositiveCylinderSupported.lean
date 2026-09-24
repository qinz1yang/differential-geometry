import DifferentialGeometry.Topology.Manifold.TruncatedCylinderAnnulus
import DifferentialGeometry.Topology.Manifold.CylinderAnnulusSupported

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Pos : TopologicalSpace.Opens SphereCylinder :=
  ⟨univ ×ˢ Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

theorem exists_supported_diffeomorph_matching_positive_cylinder_sphere
    (σ : S2 → Pos) (hσ : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (range σ))
    (hleft : range σ ⊆ closure p.left) (hright : range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    {ρ a b : ℝ} (ha : 0 < a) (hρa : ρ < a) (hab : a < b)
    (hlow : ∀ q : Pos, q.val.2 < b → q ∈ p.left)
    (hdepth : ∀ q : S2, b < (σ q).val.2) :
    ∃ (F : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      (∀ q : S2, F (η q,a) = (σ q).val) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
        EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ :=
    exists_smooth_truncated_positive_cylinder_lower_annulus σ hσ p hleft hright hK ha hab hlow hdepth
  have heρ : ∀ q ∈ e.target, ρ < q.2 := by
    intro q hq
    rw [het] at hq
    exact hρa.trans_le hq.2.2
  obtain ⟨F,hF,K,hKc,hKρ,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_matching_cylinder_annulus_ends e hes he hei ρ heρ
  refine ⟨F,η,?_,K,hKc,hKρ,hfix,hfixi⟩
  intro q
  rw [← h₀ (η q),hF,h₁]

end DifferentialGeometry.Topology.Manifold
