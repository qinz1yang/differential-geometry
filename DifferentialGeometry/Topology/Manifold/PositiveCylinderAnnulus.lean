import DifferentialGeometry.Topology.Manifold.CylinderAnnulus
import DifferentialGeometry.Topology.SphereSeparation.PositiveProductFrontier
import DifferentialGeometry.Topology.Embedding.Factor
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Pos : TopologicalSpace.Opens SphereCylinder :=
  ⟨univ ×ˢ Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

theorem exists_smooth_positive_cylinder_lower_annulus
    (σ : S2 → Pos) (hσ : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (range σ))
    (hleft : range σ ⊆ closure p.left) (hright : range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    (a : ℝ) (ha : 0 < a) (hlow : ∀ q : Pos, q.val.2 < a → q ∈ p.left) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = univ ∧ e.target = closure ((Subtype.val : Pos → SphereCylinder) '' p.left) ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm e.target ∧
      (∀ q : S2, e (q,0) = (q,0)) ∧ ∀ q : S2, e (η q,1) = (σ q).val := by
  let B := (Subtype.val : Pos → SphereCylinder) '' p.left
  have hi : interior (closure B) = B :=
    SphereSeparation.interior_closure_image_subtype_val_positive_product
      (p.interior_closure_left_eq hleft hright)
  have hBo : IsOpen B := Pos.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ p.isOpen_left
  have hreg : closure (interior (closure B)) = closure B := by rw [hi]
  have hconn : IsPreconnected (interior (closure B)) := by
    rw [hi]
    exact p.isConnected_left.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn
  have hf : frontier (closure B) = range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,(0 : ℝ))) := by
    rw [frontier,closure_closure,hi,← hBo.frontier_eq]
    change frontier ((Subtype.val : Pos → SphereCylinder) '' p.left) = _
    have h := SphereSeparation.frontier_image_subtype_val_positive_product p
      (p.frontier_left_eq hleft) a ha hlow
    rw [← range_comp] at h
    convert h using 1 <;> rfl
  have hs : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (σ q).val) :=
    isSmoothEmbedding_fromOpen (𝓡 2) SphereCylinderModel Pos σ hσ
  have hz : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (q,(0 : ℝ))) := by
    have hid : IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : S2 => (q,(0 : ℝ))) := IsSmoothEmbedding.id
    exact hid.of_comp (J := SphereCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hd : Disjoint (range (fun q : S2 => (σ q).val))
      (range (fun q : S2 => (q,(0 : ℝ)))) := by
    rw [disjoint_left]
    rintro q ⟨x,hx⟩ ⟨y,hy⟩
    have h := congrArg Prod.snd (hx.trans hy.symm)
    exact (ne_of_gt (σ x).property.2) h
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ := exists_smooth_cylinder_annulus_parametrization
    hK hreg hconn _ _ hz hs (hf.trans (union_comm _ _)) hd.symm
  exact ⟨e,η,hes,het,he,het.symm ▸ hei,h₀,h₁⟩

end DifferentialGeometry.Topology.Manifold
