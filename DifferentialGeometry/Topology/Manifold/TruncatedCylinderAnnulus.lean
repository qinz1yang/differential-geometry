import DifferentialGeometry.Topology.Manifold.PositiveCylinderAnnulus
import DifferentialGeometry.Topology.SphereSeparation.PositiveProductTruncation

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev Pos : TopologicalSpace.Opens SphereCylinder :=
  ⟨univ ×ˢ Ioi (0 : ℝ),isOpen_univ.prod isOpen_Ioi⟩

theorem exists_smooth_truncated_positive_cylinder_lower_annulus
    (σ : S2 → Pos) (hσ : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ σ)
    (p : SphereSeparation.ComplementPair (range σ))
    (hleft : range σ ⊆ closure p.left) (hright : range σ ⊆ closure p.right)
    (hK : IsCompact (closure ((Subtype.val : Pos → SphereCylinder) '' p.left)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hlow : ∀ q : Pos, q.val.2 < b → q ∈ p.left)
    (hdepth : ∀ q : S2, b < (σ q).val.2) :
    ∃ (e : PartialEquiv (S2 × unitInterval) SphereCylinder)
      (η : Diffeomorph (𝓡 2) (𝓡 2) S2 S2 ∞),
      e.source = univ ∧
      e.target = closure ((Subtype.val : Pos → SphereCylinder) '' p.left) ∩ (univ ×ˢ Ici a) ∧
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e ∧
      ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm e.target ∧
      (∀ q : S2, e (q,0) = (q,a)) ∧ ∀ q : S2, e (η q,1) = (σ q).val := by
  let : ConnectedSpace S2 := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1))
  let B := (Subtype.val : Pos → SphereCylinder) '' p.left
  let K := closure B ∩ (univ ×ˢ Ici a)
  have hBo : IsOpen B := Pos.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ p.isOpen_left
  have hiB : interior (closure B) = B :=
    SphereSeparation.interior_closure_image_subtype_val_positive_product
      (p.interior_closure_left_eq hleft hright)
  have hband : univ ×ˢ Ioo (0 : ℝ) b ⊆ B := by
    intro q hq
    exact ⟨⟨q,mem_univ _,hq.2.1⟩,hlow _ hq.2.2,rfl⟩
  have hKi : interior K = B ∩ (univ ×ˢ Ioi a) := by
    rw [show K = closure B ∩ (univ ×ˢ Ici a) from rfl,interior_inter,hiB,
      interior_prod_eq,interior_univ,interior_Ici]
  have hKr : closure (interior K) = K := by
    rw [hKi]
    exact SphereSeparation.closure_inter_positive_product_tail ha hab hband
  have hKconn : IsPreconnected (interior K) := by
    rw [hKi]
    exact SphereSeparation.isPreconnected_inter_positive_product_tail
      (p.isConnected_left.isPreconnected.image Subtype.val continuous_subtype_val.continuousOn) ha hab hband
  have hKc : IsCompact K := hK.inter_right (isClosed_univ.prod isClosed_Ici)
  have hfB : frontier B = range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,(0 : ℝ))) := by
    have h := SphereSeparation.frontier_image_subtype_val_positive_product p
      (p.frontier_left_eq hleft) b (ha.trans hab) hlow
    rw [← range_comp] at h
    convert h using 1 <;> rfl
  have hfK : frontier K = range (fun q : S2 => (σ q).val) ∪
      range (fun q : S2 => (q,a)) := by
    rw [frontier,hKc.isClosed.closure_eq,hKi]
    ext q
    constructor
    · rintro ⟨⟨hqB,hqa⟩,hqn⟩
      rcases (show a ≤ q.2 from hqa.2).eq_or_lt with hqa | hqa
      · exact Or.inr ⟨q.1,Prod.ext rfl hqa⟩
      · have hqnot : q ∉ B := fun hq => hqn ⟨hq,mem_univ _,hqa⟩
        have hfq : q ∈ frontier B := by rw [hBo.frontier_eq]; exact ⟨hqB,hqnot⟩
        rw [hfB] at hfq
        rcases hfq with hS | ⟨x,hx⟩
        · exact Or.inl hS
        · have h := congrArg Prod.snd hx
          exfalso
          change 0 = q.2 at h
          linarith
    · rintro (⟨x,rfl⟩ | ⟨x,rfl⟩)
      · have hσcl : (σ x).val ∈ closure B :=
          image_closure_subset_closure_image continuous_subtype_val ⟨σ x,hleft (mem_range_self x),rfl⟩
        refine ⟨⟨hσcl,mem_univ _,(hab.trans (hdepth x)).le⟩,?_⟩
        rintro ⟨⟨z,hz,hzx⟩,_⟩
        exact p.left_disjoint_sphere.le_bot ⟨(Subtype.val_injective hzx) ▸ hz,mem_range_self x⟩
      · refine ⟨⟨subset_closure (hband ⟨mem_univ _,ha,hab⟩),mem_univ _,show a ≤ a from le_rfl⟩,?_⟩
        exact fun h => (lt_irrefl a) h.2.2
  have hs : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (σ q).val) :=
    isSmoothEmbedding_fromOpen (𝓡 2) SphereCylinderModel Pos σ hσ
  have hz : IsSmoothEmbedding (𝓡 2) SphereCylinderModel ∞ (fun q : S2 => (q,a)) := by
    have hid : IsSmoothEmbedding (𝓡 2) (𝓡 2) ∞
        (Prod.fst ∘ fun q : S2 => (q,a)) := IsSmoothEmbedding.id
    exact hid.of_comp (J := SphereCylinderModel) (by simp)
      (contMDiff_id.prodMk contMDiff_const) contMDiff_fst
  have hd : Disjoint (range (fun q : S2 => (σ q).val)) (range (fun q : S2 => (q,a))) := by
    rw [disjoint_left]
    rintro q ⟨x,hx⟩ ⟨y,hy⟩
    have h := congrArg Prod.snd (hx.trans hy.symm)
    change (σ x).val.2 = a at h
    linarith [hdepth x]
  obtain ⟨e,η,hes,het,he,hei,h₀,h₁⟩ := exists_smooth_cylinder_annulus_parametrization
    hKc hKr hKconn _ _ hz hs (hfK.trans (union_comm _ _)) hd.symm
  exact ⟨e,η,hes,het,he,het.symm ▸ hei,h₀,h₁⟩

end DifferentialGeometry.Topology.Manifold
