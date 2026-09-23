import DifferentialGeometry.Topology.Manifold.CylinderCollar.Compression

set_option autoImplicit false
noncomputable section

open Set Function Manifold Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_supported_diffeomorph_eq_on_compact_cylinder_collar_of_germ
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    {r R ε : ℝ} (hr : 0 < r) (hrR : r < R) (hε : 0 < ε)
    (hsource : univ ×ˢ Icc (-R) R ⊆ A.source)
    (G : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (hG : ∀ q : SphereCylinder, |q.2| < ε → G q = A q)
    (U : Set SphereCylinder) (hband : univ ×ˢ Icc (-R) R ⊆ U)
    (himage : A '' (univ ×ˢ Icc (-R) R) ⊆ U)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀band : K₀ ⊆ U)
    (hGfix : EqOn G id K₀ᶜ) (hGfixi : EqOn G.symm id K₀ᶜ) :
    ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → F q = A q) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ U ∧
        EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  classical
  have hR : 0 < R := hr.trans hrR
  obtain ⟨C, hC, K, hK, hKR, hCfix, hCfixi⟩ :=
    exists_supported_cylinder_compression hr hrR (lt_min hε hR)
  have hKs : K ⊆ A.source := by
    intro q hq
    have hqR := (hKR hq).2
    exact hsource ⟨mem_univ _, hqR.1.le, hqR.2.le⟩
  obtain ⟨H, _, _, hHeq, hAK, _, hHfix⟩ :=
    A.exists_diffeomorph_family_extension (IP := 𝓘(ℝ)) (fun _ : ℝ => C)
      (C.contMDiff.comp contMDiff_snd) (C.symm.contMDiff.comp contMDiff_snd)
      hK hKs (fun _ q hq => hCfix hq)
  have hHtrack (q : SphereCylinder) (hq : q ∈ A.source) : H 0 (A q) = A (C q) := by
    rw [(hHeq 0 (A q)).1]
    have htarget : A q ∈ A.target := A.map_source hq
    change (if A q ∈ A.target then A (C (A.symm (A q))) else A q) = _
    rw [if_pos htarget]
    exact congrArg (fun x => A (C x)) (A.left_inv hq)
  let F := (C.trans G).trans (H 0).symm
  have hmatch (q : SphereCylinder) (hq : |q.2| ≤ r) : F q = A q := by
    have hqsource : q ∈ A.source := hsource ⟨mem_univ _,
      (neg_le_neg hrR.le).trans (abs_le.mp hq).1, (abs_le.mp hq).2.trans hrR.le⟩
    have hsmall := hC q hq
    have hCG : G (C q) = A (C q) := hG (C q) (hsmall.trans_le (min_le_left _ _))
    change (H 0).symm (G (C q)) = _
    rw [hCG, ← hHtrack q hqsource, Diffeomorph.symm_apply_apply]
  have hKband : K ⊆ U := by
    intro q hq
    exact hband ⟨mem_univ _,(hKR hq).2.1.le,(hKR hq).2.2.le⟩
  have hAKband : A '' K ⊆ U := by
    apply (image_mono ?_).trans himage
    intro q hq
    exact ⟨mem_univ _, (hKR hq).2.1.le, (hKR hq).2.2.le⟩
  refine ⟨F, hmatch, K ∪ K₀ ∪ A '' K, (hK.union hK₀).union hAK,
    union_subset (union_subset hKband hK₀band) hAKband, ?_, ?_⟩
  · intro q hq
    have hnK : q ∉ K := fun hx => hq (Or.inl (Or.inl hx))
    have hnK₀ : q ∉ K₀ := fun hx => hq (Or.inl (Or.inr hx))
    have hnAK : q ∉ A '' K := fun hx => hq (Or.inr hx)
    change (H 0).symm (G (C q)) = q
    rw [hCfix hnK, id_eq, hGfix hnK₀, id_eq, (hHfix 0 q hnAK).2]
  · intro q hq
    have hnK : q ∉ K := fun hx => hq (Or.inl (Or.inl hx))
    have hnK₀ : q ∉ K₀ := fun hx => hq (Or.inl (Or.inr hx))
    have hnAK : q ∉ A '' K := fun hx => hq (Or.inr hx)
    change C.symm (G.symm (H 0 q)) = q
    rw [(hHfix 0 q hnAK).1, hGfixi hnK₀, id_eq, hCfixi hnK]
    rfl


theorem exists_supported_diffeomorph_eq_on_compact_cylinder_collar
    (A : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    {r R l u : ℝ} (hr : 0 < r) (hrR : r < R) (hlR : l < -R) (hRu : R < u)
    (hsource : univ ×ˢ Icc (-R) R ⊆ A.source)
    (hfixed : ∀ p : S2, A (p, 0) = (p, 0))
    (hside : ∀ q ∈ A.source, q.2 ≤ 0 → (A q).2 ≤ 0)
    (himage : A '' (univ ×ˢ Icc (-R) R) ⊆ univ ×ˢ Ioo l u) :
    ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
      (∀ q : SphereCylinder, |q.2| ≤ r → F q = A q) ∧
      (∀ p : S2, F (p, 0) = (p, 0)) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioo l u ∧
        EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  have hR : 0 < R := hr.trans hrR
  have hzsource (p : S2) : (p, (0 : ℝ)) ∈ A.source :=
    hsource ⟨mem_univ _,by constructor <;> linarith⟩
  obtain ⟨ε,hε,G,hG,hGzero,hGtail,K₀,hK₀,hK₀band,hGfix,hGfixi⟩ :=
    exists_supported_diffeomorph_eq_on_cylinder_collar A hzsource hfixed hside l u
      (by linarith) (by linarith)
  obtain ⟨F,hF,K,hK,hKU,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_eq_on_compact_cylinder_collar_of_germ A hr hrR hε hsource G
      (fun q hq => (hG q.1 q.2 hq).2) (univ ×ˢ Ioo l u)
      (fun q hq => ⟨mem_univ _,hlR.trans_le hq.2.1,hq.2.2.trans_lt hRu⟩)
      himage K₀ hK₀ hK₀band hGfix hGfixi
  exact ⟨F,hF,fun p => (hF (p,0) (by simpa using hr.le)).trans (hfixed p),K,hK,hKU,hfix,hfixi⟩

end DifferentialGeometry.Topology.Manifold
