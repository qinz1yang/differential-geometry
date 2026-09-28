import DifferentialGeometry.Topology.Manifold.CylinderCollar.CoorientedExtension
import DifferentialGeometry.Topology.Manifold.SphereDegreeReflection
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingFromOpen

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

private abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

theorem exists_signed_supported_collar_matching_of_sphere
    (φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (hη : sphereDiffeomorphDegree η = 1)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : univ ×ˢ Icc (-R) R ⊆ φ.source)
    (hzero : ∀ p : S2, F₀ (η p,a) = φ (p,0))
    (hdepth : ∀ q ∈ univ ×ˢ Icc (-R) R, ρ < (φ q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ univ ×ˢ Ioi ρ)
    (hfix₀ : EqOn F₀ id K₀ᶜ) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F (q.1,a + q.2) = φ (q.1,σ * q.2)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  let T : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder :=
    Diffeomorph.fiberwiseAffine (fun _ => a) (fun _ => 1)
      contMDiff_const contMDiff_const (fun _ => one_ne_zero)
  let A := (φ.trans F₀.symm.toPartialDiffeomorph).trans T.symm.toPartialDiffeomorph
  have hAs : univ ×ˢ Icc (-R) R ⊆ A.source :=
    fun q hq => ⟨⟨hsource hq,mem_univ _⟩,mem_univ _⟩
  have hAq (q : SphereCylinder) : A q = ((F₀.symm (φ q)).1,(F₀.symm (φ q)).2-a) := by
    change ((F₀.symm (φ q)).1,((F₀.symm (φ q)).2-a) / 1) = _
    rw [div_one]
  have hA0 (p : S2) : A (p,0) = (η p,0) := by
    rw [hAq,← hzero,F₀.symm_apply_apply,sub_self]
  have hlow (q : SphereCylinder) (hq : q ∈ univ ×ˢ Icc (-R) R) : ρ-a < (A q).2 := by
    have hFi : ρ < (F₀.symm (φ q)).2 := by
      by_contra hn
      have hh : F₀.symm (φ q) ∉ K₀ := fun hm => (not_lt_of_ge (le_of_not_gt hn)) (hK₀ρ hm).2
      have h := hfix₀ hh
      have heq : F₀.symm (φ q) = φ q := h.symm.trans (F₀.apply_symm_apply _)
      rw [heq] at hn
      exact hn (hdepth q hq)
    rw [hAq]
    exact sub_lt_sub_right hFi a
  have hAc : IsCompact (A '' (univ ×ˢ Icc (-R) R)) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn (A.contMDiffOn_toFun.continuousOn.mono hAs)
  obtain ⟨C,hC⟩ := hAc.bddAbove_image continuous_snd.continuousOn
  let u := max C R + 1
  have hAu : A '' (univ ×ˢ Icc (-R) R) ⊆ univ ×ˢ Ioo (ρ-a) u := by
    rintro q ⟨z,hz,rfl⟩
    refine ⟨mem_univ _,hlow z hz,?_⟩
    have hh := hC (mem_image_of_mem Prod.snd (mem_image_of_mem A hz))
    exact hh.trans_lt (lt_of_le_of_lt (le_max_left C R) (lt_add_one _))
  obtain ⟨σ,hσ,G,hG,hG0,K,hK,hKU,hfix,hfixi⟩ :=
    exists_signed_supported_compact_collar_extension A η hη hr hrR
      (by linarith) (lt_of_le_of_lt (le_max_right C R) (lt_add_one _)) hAs hA0 hAu
  let F := ((T.symm.trans G).trans T).trans F₀
  have hF (q : SphereCylinder) (hq : |q.2| ≤ r) : F (q.1,a+q.2) = φ (q.1,σ*q.2) := by
    have hTq : T.symm (q.1,a+q.2) = q := by
      change (q.1,(a+q.2-a) / 1) = q
      simp only [div_one,add_sub_cancel_left,Prod.mk.eta]
    change F₀ (T (G (T.symm (q.1,a+q.2)))) = _
    rw [hTq,hG q hq]
    change F₀ (T (T.symm (F₀.symm (φ (q.1,σ*q.2))))) = _
    rw [T.apply_symm_apply,F₀.apply_symm_apply]
  have hKT : T '' K ⊆ univ ×ˢ Ioi ρ := by
    rintro q ⟨z,hz,rfl⟩
    refine ⟨mem_univ _,?_⟩
    change ρ < a+1*z.2
    have hh := (hKU hz).2.1
    linarith
  have hFfix (q : SphereCylinder) (hq : q ∉ K₀ ∪ T '' K) : F q = q := by
    have hn₀ : q ∉ K₀ := fun h => hq (Or.inl h)
    have hnK : T.symm q ∉ K := fun h => hq (Or.inr ⟨T.symm q,h,T.apply_symm_apply q⟩)
    change F₀ (T (G (T.symm q))) = q
    rw [hfix hnK,id_eq,T.apply_symm_apply,hfix₀ hn₀]
    rfl
  refine ⟨σ,hσ,F,hF,K₀ ∪ T '' K,hK₀.union (hK.image T.continuous),union_subset hK₀ρ hKT,hFfix,?_⟩
  intro q hq
  exact (F.toEquiv.symm_apply_eq).2 (hFfix q hq).symm


private theorem exists_partialDiffeomorph_of_open_cylinder_embedding
    (U : TopologicalSpace.Opens SphereCylinder) (x₀ : U)
    (f : U → SphereCylinder) (hf : IsSmoothEmbedding SphereCylinderModel SphereCylinderModel ∞ f) :
    ∃ φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞,
      φ.source = U ∧ φ.target = range f ∧ ∀ q : U, φ q.val = f q := by
  have hlocal : IsLocalDiffeomorph SphereCylinderModel SphereCylinderModel ∞ f :=
    isLocalDiffeomorph_of_injective_mfderiv f hf.contMDiff
      (fun q => (hf.isImmersion.isImmersionAt q).injective_mfderiv (by simp)) rfl
  let V := hlocal.image
  let e := diffeomorphOntoImage f hlocal hf.isEmbedding.injective
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph SphereCylinderModel U ⟨x₀⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph SphereCylinderModel V ⟨e x₀⟩
  let φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hiU : iU.target = (U : Set SphereCylinder) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hiV : iV.target = (V : Set SphereCylinder) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  refine ⟨φ,?_,?_,?_⟩
  · ext q
    change ((q ∈ iU.target ∧ iU.symm q ∈ (univ : Set U)) ∧ e (iU.symm q) ∈ (univ : Set V)) ↔ q ∈ U
    simp only [mem_univ,and_true,hiU]
    rfl
  · ext q
    change (q ∈ iV.target ∧ (iV.symm q ∈ (univ : Set V) ∧ e.symm (iV.symm q) ∈ (univ : Set U))) ↔ q ∈ range f
    simp only [mem_univ,and_self,and_true,hiV]
    rfl
  · intro q
    have hq := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply SphereCylinderModel U ⟨x₀⟩ q.property
    change (e (iU.symm q.val)).val = f q
    rw [hq]
    rfl


theorem exists_reflected_supported_collar_matching_of_sphere
    (φ : PartialDiffeomorph SphereCylinderModel SphereCylinderModel SphereCylinder SphereCylinder ∞)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : univ ×ˢ Icc (-R) R ⊆ φ.source)
    (hzero : ∀ p : S2, F₀ (η p,a) = φ (p,0))
    (hdepth : ∀ q ∈ univ ×ˢ Icc (-R) R, ρ < (φ q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ univ ×ˢ Ioi ρ)
    (hfix₀ : EqOn F₀ id K₀ᶜ) :
    ∃ (β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (σ : ℝ),
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r → F (q.1,a + q.2) = φ (β q.1,σ * q.2)) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  have hβ : ∃ β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2,
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      sphereDiffeomorphDegree (β.trans η) = 1 := by
    rcases sphereDiffeomorphDegree_eq_one_or_neg_one η with h | h
    · refine ⟨Diffeomorph.refl (𝓡 2) S2 ∞,Or.inl rfl,?_⟩
      have heq : (Diffeomorph.refl (𝓡 2) S2 ∞).trans η = η := by ext p; rfl
      rw [heq]
      exact h
    · exact ⟨sphereAntipodalDiffeomorph (n := 2),Or.inr rfl,
        sphereDiffeomorphDegree_pre_antipodal_eq_one η h⟩
  obtain ⟨β,hβ,hdeg⟩ := hβ
  let D := β.prodCongr (Diffeomorph.refl 𝓘(ℝ) ℝ ∞)
  let ψ := D.toPartialDiffeomorph.trans φ
  have hs : univ ×ˢ Icc (-R) R ⊆ ψ.source :=
    fun q hq => ⟨mem_univ _,hsource ⟨mem_univ _,hq.2⟩⟩
  have hz (p : S2) : F₀ ((β.trans η) p,a) = ψ (p,0) := hzero (β p)
  have hd : ∀ q ∈ univ ×ˢ Icc (-R) R, ρ < (ψ q).2 :=
    fun q hq => hdepth (β q.1,q.2) ⟨mem_univ _,hq.2⟩
  obtain ⟨σ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_signed_supported_collar_matching_of_sphere ψ F₀ (β.trans η) hdeg hr hrR hρa
      hs hz hd K₀ hK₀ hK₀ρ hfix₀
  exact ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩


theorem exists_reflected_supported_collar_matching_of_embedding
    (U : TopologicalSpace.Opens SphereCylinder)
    (f : U → SphereCylinder) (hf : IsSmoothEmbedding SphereCylinderModel SphereCylinderModel ∞ f)
    (F₀ : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder)
    (η : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2)
    {r R ρ a : ℝ} (hr : 0 < r) (hrR : r < R) (hρa : ρ + R < a)
    (hsource : univ ×ˢ Icc (-R) R ⊆ (U : Set SphereCylinder))
    (hz : ∀ p : S2, (p,(0 : ℝ)) ∈ (U : Set SphereCylinder))
    (hzero : ∀ p : S2, F₀ (η p,a) = f ⟨(p,0),hz p⟩)
    (hdepth : ∀ q : U, q.val ∈ univ ×ˢ Icc (-R) R → ρ < (f q).2)
    (K₀ : Set SphereCylinder) (hK₀ : IsCompact K₀) (hK₀ρ : K₀ ⊆ univ ×ˢ Ioi ρ)
    (hfix₀ : EqOn F₀ id K₀ᶜ) :
    ∃ (β : S2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S2) (σ : ℝ),
      (β = Diffeomorph.refl (𝓡 2) S2 ∞ ∨ β = sphereAntipodalDiffeomorph (n := 2)) ∧
      (σ = 1 ∨ σ = -1) ∧
      ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel, SphereCylinderModel⟯ SphereCylinder,
        (∀ q : SphereCylinder, |q.2| ≤ r →
          ∃ hq : (β q.1,σ*q.2) ∈ U, F (q.1,a+q.2) = f ⟨(β q.1,σ*q.2),hq⟩) ∧
        ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
          EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  obtain ⟨φ,hφs,hφt,hφ⟩ := exists_partialDiffeomorph_of_open_cylinder_embedding U ⟨(v,0),hz v⟩ f hf
  have hs : univ ×ˢ Icc (-R) R ⊆ φ.source := hφs.symm ▸ hsource
  have hzero' (p : S2) : F₀ (η p,a) = φ (p,0) := (hzero p).trans (hφ ⟨(p,0),hz p⟩).symm
  have hdepth' : ∀ q ∈ univ ×ˢ Icc (-R) R, ρ < (φ q).2 := by
    intro q hq
    rw [hφ ⟨q,hsource hq⟩]
    exact hdepth ⟨q,hsource hq⟩ hq
  obtain ⟨β,σ,hβ,hσ,F,hF,K,hK,hKρ,hfix,hfixi⟩ :=
    exists_reflected_supported_collar_matching_of_sphere φ F₀ η hr hrR hρa hs hzero' hdepth' K₀ hK₀ hK₀ρ hfix₀
  refine ⟨β,σ,hβ,hσ,F,?_,K,hK,hKρ,hfix,hfixi⟩
  intro q hq
  have hσabs : |σ*q.2| = |q.2| := by rcases hσ with h | h <;> simp [h]
  have hqR : (β q.1,σ*q.2) ∈ univ ×ˢ Icc (-R) R :=
    ⟨mem_univ _,abs_le.mp (hσabs ▸ hq.trans hrR.le)⟩
  exact ⟨hsource hqR,(hF q hq).trans (hφ ⟨_,hsource hqR⟩)⟩


end DifferentialGeometry.Topology.Manifold
