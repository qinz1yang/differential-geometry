import DifferentialGeometry.Topology.Manifold.AnnulusAmbientIsotopy
import DifferentialGeometry.Topology.Manifold.CylinderCollar.Germ

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

open private cylindricalConjugate cylindricalConjugate_apply from
  DifferentialGeometry.Topology.Manifold.CylinderCollar.Germ

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

theorem exists_supported_diffeomorph_matching_cylinder_annulus_ends
    (e : PartialEquiv (S2 × unitInterval) SphereCylinder) (hes : e.source = univ)
    (he : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) SphereCylinderModel ∞ e)
    (hei : ContMDiffOn SphereCylinderModel ((𝓡 2).prod (𝓡∂ 1)) ∞ e.symm e.target)
    (ρ : ℝ) (hetρ : ∀ q ∈ e.target, ρ < q.2) :
    ∃ F : SphereCylinder ≃ₘ⟮SphereCylinderModel,SphereCylinderModel⟯ SphereCylinder,
      (∀ p : S2, F (e (p,0)) = e (p,1)) ∧
      ∃ K : Set SphereCylinder, IsCompact K ∧ K ⊆ univ ×ˢ Ioi ρ ∧
        EqOn F id Kᶜ ∧ EqOn F.symm id Kᶜ := by
  let v : S2 := ⟨EuclideanSpace.single 0 1,by simp⟩
  let C := cylinderExponentialChart v
  have hCs : C.source = univ := cylinderExponentialChart_source v
  let ec := e.trans C.toPartialEquiv
  have hecs : ec.source = univ := by
    ext p
    change (p ∈ e.source ∧ e p ∈ C.source) ↔ p ∈ univ
    simp only [hes,hCs,mem_univ,and_self]
  have hect : ec.target = C '' e.target := by
    ext x
    constructor
    · rintro ⟨hx,hxe⟩
      exact ⟨C.symm x,hxe,C.right_inv hx⟩
    · rintro ⟨q,hq,rfl⟩
      refine ⟨C.map_source (hCs ▸ mem_univ q),?_⟩
      change C.symm (C q) ∈ e.target
      erw [C.left_inv (hCs ▸ mem_univ q)]
      exact hq
  have hec : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ ec := by
    apply contMDiffOn_univ.mp
    exact C.contMDiffOn_toFun.comp he.contMDiffOn (fun p _ => hCs ▸ mem_univ (e p))
  have heci : ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡∂ 1)) ∞ ec.symm ec.target :=
    hei.comp (C.contMDiffOn_invFun.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
  let U := {x : E3 | Real.exp ρ < ‖x‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hetU : ec.target ⊆ U := by
    rw [hect]
    rintro x ⟨q,hq,rfl⟩
    change Real.exp ρ < ‖C q‖
    rw [norm_cylinderExponentialChart]
    exact Real.exp_lt_exp.mpr (hetρ q hq)
  obtain ⟨G,hG,K,hK,hKU,hfix,hfixi⟩ :=
    exists_supported_diffeomorph_matching_annulus_ends ec hecs hec heci hU hetU
  have hG0 : G 0 = 0 := hfix (by
    intro h
    have hx := hKU h
    change Real.exp ρ < ‖(0 : E3)‖ at hx
    simpa using (lt_trans (Real.exp_pos ρ) hx))
  let F := cylindricalConjugate v G hG0
  have hmatch (p : S2) : F (e (p,0)) = e (p,1) := by
    apply C.toPartialEquiv.injective_of_source_eq_univ hCs
    rw [cylindricalConjugate_apply]
    exact hG p
  let K' := C.symm '' K
  have hKtarget : K ⊆ C.target := by
    intro x hx
    rw [cylinderExponentialChart_target]
    change x ≠ 0
    have h := (Real.exp_pos ρ).trans (hKU hx)
    exact norm_pos_iff.mp h
  have hK' : IsCompact K' := hK.image_of_continuousOn
    (C.contMDiffOn_invFun.continuousOn.mono hKtarget)
  have hK'ρ : K' ⊆ univ ×ˢ Ioi ρ := by
    rintro q ⟨x,hx,rfl⟩
    refine ⟨mem_univ _,?_⟩
    have hnorm : ‖x‖ = Real.exp (C.symm x).2 := by
      rw [← norm_cylinderExponentialChart v (C.symm x)]
      exact congrArg norm (C.right_inv (hKtarget hx)).symm
    have hh := hKU hx
    change Real.exp ρ < ‖x‖ at hh
    rw [hnorm] at hh
    exact Real.exp_lt_exp.mp hh
  have hFfix (q : SphereCylinder) (hq : q ∉ K') : F q = q := by
    have hCq : C q ∉ K := by
      intro h
      exact hq ⟨C q,h,C.left_inv (hCs ▸ mem_univ q)⟩
    apply C.toPartialEquiv.injective_of_source_eq_univ hCs
    rw [cylindricalConjugate_apply,hfix hCq]
    rfl
  refine ⟨F,hmatch,K',hK',hK'ρ,hFfix,?_⟩
  intro q hq
  apply F.injective
  exact (F.apply_symm_apply q).trans (hFfix q hq).symm

end DifferentialGeometry.Topology.Manifold
