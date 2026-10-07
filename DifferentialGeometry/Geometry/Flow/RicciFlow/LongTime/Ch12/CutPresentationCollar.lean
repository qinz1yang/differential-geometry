import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongToriGluing
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationStretch

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section Param

/-- Collar parameter of the side `ε = ±1` at height `h ≥ 0`: `ε ψ(h)`. -/
def sideParam_S12 (ε h : ℝ) : ℝ := ε * psi_S12 h

theorem sideParam_mem_source_S12 {ε h : ℝ} (hε : ε = 1 ∨ ε = -1) (t : Torus) (h0 : 0 ≤ h)
    (h1 : h < 1) : (t, sideParam_S12 ε h) ∈ signedCollarSource := by
  have a := half_le_psi_S12 h0
  have b := psi_lt_one_S12 h1
  rcases hε with rfl | rfl <;> exact ⟨by simp only [sideParam_S12]; linarith,
    by simp only [sideParam_S12]; linarith⟩

theorem sideParam_abs_S12 {ε h : ℝ} (hε : ε = 1 ∨ ε = -1) (h0 : 0 ≤ h) :
    1/2 ≤ |sideParam_S12 ε h| := by
  have a := half_le_psi_S12 h0
  rcases hε with rfl | rfl
  · simp only [sideParam_S12]; rw [abs_of_nonneg (by linarith)]; linarith
  · simp only [sideParam_S12]; rw [abs_of_nonpos (by linarith)]; linarith

theorem sideParam_zero_S12 (ε : ℝ) : sideParam_S12 ε 0 = ε * (1/2 + 0/2) := by
  simp only [sideParam_S12, psi_zero_S12]; ring

theorem eps_mul_sideParam_S12 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (h : ℝ) :
    ε * sideParam_S12 ε h = psi_S12 h := by
  rcases hε with rfl | rfl <;> simp only [sideParam_S12] <;> ring

theorem sideParam_inv_S12 {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (s : ℝ) :
    sideParam_S12 ε (rho_S12 (ε * s)) = s := by
  rw [sideParam_S12, psi_rho_S12]
  rcases hε with rfl | rfl <;> ring

end Param

section SideCollar

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (i : Fin F.count) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)

include hε in
theorem sideMem_S12 (t : Torus) {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    F.collar i (t, sideParam_S12 ε h) ∈ cutSet_C2a F :=
  collar_mem_cutSet_C2a i (sideParam_mem_source_S12 hε t h0 h1) (sideParam_abs_S12 hε h0)

/-- The forward map of the side half collar. -/
def sideFun_S12 (p : Torus × EuclideanHalfSpace 1) : ↥(cutSet_C2a F) :=
  if hp : p.2.val 0 < 1 then
    ⟨F.collar i (p.1, sideParam_S12 ε (p.2.val 0)), sideMem_S12 F i hε p.1 p.2.2 hp⟩
  else sideTorus_C2a F i hε p.1

/-- The inverse map of the side half collar. -/
def sideInv_S12 (x : ↥(cutSet_C2a F)) : Torus × EuclideanHalfSpace 1 :=
  (((F.collar i).symm x.1).1, halfSpaceOneLift (rho_S12 (ε * ((F.collar i).symm x.1).2)))

theorem sideFun_val_S12 {p : Torus × EuclideanHalfSpace 1} (hp : p.2.val 0 < 1) :
    (sideFun_S12 F i hε p).1 = F.collar i (p.1, sideParam_S12 ε (p.2.val 0)) := by
  unfold sideFun_S12; rw [dite_eq_left hp]

/-- The open partial homeomorphism underlying the side half collar. -/
def sideHomeo_S12 : OpenPartialHomeomorph (Torus × EuclideanHalfSpace 1) ↥(cutSet_C2a F) where
  toFun := sideFun_S12 F i hε
  invFun := sideInv_S12 F i (ε := ε)
  source := halfCollarSource
  target := sideTarget_C2a (ε := ε) F i
  map_source' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    have h0 : 0 ≤ p.2.val 0 := p.2.2
    have a := half_le_psi_S12 h0
    have b := psi_lt_one_S12 hp'
    refine ⟨(p.1, sideParam_S12 ε (p.2.val 0)), ⟨trivial, ?_, ?_⟩, ?_⟩
    · change 1/4 < ε * sideParam_S12 ε (p.2.val 0)
      rw [eps_mul_sideParam_S12 hε]; linarith
    · change ε * sideParam_S12 ε (p.2.val 0) < 1
      rw [eps_mul_sideParam_S12 hε]; exact b
    · rw [sideFun_val_S12 F i hε hp']
  map_target' := by
    intro x hx
    obtain ⟨-, -, h1, h2⟩ := sideTarget_param_C2a F i hε hx
    change (halfSpaceOneLift _).val 0 < 1
    rw [halfSpaceOneLift_val_C2a]
    exact max_lt (rho_lt_one_S12 h2) one_pos
  left_inv' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    have h0 : 0 ≤ p.2.val 0 := p.2.2
    have hs := sideParam_mem_source_S12 hε p.1 h0 hp'
    have hs' : (p.1, sideParam_S12 ε (p.2.val 0)) ∈ (F.collar i).source := by
      rw [F.source_eq]; exact hs
    change sideInv_S12 F i (sideFun_S12 F i hε p) = p
    unfold sideInv_S12
    have hl : (F.collar i).symm.toPartialEquiv ((F.collar i).toPartialEquiv (p.1, sideParam_S12 ε (p.2.val 0))) = (p.1, sideParam_S12 ε (p.2.val 0)) := (F.collar i).left_inv hs'
    rw [sideFun_val_S12 F i hε hp']
    simp only [hl]
    refine Prod.ext rfl ?_
    change halfSpaceOneLift (rho_S12 (ε * sideParam_S12 ε (p.2.val 0))) = p.2
    rw [eps_mul_sideParam_S12 hε, rho_psi_S12]
    exact halfSpaceOneLift_coord_C2a p.2
  right_inv' := by
    intro x hx
    obtain ⟨hqs, hq, h1, h2⟩ := sideTarget_param_C2a F i hε hx
    set q := (F.collar i).symm x.1 with hqdef
    have hlift : (halfSpaceOneLift (rho_S12 (ε * q.2))).val 0 = rho_S12 (ε * q.2) := by
      rw [halfSpaceOneLift_val_C2a]; exact max_eq_left (rho_nonneg_S12 h1)
    have hlt : (halfSpaceOneLift (rho_S12 (ε * q.2))).val 0 < 1 := by
      rw [hlift]; exact rho_lt_one_S12 h2
    apply Subtype.ext
    have hinv : sideInv_S12 F i (ε := ε) x = (q.1, halfSpaceOneLift (rho_S12 (ε * q.2))) := rfl
    rw [hinv, sideFun_val_S12 F i hε (p := (q.1, halfSpaceOneLift (rho_S12 (ε * q.2)))) hlt]
    change F.collar i (q.1, sideParam_S12 ε ((halfSpaceOneLift (rho_S12 (ε * q.2))).val 0)) = x.1
    rw [hlift, sideParam_inv_S12 hε]
    exact hq
  open_source := isOpen_lt ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)) continuous_const
  open_target := by
    have : sideTarget_C2a (ε := ε) F i =
        Subtype.val ⁻¹' (F.collar i '' (univ ×ˢ {s : ℝ | 1/4 < ε * s ∧ ε * s < 1})) := rfl
    rw [this]
    refine IsOpen.preimage continuous_subtype_val ?_
    refine (F.collar i).toOpenPartialHomeomorph.isOpen_image_of_subset_source ?_ ?_
    · exact isOpen_univ.prod (isOpen_lt continuous_const (continuous_const.mul continuous_id) |>.inter
        (isOpen_lt (continuous_const.mul continuous_id) continuous_const))
    · change _ ⊆ (F.collar i).source
      rw [F.source_eq]
      rintro ⟨t, s⟩ ⟨-, h1, h2⟩
      rcases hε with rfl | rfl <;> exact ⟨by simp at h1 h2 ⊢; linarith, by simp at h1 h2 ⊢; linarith⟩
  continuousOn_toFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    have hc : Continuous (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) :=
      (EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)
    have hρ : Continuous (fun p : Torus × EuclideanHalfSpace 1 =>
        ((p.1, sideParam_S12 ε (p.2.val 0)) : Torus × ℝ)) := by
      refine continuous_fst.prodMk ?_
      exact continuous_const.mul (contDiff_psi_S12.continuous.comp hc)
    have h1 : ContinuousOn (fun p : Torus × EuclideanHalfSpace 1 =>
        F.collar i (p.1, sideParam_S12 ε (p.2.val 0))) halfCollarSource := by
      refine ContinuousOn.comp (g := F.collar i) (F.collar i).toOpenPartialHomeomorph.continuousOn
        hρ.continuousOn ?_
      intro p hp
      have hp' : p.2.val 0 < 1 := hp
      have h0 : 0 ≤ p.2.val 0 := p.2.2
      change _ ∈ (F.collar i).source
      rw [F.source_eq]; exact sideParam_mem_source_S12 hε p.1 h0 hp'
    refine h1.congr ?_
    intro p hp
    exact sideFun_val_S12 F i hε hp
  continuousOn_invFun := by
    have hsym : ContinuousOn (fun x : ↥(cutSet_C2a F) => (F.collar i).symm x.1)
        (sideTarget_C2a (ε := ε) F i) :=
      (F.collar i).symm.toOpenPartialHomeomorph.continuousOn.comp
        continuous_subtype_val.continuousOn
        (fun x hx => sideTarget_subset_target_C2a F i hε hx)
    refine hsym.fst.prodMk ?_
    refine ContinuousOn.comp (g := halfSpaceOneLift) contMDiffOn_halfSpaceOneLift.continuousOn
      (contDiff_rho_S12.continuous.comp_continuousOn (continuousOn_const.mul hsym.snd)) ?_
    intro x hx
    obtain ⟨-, -, h1, -⟩ := sideTarget_param_C2a F i hε hx
    exact rho_nonneg_S12 h1

/-- **The side half collar** `(t, u) ↦ σ_i(t, ε ψ(u))` of the cut carrier, as a partial
diffeomorphism from `T² × [0,1)`. -/
def sideCollar_S12 : PartialDiffeomorph halfCollarModel (cutCarrier_C2a F).model
    (Torus × EuclideanHalfSpace 1) (cutCarrier_C2a F).Carrier ∞ :=
  { sideHomeo_S12 F i hε with
    contMDiffOn_toFun := by
      refine ((cutAtlas_C2a F).contMDiffOn_iff_subtype_val _ _).mpr ?_
      have hcoord : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) ∞
          (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) :=
        contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
      have hρ : ContMDiff halfCollarModel signedCollarModel ∞
          (fun p : Torus × EuclideanHalfSpace 1 =>
            ((p.1, sideParam_S12 ε (p.2.val 0)) : Torus × ℝ)) := by
        refine contMDiff_fst.prodMk ?_
        exact ((contDiff_const.mul contDiff_psi_S12).contMDiff
          (f := fun r : ℝ => ε * psi_S12 r)).comp hcoord
      have h1 : ContMDiffOn halfCollarModel (𝓡 3) ∞
          (fun p : Torus × EuclideanHalfSpace 1 =>
            F.collar i (p.1, sideParam_S12 ε (p.2.val 0))) halfCollarSource := by
        refine ContMDiffOn.comp (g := F.collar i) (F.collar i).contMDiffOn hρ.contMDiffOn ?_
        intro p hp
        have hp' : p.2.val 0 < 1 := hp
        have h0 : 0 ≤ p.2.val 0 := p.2.2
        change _ ∈ (F.collar i).source
        rw [F.source_eq]; exact sideParam_mem_source_S12 hε p.1 h0 hp'
      refine h1.congr ?_
      intro p hp
      exact sideFun_val_S12 F i hε hp
    contMDiffOn_invFun := by
      let _ : ChartedSpace (EuclideanHalfSpace 3) ↥(cutSet_C2a F) := (cutAtlas_C2a F).toChartedSpace
      have hval : ContMDiff (𝓡∂ 3) (𝓡 3) ∞
          (Subtype.val : ↥(cutSet_C2a F) → M.Carrier) :=
        (cutAtlas_C2a F).contMDiff_subtype_val
      have hsym : ContMDiffOn (𝓡∂ 3) signedCollarModel ∞
          (fun x : ↥(cutSet_C2a F) => (F.collar i).symm x.1) (sideTarget_C2a (ε := ε) F i) :=
        ContMDiffOn.comp (g := (F.collar i).symm) (F.collar i).symm.contMDiffOn
          hval.contMDiffOn (fun x hx => sideTarget_subset_target_C2a F i hε hx)
      refine ContMDiffOn.prodMk (contMDiff_fst.comp_contMDiffOn hsym) ?_
      have h2 : ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞
          (fun x : ↥(cutSet_C2a F) => rho_S12 (ε * ((F.collar i).symm x.1).2))
          (sideTarget_C2a (ε := ε) F i) :=
        (contDiff_rho_S12.contMDiff).comp_contMDiffOn
          ((contDiff_const.mul contDiff_id).contMDiff.comp_contMDiffOn
            (contMDiff_snd.comp_contMDiffOn hsym))
      refine ContMDiffOn.comp (g := halfSpaceOneLift) contMDiffOn_halfSpaceOneLift h2 ?_
      intro x hx
      obtain ⟨-, -, h1, -⟩ := sideTarget_param_C2a F i hε hx
      exact rho_nonneg_S12 h1 }

theorem sideCollar_source_S12 : (sideCollar_S12 F i hε).source = halfCollarSource := rfl

theorem sideCollar_val_S12 {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (sideCollar_S12 F i hε p).1 = F.collar i (p.1, ε * psi_S12 (p.2.val 0)) :=
  sideFun_val_S12 F i hε hp

theorem sideCollar_zero_S12 (t : Torus) :
    sideCollar_S12 F i hε (t, halfZero) = sideTorus_C2a F i hε t := by
  apply Subtype.ext
  change (sideFun_S12 F i hε (t, halfZero)).1 = _
  rw [sideFun_val_S12 F i hε (p := (t, halfZero)) (by change (0:ℝ) < 1; norm_num)]
  change F.collar i (t, sideParam_S12 ε 0) = F.collar i (t, sideParam_C2a ε 0)
  rw [sideParam_zero_S12]; rfl

end SideCollar

end GC.LongTime.Ch12
