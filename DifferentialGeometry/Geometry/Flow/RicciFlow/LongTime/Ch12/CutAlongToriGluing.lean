import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongToriCarrier
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Decomposition

set_option autoImplicit false
noncomputable section
open Set Function Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

section Param

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] {F : CollaredTorusFamily_C2a N}

/-- Collar parameter of the side `ε = ±1` at height `h ≥ 0`: `ε (1/2 + h/2)`. -/
def sideParam_C2a (ε h : ℝ) : ℝ := ε * (1/2 + h/2)

theorem sideParam_mem_source_C2a {ε h : ℝ} (hε : ε = 1 ∨ ε = -1) (t : Torus) (h0 : 0 ≤ h)
    (h1 : h < 1) : (t, sideParam_C2a ε h) ∈ signedCollarSource := by
  rcases hε with rfl | rfl <;> exact ⟨by simp only [sideParam_C2a]; linarith,
    by simp only [sideParam_C2a]; linarith⟩

theorem sideParam_abs_C2a {ε h : ℝ} (hε : ε = 1 ∨ ε = -1) (h0 : 0 ≤ h) :
    1/2 ≤ |sideParam_C2a ε h| := by
  rcases hε with rfl | rfl
  · simp only [sideParam_C2a]; rw [abs_of_nonneg (by linarith)]; linarith
  · simp only [sideParam_C2a]; rw [abs_of_nonpos (by linarith)]; linarith

theorem sideParam_zero_C2a {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    sideParam_C2a ε 0 = 1/2 ∨ sideParam_C2a ε 0 = -1/2 := by
  rcases hε with rfl | rfl
  · left; simp [sideParam_C2a]
  · right; simp [sideParam_C2a]; norm_num

end Param

section SideCollar

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (i : Fin F.count) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)

include hε in
theorem sideMem_C2a (t : Torus) {h : ℝ} (h0 : 0 ≤ h) (h1 : h < 1) :
    F.collar i (t, sideParam_C2a ε h) ∈ cutSet_C2a F :=
  collar_mem_cutSet_C2a i (sideParam_mem_source_C2a hε t h0 h1) (sideParam_abs_C2a hε h0)

/-- The torus `σ_i(·, ε/2)` as a map into the cut carrier. -/
def sideTorus_C2a (t : Torus) : ↥(cutSet_C2a F) :=
  ⟨F.collar i (t, sideParam_C2a ε 0), sideMem_C2a F i hε t le_rfl zero_lt_one⟩

/-- The forward map of the side half collar. -/
def sideFun_C2a (p : Torus × EuclideanHalfSpace 1) : ↥(cutSet_C2a F) :=
  if hp : p.2.val 0 < 1 then
    ⟨F.collar i (p.1, sideParam_C2a ε (p.2.val 0)), sideMem_C2a F i hε p.1 p.2.2 hp⟩
  else sideTorus_C2a F i hε p.1

/-- The inverse map of the side half collar. -/
def sideInv_C2a (x : ↥(cutSet_C2a F)) : Torus × EuclideanHalfSpace 1 :=
  (((F.collar i).symm x.1).1, halfSpaceOneLift (2 * (ε * ((F.collar i).symm x.1).2) - 1))

/-- The open target of the side half collar: `K ∩ σ_i(T² × {1/4 < ε s < 1})`. -/
def sideTarget_C2a : Set ↥(cutSet_C2a F) :=
  {x | x.1 ∈ F.collar i '' (univ ×ˢ {s : ℝ | 1/4 < ε * s ∧ ε * s < 1})}

theorem halfSpaceOneLift_val_C2a (t : ℝ) : (halfSpaceOneLift t).val 0 = max t 0 := rfl

theorem halfSpaceOneLift_coord_C2a (h : EuclideanHalfSpace 1) : halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  ext j
  rw [Subsingleton.elim j 0]
  change max (h.val 0) 0 = h.val 0
  exact max_eq_left h.2

include hε in
theorem sideTarget_param_C2a {x : ↥(cutSet_C2a F)} (hx : x ∈ sideTarget_C2a (ε := ε) F i) :
    (F.collar i).symm x.1 ∈ signedCollarSource ∧ F.collar i ((F.collar i).symm x.1) = x.1 ∧
      1/2 ≤ ε * ((F.collar i).symm x.1).2 ∧ ε * ((F.collar i).symm x.1).2 < 1 := by
  obtain ⟨q, ⟨-, h1, h2⟩, hq⟩ := hx
  have hqs : q ∈ signedCollarSource := by
    rcases hε with rfl | rfl <;> exact ⟨by linarith, by linarith⟩
  have hqsrc : q ∈ (F.collar i).source := by rw [F.source_eq]; exact hqs
  have hsymm : (F.collar i).symm x.1 = q := by
    rw [← hq]; exact (F.collar i).left_inv hqsrc
  rw [hsymm]
  refine ⟨hqs, hq, ?_, h2⟩
  have hK : x.1 ∈ cutSet_C2a F := x.2
  have hnot : ¬ (-1/2 < q.2 ∧ q.2 < 1/2) := by
    rw [← collar_mem_tubeOpen_iff_C2a i hqs, hq]
    intro h; exact (mem_compl_iff _ _).mp hK (mem_iUnion.mpr ⟨i, h⟩)
  rcases hε with rfl | rfl
  · simp only [one_mul] at h1 h2 ⊢
    by_contra hc; exact hnot ⟨by linarith, by linarith⟩
  · simp only [neg_mul, one_mul] at h1 h2 ⊢
    by_contra hc; exact hnot ⟨by linarith, by linarith⟩

include hε in
theorem eps_mul_sideParam_C2a (h : ℝ) : ε * sideParam_C2a ε h = 1/2 + h/2 := by
  rcases hε with rfl | rfl <;> simp only [sideParam_C2a] <;> ring

include hε in
theorem sideParam_inv_C2a (s : ℝ) : sideParam_C2a ε (2 * (ε * s) - 1) = s := by
  rcases hε with rfl | rfl <;> simp only [sideParam_C2a] <;> ring

theorem sideFun_val_C2a {p : Torus × EuclideanHalfSpace 1} (hp : p.2.val 0 < 1) :
    (sideFun_C2a F i hε p).1 = F.collar i (p.1, sideParam_C2a ε (p.2.val 0)) := by
  unfold sideFun_C2a; rw [dite_eq_left hp]

include hε in
theorem sideTarget_subset_target_C2a {x : ↥(cutSet_C2a F)}
    (hx : x ∈ sideTarget_C2a (ε := ε) F i) : x.1 ∈ (F.collar i).target := by
  obtain ⟨q, hq, hqx⟩ := hx
  rw [← hqx]
  refine (F.collar i).map_source (by rw [F.source_eq]; obtain ⟨-, h1, h2⟩ := hq; rcases hε with rfl | rfl <;> exact ⟨by linarith, by linarith⟩)

/-- The open partial homeomorphism underlying the side half collar. -/
def sideHomeo_C2a : OpenPartialHomeomorph (Torus × EuclideanHalfSpace 1) ↥(cutSet_C2a F) where
  toFun := sideFun_C2a F i hε
  invFun := sideInv_C2a F i (ε := ε)
  source := halfCollarSource
  target := sideTarget_C2a (ε := ε) F i
  map_source' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    refine ⟨(p.1, sideParam_C2a ε (p.2.val 0)), ⟨trivial, ?_, ?_⟩, ?_⟩
    · change 1/4 < ε * sideParam_C2a ε (p.2.val 0)
      rw [eps_mul_sideParam_C2a hε]; have := p.2.2; change 0 ≤ p.2.val 0 at this; linarith
    · change ε * sideParam_C2a ε (p.2.val 0) < 1
      rw [eps_mul_sideParam_C2a hε]; linarith
    · rw [sideFun_val_C2a F i hε hp']
  map_target' := by
    intro x hx
    obtain ⟨-, -, h1, h2⟩ := sideTarget_param_C2a F i hε hx
    change (halfSpaceOneLift _).val 0 < 1
    rw [halfSpaceOneLift_val_C2a]
    exact max_lt (by linarith) one_pos
  left_inv' := by
    intro p hp
    have hp' : p.2.val 0 < 1 := hp
    have h0 : 0 ≤ p.2.val 0 := p.2.2
    have hs := sideParam_mem_source_C2a hε p.1 h0 hp'
    have hs' : (p.1, sideParam_C2a ε (p.2.val 0)) ∈ (F.collar i).source := by
      rw [F.source_eq]; exact hs
    change sideInv_C2a F i (sideFun_C2a F i hε p) = p
    unfold sideInv_C2a
    have hl : (F.collar i).symm.toPartialEquiv ((F.collar i).toPartialEquiv (p.1, sideParam_C2a ε (p.2.val 0))) = (p.1, sideParam_C2a ε (p.2.val 0)) := (F.collar i).left_inv hs'
    rw [sideFun_val_C2a F i hε hp']
    simp only [hl]
    refine Prod.ext rfl ?_
    change halfSpaceOneLift (2 * (ε * sideParam_C2a ε (p.2.val 0)) - 1) = p.2
    rw [eps_mul_sideParam_C2a hε]
    have : 2 * (1/2 + p.2.val 0 / 2) - 1 = p.2.val 0 := by ring
    rw [this]; exact halfSpaceOneLift_coord_C2a p.2
  right_inv' := by
    intro x hx
    obtain ⟨hqs, hq, h1, h2⟩ := sideTarget_param_C2a F i hε hx
    set q := (F.collar i).symm x.1 with hqdef
    have hlift : (halfSpaceOneLift (2 * (ε * q.2) - 1)).val 0 = 2 * (ε * q.2) - 1 := by
      rw [halfSpaceOneLift_val_C2a]; exact max_eq_left (by linarith)
    have hlt : (halfSpaceOneLift (2 * (ε * q.2) - 1)).val 0 < 1 := by rw [hlift]; linarith
    apply Subtype.ext
    have hinv : sideInv_C2a F i (ε := ε) x = (q.1, halfSpaceOneLift (2 * (ε * q.2) - 1)) := rfl
    rw [hinv, sideFun_val_C2a F i hε (p := (q.1, halfSpaceOneLift (2 * (ε * q.2) - 1))) hlt]
    change F.collar i (q.1, sideParam_C2a ε ((halfSpaceOneLift (2 * (ε * q.2) - 1)).val 0)) = x.1
    rw [hlift, sideParam_inv_C2a hε]
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
    have hρ : Continuous (fun p : Torus × EuclideanHalfSpace 1 =>
        ((p.1, sideParam_C2a ε (p.2.val 0)) : Torus × ℝ)) := by
      refine continuous_fst.prodMk ?_
      have hc : Continuous (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) :=
        (EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)
      exact continuous_const.mul (continuous_const.add (hc.div_const 2))
    have h1 : ContinuousOn (fun p : Torus × EuclideanHalfSpace 1 =>
        F.collar i (p.1, sideParam_C2a ε (p.2.val 0))) halfCollarSource := by
      refine ContinuousOn.comp (g := F.collar i) (F.collar i).toOpenPartialHomeomorph.continuousOn
        hρ.continuousOn ?_
      intro p hp
      have hp' : p.2.val 0 < 1 := hp
      have h0 : 0 ≤ p.2.val 0 := p.2.2
      change _ ∈ (F.collar i).source
      rw [F.source_eq]; exact sideParam_mem_source_C2a hε p.1 h0 hp'
    refine h1.congr ?_
    intro p hp
    exact sideFun_val_C2a F i hε hp
  continuousOn_invFun := by
    have hsym : ContinuousOn (fun x : ↥(cutSet_C2a F) => (F.collar i).symm x.1)
        (sideTarget_C2a (ε := ε) F i) :=
      (F.collar i).symm.toOpenPartialHomeomorph.continuousOn.comp
        continuous_subtype_val.continuousOn
        (fun x hx => sideTarget_subset_target_C2a F i hε hx)
    refine hsym.fst.prodMk ?_
    refine ContinuousOn.comp (g := halfSpaceOneLift) contMDiffOn_halfSpaceOneLift.continuousOn
      (continuousOn_const.mul hsym.snd |>.const_smul (2 : ℝ) |>.sub continuousOn_const) ?_
    intro x hx
    obtain ⟨-, -, h1, -⟩ := sideTarget_param_C2a F i hε hx
    change 0 ≤ 2 * (ε * ((F.collar i).symm x.1).2) - 1
    linarith

/-- **The side half collar** `(t, u) ↦ σ_i(t, ε (1/2 + u/2))` of the cut carrier, as a partial
diffeomorphism from `T² × [0,1)`. -/
def sideCollar_C2a : PartialDiffeomorph halfCollarModel (cutCarrier_C2a F).model
    (Torus × EuclideanHalfSpace 1) (cutCarrier_C2a F).Carrier ∞ :=
  { sideHomeo_C2a F i hε with
    contMDiffOn_toFun := by
      refine ((cutAtlas_C2a F).contMDiffOn_iff_subtype_val _ _).mpr ?_
      have hcoord : ContMDiff halfCollarModel 𝓘(ℝ, ℝ) ∞
          (fun p : Torus × EuclideanHalfSpace 1 => p.2.val 0) :=
        contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
      have hρ : ContMDiff halfCollarModel signedCollarModel ∞
          (fun p : Torus × EuclideanHalfSpace 1 =>
            ((p.1, sideParam_C2a ε (p.2.val 0)) : Torus × ℝ)) := by
        refine contMDiff_fst.prodMk ?_
        exact ((contDiff_const.mul (contDiff_const.add (contDiff_id.div_const 2))).contMDiff
          (f := fun r : ℝ => ε * (1/2 + r/2))).comp hcoord
      have h1 : ContMDiffOn halfCollarModel (𝓡 3) ∞
          (fun p : Torus × EuclideanHalfSpace 1 =>
            F.collar i (p.1, sideParam_C2a ε (p.2.val 0))) halfCollarSource := by
        refine ContMDiffOn.comp (g := F.collar i) (F.collar i).contMDiffOn hρ.contMDiffOn ?_
        intro p hp
        have hp' : p.2.val 0 < 1 := hp
        have h0 : 0 ≤ p.2.val 0 := p.2.2
        change _ ∈ (F.collar i).source
        rw [F.source_eq]; exact sideParam_mem_source_C2a hε p.1 h0 hp'
      refine h1.congr ?_
      intro p hp
      exact sideFun_val_C2a F i hε hp
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
          (fun x : ↥(cutSet_C2a F) => 2 * (ε * ((F.collar i).symm x.1).2) - 1)
          (sideTarget_C2a (ε := ε) F i) :=
        ((contDiff_const.mul (contDiff_const.mul contDiff_id)).sub contDiff_const).contMDiff.comp_contMDiffOn
          (contMDiff_snd.comp_contMDiffOn hsym)
      refine ContMDiffOn.comp (g := halfSpaceOneLift) contMDiffOn_halfSpaceOneLift h2 ?_
      intro x hx
      obtain ⟨-, -, h1, -⟩ := sideTarget_param_C2a F i hε hx
      change 0 ≤ 2 * (ε * ((F.collar i).symm x.1).2) - 1
      linarith }

theorem sideCollar_source_C2a : (sideCollar_C2a F i hε).source = halfCollarSource := rfl

theorem sideCollar_zero_C2a (t : Torus) :
    sideCollar_C2a F i hε (t, halfZero) = sideTorus_C2a F i hε t := by
  apply Subtype.ext
  change (sideFun_C2a F i hε (t, halfZero)).1 = _
  rw [sideFun_val_C2a F i hε (p := (t, halfZero)) (by change (0:ℝ) < 1; norm_num)]
  rfl

theorem sideCollar_val_C2a {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (sideCollar_C2a F i hε p).1 = F.collar i (p.1, sideParam_C2a ε (p.2.val 0)) :=
  sideFun_val_C2a F i hε hp

include hε in
theorem sideTorus_val_C2a (t : Torus) : (sideTorus_C2a F i hε t).1 =
    F.collar i (t, sideParam_C2a ε 0) := rfl

theorem continuous_sideTorus_C2a : Continuous (sideTorus_C2a F i hε) := by
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous (fun t : Torus => ((t, sideParam_C2a ε 0) : Torus × ℝ)) :=
    continuous_id.prodMk continuous_const
  refine ContinuousOn.comp_continuous (F.collar i).toOpenPartialHomeomorph.continuousOn h1 ?_
  intro t
  change _ ∈ (F.collar i).source
  rw [F.source_eq]; exact sideParam_mem_source_C2a hε t le_rfl zero_lt_one

theorem injective_sideTorus_C2a : Function.Injective (sideTorus_C2a F i hε) := by
  intro t t' h
  have h1 : F.collar i (t, sideParam_C2a ε 0) = F.collar i (t', sideParam_C2a ε 0) :=
    congrArg Subtype.val h
  have hs := fun t : Torus => show (t, sideParam_C2a ε 0) ∈ (F.collar i).source by
    rw [F.source_eq]; exact sideParam_mem_source_C2a hε t le_rfl zero_lt_one
  have := (F.collar i).toOpenPartialHomeomorph.injOn (hs t) (hs t') h1
  exact (Prod.ext_iff.mp this).1

/-- The cut torus on the side `ε`, as a subset of the cut carrier. -/
def sideSet_C2a : Set ↥(cutSet_C2a F) := range (sideTorus_C2a F i hε)

/-- Homeomorphism of the model torus onto the side torus. -/
def sideParamHomeo_C2a : Torus ≃ₜ sideSet_C2a F i hε :=
  ((continuous_sideTorus_C2a F i hε).isClosedEmbedding (injective_sideTorus_C2a F i hε)).isEmbedding.toHomeomorph

theorem sideParamHomeo_val_C2a (t : Torus) :
    ((sideParamHomeo_C2a F i hε) t).1 = sideTorus_C2a F i hε t := rfl

end SideCollar

section Gluing

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)

theorem hL_C2a : ((-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1) := Or.inr rfl
theorem hR_C2a : ((1 : ℝ) = 1 ∨ (1 : ℝ) = -1) := Or.inl rfl

theorem sideSet_val_C2a (i : Fin F.count) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {x : ↥(cutSet_C2a F)}
    (hx : x ∈ sideSet_C2a F i hε) : ∃ t, x.1 = F.collar i (t, ε / 2) := by
  obtain ⟨t, rfl⟩ := hx
  refine ⟨t, ?_⟩
  rcases hε with rfl | rfl <;> simp [sideTorus_C2a, sideParam_C2a]; try norm_num

theorem sideSet_disjoint_C2a (i : Fin F.count) :
    Disjoint (sideSet_C2a F i (hL_C2a)) (sideSet_C2a F i (hR_C2a)) := by
  rw [Set.disjoint_left]
  rintro x ⟨t, rfl⟩ ⟨t', h⟩
  have h1 : F.collar i (t', sideParam_C2a 1 0) = F.collar i (t, sideParam_C2a (-1) 0) :=
    congrArg Subtype.val h
  have hs : ∀ (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (t : Torus),
      (t, sideParam_C2a ε 0) ∈ (F.collar i).source := fun ε hε t => by
    rw [F.source_eq]; exact sideParam_mem_source_C2a hε t le_rfl zero_lt_one
  have := (F.collar i).toOpenPartialHomeomorph.injOn (hs 1 hR_C2a t') (hs (-1) hL_C2a t) h1
  have h2 := (Prod.ext_iff.mp this).2
  simp [sideParam_C2a] at h2
  norm_num at h2

theorem sideSet_closed_C2a (i : Fin F.count) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsClosed (sideSet_C2a F i hε) :=
  (isCompact_range (continuous_sideTorus_C2a F i hε)).isClosed

theorem sideSet_subset_target_C2a (i : Fin F.count) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    {x : ↥(cutSet_C2a F)} (hx : x ∈ sideSet_C2a F i hε) : x.1 ∈ (F.collar i).target := by
  obtain ⟨t, rfl⟩ := hx
  exact (F.collar i).map_source (by rw [F.source_eq]; exact sideParam_mem_source_C2a hε t le_rfl zero_lt_one)

theorem sideSet_blocks_disjoint_C2a {i j : Fin F.count} (hij : i ≠ j) :
    Disjoint (sideSet_C2a F i hL_C2a ∪ sideSet_C2a F i hR_C2a)
      (sideSet_C2a F j hL_C2a ∪ sideSet_C2a F j hR_C2a) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  have hi : x.1 ∈ (F.collar i).target := by
    rcases hx with h | h
    · exact sideSet_subset_target_C2a F i hL_C2a h
    · exact sideSet_subset_target_C2a F i hR_C2a h
  have hj : x.1 ∈ (F.collar j).target := by
    rcases hx' with h | h
    · exact sideSet_subset_target_C2a F j hL_C2a h
    · exact sideSet_subset_target_C2a F j hR_C2a h
  exact (Set.disjoint_left.mp (F.disjoint hij)) hi hj

/-- **S2: the gluing data.** The cut carrier with its `count` pairs of boundary tori
`σ_i(·, -1/2)` (left) and `σ_i(·, 1/2)` (right), matched by the identity of the model torus. -/
def cutGluing_C2a : TorusGluing (cutCarrier_C2a F) where
  count := F.count
  gluing :=
    { left := fun i => sideSet_C2a F i hL_C2a
      right := fun i => sideSet_C2a F i hR_C2a
      attaching := fun i => (sideParamHomeo_C2a F i hL_C2a).symm.trans (sideParamHomeo_C2a F i hR_C2a)
      isClosed_left := fun i => sideSet_closed_C2a F i hL_C2a
      isClosed_right := fun i => sideSet_closed_C2a F i hR_C2a
      disjoint_left_right := fun i => sideSet_disjoint_C2a F i
      disjoint_blocks := fun i j hij => sideSet_blocks_disjoint_C2a F hij }
  leftParam := fun i => sideParamHomeo_C2a F i hL_C2a
  rightParam := fun i => sideParamHomeo_C2a F i hR_C2a
  matching := fun _ => Diffeomorph.refl torusModel Torus ∞
  matching_eq := fun i t => by
    change (sideParamHomeo_C2a F i hR_C2a) ((sideParamHomeo_C2a F i hL_C2a).symm
      ((sideParamHomeo_C2a F i hL_C2a) t)) = (sideParamHomeo_C2a F i hR_C2a) t
    rw [Homeomorph.symm_apply_apply]
  torusOrientation := fun _ => GC.Seifert.productTorusOrientation
  leftCollar := fun i => sideCollar_C2a F i hL_C2a
  rightCollar := fun i => sideCollar_C2a F i hR_C2a
  left_source := fun i => rfl
  right_source := fun i => rfl
  left_zero := fun i t => by
    rw [sideCollar_zero_C2a]; rfl
  right_zero := fun i t => by
    rw [sideCollar_zero_C2a]; rfl
  boundary_exhausted := by
    ext x
    rw [cutIncl_boundary_iff_C2a F x, Set.mem_iUnion]
    constructor
    · rintro ⟨i, ⟨t, ht⟩ | ⟨t, ht⟩⟩
      · exact ⟨i, Or.inr ⟨t, Subtype.ext (by rw [ht]; simp [sideTorus_C2a, sideParam_C2a])⟩⟩
      · exact ⟨i, Or.inl ⟨t, Subtype.ext (by rw [ht]; simp [sideTorus_C2a, sideParam_C2a]; norm_num)⟩⟩
    · rintro ⟨i, h | h⟩
      · obtain ⟨t, ht⟩ := sideSet_val_C2a F i hL_C2a h
        exact ⟨i, Or.inr ⟨t, by rw [ht]⟩⟩
      · obtain ⟨t, ht⟩ := sideSet_val_C2a F i hR_C2a h
        exact ⟨i, Or.inl ⟨t, by rw [ht]⟩⟩

theorem cutGluing_count_C2a : (cutGluing_C2a F).count = F.count := rfl

/-- Left collar value in the original collar coordinate: `σ_i(t, -(1/2 + u/2))`. -/
theorem cutGluing_leftCollar_val_C2a (i : Fin F.count) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    ((cutGluing_C2a F).leftCollar i p).1 = F.collar i (p.1, -(1/2 + p.2.val 0 / 2)) := by
  change (sideCollar_C2a F i hL_C2a p).1 = _
  rw [sideCollar_val_C2a F i hL_C2a hp]; simp [sideParam_C2a]

theorem cutGluing_rightCollar_val_C2a (i : Fin F.count) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    ((cutGluing_C2a F).rightCollar i p).1 = F.collar i (p.1, 1/2 + p.2.val 0 / 2) := by
  change (sideCollar_C2a F i hR_C2a p).1 = _
  rw [sideCollar_val_C2a F i hR_C2a hp]; simp [sideParam_C2a]

end Gluing

end GC.LongTime.Ch12
