import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutAlongToriCarrier
import DifferentialGeometry.Topology.Manifold.HalfLine

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
    change (sideFun_C2a F i hε (sideInv_C2a F i (ε := ε) x)).1 = x.1
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
    sorry
  continuousOn_invFun := by
    sorry

end SideCollar

end GC.LongTime.Ch12
