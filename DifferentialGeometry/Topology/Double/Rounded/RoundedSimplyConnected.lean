import DifferentialGeometry.Topology.Double.Rounded.RoundedCollar
import DifferentialGeometry.Topology.Homotopy.SimplyConnectedUnion

namespace DifferentialGeometry.Topology

open Set _root_.Topology unitInterval
open scoped ContinuousMap

namespace CollaredHeight

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {f : Y → ℝ} {η : ℝ}

noncomputable def lowerHomotopyEquiv (hf : Continuous f) (hη : 0 < η)
    (Φ : Z × Icc (-η) η ≃ₜ (f ⁻¹' Icc (-η) η))
    (hΦ : ∀ p, f (Φ p).1 = p.2.1) :
    {y : Y | f y < η} ≃ₕ {y : Y | f y ≤ 0} := by
  classical
  let U := {y : Y | f y < η}
  let A : Set (I × U) := {p | f p.2.1 ≤ 0}
  let B : Set (I × U) := {p | 0 ≤ f p.2.1}
  have hheight : Continuous (fun p : I × U => f p.2.1) :=
    hf.comp (continuous_subtype_val.comp continuous_snd)
  have hband (p : B) : f p.1.2.1 ∈ Icc (-η) η :=
    ⟨le_trans (neg_nonpos.mpr hη.le) p.2, le_of_lt p.1.2.2⟩
  let coord (p : B) := Φ.symm ⟨p.1.2.1, hband p⟩
  have hc : Continuous coord :=
    Φ.symm.continuous.comp (continuous_subtype_val.snd.subtype_val.subtype_mk _)
  have hcoord (p : B) : (coord p).2.1 = f p.1.2.1 := by
    have h := hΦ (coord p)
    simpa only [coord, Φ.apply_symm_apply] using h.symm
  have hscaled (p : B) : (p.1.1 : ℝ) * f p.1.2.1 ∈ Icc (-η) η := by
    constructor
    · exact le_trans (neg_nonpos.mpr hη.le) (mul_nonneg p.1.1.2.1 p.2)
    · exact (mul_le_of_le_one_left p.2 p.1.1.2.2).trans (le_of_lt p.1.2.2)
  let move (p : B) : Y := (Φ ((coord p).1, ⟨p.1.1 * f p.1.2.1, hscaled p⟩)).1
  have hmove : Continuous move := by
    apply continuous_subtype_val.comp
    apply Φ.continuous.comp
    apply Continuous.prodMk hc.fst
    exact ((continuous_subtype_val.fst.subtype_val).mul
      (hheight.comp continuous_subtype_val)).subtype_mk _
  have move_height (p : B) : f (move p) = p.1.1 * f p.1.2.1 := hΦ _
  have move_eq (p : B) (hp : p.1.1 * f p.1.2.1 = f p.1.2.1) :
      move p = p.1.2.1 := by
    have heq : ((coord p).1, (⟨p.1.1 * f p.1.2.1, hscaled p⟩ : Icc (-η) η)) =
        coord p := Prod.ext rfl (Subtype.ext (hp.trans (hcoord p).symm))
    dsimp only [move]
    rw [heq]
    exact congrArg Subtype.val (Φ.apply_symm_apply _)
  let F (p : I × U) : Y := if hp : 0 ≤ f p.2.1 then move ⟨p, hp⟩ else p.2.1
  have F_nonpos (p : I × U) (hp : f p.2.1 ≤ 0) : F p = p.2.1 := by
    dsimp only [F]
    split_ifs with h
    · apply move_eq
      have hz := le_antisymm hp h
      simp only [hz, mul_zero]
    · rfl
  have F_cont : Continuous F := by
    have hA : ContinuousOn F A := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.snd.subtype_val).congr
        (fun p => (F_nonpos p.1 p.2).symm)
    have hB : ContinuousOn F B := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hmove.congr (fun p => by
        change move p = F p.1
        dsimp only [F]
        split_ifs with hp
        · rfl
        · exact False.elim (hp p.2))
    have hcAB : A ∪ B = univ := by
      ext p
      exact iff_true_intro (show f p.2.1 ≤ 0 ∨ 0 ≤ f p.2.1 from le_total _ _)
    rw [← continuousOn_univ, ← hcAB]
    exact hA.union_of_isClosed hB (isClosed_le hheight continuous_const)
      (isClosed_le continuous_const hheight)
  have F_height (p : I × U) : f (F p) < η := by
    dsimp only [F]
    split_ifs with hp
    · rw [move_height]
      exact lt_of_le_of_lt (mul_le_of_le_one_left hp p.1.2.2) p.2.2
    · exact p.2.2
  have F_zero (p : U) : f (F (0, p)) ≤ 0 := by
    dsimp only [F]
    split_ifs with hp
    · rw [move_height]
      simp
    · exact le_of_lt (lt_of_not_ge hp)
  have F_one (p : U) : F (1, p) = p.1 := by
    dsimp only [F]
    split_ifs with hp
    · exact move_eq _ (by simp)
    · rfl
  let r : C(U, {y : Y | f y ≤ 0}) :=
    ⟨fun p => ⟨F (0, p), F_zero p⟩,
      (F_cont.comp (continuous_const.prodMk continuous_id)).subtype_mk _⟩
  let i : C({y : Y | f y ≤ 0}, U) :=
    ⟨fun p => ⟨p.1, lt_of_le_of_lt p.2 hη⟩, continuous_subtype_val.subtype_mk _⟩
  refine { toFun := r, invFun := i, left_inv := ?_, right_inv := ?_ }
  · exact ⟨{
      toFun := fun p => ⟨F p, F_height p⟩
      continuous_toFun := F_cont.subtype_mk _
      map_zero_left := fun _ => rfl
      map_one_left := fun p => Subtype.ext (F_one p) }⟩
  · have heq : r.comp i = ContinuousMap.id _ := by
      ext p
      exact F_nonpos (0, i p) p.2
    rw [heq]

noncomputable def upperHomotopyEquiv (hf : Continuous f) (hη : 0 < η)
    (Φ : Z × Icc (-η) η ≃ₜ (f ⁻¹' Icc (-η) η))
    (hΦ : ∀ p, f (Φ p).1 = p.2.1) :
    {y : Y | -η < f y} ≃ₕ {y : Y | 0 ≤ f y} := by
  let negMap : Icc (-η) η → Icc (-η) η := fun t =>
    ⟨-t.1, neg_le_neg t.2.2, (neg_le_neg t.2.1).trans_eq (neg_neg η)⟩
  let flip : Icc (-η) η ≃ₜ Icc (-η) η :=
    { toFun := negMap
      invFun := negMap
      left_inv := fun t => Subtype.ext (neg_neg t.1)
      right_inv := fun t => Subtype.ext (neg_neg t.1)
      continuous_toFun := continuous_subtype_val.neg.subtype_mk _
      continuous_invFun := continuous_subtype_val.neg.subtype_mk _ }
  let b : (f ⁻¹' Icc (-η) η) ≃ₜ ((fun y => -f y) ⁻¹' Icc (-η) η) :=
    Homeomorph.setCongr (by ext y; change (-η ≤ f y ∧ f y ≤ η) ↔
      (-η ≤ -f y ∧ -f y ≤ η); constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith)
  let Ψ := (Homeomorph.prodCongr (Homeomorph.refl Z) flip).trans (Φ.trans b)
  have hΨ (p : Z × Icc (-η) η) : -f (Ψ p).1 = p.2.1 := by
    have h := hΦ (p.1, flip p.2)
    change f (Ψ p).1 = -p.2.1 at h
    linarith
  let d : {y : Y | -η < f y} ≃ₜ {y : Y | -f y < η} :=
    Homeomorph.setCongr (by ext y; change (-η < f y) ↔ (-f y < η); constructor <;> intro h <;> linarith)
  let c : {y : Y | -f y ≤ 0} ≃ₜ {y : Y | 0 ≤ f y} :=
    Homeomorph.setCongr (by ext y; change (-f y ≤ 0) ↔ (0 ≤ f y); exact neg_nonpos)
  exact d.toHomotopyEquiv.trans ((lowerHomotopyEquiv hf.neg hη Ψ hΨ).trans c.toHomotopyEquiv)

theorem simplyConnectedSpace [PathConnectedSpace Z] (hf : Continuous f) (hη : 0 < η)
    (Φ : Z × Icc (-η) η ≃ₜ (f ⁻¹' Icc (-η) η))
    (hΦ : ∀ p, f (Φ p).1 = p.2.1)
    (hlo : IsSimplyConnected {y : Y | f y ≤ 0})
    (hup : IsSimplyConnected {y : Y | 0 ≤ f y}) : SimplyConnectedSpace Y := by
  let U : Set Y := {y | f y < η}
  let V : Set Y := {y | -η < f y}
  have hU : IsSimplyConnected U := by
    have : SimplyConnectedSpace {y : Y | f y ≤ 0} := hlo
    exact (lowerHomotopyEquiv hf hη Φ hΦ).simplyConnectedSpace
  have hV : IsSimplyConnected V := by
    have : SimplyConnectedSpace {y : Y | 0 ≤ f y} := hup
    exact (upperHomotopyEquiv hf hη Φ hΦ).simplyConnectedSpace
  have hinterval : IsPathConnected (Ioo (-η) η) :=
    (convex_Ioo (-η) η).isPathConnected ⟨0, neg_lt_zero.mpr hη, hη⟩
  have : PathConnectedSpace (Ioo (-η) η) :=
    isPathConnected_iff_pathConnectedSpace.mp hinterval
  let F : Z × Ioo (-η) η → Y := fun p =>
    (Φ (p.1, ⟨p.2.1, p.2.2.1.le, p.2.2.2.le⟩)).1
  have hF : Continuous F := continuous_subtype_val.comp
    (Φ.continuous.comp (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)))
  have hrange : range F = U ∩ V := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      change f (F p) < η ∧ -η < f (F p)
      have hp : f (F p) = p.2.1 := hΦ _
      rw [hp]
      exact ⟨p.2.2.2, p.2.2.1⟩
    · rintro ⟨hyU, hyV⟩
      let y' : f ⁻¹' Icc (-η) η := ⟨y, hyV.le, hyU.le⟩
      have hcoord : (Φ.symm y').2.1 = f y := by
        have h := hΦ (Φ.symm y')
        simpa only [Φ.apply_symm_apply] using h.symm
      refine ⟨((Φ.symm y').1, ⟨f y, hyV, hyU⟩), ?_⟩
      have heq : ((Φ.symm y').1, (⟨f y, hyV.le, hyU.le⟩ : Icc (-η) η)) =
          Φ.symm y' := Prod.ext rfl (Subtype.ext hcoord.symm)
      dsimp only [F]
      rw [heq]
      exact congrArg Subtype.val (Φ.apply_symm_apply y')
  apply simplyConnectedSpace_of_open_cover (U := U) (V := V)
    (isOpen_lt hf continuous_const) (isOpen_lt continuous_const hf)
  · ext y
    simp only [U, V, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    by_cases hy : f y < η
    · exact Or.inl hy
    · exact Or.inr (by linarith [le_of_not_gt hy])
  · exact hU
  · exact hV
  · rw [← hrange]
    exact isPathConnected_range hF

end CollaredHeight

namespace RoundedDouble

variable {X : Type*} [TopologicalSpace X] {g : X → ℝ}

theorem simplyConnectedSpace_boundary_of_collar (hg : Continuous g)
    (hbase : IsSimplyConnected (base g)) (hzero : IsPathConnected (g ⁻¹' {0}))
    {η : ℝ} (hη : 0 < η)
    (Φ : (g ⁻¹' {0}) × Icc (-η) η ≃ₜ boundaryBand g η)
    (hΦ : ∀ p, (Φ p).1.1.2 = p.2.1) : SimplyConnectedSpace (boundary g) := by
  have : SimplyConnectedSpace (base g) := hbase
  have : PathConnectedSpace (g ⁻¹' {0}) :=
    isPathConnected_iff_pathConnectedSpace.mp hzero
  apply CollaredHeight.simplyConnectedSpace continuous_subtype_val.snd hη Φ hΦ
  · have heq : range (lower g) = {p : boundary g | p.1.2 ≤ 0} :=
      Set.ext mem_range_lower
    rw [← heq]
    exact (isClosedEmbedding_lower hg).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  · have heq : range (upper g) = {p : boundary g | 0 ≤ p.1.2} :=
      Set.ext mem_range_upper
    rw [← heq]
    exact (isClosedEmbedding_upper hg).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end RoundedDouble

end DifferentialGeometry.Topology
