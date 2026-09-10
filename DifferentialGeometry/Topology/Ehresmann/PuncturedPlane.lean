import DifferentialGeometry.Topology.Manifold.OpenSubtype
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

def puncturedPlane : TopologicalSpace.Opens (ℝ × ℝ) :=
  ⟨{0}ᶜ, isOpen_compl_singleton⟩

def puncturedPlaneProjection (p : puncturedPlane) : ℝ := p.1.1

abbrev puncturedPlaneFiber (x : ℝ) := {p : puncturedPlane // puncturedPlaneProjection p = x}

theorem contMDiff_puncturedPlaneProjection :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) ∞ puncturedPlaneProjection :=
  contDiff_fst.contMDiff.comp contMDiff_subtype_val

theorem surjective_puncturedPlaneProjection : Function.Surjective puncturedPlaneProjection := by
  intro x
  exact ⟨⟨(x, 1), by simp [puncturedPlane]⟩, rfl⟩

theorem mfderiv_puncturedPlaneProjection (p : puncturedPlane) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) puncturedPlaneProjection p =
      ContinuousLinearMap.fst ℝ ℝ ℝ := by
  have h := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasMFDerivAt.comp p
    (DifferentialGeometry.hasMFDerivAt_subtype_val puncturedPlane p)
  exact h.mfderiv.trans (by ext; rfl)

theorem surjective_mfderiv_puncturedPlaneProjection (p : puncturedPlane) :
    Function.Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ) puncturedPlaneProjection p) := by
  rw [mfderiv_puncturedPlaneProjection]
  intro v
  exact ⟨(v, 0), rfl⟩

def puncturedPlaneFiberHomeomorphReal (x : ℝ) (hx : x ≠ 0) :
    puncturedPlaneFiber x ≃ₜ ℝ where
  toFun p := p.1.1.2
  invFun y := ⟨⟨(x, y), by
    change (x, y) ≠ (0 : ℝ × ℝ)
    exact fun h ↦ hx (congrArg Prod.fst h)⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext p.2.symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _ |>.subtype_mk _

theorem connectedSpace_puncturedPlaneFiber_of_ne_zero (x : ℝ) (hx : x ≠ 0) :
    ConnectedSpace (puncturedPlaneFiber x) :=
  (puncturedPlaneFiberHomeomorphReal x hx).symm.surjective.connectedSpace
    (puncturedPlaneFiberHomeomorphReal x hx).symm.continuous

private theorem zeroFiber_snd_ne (p : puncturedPlaneFiber 0) : p.1.1.2 ≠ 0 := by
  intro h
  exact p.1.2 (Prod.ext p.2 h)

private def zeroFiberPoint (y : ℝ) (hy : y ≠ 0) : puncturedPlaneFiber 0 :=
  ⟨⟨(0, y), fun h ↦ hy (congrArg Prod.snd h)⟩, rfl⟩

private theorem zeroFiberPoint_snd (p : puncturedPlaneFiber 0) :
    zeroFiberPoint p.1.1.2 (zeroFiber_snd_ne p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext p.2.symm rfl

theorem isConnected_puncturedPlaneFiber_zero_neg :
    IsConnected {p : puncturedPlaneFiber 0 | p.1.1.2 < 0} := by
  let : ConnectedSpace (Iio (0 : ℝ)) := isConnected_iff_connectedSpace.mp isConnected_Iio
  let f : Iio (0 : ℝ) → puncturedPlaneFiber 0 := fun y ↦ zeroFiberPoint y (ne_of_lt y.2)
  have hf : Continuous f :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _ |>.subtype_mk _
  have hrange : range f = {p : puncturedPlaneFiber 0 | p.1.1.2 < 0} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hp
      exact ⟨⟨p.1.1.2, hp⟩, zeroFiberPoint_snd p⟩
  rw [← hrange]
  exact isConnected_range hf

theorem isConnected_puncturedPlaneFiber_zero_pos :
    IsConnected {p : puncturedPlaneFiber 0 | 0 < p.1.1.2} := by
  let : ConnectedSpace (Ioi (0 : ℝ)) := isConnected_iff_connectedSpace.mp isConnected_Ioi
  let f : Ioi (0 : ℝ) → puncturedPlaneFiber 0 := fun y ↦ zeroFiberPoint y (ne_of_gt y.2)
  have hf : Continuous f :=
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _ |>.subtype_mk _
  have hrange : range f = {p : puncturedPlaneFiber 0 | 0 < p.1.1.2} := by
    ext p
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hp
      exact ⟨⟨p.1.1.2, hp⟩, zeroFiberPoint_snd p⟩
  rw [← hrange]
  exact isConnected_range hf

theorem connectedComponent_puncturedPlaneFiber_zero_of_neg
    (p : puncturedPlaneFiber 0) (hp : p.1.1.2 < 0) :
    connectedComponent p = {q : puncturedPlaneFiber 0 | q.1.1.2 < 0} := by
  apply Subset.antisymm
  · intro q hq
    exact isPreconnected_connectedComponent.gt_of_ne
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).continuousOn
      (fun r _ ↦ zeroFiber_snd_ne r) ⟨p, mem_connectedComponent, hp⟩ hq
  · exact isConnected_puncturedPlaneFiber_zero_neg.isPreconnected.subset_connectedComponent hp

theorem connectedComponent_puncturedPlaneFiber_zero_of_pos
    (p : puncturedPlaneFiber 0) (hp : 0 < p.1.1.2) :
    connectedComponent p = {q : puncturedPlaneFiber 0 | 0 < q.1.1.2} := by
  apply Subset.antisymm
  · intro q hq
    exact isPreconnected_connectedComponent.lt_of_ne
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).continuousOn
      (fun r _ ↦ zeroFiber_snd_ne r) ⟨p, mem_connectedComponent, hp⟩ hq
  · exact isConnected_puncturedPlaneFiber_zero_pos.isPreconnected.subset_connectedComponent hp

theorem connectedComponents_puncturedPlaneFiber_zero :
    {C : Set (puncturedPlaneFiber 0) | ∃ p, connectedComponent p = C} =
      {{p : puncturedPlaneFiber 0 | p.1.1.2 < 0},
        {p : puncturedPlaneFiber 0 | 0 < p.1.1.2}} := by
  ext C
  constructor
  · rintro ⟨p, rfl⟩
    rcases lt_or_gt_of_ne (zeroFiber_snd_ne p) with hp | hp
    · exact Or.inl (connectedComponent_puncturedPlaneFiber_zero_of_neg p hp)
    · exact Or.inr (connectedComponent_puncturedPlaneFiber_zero_of_pos p hp)
  · rintro (rfl | rfl)
    · exact ⟨zeroFiberPoint (-1) (by norm_num),
        connectedComponent_puncturedPlaneFiber_zero_of_neg _ (by norm_num [zeroFiberPoint])⟩
    · exact ⟨zeroFiberPoint 1 one_ne_zero,
        connectedComponent_puncturedPlaneFiber_zero_of_pos _ (by norm_num [zeroFiberPoint])⟩

theorem not_connectedSpace_puncturedPlaneFiber_zero :
    ¬ ConnectedSpace (puncturedPlaneFiber 0) := by
  intro h
  let : ConnectedSpace (puncturedPlaneFiber 0) := h
  have hsign := isPreconnected_univ.gt_of_ne
    (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).continuousOn
    (fun r _ ↦ zeroFiber_snd_ne r)
    ⟨zeroFiberPoint (-1) (by norm_num), mem_univ _, by norm_num [zeroFiberPoint]⟩
    (mem_univ (zeroFiberPoint 1 one_ne_zero))
  norm_num [zeroFiberPoint] at hsign

theorem not_homeomorphic_puncturedPlaneFiber_zero (x : ℝ) (hx : x ≠ 0) :
    ¬ Nonempty (puncturedPlaneFiber 0 ≃ₜ puncturedPlaneFiber x) := by
  rintro ⟨e⟩
  exact not_connectedSpace_puncturedPlaneFiber_zero
    (e.connectedSpace_iff.mpr (connectedSpace_puncturedPlaneFiber_of_ne_zero x hx))

theorem not_eventually_homeomorphic_puncturedPlaneFiber_zero :
    ¬ ∀ᶠ x in 𝓝 (0 : ℝ), Nonempty (puncturedPlaneFiber 0 ≃ₜ puncturedPlaneFiber x) := by
  intro h
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp h
  apply not_homeomorphic_puncturedPlaneFiber_zero (ε / 2) (ne_of_gt (half_pos hε))
  apply he
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)] using half_lt_self hε

theorem not_isProperMap_puncturedPlaneProjection : ¬ IsProperMap puncturedPlaneProjection := by
  intro h
  have hc : IsCompact (puncturedPlaneProjection ⁻¹' {(1 : ℝ)}) :=
    h.isCompact_preimage isCompact_singleton
  let : CompactSpace (puncturedPlaneFiber 1) := isCompact_iff_compactSpace.mp hc
  let e := puncturedPlaneFiberHomeomorphReal 1 one_ne_zero
  have : CompactSpace ℝ := e.surjective.compactSpace e.continuous
  exact noncompact_univ ℝ isCompact_univ

end DifferentialGeometry.Topology.Ehresmann
