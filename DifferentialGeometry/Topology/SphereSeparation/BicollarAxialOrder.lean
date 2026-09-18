import DifferentialGeometry.Topology.SphereSeparation.BicollarLineReparametrization
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

noncomputable section

open Set Metric Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

theorem bicollar_axial_strictMono (a : ℝ) (ha : 0 < a) :
    StrictMono (OpenPartialHomeomorph.univBall (0 : ℝ) a) := by
  have hinj : Function.Injective (OpenPartialHomeomorph.univBall (0 : ℝ) a) := by
    intro x y hxy
    have hx := (OpenPartialHomeomorph.univBall (0 : ℝ) a).left_inv
      (by simp : x ∈ (OpenPartialHomeomorph.univBall (0 : ℝ) a).source)
    have hy := (OpenPartialHomeomorph.univBall (0 : ℝ) a).left_inv
      (by simp : y ∈ (OpenPartialHomeomorph.univBall (0 : ℝ) a).source)
    exact hx.symm.trans ((congrArg
      (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm hxy).trans hy)
  rcases (OpenPartialHomeomorph.continuous_univBall (0 : ℝ) a).strictMono_of_inj
    hinj with hmono | hanti
  · exact hmono
  · have hpos : 0 < OpenPartialHomeomorph.univBall (0 : ℝ) a 1 :=
      (bicollarLineHomeomorph_positive_iff a ha (PUnit.unit : PUnit.{1}) 1).mpr zero_lt_one
    have hneg := hanti (zero_lt_one : (0 : ℝ) < 1)
    rw [OpenPartialHomeomorph.univBall_apply_zero] at hneg
    exact False.elim (lt_asymm hpos hneg)


theorem bicollar_axial_apply_inverse (a : ℝ) (ha : 0 < a) (s : ℝ)
    (hs : -a < s ∧ s < a) :
    OpenPartialHomeomorph.univBall (0 : ℝ) a
      ((OpenPartialHomeomorph.univBall (0 : ℝ) a).symm s) = s := by
  apply (OpenPartialHomeomorph.univBall (0 : ℝ) a).right_inv
  rw [OpenPartialHomeomorph.univBall_target _ ha, Real.ball_eq_Ioo]
  simpa using hs


theorem bicollarLineHomeomorph_slice {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : -a < s ∧ s < a) (y : A) :
    bicollarLineHomeomorph a ha
      (y, (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm s) = ⟨(y, s), hs⟩ := by
  apply Subtype.ext
  exact Prod.ext rfl (bicollar_axial_apply_inverse a ha s hs)


theorem bicollar_axial_inverse_lt_iff (a : ℝ) (ha : 0 < a) (s t : ℝ)
    (hs : -a < s ∧ s < a) (ht : -a < t ∧ t < a) :
    (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm s <
      (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm t ↔ s < t := by
  have h := (bicollar_axial_strictMono a ha).lt_iff_lt
    (a := (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm s)
    (b := (OpenPartialHomeomorph.univBall (0 : ℝ) a).symm t)
  rw [bicollar_axial_apply_inverse a ha s hs, bicollar_axial_apply_inverse a ha t ht] at h
  exact h.symm

theorem bicollarLineHomeomorph_image_band {A : Type*} [TopologicalSpace A]
    (a : ℝ) (ha : 0 < a) (s t : ℝ)
    (hs : -a < s ∧ s < a) (ht : -a < t ∧ t < a) :
    bicollarLineHomeomorph (A := A) a ha ''
        ((univ : Set A) ×ˢ Icc
          ((OpenPartialHomeomorph.univBall (0 : ℝ) a).symm s)
          ((OpenPartialHomeomorph.univBall (0 : ℝ) a).symm t)) =
      {q | s ≤ q.val.2 ∧ q.val.2 ≤ t} := by
  let f := OpenPartialHomeomorph.univBall (0 : ℝ) a
  have hmono := bicollar_axial_strictMono a ha
  have hfs : f (f.symm s) = s := bicollar_axial_apply_inverse a ha s hs
  have hft : f (f.symm t) = t := bicollar_axial_apply_inverse a ha t ht
  ext q
  constructor
  · rintro ⟨⟨y, z⟩, ⟨_, hsz, hzt⟩, rfl⟩
    change s ≤ f z ∧ f z ≤ t
    exact ⟨hfs ▸ hmono.monotone hsz, hft ▸ hmono.monotone hzt⟩
  · intro hq
    change s ≤ q.val.2 ∧ q.val.2 ≤ t at hq
    refine ⟨(bicollarLineHomeomorph a ha).symm q, ⟨mem_univ _, ?_, ?_⟩,
      (bicollarLineHomeomorph a ha).apply_symm_apply q⟩
    · change f.symm s ≤ f.symm q.val.2
      apply hmono.le_iff_le.mp
      rw [hfs, bicollar_axial_apply_inverse a ha q.val.2 q.property]
      exact hq.1
    · change f.symm q.val.2 ≤ f.symm t
      apply hmono.le_iff_le.mp
      rw [hft, bicollar_axial_apply_inverse a ha q.val.2 q.property]
      exact hq.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
