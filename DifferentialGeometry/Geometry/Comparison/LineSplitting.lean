import DifferentialGeometry.Geometry.Comparison.LineTranslation
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.HausdorffDimension

set_option autoImplicit false

open Set MeasureTheory

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

universe u

variable {X : Type u} [MetricSpace X] [ProperSpace X]
variable (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
variable (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
  Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
  ∀ s t, dist (f s) (f t) = dist a b * dist s t)

noncomputable def lineSplitting : X ≃ᵢ WithLp 2 (ℝ × {x : X // lineCoordinate γ x = 0}) :=
  IsometryEquiv.symm {
    toFun := fun a => lineTranslation hs hγ hsegments a.fst a.snd.val
    invFun := fun x => WithLp.toLp 2 (lineCoordinate γ x,
      ⟨lineTranslation hs hγ hsegments (-lineCoordinate γ x) x,
        by rw [lineCoordinate_lineTranslation]; ring⟩)
    left_inv := by
      intro a
      apply (WithLp.equiv 2 _).injective
      apply Prod.ext
      · change lineCoordinate γ (lineTranslation hs hγ hsegments a.fst a.snd.val) = a.fst
        rw [lineCoordinate_lineTranslation, a.snd.property, zero_add]
      · apply Subtype.ext
        change lineTranslation hs hγ hsegments
          (-lineCoordinate γ (lineTranslation hs hγ hsegments a.fst a.snd.val))
          (lineTranslation hs hγ hsegments a.fst a.snd.val) = a.snd.val
        rw [lineCoordinate_lineTranslation, a.snd.property, zero_add,
          lineTranslation_add, neg_add_cancel, lineTranslation_zero]
    right_inv := by
      intro x
      change lineTranslation hs hγ hsegments (lineCoordinate γ x)
        (lineTranslation hs hγ hsegments (-lineCoordinate γ x) x) = x
      rw [lineTranslation_add, add_neg_cancel, lineTranslation_zero]
    isometry_toFun := by
      apply Isometry.of_dist_eq
      intro a b
      have hd := sq_dist_lineTranslation hs hγ hsegments a.fst b.fst a.snd.val b.snd.val
      rw [a.snd.property, b.snd.property] at hd
      have hprod : dist a b = Real.sqrt (dist a.fst b.fst ^ 2 + dist a.snd b.snd ^ 2) := by
        rw [WithLp.prod_dist_eq_add (by norm_num : 0 < (2 : ENNReal).toReal)]
        norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
      rw [hprod]
      change dist (lineTranslation hs hγ hsegments a.fst a.snd.val)
        (lineTranslation hs hγ hsegments b.fst b.snd.val) =
          Real.sqrt (dist a.fst b.fst ^ 2 + dist a.snd.val b.snd.val ^ 2)
      rw [Real.dist_eq, sq_abs]
      apply (sq_eq_sq₀ dist_nonneg (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (by positivity)]
      nlinarith }

theorem lineSplitting_fst (x : X) :
    (lineSplitting hs hγ hsegments x).fst = lineCoordinate γ x := rfl

theorem lineSplitting_symm_apply (a : WithLp 2 (ℝ × {x : X // lineCoordinate γ x = 0})) :
    (lineSplitting hs hγ hsegments).symm a = lineTranslation hs hγ hsegments a.fst a.snd.val := rfl

theorem lineSplitting_apply_line (t : ℝ) :
    lineSplitting hs hγ hsegments (γ t) = WithLp.toLp 2
      (t, ⟨γ 0, by rw [lineCoordinate_apply_isometry hγ]⟩) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · exact lineCoordinate_apply_isometry hγ t
  · apply Subtype.ext
    change lineTranslation hs hγ hsegments (-lineCoordinate γ (γ t)) (γ t) = γ 0
    rw [lineCoordinate_apply_isometry hγ, lineTranslation_apply_line, add_neg_cancel]

include hs hγ in
omit [ProperSpace X] in
theorem isClosed_lineCoordinate_zero : IsClosed {x : X | lineCoordinate γ x = 0} :=
  isClosed_eq (lipschitzWith_lineCoordinate hs hγ).continuous continuous_const

include hs hγ in
theorem properSpace_lineCoordinate_zero : ProperSpace {x : X // lineCoordinate γ x = 0} :=
  ProperSpace.of_isClosed (isClosed_lineCoordinate_zero hs hγ)

include hs hγ in
theorem completeSpace_lineCoordinate_zero : CompleteSpace {x : X // lineCoordinate γ x = 0} := by
  let := properSpace_lineCoordinate_zero hs hγ
  infer_instance

include hs in
omit [ProperSpace X] in
theorem fourPointComparison_lineCoordinate_zero :
    fourPointComparison 0 (univ : Set {x : X // lineCoordinate γ x = 0}) := by
  intro p hp a ha b hb c hc hap hbp hcp
  exact hs p.val (mem_univ _) a.val (mem_univ _) b.val (mem_univ _) c.val (mem_univ _)
    (fun he => hap (Subtype.ext he)) (fun he => hbp (Subtype.ext he))
    (fun he => hcp (Subtype.ext he))

include hs hγ hsegments in
omit [ProperSpace X] in
theorem exists_segment_lineCoordinate_zero
    (a b : {x : X // lineCoordinate γ x = 0}) :
    ∃ f : Icc (0 : ℝ) 1 → {x : X // lineCoordinate γ x = 0},
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  obtain ⟨f, hf, hzero, hone, hd⟩ := hsegments a.val b.val
  have hb : ∀ t, lineCoordinate γ (f t) = 0 := by
    intro t
    have haz : dist a.val (f t) = (t : ℝ) * dist a.val b.val := by
      have h := hd ⟨0, by norm_num⟩ t
      rw [hzero] at h
      simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg t.property.1, mul_comm] using h
    have hzb : dist (f t) b.val = (1 - (t : ℝ)) * dist a.val b.val := by
      have h := hd t ⟨1, by norm_num⟩
      rw [hone] at h
      simpa only [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr t.property.2),
        neg_sub, mul_comm] using h
    have h := lineCoordinate_affine_of_dist hs hγ t.property haz hzb
    simpa only [a.property, b.property, mul_zero, add_zero] using h
  refine ⟨fun t => ⟨f t, hb t⟩, hf.subtype_mk hb, Subtype.ext hzero, Subtype.ext hone, ?_⟩
  exact hd

omit [ProperSpace X] in
theorem dimH_lineCoordinate_zero_le :
    dimH (univ : Set {x : X // lineCoordinate γ x = 0}) ≤ dimH (univ : Set X) := by
  rw [← isometry_subtype_coe.dimH_image]
  exact dimH_mono (subset_univ _)

include hs hγ hsegments in
theorem exists_isometryEquiv_real_prod :
    ∃ (Y : Type u) (m : MetricSpace Y), letI := m
      ∃ (p : Y) (e : X ≃ᵢ WithLp 2 (ℝ × Y)),
        (∀ t, e (γ t) = WithLp.toLp 2 (t, p)) ∧
        ProperSpace Y ∧ CompleteSpace Y ∧ fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y,
          Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        dimH (univ : Set Y) ≤ dimH (univ : Set X) := by
  refine ⟨{x : X // lineCoordinate γ x = 0}, inferInstance,
    ⟨γ 0, lineCoordinate_apply_isometry hγ 0⟩, lineSplitting hs hγ hsegments,
    lineSplitting_apply_line hs hγ hsegments, properSpace_lineCoordinate_zero hs hγ,
    completeSpace_lineCoordinate_zero hs hγ, fourPointComparison_lineCoordinate_zero hs,
    exists_segment_lineCoordinate_zero hs hγ hsegments, dimH_lineCoordinate_zero_le⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
