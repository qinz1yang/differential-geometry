/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Boundary.VisualMetric
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Deformation

noncomputable section

open Set Filter Matrix
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.BoundaryTripleCompactness

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicBoundary BoundaryTopology
open BoundaryHomeomorph BoundaryVisual

variable {n : ℕ}

def Triple (n : ℕ) :=
  {p : BoundaryH n × BoundaryH n × BoundaryH n |
    p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2}

abbrev first (t : Triple n) : BoundaryH n := t.val.1
abbrev second (t : Triple n) : BoundaryH n := t.val.2.1
abbrev third (t : Triple n) : BoundaryH n := t.val.2.2

def map (F : BoundaryH n → BoundaryH n) (hF : Function.Injective F) (t : Triple n) : Triple n :=
  ⟨(F (first t), F (second t), F (third t)),
    fun h => t.property.1 (hF h), fun h => t.property.2.1 (hF h),
      fun h => t.property.2.2 (hF h)⟩

def raw (t : Triple n) : LorVec n :=
  bratioB (second t) (third t) • (first t).val +
    bratioB (first t) (third t) • (second t).val

def scale (t : Triple n) : ℝ :=
  Real.sqrt (2 * bratioB (first t) (second t) *
    bratioB (first t) (third t) * bratioB (second t) (third t))

theorem scale_pos (t : Triple n) : 0 < scale t :=
  Real.sqrt_pos.mpr (mul_pos (mul_pos (mul_pos (by norm_num)
    (bratioB_pos t.property.1)) (bratioB_pos t.property.2.1)) (bratioB_pos t.property.2.2))

def center (t : Triple n) : HUpper n :=
  tripleCenter (first t) (second t) (third t) t.property.1 t.property.2.1 t.property.2.2

theorem center_val (t : Triple n) : (center t).val = (scale t)⁻¹ • raw t := rfl

theorem raw_eq_scale_center (t : Triple n) : raw t = scale t • (center t).val := by
  rw [center_val, smul_smul, mul_inv_cancel₀ (scale_pos t).ne', one_smul]

theorem continuous_first : Continuous (first : Triple n → BoundaryH n) :=
  continuous_fst.comp continuous_subtype_val
theorem continuous_second : Continuous (second : Triple n → BoundaryH n) :=
  (continuous_fst.comp continuous_snd).comp continuous_subtype_val
theorem continuous_third : Continuous (third : Triple n → BoundaryH n) :=
  (continuous_snd.comp continuous_snd).comp continuous_subtype_val

theorem continuous_bratioB : Continuous (fun p : BoundaryH n × BoundaryH n => bratioB p.1 p.2) :=
  (continuous_lorB_pair.comp
    ((isEmbedding_val.continuous.comp continuous_fst).prodMk
      (isEmbedding_val.continuous.comp continuous_snd))).neg

theorem continuous_center : Continuous (center : Triple n → HUpper n) := by
  apply StratumDeformation.continuous_of_val
  have hab := (continuous_bratioB (n := n)).comp (continuous_first.prodMk continuous_second)
  have hac := (continuous_bratioB (n := n)).comp (continuous_first.prodMk continuous_third)
  have hbc := (continuous_bratioB (n := n)).comp (continuous_second.prodMk continuous_third)
  have hs : Continuous (scale : Triple n → ℝ) :=
    Real.continuous_sqrt.comp (((continuous_const.mul hab).mul hac).mul hbc)
  exact (hs.inv₀ (fun t => (scale_pos t).ne')).smul
    ((hbc.smul (isEmbedding_val.continuous.comp continuous_first)).add
      (hac.smul (isEmbedding_val.continuous.comp continuous_second)))

theorem eq_of_boundaryRep_eq (x y : HUpper n)
    (h : boundaryRep x.val = boundaryRep y.val) : x = y := by
  have hc : 0 < tc x.val / tc y.val := div_pos x.future y.future
  have he : x.val = (tc x.val / tc y.val) • y.val := by
    calc
      x.val = tc x.val • boundaryRep x.val := by
        rw [boundaryRep, smul_smul, mul_inv_cancel₀ x.future.ne', one_smul]
      _ = tc x.val • boundaryRep y.val := by rw [h]
      _ = _ := by rw [boundaryRep, smul_smul, div_eq_mul_inv]
  have hu := congrArg (fun v : LorVec n => lorB v v) he
  rw [x.is_unit, lorB_smul_left, lorB_smul_right, y.is_unit] at hu
  have he1 : tc x.val / tc y.val = 1 :=
    (sq_eq_sq₀ hc.le (by norm_num : (0 : ℝ) ≤ 1)).mp (by nlinarith [hu])
  apply HUpper.ext
  simpa only [he1, one_smul] using he

theorem bratioB_actB (A : LorGrp n) (a b : BoundaryH n) :
    bratioB (actB A a) (actB A b) =
      (tc (matOf A *ᵥ a.val))⁻¹ * (tc (matOf A *ᵥ b.val))⁻¹ * bratioB a b := by
  change -lorB (boundaryRep (matOf A *ᵥ a.val)) (boundaryRep (matOf A *ᵥ b.val)) = _
  rw [boundaryRep, boundaryRep, lorB_smul_left, lorB_smul_right, lorB_matOf_mulVec]
  simp only [bratioB]
  ring

theorem raw_map_lor (A : LorGrp n) (t : Triple n) :
    raw (map (actB A) (MulAction.injective A) t) =
      (tc (matOf A *ᵥ (first t).val) * tc (matOf A *ᵥ (second t).val) *
        tc (matOf A *ᵥ (third t).val))⁻¹ • (matOf A *ᵥ raw t) := by
  change bratioB (actB A (second t)) (actB A (third t)) • (actB A (first t)).val +
    bratioB (actB A (first t)) (actB A (third t)) • (actB A (second t)).val = _
  rw [bratioB_actB, bratioB_actB]
  simp only [actB, boundaryRep, raw, mulVec_add, mulVec_smul,
    smul_add, smul_smul, _root_.mul_inv_rev]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem center_map_lor (A : LorGrp n) (t : Triple n) :
    center (map (actB A) (MulAction.injective A) t) = actH A (center t) := by
  apply eq_of_boundaryRep_eq
  let t' := map (actB A) (MulAction.injective A) t
  have hprod : tc (matOf A *ᵥ (first t).val) * tc (matOf A *ᵥ (second t).val) *
      tc (matOf A *ᵥ (third t).val) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (tc_matOf_mulVec_ne_zero A _) (tc_matOf_mulVec_ne_zero A _))
      (tc_matOf_mulVec_ne_zero A _)
  have hs : (scale t')⁻¹ *
      (tc (matOf A *ᵥ (first t).val) * tc (matOf A *ᵥ (second t).val) *
        tc (matOf A *ᵥ (third t).val))⁻¹ * scale t ≠ 0 :=
    mul_ne_zero (mul_ne_zero (inv_ne_zero (scale_pos t').ne') (inv_ne_zero hprod)) (scale_pos t).ne'
  have ht := matOf_mulVec_ne_tc A (center t).is_unit
  rw [center_val, raw_map_lor, raw_eq_scale_center t, mulVec_smul, smul_smul, smul_smul,
    boundaryRep_smul _ hs]
  change boundaryRep (matOf A *ᵥ (center t).val) =
    boundaryRep (upperize (matOf A *ᵥ (center t).val))
  unfold upperize
  split_ifs
  · rfl
  · exact (boundaryRep_neg _).symm

section Projective

variable (hn : 1 ≤ n)

def act (g : PO n 1) (t : Triple n) : Triple n :=
  letI := poBoundaryMulAction hn
  map (fun v => g • v) (MulAction.injective g) t

theorem center_act (g : PO n 1) (t : Triple n) :
    center (act hn g t) = (poMulAction hn).smul g (center t) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective _ g
  exact center_map_lor A t

theorem exists_subsequence_of_triples {g : ℕ → PO n 1} {t : ℕ → Triple n}
    {p q : Triple n} (ht : Tendsto t atTop (𝓝 p))
    (hg : Tendsto (fun j => act hn (g j) (t j)) atTop (𝓝 q)) :
    ∃ (a : PO n 1) (r : ℕ → ℕ), StrictMono r ∧ Tendsto (g ∘ r) atTop (𝓝 a) := by
  let := poMulAction hn
  let : T3Space (PO n 1) := DifferentialGeometry.ProjectiveOrthogonalGroup.Center.t3Space_PO hn
  let o : HUpper n := basepointH
  let B : ℝ := dist o (center p) + dist (center q) o
  have hlim : Tendsto (fun j => dist o (center (t j)) + dist (center (act hn (g j) (t j))) o)
      atTop (𝓝 B) :=
    (tendsto_const_nhds.dist (continuous_center.tendsto p |>.comp ht)).add
      ((continuous_center.tendsto q |>.comp hg).dist tendsto_const_nhds)
  have hbound : ∀ᶠ j in atTop, dist (g j • o) o ≤ B + 1 := by
    filter_upwards [hlim.eventually (Iio_mem_nhds (by linarith : B < B + 1))] with j hj
    have hi : dist (g j • o) (g j • center (t j)) = dist o (center (t j)) :=
      po_dist_smul hn (g j) _ _
    have hc : center (act hn (g j) (t j)) = g j • center (t j) := center_act hn (g j) (t j)
    have hb := dist_triangle (g j • o) (g j • center (t j)) o
    rw [hi, ← hc] at hb
    exact hb.trans hj.le
  obtain ⟨a, _, r, hr, hlim⟩ := (DirichletDomain.isCompact_orbit_preimage hn (B + 1)).tendsto_subseq'
    hbound.frequently
  exact ⟨a, r, hr, hlim⟩

end Projective

end DifferentialGeometry.BoundaryTripleCompactness
