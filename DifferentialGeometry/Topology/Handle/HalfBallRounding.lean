import DifferentialGeometry.Topology.Manifold.SphereDirection
import DifferentialGeometry.Topology.Manifold.SectorRoundingComparison
import DifferentialGeometry.Analysis.Calculus.SmoothMax
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.Calculus

open Set Metric
open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def halfBallCorner (r : ℝ) (v : sphere (0 : E) 1) :
    OpenPartialHomeomorph (E × ℝ) (sphere (0 : E) 1 × (ℝ × ℝ)) := by
  let f : E × ℝ → sphere (0 : E) 1 × (ℝ × ℝ) := fun p =>
    (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
      (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2, p.2))
  let g : sphere (0 : E) 1 × (ℝ × ℝ) → E × ℝ := fun p =>
    (Real.sqrt (r ^ 2 - p.2.1 - p.2.2 ^ 2) • p.1.val, p.2.2)
  let S : Set (E × ℝ) := {p | p.1 ≠ 0}
  let T : Set (sphere (0 : E) 1 × (ℝ × ℝ)) := {p | 0 < r ^ 2 - p.2.1 - p.2.2 ^ 2}
  have hdir : ContinuousOn (DifferentialGeometry.Topology.Manifold.sphereDirection v) ({0}ᶜ : Set E) := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    have hn : ContinuousOn (fun x : E => ‖x‖) ({0}ᶜ : Set E) := continuous_norm.continuousOn
    have h := ((hn.inv₀ (fun x hx => norm_ne_zero_iff.mpr (show x ≠ 0 from hx))).smul continuousOn_id)
    exact h.congr (fun x hx => DifferentialGeometry.Topology.Manifold.coe_sphereDirection v hx)
  have hrad : Continuous
      (fun p : sphere (0 : E) 1 × (ℝ × ℝ) => r ^ 2 - p.2.1 - p.2.2 ^ 2) :=
    (continuous_const.sub continuous_snd.fst).sub (continuous_snd.snd.pow 2)
  refine
    { toFun := f
      invFun := g
      source := S
      target := T
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := isOpen_compl_singleton.preimage continuous_fst
      open_target := isOpen_lt continuous_const hrad
      continuousOn_toFun := (hdir.comp continuous_fst.continuousOn (fun _ hp => hp)).prodMk
        ((((continuous_const.sub ((continuous_norm.comp continuous_fst).pow 2)).sub
          (continuous_snd.pow 2)).prodMk continuous_snd).continuousOn)
      continuousOn_invFun := ((hrad.sqrt.smul (continuous_subtype_val.comp continuous_fst)).prodMk
        continuous_snd.snd).continuousOn }
  · intro p hp
    change 0 < r ^ 2 - (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2) - p.2 ^ 2
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hp)]
  · intro p hp
    exact smul_ne_zero (Real.sqrt_pos.mpr hp).ne' (ne_zero_of_mem_unit_sphere p.1)
  · intro p hp
    apply Prod.ext
    · change Real.sqrt (r ^ 2 - (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2) - p.2 ^ 2) •
        (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1).val = p.1
      rw [show r ^ 2 - (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2) - p.2 ^ 2 = ‖p.1‖ ^ 2 by ring,
        Real.sqrt_sq (norm_nonneg _)]
      exact DifferentialGeometry.Topology.Manifold.norm_smul_sphereDirection v hp
    · rfl
  · intro p hp
    apply Prod.ext
    · exact DifferentialGeometry.Topology.Manifold.sphereDirection_pos_smul v p.1
        (Real.sqrt_pos.mpr hp)
    · apply Prod.ext
      · change r ^ 2 - ‖Real.sqrt (r ^ 2 - p.2.1 - p.2.2 ^ 2) • p.1.val‖ ^ 2 - p.2.2 ^ 2 = p.2.1
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_eq_of_mem_sphere,
          mul_one, Real.sq_sqrt hp.le]
        ring
      · rfl

@[simp] theorem halfBallCorner_apply (r : ℝ) (v : sphere (0 : E) 1) (p : E × ℝ) :
    halfBallCorner r v p =
      (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
        (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2, p.2)) := rfl

@[simp] theorem halfBallCorner_symm_apply (r : ℝ) (v : sphere (0 : E) 1)
    (p : sphere (0 : E) 1 × (ℝ × ℝ)) :
    (halfBallCorner r v).symm p =
      (Real.sqrt (r ^ 2 - p.2.1 - p.2.2 ^ 2) • p.1.val, p.2.2) := rfl

@[simp] theorem halfBallCorner_source (r : ℝ) (v : sphere (0 : E) 1) :
    (halfBallCorner r v).source = {p | p.1 ≠ 0} := rfl

@[simp] theorem halfBallCorner_target (r : ℝ) (v : sphere (0 : E) 1) :
    (halfBallCorner r v).target = {p | 0 < r ^ 2 - p.2.1 - p.2.2 ^ 2} := rfl

theorem halfBallCorner_symm_norm_sq_add_sq (r : ℝ) (v : sphere (0 : E) 1)
    {p : sphere (0 : E) 1 × (ℝ × ℝ)} (hp : p ∈ (halfBallCorner r v).target) :
    ‖((halfBallCorner r v).symm p).1‖ ^ 2 + ((halfBallCorner r v).symm p).2 ^ 2 =
      r ^ 2 - p.2.1 := by
  rw [halfBallCorner_symm_apply]
  dsimp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), norm_eq_of_mem_sphere,
    mul_one, Real.sq_sqrt hp.le]
  ring

theorem halfBallCorner_symm_mem_halfBall (r : ℝ) (v : sphere (0 : E) 1)
    {p : sphere (0 : E) 1 × (ℝ × ℝ)} (hp : p ∈ (halfBallCorner r v).target) :
    ‖((halfBallCorner r v).symm p).1‖ ^ 2 + ((halfBallCorner r v).symm p).2 ^ 2 ≤ r ^ 2 ∧
        0 ≤ ((halfBallCorner r v).symm p).2 ↔ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 := by
  rw [halfBallCorner_symm_norm_sq_add_sq r v hp, halfBallCorner_symm_apply]
  dsimp
  constructor <;> intro h <;> exact ⟨by linarith [h.1], h.2⟩

theorem smoothMax_halfBallCorner_symm (r : ℝ) (v : sphere (0 : E) 1)
    {ε : ℝ} (hε : ε ≠ 0) {p : sphere (0 : E) 1 × (ℝ × ℝ)}
    (hp : p ∈ (halfBallCorner r v).target) :
    Real.smoothMax ε
        (‖((halfBallCorner r v).symm p).1‖ ^ 2 + ((halfBallCorner r v).symm p).2 ^ 2 - r ^ 2)
        (-((halfBallCorner r v).symm p).2) =
      (Real.smoothAbs ε (p.2.1 - p.2.2) - (p.2.1 + p.2.2)) / 2 := by
  rw [halfBallCorner_symm_norm_sq_add_sq r v hp]
  change Real.smoothMax ε (r ^ 2 - p.2.1 - r ^ 2) (-p.2.2) = _
  rw [show r ^ 2 - p.2.1 - r ^ 2 = -p.2.1 by ring, Real.smoothMax,
    show -p.2.1 - -p.2.2 = -(p.2.1 - p.2.2) by ring, Real.smoothAbs.neg hε]
  ring

theorem halfBallCorner_strip_subset_target (r : ℝ) (v : sphere (0 : E) 1)
    {ε : ℝ} (hε : ε ≤ 1) (hr : ε < r ^ 2) :
    {p : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ (halfBallCorner r v).target := by
  intro p hp
  have ht : p.2.2 ≤ 1 := by linarith [hp.1, hp.2.2]
  have ht2 : p.2.2 ^ 2 ≤ p.2.2 := by nlinarith [mul_nonneg hp.2.1 (sub_nonneg.mpr ht)]
  change 0 < r ^ 2 - p.2.1 - p.2.2 ^ 2
  linarith [hp.2.2]

end OpenPartialHomeomorph

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

noncomputable def halfBallCorner (r : ℝ) (v : sphere (0 : E) 1) :
    PartialDiffeomorph 𝓘(ℝ, E × ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ))
      (E × ℝ) (sphere (0 : E) 1 × (ℝ × ℝ)) ∞ := by
  let f : E × ℝ → sphere (0 : E) 1 × (ℝ × ℝ) := fun p =>
    (DifferentialGeometry.Topology.Manifold.sphereDirection v p.1,
      (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2, p.2))
  let S : Set (E × ℝ) := {p | p.1 ≠ 0}
  let T : Set (sphere (0 : E) 1 × (ℝ × ℝ)) := {p | 0 < r ^ 2 - p.2.1 - p.2.2 ^ 2}
  have hrad : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun p : sphere (0 : E) 1 × (ℝ × ℝ) => r ^ 2 - p.2.1 - p.2.2 ^ 2) :=
    (((contDiff_const.sub contDiff_fst).sub (contDiff_snd.pow 2) :
      ContDiff ℝ ∞ (fun q : ℝ × ℝ => r ^ 2 - q.1 - q.2 ^ 2)).contMDiff.comp contMDiff_snd)
  have hsqrt : ContMDiffOn ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ) ∞
      (fun p : sphere (0 : E) 1 × (ℝ × ℝ) => Real.sqrt (r ^ 2 - p.2.1 - p.2.2 ^ 2)) T := by
    intro p hp
    exact (Real.contDiffAt_sqrt (ne_of_gt hp)).contMDiffAt.comp_contMDiffWithinAt p
      hrad.contMDiffAt.contMDiffWithinAt
  have hf : ContMDiffOn 𝓘(ℝ, E × ℝ) ((𝓡 n).prod 𝓘(ℝ, ℝ × ℝ)) ∞ f S := by
    exact ((DifferentialGeometry.Topology.Manifold.contMDiffOn_sphereDirection v).comp
      contDiff_fst.contMDiff.contMDiffOn (fun _ hp => hp)).prodMk
      ((((contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)).sub
        (contDiff_snd.pow 2)).prodMk contDiff_snd).contMDiff.contMDiffOn)
  exact
    { toPartialEquiv := (OpenPartialHomeomorph.halfBallCorner r v).toPartialEquiv
      open_source := (OpenPartialHomeomorph.halfBallCorner r v).open_source
      open_target := (OpenPartialHomeomorph.halfBallCorner r v).open_target
      contMDiffOn_toFun := hf
      contMDiffOn_invFun := (hsqrt.smul
        (contMDiff_coe_sphere.comp contMDiff_fst).contMDiffOn).prodMk_space
        (contDiff_snd.contMDiff.comp contMDiff_snd).contMDiffOn }

@[simp] theorem halfBallCorner_toOpenPartialHomeomorph (r : ℝ) (v : sphere (0 : E) 1) :
    (halfBallCorner (n := n) r v).toOpenPartialHomeomorph =
      OpenPartialHomeomorph.halfBallCorner r v := rfl

end PartialDiffeomorph


namespace DifferentialGeometry.Topology.Handle

noncomputable def halfBallRounding {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r ε : ℝ) (p : E × ℝ) : E × ℝ := by
  classical
  let u := r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2
  let w := u - p.2
  let q := Real.smoothAbs ε (u + p.2)
  let a := (w + q) / 2
  let b := (q - w) / 2
  exact if p.1 = 0 then p else ((Real.sqrt (r ^ 2 - a - b ^ 2) / ‖p.1‖) • p.1, b)

@[simp] theorem halfBallRounding_zero_fst {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r ε t : ℝ) : halfBallRounding r ε ((0 : E), t) = (0, t) := by
  simp [halfBallRounding]

theorem halfBallRounding_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) {p : E × ℝ}
    (hp : ε ≤ r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 + p.2) : halfBallRounding r ε p = p := by
  by_cases hx : p.1 = 0
  · simp [halfBallRounding, hx]
  · have ha : (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 - p.2 +
        Real.smoothAbs ε (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 + p.2)) / 2 =
        r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 := by
      rw [Real.smoothAbs.eq_self_of_le hε hp]
      ring
    have hb : (Real.smoothAbs ε (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 + p.2) -
        (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2 - p.2)) / 2 = p.2 := by
      rw [Real.smoothAbs.eq_self_of_le hε hp]
      ring
    simp only [halfBallRounding, if_neg hx, ha, hb,
      show r ^ 2 - (r ^ 2 - ‖p.1‖ ^ 2 - p.2 ^ 2) - p.2 ^ 2 = ‖p.1‖ ^ 2 by ring,
      Real.sqrt_sq (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hx), one_smul]

theorem halfBallRounding_halfBallCorner_symm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r ε : ℝ) (v : sphere (0 : E) 1)
    {p : sphere (0 : E) 1 × (ℝ × ℝ)} (hp : p ∈ (OpenPartialHomeomorph.halfBallCorner r v).target) :
    halfBallRounding r ε ((OpenPartialHomeomorph.halfBallCorner r v).symm p) =
      (OpenPartialHomeomorph.halfBallCorner r v).symm
        (p.1, ((p.2.1 - p.2.2 + Real.smoothAbs ε (p.2.1 + p.2.2)) / 2,
          (Real.smoothAbs ε (p.2.1 + p.2.2) - (p.2.1 - p.2.2)) / 2)) := by
  let e := OpenPartialHomeomorph.halfBallCorner r v
  have hne : (e.symm p).1 ≠ 0 := e.map_target hp
  have hnorm : ‖(e.symm p).1‖ = Real.sqrt (r ^ 2 - p.2.1 - p.2.2 ^ 2) := by
    rw [OpenPartialHomeomorph.halfBallCorner_symm_apply]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      norm_eq_of_mem_sphere, mul_one]
  have hu : r ^ 2 - ‖(e.symm p).1‖ ^ 2 - (e.symm p).2 ^ 2 = p.2.1 := by
    have h := OpenPartialHomeomorph.halfBallCorner_symm_norm_sq_add_sq r v hp
    change ‖(e.symm p).1‖ ^ 2 + (e.symm p).2 ^ 2 = r ^ 2 - p.2.1 at h
    linarith
  change halfBallRounding r ε (e.symm p) = _
  simp only [halfBallRounding, if_neg hne, hu]
  change ((Real.sqrt (r ^ 2 - (p.2.1 - p.2.2 + Real.smoothAbs ε (p.2.1 + p.2.2)) / 2 -
      ((Real.smoothAbs ε (p.2.1 + p.2.2) - (p.2.1 - p.2.2)) / 2) ^ 2) / ‖(e.symm p).1‖) •
      (e.symm p).1, (Real.smoothAbs ε (p.2.1 + p.2.2) - (p.2.1 - p.2.2)) / 2) = _
  rw [hnorm]
  simp only [e, OpenPartialHomeomorph.halfBallCorner_symm_apply,
    smul_smul, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hp).ne']

private theorem smoothMax_sq_sub_neg_nonpos_iff {r ε : ℝ} (hε : 0 < ε)
    (hsmall : ε < min 1 (r ^ 2)) (t : ℝ) :
    Real.smoothMax ε (t ^ 2 - r ^ 2) (-t) ≤ 0 ↔ t ^ 2 ≤ r ^ 2 ∧ 0 ≤ t := by
  constructor
  · intro h
    have hm := max_le_iff.mp ((Real.smoothMax.max_le hε (t ^ 2 - r ^ 2) (-t)).trans h)
    constructor <;> linarith [hm.1, hm.2]
  · intro ht
    have hu : 0 ≤ r ^ 2 - t ^ 2 := sub_nonneg.mpr ht.1
    have hsum : ε ≤ r ^ 2 - t ^ 2 + t := by
      rcases le_total t 1 with h | h
      · have ht2 : t ^ 2 ≤ t := by nlinarith [mul_nonneg ht.2 (sub_nonneg.mpr h)]
        linarith [hsmall.trans_le (min_le_right 1 (r ^ 2))]
      · linarith [hsmall.trans_le (min_le_left 1 (r ^ 2))]
    let q : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2} := ⟨(r ^ 2 - t ^ 2, t), hu, ht.2⟩
    have hrounded := (Homeomorph.smoothAbsQuadrant hε q).property
    rw [Homeomorph.smoothAbsQuadrant_apply_eq_self hε q hsum] at hrounded
    rw [Real.smoothMax, show t ^ 2 - r ^ 2 - -t = -(r ^ 2 - t ^ 2 - t) by ring,
      Real.smoothAbs.neg hε.ne']
    change Real.smoothAbs ε (r ^ 2 - t ^ 2 - t) ≤ r ^ 2 - t ^ 2 + t at hrounded
    linarith

theorem _root_.OpenPartialHomeomorph.smoothAbsQuadrantSet_halfBallCorner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (v : sphere (0 : E) 1) {ε : ℝ}
    (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    (OpenPartialHomeomorph.halfBallCorner r v).smoothAbsQuadrantSet
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} ε =
      {p : E × ℝ | Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0} := by
  let A : Set (E × ℝ) := {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
  let e := OpenPartialHomeomorph.halfBallCorner r v
  ext p
  constructor
  · rintro (hp | ⟨q, hq, rfl⟩)
    · have hp0 : p.1 = 0 := not_not.mp hp.2
      have hb : p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2 := by simpa [A, hp0] using hp.1
      simpa [hp0] using (smoothMax_sq_sub_neg_nonpos_iff hε hsmall p.2).mpr hb
    · have h := OpenPartialHomeomorph.smoothMax_halfBallCorner_symm r v hε.ne' hq.1
      change Real.smoothMax ε (‖(e.symm q).1‖ ^ 2 + (e.symm q).2 ^ 2 - r ^ 2) (-(e.symm q).2) ≤ 0
      change Real.smoothMax ε (‖(e.symm q).1‖ ^ 2 + (e.symm q).2 ^ 2 - r ^ 2)
        (-(e.symm q).2) = _ at h
      rw [h]
      have hb : Real.smoothAbs ε (q.2.1 - q.2.2) ≤ q.2.1 + q.2.2 := hq.2
      linarith
  · intro hp
    change Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0 at hp
    have hmax := (Real.smoothMax.max_le hε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2)).trans hp
    have hraw : p ∈ A := ⟨by linarith [le_max_left (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2)],
      by linarith [le_max_right (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2)]⟩
    by_cases hps : p ∈ e.source
    · right
      refine ⟨e p, ⟨e.map_source hps, ?_⟩, e.left_inv hps⟩
      have h := OpenPartialHomeomorph.smoothMax_halfBallCorner_symm r v hε.ne'
        (e.map_source hps)
      change Real.smoothMax ε (‖(e.symm (e p)).1‖ ^ 2 + (e.symm (e p)).2 ^ 2 - r ^ 2)
        (-(e.symm (e p)).2) = _ at h
      rw [e.left_inv hps] at h
      rw [h] at hp
      change Real.smoothAbs ε ((e p).2.1 - (e p).2.2) ≤ (e p).2.1 + (e p).2.2
      linarith
    · exact Or.inl ⟨hraw, hps⟩

private theorem exists_homeomorph_halfBallRounding_of_nontrivial {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    ∃ H : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} ≃ₜ
        {p : E × ℝ | Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0},
      ∀ x, (H x).val = halfBallRounding r ε x.val := by
  classical
  obtain ⟨w, hw⟩ := NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1) |>.mpr zero_le_one
  let v : sphere (0 : E) 1 := ⟨w, hw⟩
  let A : Set (E × ℝ) := {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2}
  let e := OpenPartialHomeomorph.halfBallCorner r v
  have hA : IsCompact A := by
    have hclosed : IsClosed A :=
      (isClosed_le ((continuous_norm.comp continuous_fst).pow 2 |>.add (continuous_snd.pow 2))
        continuous_const).inter (isClosed_le continuous_const continuous_snd)
    apply (isCompact_closedBall (0 : E × ℝ) |r|).of_isClosed_subset hclosed
    intro p hp
    rw [mem_closedBall_zero_iff, show ‖p‖ = max ‖p.1‖ ‖p.2‖ from rfl,
      max_le_iff, Real.norm_eq_abs, abs_of_nonneg hp.2]
    constructor <;> nlinarith [hp.1, hp.2, sq_abs r, abs_nonneg r, sq_nonneg p.2,
      sq_nonneg ‖p.1‖, norm_nonneg p.1]
  have hstrip : {p : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} ⊆ e.target :=
    OpenPartialHomeomorph.halfBallCorner_strip_subset_target r v
      (hsmall.trans_le (min_le_left _ _)).le (hsmall.trans_le (min_le_right _ _))
  obtain ⟨H, hH, hHfix⟩ := e.exists_homeomorph_smoothAbs_quadrant hA hε
    (fun p hp => OpenPartialHomeomorph.halfBallCorner_symm_mem_halfBall r v hp) hstrip
  have heq := OpenPartialHomeomorph.smoothAbsQuadrantSet_halfBallCorner r v hε hsmall
  refine ⟨H.trans (Homeomorph.setCongr heq), ?_⟩
  intro x
  by_cases hx0 : x.val.1 = 0
  · have hxK : x.val ∉ e.symm ''
        {p : sphere (0 : E) 1 × (ℝ × ℝ) | 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 + p.2.2 ≤ ε} := by
      rintro ⟨p, hp, he⟩
      have hs := e.map_target (hstrip hp)
      rw [he] at hs
      exact hs hx0
    exact (hHfix x hxK).trans (by simp [halfBallRounding, hx0])
  · have hm := halfBallRounding_halfBallCorner_symm r ε v (e.map_source hx0)
    change halfBallRounding r ε (e.symm (e x.val)) = _ at hm
    rw [e.left_inv hx0] at hm
    exact (hH x hx0).trans hm.symm

theorem exists_homeomorph_halfBallRounding {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (r : ℝ) {ε : ℝ} (hε : 0 < ε) (hsmall : ε < min 1 (r ^ 2)) :
    ∃ H : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} ≃ₜ
        {p : E × ℝ | Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0},
      ∀ x, (H x).val = halfBallRounding r ε x.val := by
  rcases subsingleton_or_nontrivial E with h | h
  · let _ := h
    have heq : {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.2} =
        {p : E × ℝ | Real.smoothMax ε (‖p.1‖ ^ 2 + p.2 ^ 2 - r ^ 2) (-p.2) ≤ 0} := by
      ext p
      have hp0 : p.1 = 0 := Subsingleton.elim _ _
      simpa only [hp0, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add, mem_ofPred_eq] using
        (smoothMax_sq_sub_neg_nonpos_iff hε hsmall p.2).symm
    refine ⟨Homeomorph.setCongr heq, ?_⟩
    intro p
    have hp0 : p.val.1 = 0 := Subsingleton.elim _ _
    exact (show p.val = halfBallRounding r ε p.val from by simp [halfBallRounding, hp0])
  · let _ := h
    exact exists_homeomorph_halfBallRounding_of_nontrivial r hε hsmall

end DifferentialGeometry.Topology.Handle
