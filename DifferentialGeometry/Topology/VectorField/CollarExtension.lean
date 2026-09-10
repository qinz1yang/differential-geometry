import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace DifferentialGeometry.VectorField


def collarTransition (t : ℝ) : ℝ := Real.smoothTransition (3 * t - 1)


theorem contDiff_collarTransition : ContDiff ℝ ∞ collarTransition :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)


theorem collarTransition_eq_zero {t : ℝ} (ht : t ≤ 1 / 3) : collarTransition t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)


theorem collarTransition_eq_one {t : ℝ} (ht : 2 / 3 ≤ t) : collarTransition t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)


theorem monotone_collarTransition : Monotone collarTransition := by
  intro s t hst
  exact Real.smoothTransition.monotone (by linarith)


theorem collarTransition_mem_Icc (t : ℝ) : collarTransition t ∈ Icc 0 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem hasDerivAt_expNegInvGlue (t : ℝ) :
    HasDerivAt expNegInvGlue (t⁻¹ ^ 2 * expNegInvGlue t) t := by
  simpa using expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul 1 t

private theorem deriv_smoothTransition_pos {t : ℝ} (ht : t ∈ Ioo 0 1) :
    0 < deriv Real.smoothTransition t := by
  have hA := hasDerivAt_expNegInvGlue t
  have hB := (hasDerivAt_expNegInvGlue (1 - t)).comp t ((hasDerivAt_id t).const_sub 1)
  have hD := hA.div (hA.add hB) (Real.smoothTransition.pos_denom t).ne'
  change HasDerivAt Real.smoothTransition _ t at hD
  rw [hD.deriv]
  apply div_pos _ (sq_pos_of_pos (Real.smoothTransition.pos_denom t))
  have h1 : 0 < t⁻¹ ^ 2 * expNegInvGlue t * expNegInvGlue (1 - t) :=
    mul_pos (mul_pos (sq_pos_of_pos (inv_pos.mpr ht.1))
      (expNegInvGlue.pos_of_pos ht.1)) (expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2))
  have h2 : 0 < expNegInvGlue t * ((1 - t)⁻¹ ^ 2 * expNegInvGlue (1 - t)) :=
    mul_pos (expNegInvGlue.pos_of_pos ht.1)
      (mul_pos (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr ht.2)))
        (expNegInvGlue.pos_of_pos (sub_pos.mpr ht.2)))
  simp only [Pi.add_apply, Function.comp_apply] at *
  nlinarith


theorem deriv_collarTransition_pos {t : ℝ} (ht : t ∈ Ioo (1 / 3) (2 / 3)) :
    0 < deriv collarTransition t := by
  have hρ := (Real.smoothTransition.contDiff.differentiable_one (3 * t - 1)).hasDerivAt
  have hlin : HasDerivAt (fun t : ℝ ↦ 3 * t - 1) 3 t := by
    simpa using ((hasDerivAt_id t).const_mul 3).sub_const 1
  have h := hρ.comp t hlin
  change HasDerivAt collarTransition _ t at h
  rw [h.deriv]
  exact mul_pos (deriv_smoothTransition_pos ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (by norm_num)

private theorem collarTransition_strictMonoOn :
    StrictMonoOn collarTransition (Ioo (1 / 3) (2 / 3)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    contDiff_collarTransition.continuous.continuousOn
  intro t ht
  exact deriv_collarTransition_pos (by simpa only [interior_Ioo] using ht)

private theorem collarTransition_mem_Ioo_iff {t : ℝ} :
    collarTransition t ∈ Ioo 0 1 ↔ t ∈ Ioo (1 / 3) (2 / 3) := by
  constructor
  · intro ht
    constructor
    · by_contra h
      rw [collarTransition_eq_zero (le_of_not_gt h)] at ht
      exact lt_irrefl _ ht.1
    · by_contra h
      rw [collarTransition_eq_one (le_of_not_gt h)] at ht
      exact lt_irrefl _ ht.2
  · intro ht
    exact ⟨Real.smoothTransition.pos_of_pos (by linarith [ht.1]),
      Real.smoothTransition.lt_one_of_lt_one (by linarith [ht.2])⟩

private theorem existsUnique_collarTransition_eq {q : ℝ} (hq : q ∈ Ioo 0 1) :
    ∃! t : ℝ, collarTransition t = q := by
  have hq' : q ∈ Icc (collarTransition 0) (collarTransition 1) := by
    rw [collarTransition_eq_zero (by norm_num : (0 : ℝ) ≤ 1 / 3),
      collarTransition_eq_one (by norm_num : (2 : ℝ) / 3 ≤ 1)]
    exact ⟨hq.1.le, hq.2.le⟩
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    contDiff_collarTransition.continuous.continuousOn hq'
  refine ⟨t, ht, fun u hu ↦ ?_⟩
  apply collarTransition_strictMonoOn.injOn
  · exact collarTransition_mem_Ioo_iff.mp (hu ▸ hq)
  · exact collarTransition_mem_Ioo_iff.mp (ht ▸ hq)
  · exact hu.trans ht.symm

private theorem normalCoeff_eq_zero_iff {b q : ℝ} (hb : b ≠ 0) (hq : q ∈ Icc 0 1) :
    (1 - q) * b + q = 0 ↔ b < 0 ∧ q = -b / (1 - b) := by
  constructor
  · intro hz
    have hq1 : q < 1 := lt_of_le_of_ne hq.2 (by intro he; rw [he] at hz; norm_num at hz)
    have hb0 : b < 0 := by
      have : b ≤ 0 := by
        by_contra h
        have hp := mul_pos (sub_pos.mpr hq1) (lt_of_not_ge h)
        linarith [hq.1]
      exact lt_of_le_of_ne this hb
    refine ⟨hb0, (eq_div_iff (by linarith : 1 - b ≠ 0)).mpr ?_⟩
    nlinarith
  · rintro ⟨hb0, hq'⟩
    have hq'' := (eq_div_iff (by linarith : 1 - b ≠ 0)).mp hq'
    nlinarith

private theorem inward_zero_height_mem_Ioo {b : ℝ} (hb : b < 0) :
    -b / (1 - b) ∈ Ioo 0 1 := by
  have hd : 0 < 1 - b := by linarith
  exact ⟨div_pos (neg_pos.mpr hb) hd, (div_lt_one hd).mpr (by linarith)⟩

section ProductManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


def collarExtension (T : ∀ x : M, TangentSpace I x) (b : M → ℝ) (ρ : ℝ → ℝ)
    (p : M × ℝ) : TangentSpace (I.prod 𝓘(ℝ, ℝ)) p :=
  (T p.1, (1 - ρ p.2) * b p.1 + ρ p.2)

theorem equivTangentBundleProd_collarExtension (T : ∀ x : M, TangentSpace I x)
    (b : M → ℝ) (ρ : ℝ → ℝ) (p : M × ℝ) :
    equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ ⟨p, collarExtension T b ρ p⟩ =
      (⟨p.1, T p.1⟩, ⟨p.2, (1 - ρ p.2) * b p.1 + ρ p.2⟩) := rfl


theorem contMDiff_collarExtension [IsManifold I 1 M] {n : ℕ∞ω}
    {T : ∀ x : M, TangentSpace I x} {b : M → ℝ} {ρ : ℝ → ℝ}
    (hT : ContMDiff I I.tangent n (fun x ↦ (⟨x, T x⟩ : TangentBundle I M)))
    (hb : ContMDiff I 𝓘(ℝ, ℝ) n b) (hρ : ContDiff ℝ n ρ) :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)).tangent n
      (fun p ↦ (⟨p, collarExtension T b ρ p⟩ : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
  have hρ' : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n (fun p : M × ℝ ↦ ρ p.2) :=
    hρ.contMDiff.comp contMDiff_snd
  have hN : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) n
      (fun p : M × ℝ ↦ (1 - ρ p.2) * b p.1 + ρ p.2) :=
    ((contMDiff_const.sub hρ').mul (hb.comp contMDiff_fst)).add hρ'
  have hR : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ).tangent n
      (fun p : M × ℝ ↦ (⟨p.2, (1 - ρ p.2) * b p.1 + ρ p.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    intro p
    apply Bundle.contMDiffAt_totalSpace.mpr
    refine ⟨contMDiff_snd p, ?_⟩
    convert hN p using 1
    simp
  exact contMDiff_equivTangentBundleProd_symm.comp
    ((hT.comp contMDiff_fst).prodMk hR)


theorem collarExtension_eq_boundaryPair (T : ∀ x : M, TangentSpace I x)
    (b : M → ℝ) {p : M × ℝ} (hp : p.2 ≤ 1 / 3) :
    collarExtension T b collarTransition p = (T p.1, b p.1) := by
  simp [collarExtension, collarTransition_eq_zero hp]
  rfl


theorem collarExtension_eq_outwardPair (T : ∀ x : M, TangentSpace I x)
    (b : M → ℝ) {p : M × ℝ} (hp : 2 / 3 ≤ p.2) :
    collarExtension T b collarTransition p = (T p.1, 1) := by
  simp [collarExtension, collarTransition_eq_one hp]
  rfl

theorem collarExtension_eq_zero_iff {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {ρ : ℝ → ℝ} {p : M × ℝ}
    (hboundary : T p.1 = 0 → b p.1 ≠ 0) (hρ : ρ p.2 ∈ Icc 0 1) :
    collarExtension T b ρ p = 0 ↔
      T p.1 = 0 ∧ b p.1 < 0 ∧ ρ p.2 = -b p.1 / (1 - b p.1) := by
  change (T p.1, (1 - ρ p.2) * b p.1 + ρ p.2) = (0, 0) ↔ _
  rw [Prod.mk.injEq]
  exact and_congr_right fun hT ↦ normalCoeff_eq_zero_iff (hboundary hT) hρ

theorem existsUnique_collarExtension_eq_zero {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {x : M} (hT : T x = 0) (hb : b x < 0) :
    ∃! t : ℝ, collarExtension T b collarTransition (x, t) = 0 := by
  obtain ⟨t, ht, huniq⟩ := existsUnique_collarTransition_eq (inward_zero_height_mem_Ioo hb)
  refine ⟨t, ?_, fun u hu ↦ ?_⟩
  · exact (collarExtension_eq_zero_iff (fun _ ↦ hb.ne) (collarTransition_mem_Icc t)).mpr
      ⟨hT, hb, ht⟩
  · exact huniq u ((collarExtension_eq_zero_iff (fun _ ↦ hb.ne)
      (collarTransition_mem_Icc u)).mp hu).2.2


theorem collarExtension_zero_height_mem_Ioo {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {p : M × ℝ} (hboundary : T p.1 = 0 → b p.1 ≠ 0)
    (hp : collarExtension T b collarTransition p = 0) :
    p.2 ∈ Ioo (1 / 3) (2 / 3) := by
  obtain ⟨_, hb, hρ⟩ := (collarExtension_eq_zero_iff hboundary
    (collarTransition_mem_Icc p.2)).mp hp
  exact collarTransition_mem_Ioo_iff.mp (hρ ▸ inward_zero_height_mem_Ioo hb)

theorem hasDerivAt_collarExtension_normal {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {ρ : ℝ → ℝ} {x : M} {t ρ' : ℝ} (hρ : HasDerivAt ρ ρ' t) :
    HasDerivAt (fun s ↦ (collarExtension T b ρ (x, s)).2) (ρ' * (1 - b x)) t := by
  have h := ((hρ.const_sub 1).mul_const (b x)).add hρ
  have heq : -ρ' * b x + ρ' = ρ' * (1 - b x) := by ring
  rw [heq] at h
  exact h


theorem collarExtension_normal_deriv_pos {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} {p : M × ℝ} (hboundary : T p.1 = 0 → b p.1 ≠ 0)
    (hp : collarExtension T b collarTransition p = 0) :
    0 < deriv (fun t ↦ (collarExtension T b collarTransition (p.1, t)).2) p.2 := by
  obtain ⟨_, hb, _⟩ := (collarExtension_eq_zero_iff hboundary
    (collarTransition_mem_Icc p.2)).mp hp
  have hρ := contDiff_collarTransition.differentiable (by simp) p.2 |>.hasDerivAt
  rw [(hasDerivAt_collarExtension_normal (T := T) (b := b) hρ).deriv]
  exact mul_pos (deriv_collarTransition_pos (collarExtension_zero_height_mem_Ioo hboundary hp))
    (by linarith)

theorem collarExtension_zeroSet_proj_bijOn {T : ∀ x : M, TangentSpace I x}
    {b : M → ℝ} (hboundary : ∀ x, T x = 0 → b x ≠ 0) :
    BijOn Prod.fst {p : M × ℝ | collarExtension T b collarTransition p = 0}
      {x : M | T x = 0 ∧ b x < 0} := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact ((collarExtension_eq_zero_iff (hboundary p.1)
      (collarTransition_mem_Icc p.2)).mp hp).imp_right And.left
  · rintro ⟨x, t⟩ hp ⟨y, u⟩ hq hxy
    change x = y at hxy
    subst y
    obtain ⟨hT, hb, _⟩ := (collarExtension_eq_zero_iff (hboundary x)
      (collarTransition_mem_Icc t)).mp hp
    obtain ⟨v, _, hv⟩ := existsUnique_collarExtension_eq_zero hT hb
    exact Prod.ext rfl ((hv t hp).trans (hv u hq).symm)
  · intro x hx
    obtain ⟨t, ht, _⟩ := existsUnique_collarExtension_eq_zero hx.1 hx.2
    exact ⟨(x, t), ht, rfl⟩

end ProductManifold

section Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem collarExtension_components_eq_comp (T : E → E) (b : E → ℝ) (ρ : ℝ → ℝ) :
    collarExtension (I := 𝓘(ℝ, E)) T b ρ =
      (fun q : E × ℝ ↦ (T q.1, q.2)) ∘
        (fun p : E × ℝ ↦ (p.1, (1 - ρ p.2) * b p.1 + ρ p.2)) := rfl

end Coordinates

end DifferentialGeometry.VectorField
