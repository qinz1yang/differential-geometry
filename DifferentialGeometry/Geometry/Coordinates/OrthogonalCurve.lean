import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Normed.Operator.Bilinear

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private def normalProjection (B : V →L[ℝ] V →L[ℝ] ℝ) (t : V) : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - (B t t)⁻¹ • (B t).smulRight t

private theorem normalProjection_apply (B : V →L[ℝ] V →L[ℝ] ℝ) (t v : V) :
    normalProjection B t v = v - (B t v / B t t) • t := by
  simp only [normalProjection, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, smul_smul, div_eq_mul_inv]
  rw [mul_comm]

private theorem apply_normalProjection (B : V →L[ℝ] V →L[ℝ] ℝ) (t v : V)
    (ht : B t t ≠ 0) : B t (normalProjection B t v) = 0 := by
  rw [normalProjection_apply, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ ht, sub_self]

private def affineCurveMap (c : ℝ → V) (N : ℝ → V →L[ℝ] V)
    (l : V →L[ℝ] ℝ) (t : V) (z : V) : V :=
  c (l z) + N (l z) (z - l z • t)

private theorem affineCurveMap_axis (c : ℝ → V) (N : ℝ → V →L[ℝ] V)
    (l : V →L[ℝ] ℝ) (t : V) (hlt : l t = 1) (s : ℝ) :
    affineCurveMap c N l t (s • t) = c s := by
  simp [affineCurveMap, map_smul, hlt]

private theorem hasFDerivAt_affineCurveMap_axis {c : ℝ → V} {N : ℝ → V →L[ℝ] V}
    {l : V →L[ℝ] ℝ} {t : V} (hlt : l t = 1) {s : ℝ}
    (hc : DifferentiableAt ℝ c s) (hN : DifferentiableAt ℝ N s) :
    HasFDerivAt (affineCurveMap c N l t)
      (l.smulRight (deriv c s) + (N s).comp
        (ContinuousLinearMap.id ℝ V - l.smulRight t)) (s • t) := by
  let A : V →L[ℝ] V := ContinuousLinearMap.id ℝ V - l.smulRight t
  have hls : l (s • t) = s := by simp [map_smul, hlt]
  have hAz : A (s • t) = 0 := by simp [A, hlt]
  have hcD := (show HasFDerivAt c (ContinuousLinearMap.toSpanSingleton ℝ (deriv c s))
    (l (s • t)) by rw [hls]; exact hc.hasDerivAt.hasFDerivAt).comp (s • t) l.hasFDerivAt
  have hND := (show HasFDerivAt N (fderiv ℝ N s) (l (s • t)) by
    rw [hls]; exact hN.hasFDerivAt).comp (s • t) l.hasFDerivAt
  have hd := hcD.add (hND.clm_apply A.hasFDerivAt)
  convert! hd using 1
  ext v
  simp [hls, hAz, A]

private theorem contDiffOn_normalProjection {J : Set ℝ} {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ}
    {T : ℝ → V} (hB : ContDiffOn ℝ ∞ B J) (hT : ContDiffOn ℝ ∞ T J)
    (hq : ∀ s ∈ J, B s (T s) (T s) ≠ 0) :
    ContDiffOn ℝ ∞ (fun s => normalProjection (B s) (T s)) J := by
  have hqC := (hB.clm_apply hT).clm_apply hT
  exact contDiffOn_const.sub ((hqC.inv hq).smul ((hB.clm_apply hT).smulRight hT))

theorem exists_orthogonal_curve_coordinates [CompleteSpace V]
    {J : Set ℝ} (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J)
    {c : ℝ → V} (hc : ContDiffOn ℝ ∞ c J)
    {B : ℝ → V →L[ℝ] V →L[ℝ] ℝ} (hB : ContDiffOn ℝ ∞ B J)
    (hq0 : B 0 (deriv c 0) (deriv c 0) ≠ 0) :
    let t := deriv c 0
    let l : V →L[ℝ] ℝ := (B 0 t t)⁻¹ • B 0 t
    ∃ e : OpenPartialHomeomorph V V,
      0 ∈ e.source ∧ e.source ⊆ l ⁻¹' J ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ z, e z = c (l z) + (z - l z • t) -
        (B (l z) (deriv c (l z)) (z - l z • t) /
          B (l z) (deriv c (l z)) (deriv c (l z))) • deriv c (l z)) ∧
      ∀ s, s • t ∈ e.source →
        e (s • t) = c s ∧ e.symm (c s) = s • t ∧
        B s (deriv c s) (deriv c s) ≠ 0 ∧
        ∀ v, B s (fderiv ℝ e (s • t) t) (fderiv ℝ e (s • t) v) =
          B s (deriv c s) (deriv c s) * l v := by
  dsimp only
  let t := deriv c 0
  let l : V →L[ℝ] ℝ := (B 0 t t)⁻¹ • B 0 t
  have hlt : l t = 1 := by simp only [l, smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hq0
  let T := deriv c
  let q : ℝ → ℝ := fun s => B s (T s) (T s)
  have hT : ContDiffOn ℝ ∞ T J := hc.deriv_of_isOpen hJ (by simp)
  have hq : ContDiffOn ℝ ∞ q J := (hB.clm_apply hT).clm_apply hT
  let K : Set ℝ := J ∩ q ⁻¹' {r : ℝ | r ≠ 0}
  have hK : IsOpen K := hq.continuousOn.isOpen_inter_preimage hJ isOpen_ne
  have h0K : (0 : ℝ) ∈ K := ⟨h0, hq0⟩
  let N : ℝ → V →L[ℝ] V := fun s => normalProjection (B s) (T s)
  have hN : ContDiffOn ℝ ∞ N K :=
    contDiffOn_normalProjection (hB.mono inter_subset_left) (hT.mono inter_subset_left)
      (fun s hs => hs.2)
  let F := affineCurveMap c N l t
  have hF : ContDiffOn ℝ ∞ F (l ⁻¹' K) :=
    ((hc.mono inter_subset_left).comp l.contDiff.contDiffOn (fun z hz => hz)).add
      ((hN.comp l.contDiff.contDiffOn (fun z hz => hz)).clm_apply
        (contDiffOn_id.sub (l.contDiff.contDiffOn.smul contDiffOn_const)))
  have hU : IsOpen (l ⁻¹' K) := hK.preimage l.continuous
  have h0U : (0 : V) ∈ l ⁻¹' K := by simpa using h0K
  have hA (v : V) : N 0 v = v - l v • t := by
    rw [normalProjection_apply]
    simp only [l, smul_apply, smul_eq_mul, div_eq_mul_inv]
    rw [mul_comm]
  have hd0 := hasFDerivAt_affineCurveMap_axis hlt
    ((hc.contDiffAt (hJ.mem_nhds h0)).differentiableAt (by simp))
    ((hN.contDiffAt (hK.mem_nhds h0K)).differentiableAt (by simp))
  have hD0 : l.smulRight (deriv c 0) + (N 0).comp
      (ContinuousLinearMap.id ℝ V - l.smulRight t) = ContinuousLinearMap.id ℝ V := by
    ext v
    change l v • t + N 0 (v - l v • t) = v
    rw [hA]
    simp only [map_sub, map_smul, hlt, smul_eq_mul, mul_one, sub_self, zero_smul, sub_zero]
    exact add_sub_cancel _ _
  rw [zero_smul, hD0] at hd0
  obtain ⟨e, he0, heU, he, hei, heF⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv
      (A := ContinuousLinearEquiv.refl ℝ V) hF hU h0U hd0
  refine ⟨e, he0, fun z hz => (heU hz).1, he, hei, ?_, ?_⟩
  · intro z
    rw [heF]
    change c (l z) + N (l z) (z - l z • t) = _
    rw [normalProjection_apply]
    exact (add_sub_assoc _ _ _).symm
  · intro s hs
    have hls : l (s • t) = s := by simp [map_smul, hlt]
    have hsK : s ∈ K := by
      have hh := heU hs
      change l (s • t) ∈ K at hh
      rwa [hls] at hh
    have heaxis : e (s • t) = c s := (heF _).trans (affineCurveMap_axis c N l t hlt s)
    refine ⟨heaxis, ?_, hsK.2, ?_⟩
    · rw [← heaxis]
      exact e.left_inv hs
    · have hd := hasFDerivAt_affineCurveMap_axis hlt
        ((hc.contDiffAt (hJ.mem_nhds hsK.1)).differentiableAt (by simp))
        ((hN.contDiffAt (hK.mem_nhds hsK)).differentiableAt (by simp))
      have heF' : (e : V → V) = F := funext heF
      intro v
      rw [heF', hd.fderiv]
      have hDt : (l.smulRight (deriv c s) + (N s).comp
          (ContinuousLinearMap.id ℝ V - l.smulRight t)) t = deriv c s := by simp [hlt]
      rw [hDt]
      change B s (deriv c s) (l v • deriv c s + N s (v - l v • t)) = _
      rw [map_add, map_smul, smul_eq_mul,
        apply_normalProjection (B s) (deriv c s) (v - l v • t) hsK.2, add_zero, mul_comm]

end DifferentialGeometry.Geometry
