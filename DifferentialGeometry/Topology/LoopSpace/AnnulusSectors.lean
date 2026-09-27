import DifferentialGeometry.Topology.LoopSpace.PolarAnnulus
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.Strip
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.SpecialFunctions.ExpDeriv



noncomputable section

open Set NormedSpace
open DifferentialGeometry.Analysis
open scoped Topology NNReal ContDiff

namespace DifferentialGeometry.Topology


def annulusPolarMap (z : ℂ) : ℂ :=
  ((z.re + 1) / 2 : ℝ) • (AddCircle.toCircle (z.im : loopCircle) : ℂ)

theorem contDiff_annulusPolarMap : ContDiff ℝ ∞ annulusPolarMap := by
  unfold annulusPolarMap
  simp only [AddCircle.toCircle_apply_mk, Circle.coe_exp, div_one]
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have hc : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

theorem norm_annulusPolarMap {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) :
    ‖annulusPolarMap z‖ = (z.re + 1) / 2 := by
  rw [annulusPolarMap, norm_smul, Real.norm_eq_abs, Circle.norm_coe, mul_one,
    abs_of_pos (by linarith [hz.1] : 0 < (z.re + 1) / 2)]


theorem polarAnnulusCoordinates_annulusPolarMap {z : ℂ} (hz : z.re ∈ Icc (0 : ℝ) 1) :
    polarAnnulusCoordinates (annulusPolarMap z) = (z.re, (z.im : loopCircle)) := by
  unfold polarAnnulusCoordinates
  rw [norm_annulusPolarMap hz]
  have hd : radialDirection (annulusPolarMap z) = AddCircle.toCircle (z.im : loopCircle) :=
    radialDirection_pos_smul (by linarith [hz.1] : 0 < (z.re + 1) / 2) _
  rw [hd, ← AddCircle.homeomorphCircle_apply one_ne_zero]
  simp
  ring



theorem exists_annulusPolarMap_lipschitz :
    ∃ K : ℝ≥0, LipschitzOnWith K annulusPolarMap unitSquare := by
  have hconv : Convex ℝ unitSquare := by
    change Convex ℝ ((Complex.reCLM ⁻¹' Icc (0 : ℝ) 1) ∩ (Complex.imCLM ⁻¹' Icc (0 : ℝ) 1))
    exact ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.reCLM.toLinearMap).inter
      ((convex_Icc (0 : ℝ) 1).linear_preimage Complex.imCLM.toLinearMap)
  exact contDiff_annulusPolarMap.contDiffOn.exists_lipschitzOnWith (by simp) hconv isCompact_unitSquare



theorem annulusPolarMap_inverse_dist_le {a : ℝ} {z w : ℂ}
    (hz : z.re ∈ Icc (0 : ℝ) 1) (hw : w.re ∈ Icc (0 : ℝ) 1)
    (hzθ : z.im ∈ Icc a (a + 1 / 2)) (hwθ : w.im ∈ Icc a (a + 1 / 2)) :
    dist z w ≤ 8 * dist (annulusPolarMap z) (annulusPolarMap w) := by
  have hzR : 1 / 2 ≤ ‖annulusPolarMap z‖ := by rw [norm_annulusPolarMap hz]; linarith [hz.1]
  have hwR : 1 / 2 ≤ ‖annulusPolarMap w‖ := by rw [norm_annulusPolarMap hw]; linarith [hw.1]
  have h := polarAnnulusCoordinates_lipschitz.dist_le_mul _ hzR _ hwR
  rw [polarAnnulusCoordinates_annulusPolarMap hz, polarAnnulusCoordinates_annulusPolarMap hw] at h
  have hnorm : ‖((z.im - w.im : ℝ) : loopCircle)‖ = |z.im - w.im| :=
    (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr (by
      rw [abs_one, abs_le]
      constructor <;> linarith [hzθ.1, hzθ.2, hwθ.1, hwθ.2])
  have hc : dist (z.im : loopCircle) (w.im : loopCircle) = |z.im - w.im| := by
    rw [dist_eq_norm, ← AddCircle.coe_sub, hnorm]
  rw [Prod.dist_eq, Real.dist_eq, hc] at h
  have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
  simp only [Complex.sub_re, Complex.sub_im] at hn
  rw [Complex.dist_eq]
  have hh := max_le_iff.mp h
  norm_num only [NNReal.coe_ofNat] at hh
  linarith [hh.1, hh.2]


def annulusSector (a : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo (0 : ℝ) 1 ∧ z.im ∈ Ioo a (a + 1 / 2)}

theorem isOpen_annulusSector (a : ℝ) : IsOpen (annulusSector a) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)

theorem annulusSector_subset_square {a : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a + 1 / 2 ≤ 1) :
    annulusSector a ⊆ unitSquare := by
  intro z hz
  exact ⟨Ioo_subset_Icc_self hz.1, ⟨ha₀.trans hz.2.1.le, hz.2.2.le.trans ha₁⟩⟩

theorem annulusPolarMap_injective_on_period :
    InjOn annulusPolarMap {z : ℂ | z.re ∈ Icc (0 : ℝ) 1 ∧ z.im ∈ Ico (0 : ℝ) 1} := by
  intro z hz w hw heq
  have h := congrArg polarAnnulusCoordinates heq
  rw [polarAnnulusCoordinates_annulusPolarMap hz.1, polarAnnulusCoordinates_annulusPolarMap hw.1] at h
  apply Complex.ext (congrArg Prod.fst h)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa using hz.2) (by simpa using hw.2)).mp (congrArg Prod.snd h)

end DifferentialGeometry.Topology
