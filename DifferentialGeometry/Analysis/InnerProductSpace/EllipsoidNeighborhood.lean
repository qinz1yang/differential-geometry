import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit
import Mathlib.Topology.MetricSpace.ProperSpace

open Set Metric
open scoped Topology

namespace EuclideanSpace

theorem exists_linearEquiv_image_closedBall_subset_of_disk_subset {n : ℕ}
    {r : ℝ} (hr : 0 ≤ r) {U : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    (hU : IsOpen U)
    (hKU : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ r →
      (equivProdLast n).symm (x, 0) ∈ U) :
    ∃ (A : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (n + 1))) (δ : ℝ), 0 < δ ∧
      A '' closedBall 0 1 ⊆ U ∧
      ∀ (x : EuclideanSpace ℝ (Fin n)) (s : ℝ), ‖x‖ ≤ r + δ → |s| ≤ δ →
        (equivProdLast n).symm (x, s) ∈ A '' closedBall 0 1 := by
  let E := EuclideanSpace ℝ (Fin (n + 1))
  let F := EuclideanSpace ℝ (Fin n)
  let L := equivProdLast (𝕜 := ℝ) n
  let f : ℝ → E → E := fun ε z => L.symm ((r + ε) • (L z).1, ε * (L z).2)
  have hf : Continuous (fun p : ℝ × E => f p.1 p.2) := by
    exact L.symm.continuous.comp
      (((continuous_const.add continuous_fst).smul (L.continuous.fst.comp continuous_snd)).prodMk
        (continuous_fst.mul (L.continuous.snd.comp continuous_snd)))
  have hnear : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ z ∈ closedBall (0 : E) 1, f ε z ∈ U := by
    apply (isCompact_closedBall (0 : E) 1).eventually_forall_of_forall_eventually
    intro z hz
    apply hf.continuousAt.eventually_mem (hU.mem_nhds ?_)
    dsimp [f]
    simp only [add_zero, zero_mul]
    apply hKU
    have hz' : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz
    have hfst : ‖(L z).1‖ ≤ 1 := by
      have he := norm_sq_equivProdLast (𝕜 := ℝ) n z
      change ‖z‖ ^ 2 = ‖(L z).1‖ ^ 2 + ‖(L z).2‖ ^ 2 at he
      nlinarith [norm_nonneg z, norm_nonneg (L z).1, sq_nonneg ‖(L z).2‖]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left hfst hr).trans (by simp)
  obtain ⟨η, hη, hηU⟩ := Metric.eventually_nhds_iff.mp hnear
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have ha : 0 < r + ε := add_pos_of_nonneg_of_pos hr hε
  let T : F ≃L[ℝ] F := (LinearEquiv.smulOfNeZero ℝ F (r + ε) ha.ne').toContinuousLinearEquiv
  let S : ℝ ≃L[ℝ] ℝ := (LinearEquiv.smulOfNeZero ℝ ℝ ε hε.ne').toContinuousLinearEquiv
  let A : E ≃L[ℝ] E := (L.trans (T.prodCongr S)).trans L.symm
  have hA (z : E) : A z = f ε z := rfl
  have hAU : A '' closedBall 0 1 ⊆ U := by
    rintro z ⟨y, hy, rfl⟩
    rw [hA]
    apply hηU _ y hy
    simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hε]
    dsimp [ε]
    linarith
  have hcore : ∀ x : F, ‖x‖ ≤ r + ε / 2 → L.symm (x, 0) ∈ A '' ball 0 1 := by
    intro x hx
    refine ⟨L.symm ((r + ε)⁻¹ • x, 0), ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      apply (sq_lt_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
      rw [norm_sq_equivProdLast_symm]
      simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero, norm_smul,
        Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), one_pow]
      have hlt : (r + ε)⁻¹ * ‖x‖ < 1 := by
        rw [inv_mul_lt_iff₀ ha]
        linarith
      nlinarith [mul_nonneg (inv_nonneg.mpr ha.le) (norm_nonneg x)]
    · rw [hA]
      simp [f, L, ha.ne', smul_smul]
  have hopen : IsOpen (A '' ball (0 : E) 1) := A.toHomeomorph.isOpenMap _ isOpen_ball
  have hstrip : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ x ∈ closedBall (0 : F) (r + ε / 2),
      L.symm (x, s) ∈ A '' ball 0 1 := by
    apply (isCompact_closedBall (0 : F) (r + ε / 2)).eventually_forall_of_forall_eventually
    intro x hx
    have hc : Continuous (fun p : ℝ × F => L.symm (p.2, p.1)) :=
      L.symm.continuous.comp (continuous_snd.prodMk continuous_fst)
    exact hc.continuousAt.eventually_mem
      (hopen.mem_nhds (hcore x (mem_closedBall_zero_iff.mp hx)))
  obtain ⟨ζ, hζ, hζstrip⟩ := Metric.eventually_nhds_iff.mp hstrip
  refine ⟨A, min (ε / 2) (ζ / 2), lt_min (by positivity) (by positivity), hAU, ?_⟩
  intro x s hx hs
  apply image_mono ball_subset_closedBall
  apply hζstrip ?_ x
    (mem_closedBall_zero_iff.mpr (hx.trans (add_le_add_right (min_le_left _ _) r)))
  simp only [dist_zero_right, Real.norm_eq_abs]
  exact (hs.trans (min_le_right _ _)).trans_lt (by linarith)

end EuclideanSpace
