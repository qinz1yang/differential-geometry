import DifferentialGeometry.Analysis.ODE.Flow.ParamTangent
import DifferentialGeometry.Analysis.Calculus.Periodic.Derivative

namespace DifferentialGeometry.Analysis.ODE.Flow

open Metric Set
open scoped NNReal

theorem paramTangentVF_lipschitzOnWith
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (t : ℝ) {V : Set X} {L₀ L₁ B M : ℝ≥0}
    (hv : LipschitzOnWith L₀ (v t) V)
    (hDv : LipschitzOnWith L₁ (fderiv ℝ (v t)) V)
    (hbound : ∀ x ∈ V, ‖fderiv ℝ (v t) x‖ ≤ (M : ℝ)) :
    LipschitzOnWith (max L₀ (L₁ * B + M)) (paramTangentVF P v t)
      (V ×ˢ closedBall (0 : P →L[ℝ] X) (B : ℝ)) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro z hz w hw
  have hfst : dist z.1 w.1 ≤ dist z w := le_max_left _ _
  have hsnd : dist z.2 w.2 ≤ dist z w := le_max_right _ _
  have hZ : ‖z.2‖ ≤ (B : ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz.2
  have hD := hDv.dist_le_mul z.1 hz.1 w.1 hw.1
  have hnorm : ‖fderiv ℝ (v t) z.1 - fderiv ℝ (v t) w.1‖ ≤
      (L₁ : ℝ) * dist z.1 w.1 := by
    simpa only [dist_eq_norm] using hD
  have heq : (fderiv ℝ (v t) z.1).comp z.2 - (fderiv ℝ (v t) w.1).comp w.2 =
      (fderiv ℝ (v t) z.1 - fderiv ℝ (v t) w.1).comp z.2 +
        (fderiv ℝ (v t) w.1).comp (z.2 - w.2) := by
    ext u
    simp only [sub_apply, ContinuousLinearMap.comp_apply,
      add_apply, map_sub]
    abel
  have hsecond : dist ((fderiv ℝ (v t) z.1).comp z.2)
      ((fderiv ℝ (v t) w.1).comp w.2) ≤
      ((L₁ : ℝ) * B + M) * dist z w := by
    rw [dist_eq_norm, heq]
    calc
      ‖(fderiv ℝ (v t) z.1 - fderiv ℝ (v t) w.1).comp z.2 +
          (fderiv ℝ (v t) w.1).comp (z.2 - w.2)‖ ≤
          ‖fderiv ℝ (v t) z.1 - fderiv ℝ (v t) w.1‖ * ‖z.2‖ +
            ‖fderiv ℝ (v t) w.1‖ * ‖z.2 - w.2‖ :=
        (norm_add_le _ _).trans (add_le_add
          (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ ((L₁ : ℝ) * dist z.1 w.1) * B + M * dist z.2 w.2 := by
        rw [dist_eq_norm z.2 w.2]
        gcongr
        exact hbound w.1 hw.1
      _ ≤ ((L₁ : ℝ) * dist z w) * B + M * dist z w := by
        gcongr
      _ = ((L₁ : ℝ) * B + M) * dist z w := by ring
  have hK₀ : (L₀ : ℝ) ≤ (max L₀ (L₁ * B + M) : ℝ≥0) := by
    exact_mod_cast le_max_left L₀ (L₁ * B + M)
  have hK₁ : (L₁ : ℝ) * B + M ≤ (max L₀ (L₁ * B + M) : ℝ≥0) := by
    exact_mod_cast le_max_right L₀ (L₁ * B + M)
  change max (dist (v t z.1) (v t w.1))
    (dist ((fderiv ℝ (v t) z.1).comp z.2) ((fderiv ℝ (v t) w.1).comp w.2)) ≤ _
  apply max_le
  · exact (hv.dist_le_mul z.1 hz.1 w.1 hw.1).trans
      ((mul_le_mul_of_nonneg_left hfst L₀.coe_nonneg).trans
        (mul_le_mul_of_nonneg_right hK₀ dist_nonneg))
  · exact hsecond.trans (mul_le_mul_of_nonneg_right hK₁ dist_nonneg)

theorem paramTangentVF_lipschitzOnWith_closedBall
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : ℝ → X → X) (t : ℝ) (z₀ : X × (P →L[ℝ] X))
    (r L₀ L₁ M : ℝ≥0)
    (hv : LipschitzOnWith L₀ (v t) (closedBall z₀.1 (r : ℝ)))
    (hDv : LipschitzOnWith L₁ (fderiv ℝ (v t)) (closedBall z₀.1 (r : ℝ)))
    (hbound : ∀ x ∈ closedBall z₀.1 (r : ℝ), ‖fderiv ℝ (v t) x‖ ≤ (M : ℝ)) :
    LipschitzOnWith (max L₀ (L₁ * (‖z₀.2‖₊ + r) + M)) (paramTangentVF P v t)
      (closedBall z₀ (r : ℝ)) := by
  apply (paramTangentVF_lipschitzOnWith (P := P) v t hv hDv hbound
    (B := ‖z₀.2‖₊ + r)).mono
  intro z hz
  have hz' : dist z.1 z₀.1 ≤ (r : ℝ) ∧ dist z.2 z₀.2 ≤ (r : ℝ) := by
    simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using hz
  refine ⟨hz'.1, ?_⟩
  change dist z.2 0 ≤ ((‖z₀.2‖₊ + r : ℝ≥0) : ℝ)
  simpa only [dist_zero_right, NNReal.coe_add, coe_nnnorm] using
    norm_le_norm_add_const_of_dist_le hz'.2

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set

theorem norm_fderiv_paramTangentVF_sub_le
    {P X : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v w : ℝ → X → X) (t : ℝ) (x : X) (Z : P →L[ℝ] X)
    (hv : DifferentiableAt ℝ (v t) x)
    (hDv : DifferentiableAt ℝ (fderiv ℝ (v t)) x)
    (hw : DifferentiableAt ℝ (w t) x)
    (hDw : DifferentiableAt ℝ (fderiv ℝ (w t)) x) :
    ‖fderiv ℝ (paramTangentVF P v t) (x, Z) -
        fderiv ℝ (paramTangentVF P w t) (x, Z)‖ ≤
      ‖fderiv ℝ (v t) x - fderiv ℝ (w t) x‖ +
        ‖fderiv ℝ (fderiv ℝ (v t)) x - fderiv ℝ (fderiv ℝ (w t)) x‖ * ‖Z‖ := by
  let A := fderiv ℝ (v t) x - fderiv ℝ (w t) x
  let B := fderiv ℝ (fderiv ℝ (v t)) x - fderiv ℝ (fderiv ℝ (w t)) x
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  rcases q with ⟨h, H⟩
  have hfirst : ‖fderiv ℝ (v t) x h - fderiv ℝ (w t) x h‖ ≤
      (‖A‖ + ‖B‖ * ‖Z‖) * ‖(h, H)‖ := by
    change ‖A h‖ ≤ _
    calc
      ‖A h‖ ≤ ‖A‖ * ‖h‖ := A.le_opNorm h
      _ ≤ ‖A‖ * ‖(h, H)‖ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      _ ≤ (‖A‖ + ‖B‖ * ‖Z‖) * ‖(h, H)‖ :=
        mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
          (norm_nonneg _)
  have heq : (fderiv ℝ (v t) x).comp H +
        (fderiv ℝ (fderiv ℝ (v t)) x h).comp Z -
        ((fderiv ℝ (w t) x).comp H +
          (fderiv ℝ (fderiv ℝ (w t)) x h).comp Z) =
      A.comp H + (B h).comp Z := by
    ext u
    simp only [A, B, ContinuousLinearMap.comp_apply, add_apply, sub_apply]
    abel
  have hsecond : ‖A.comp H + (B h).comp Z‖ ≤
      (‖A‖ + ‖B‖ * ‖Z‖) * ‖(h, H)‖ := by
    calc
      ‖A.comp H + (B h).comp Z‖ ≤ ‖A‖ * ‖H‖ + ‖B h‖ * ‖Z‖ :=
        (norm_add_le _ _).trans (add_le_add
          (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ ‖A‖ * ‖(h, H)‖ + (‖B‖ * ‖(h, H)‖) * ‖Z‖ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (B.le_opNorm h).trans
            (mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _))
      _ = (‖A‖ + ‖B‖ * ‖Z‖) * ‖(h, H)‖ := by ring
  rw [sub_apply, fderiv_paramTangentVF_apply v t x h Z H hv hDv,
    fderiv_paramTangentVF_apply w t x h Z H hw hDw]
  simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub]
  rw [heq]
  exact max_le hfirst hsecond

end DifferentialGeometry.Analysis.ODE.Flow

namespace DifferentialGeometry.Analysis.ODE.Flow

open Filter Metric Set
open scoped ContDiff NNReal

theorem paramTangentVF_lipschitzOnWith_closedBall_of_periodic
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (v : ℝ → ℝ → ℝ) (t : ℝ) (z₀ : ℝ × (P →L[ℝ] ℝ))
    (r L₀ L₁ : ℝ≥0) {c : ℝ} (hc : 0 < c)
    (hper : Function.Periodic (v t) c) (hv : ContDiff ℝ 2 (v t))
    (hDv : ∀ x ∈ Icc (0 : ℝ) c, ‖fderiv ℝ (v t) x‖ ≤ (L₀ : ℝ))
    (hD₂v : ∀ x ∈ Icc (0 : ℝ) c, ‖fderiv ℝ (fderiv ℝ (v t)) x‖ ≤ (L₁ : ℝ)) :
    LipschitzOnWith (max L₀ (L₁ * (‖z₀.2‖₊ + r) + L₀)) (paramTangentVF P v t)
      (closedBall z₀ (r : ℝ)) := by
  have hvLip : LipschitzWith L₀ (v t) :=
    hper.lipschitzWith_of_norm_fderiv_le_Icc hc (hv.differentiable (by norm_num)) hDv
  have hDvLip : LipschitzWith L₁ (fderiv ℝ (v t)) :=
    (hper.fderiv (𝕜 := ℝ)).lipschitzWith_of_norm_fderiv_le_Icc hc
      ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) hD₂v
  apply paramTangentVF_lipschitzOnWith_closedBall v t z₀ r L₀ L₁ L₀
    hvLip.lipschitzOnWith hDvLip.lipschitzOnWith
  intro x _
  obtain ⟨y, hy, hxy⟩ := (hper.fderiv (𝕜 := ℝ)).exists_mem_Ico₀ hc x
  rw [hxy]
  exact hDv y ⟨hy.1, hy.2.le⟩

theorem paramTangentVF_eventually_lipschitzOnWith_closedBall_of_periodic
    {ι P Q : Type*} {l : Filter ι}
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    {v : ι → ℝ → ℝ → ℝ} {J : Set ℝ} {K : Set P}
    (z : P → ℝ → ℝ × (Q →L[ℝ] ℝ)) (r B L₀ L₁ : ℝ≥0) {c : ℝ} (hc : 0 < c)
    (hper : ∀ᶠ i in l, ∀ t ∈ J, Function.Periodic (v i t) c)
    (hv : ∀ᶠ i in l, ∀ t ∈ J, ContDiff ℝ 2 (v i t))
    (hbound : ∀ᶠ i in l, ∀ t ∈ J, ∀ x ∈ Icc (0 : ℝ) c,
      ‖fderiv ℝ (v i t) x‖ ≤ (L₀ : ℝ) ∧
        ‖fderiv ℝ (fderiv ℝ (v i t)) x‖ ≤ (L₁ : ℝ))
    (hz : ∀ p ∈ K, ∀ t ∈ J, ‖(z p t).2‖ ≤ (B : ℝ)) :
    ∀ᶠ i in l, ∀ p ∈ K, ∀ t ∈ J,
      LipschitzOnWith (max L₀ (L₁ * (B + r) + L₀)) (paramTangentVF Q (v i) t)
        (closedBall (z p t) (r : ℝ)) := by
  filter_upwards [hper, hv, hbound] with i hpi hvi hbi
  intro p hp t ht
  have hflow := paramTangentVF_lipschitzOnWith_closedBall_of_periodic
    (v i) t (z p t) r L₀ L₁ hc (hpi t ht) (hvi t ht)
    (fun x hx => (hbi t ht x hx).1) (fun x hx => (hbi t ht x hx).2)
  apply hflow.weaken
  have hz' : ‖(z p t).2‖₊ ≤ B := by exact_mod_cast hz p hp t ht
  gcongr

end DifferentialGeometry.Analysis.ODE.Flow
