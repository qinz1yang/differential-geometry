import DifferentialGeometry.Geometry.Metric.TensorInner.CoerciveBilinInverse
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue

/-!
# ODEs with a state-dependent coercive mass

Finite-dimensional geometric Galerkin equations have the form

`M(t, u(t)) u'(t) = R(t, u(t))`.

The mass form is nonlinear in the state when the geometric unknown is written
in a local-addition coordinate.  This file supplies the local
Picard--Lindelof theorem for that faithful equation.  It deliberately asks
for continuity only in time at each fixed state and for uniform Lipschitz
bounds only in the state variable, matching the hypotheses of mathlib's
time-dependent Picard theorem.
-/

noncomputable section

open Set Metric
open scoped NNReal Topology

namespace DifferentialGeometry.Analysis.ODE

/-- A uniform Lipschitz bound for a bilinear family transfers a quantitative
coercivity bound at the origin to the whole closed state ball.  The radius is
explicit, so this lemma can be used uniformly in an additional time
parameter. -/
theorem coerOn_of_lip
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : V → V →L[ℝ] V →L[ℝ] ℝ) {c R : ℝ} {K : ℝ≥0}
    (hR : 0 ≤ R)
    (hB_lip : LipschitzOnWith K B (closedBall (0 : V) R))
    (hB_zero : ∀ v : V, c * ‖v‖ * ‖v‖ ≤ B 0 v v)
    (hKR : (K : ℝ) * R ≤ c / 2) :
    ∀ u ∈ closedBall (0 : V) R, ∀ v : V,
      (c / 2) * ‖v‖ * ‖v‖ ≤ B u v v := by
  intro u hu v
  have hzero : (0 : V) ∈ closedBall (0 : V) R :=
    mem_closedBall_self hR
  have huR : ‖u‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hu
  have hdiff : ‖B u - B 0‖ ≤ (K : ℝ) * R := by
    calc
      ‖B u - B 0‖ = dist (B u) (B 0) := (dist_eq_norm _ _).symm
      _ ≤ (K : ℝ) * dist u 0 := hB_lip.dist_le_mul u hu 0 hzero
      _ = (K : ℝ) * ‖u‖ := by rw [dist_zero_right]
      _ ≤ (K : ℝ) * R :=
        mul_le_mul_of_nonneg_left huR K.coe_nonneg
  let D : V →L[ℝ] V →L[ℝ] ℝ := B u - B 0
  have habs : |D v v| ≤ (c / 2) * ‖v‖ * ‖v‖ := by
    calc
      |D v v| = ‖D v v‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖D v‖ * ‖v‖ := (D v).le_opNorm v
      _ ≤ (‖D‖ * ‖v‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right (D.le_opNorm v) (norm_nonneg v)
      _ ≤ (((K : ℝ) * R) * ‖v‖) * ‖v‖ := by
        gcongr
        simpa only [D] using hdiff
      _ ≤ ((c / 2) * ‖v‖) * ‖v‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hKR (norm_nonneg v)) (norm_nonneg v)
      _ = (c / 2) * ‖v‖ * ‖v‖ := rfl
  have hDlow : -((c / 2) * ‖v‖ * ‖v‖) ≤ D v v :=
    neg_le_of_abs_le habs
  have heval : B u v v = B 0 v v + D v v := by
    simp only [D, ContinuousLinearMap.sub_apply]
    ring
  rw [heval]
  calc
    (c / 2) * ‖v‖ * ‖v‖ =
        c * ‖v‖ * ‖v‖ - (c / 2) * ‖v‖ * ‖v‖ := by ring
    _ ≤ B 0 v v + D v v := add_le_add (hB_zero v) hDlow

/-- Local existence for an ODE whose velocity is obtained by raising a
covector through a uniformly coercive, state-dependent bilinear form.

The returned trajectory remains in the input state ball, so its equation is
the genuine untruncated equation throughout the produced interval. -/
theorem stateMass_exists
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V]
    {mass : ℝ → V → V →L[ℝ] V →L[ℝ] ℝ}
    {resid : ℝ → V → (V →L[ℝ] ℝ)}
    {T R c A : ℝ} {Km Kr : ℝ≥0}
    (hT : 0 < T) (hR : 0 < R) (hc : 0 < c) (hA : 0 ≤ A)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u ∈ closedBall (0 : V) R, ∀ v : V,
        c * ‖v‖ * ‖v‖ ≤ mass t u v v)
    (hmass_lip : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith Km (mass t) (closedBall (0 : V) R))
    (hmass_time : ∀ u ∈ closedBall (0 : V) R,
      ContinuousOn (fun t ↦ mass t u) (Icc (0 : ℝ) T))
    (hres_lip : ∀ t ∈ Icc (0 : ℝ) T,
      LipschitzOnWith Kr (resid t) (closedBall (0 : V) R))
    (hres_time : ∀ u ∈ closedBall (0 : V) R,
      ContinuousOn (fun t ↦ resid t u) (Icc (0 : ℝ) T))
    (hres_bound : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u ∈ closedBall (0 : V) R, ‖resid t u‖ ≤ A) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧
      ∃ γ : ℝ → V, γ 0 = 0 ∧ ContinuousOn γ (Icc (0 : ℝ) τ) ∧
        (∀ t ∈ Icc (0 : ℝ) τ, γ t ∈ closedBall (0 : V) R) ∧
        ∃ vel : ℝ → V,
          (∀ t, t ∈ Icc (0 : ℝ) τ →
            HasDerivWithinAt γ (vel t) (Icc (0 : ℝ) τ) t) ∧
          ∀ t, t ∈ Icc (0 : ℝ) τ →
            mass t (γ t) (vel t) = resid t (γ t) := by
  let cinv : ℝ≥0 := ⟨c⁻¹, inv_nonneg.mpr hc.le⟩
  let An : ℝ≥0 := ⟨A, hA⟩
  let Lf : ℝ≥0 := cinv * An
  let Kf : ℝ≥0 := cinv * Kr + cinv * (Km * (cinv * An))
  let τ : ℝ := min T (R / ((Lf : ℝ) + 1))
  have hden : 0 < (Lf : ℝ) + 1 := by positivity
  have hτ : 0 < τ := lt_min hT (div_pos hR hden)
  have hτT : τ ≤ T := min_le_left _ _
  have hτR : τ ≤ R / ((Lf : ℝ) + 1) := min_le_right _ _
  have hLfR : (Lf : ℝ) * τ ≤ R := by
    calc
      (Lf : ℝ) * τ ≤ (Lf : ℝ) * (R / ((Lf : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hτR Lf.coe_nonneg
      _ = ((Lf : ℝ) / ((Lf : ℝ) + 1)) * R := by ring
      _ ≤ 1 * R := by
        apply mul_le_mul_of_nonneg_right _ hR.le
        exact (div_le_one hden).2 (by linarith)
      _ = R := one_mul R
  let hco : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u ∈ closedBall (0 : V) R, IsCoercive (mass t u) :=
    fun t ht u hu ↦ ⟨c, hc, hcoer t ht u hu⟩
  let f : ℝ → V → V := fun t u ↦
    if ht : t ∈ Icc (0 : ℝ) T then
      if hu : u ∈ closedBall (0 : V) R then
        (hco t ht u hu).sharpCLM (resid t u)
      else 0
    else 0
  have htime_sub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) T := by
    intro t ht
    exact ⟨ht.1, ht.2.trans hτT⟩
  have hfnorm : ∀ t u, ‖f t u‖ ≤ (Lf : ℝ) := by
    intro t u
    by_cases ht : t ∈ Icc (0 : ℝ) T
    · by_cases hu : u ∈ closedBall (0 : V) R
      · have hsharp : ‖(hco t ht u hu).sharpCLM‖ ≤ c⁻¹ :=
          (hco t ht u hu).sharpCLM_norm_le hc (hcoer t ht u hu)
        calc
          ‖f t u‖ = ‖(hco t ht u hu).sharpCLM (resid t u)‖ := by
            simp only [f, dif_pos ht, dif_pos hu]
          _ ≤ ‖(hco t ht u hu).sharpCLM‖ * ‖resid t u‖ :=
            ContinuousLinearMap.le_opNorm _ _
          _ ≤ c⁻¹ * A := by
            exact mul_le_mul hsharp (hres_bound t ht u hu)
              (norm_nonneg _) (inv_nonneg.mpr hc.le)
          _ = (Lf : ℝ) := by rfl
      · simp only [f, dif_pos ht, dif_neg hu, norm_zero]
        exact Lf.coe_nonneg
    · simp only [f, dif_neg ht, norm_zero]
      exact Lf.coe_nonneg
  have hflip : ∀ t ∈ Icc (0 : ℝ) τ,
      LipschitzOnWith Kf (f t) (closedBall (0 : V) R) := by
    intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := htime_sub ht
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro u hu v hv
    have hm : ‖mass t v - mass t u‖ ≤ (Km : ℝ) * ‖u - v‖ := by
      have h := (hmass_lip t htT).dist_le_mul v hv u hu
      rw [dist_eq_norm, dist_eq_norm] at h
      calc
        ‖mass t v - mass t u‖ ≤ (Km : ℝ) * ‖v - u‖ := h
        _ = (Km : ℝ) * ‖u - v‖ := by rw [norm_sub_rev]
    have hr : ‖resid t u - resid t v‖ ≤ (Kr : ℝ) * ‖u - v‖ := by
      simpa only [dist_eq_norm] using
        (hres_lip t htT).dist_le_mul u hu v hv
    have hs := (hco t htT u hu).sharp_var_le (hco t htT v hv)
      hc hc (hcoer t htT u hu) (hcoer t htT v hv)
      (resid t u) (resid t v)
    rw [dist_eq_norm]
    simp only [f, dif_pos htT, dif_pos hu, dif_pos hv]
    calc
      ‖(hco t htT u hu).sharpCLM (resid t u) -
          (hco t htT v hv).sharpCLM (resid t v)‖
          ≤ c⁻¹ * ‖resid t u - resid t v‖ +
            c⁻¹ * (‖mass t v - mass t u‖ *
              (c⁻¹ * ‖resid t v‖)) := by
            simpa only [IsCoercive.sharpCLM_apply] using hs
      _ ≤ c⁻¹ * ((Kr : ℝ) * ‖u - v‖) +
            c⁻¹ * (((Km : ℝ) * ‖u - v‖) * (c⁻¹ * A)) := by
            gcongr
            exact hres_bound t htT v hv
      _ = (Kf : ℝ) * ‖u - v‖ := by
            simp only [Kf, cinv, An, NNReal.coe_add, NNReal.coe_mul,
              NNReal.coe_mk]
            ring
  have hftime : ∀ u ∈ closedBall (0 : V) R,
      ContinuousOn (fun t ↦ f t u) (Icc (0 : ℝ) τ) := by
    intro u hu
    have hm : ContinuousOn (fun t ↦ mass t u) (Icc (0 : ℝ) τ) :=
      (hmass_time u hu).mono htime_sub
    let hcsub : ∀ t ∈ Icc (0 : ℝ) τ, IsCoercive (mass t u) :=
      fun t ht ↦ hco t (htime_sub ht) u hu
    have hsharp : Continuous
        (fun t : Icc (0 : ℝ) τ ↦ (hcsub t t.2).sharpCLM) :=
      IsCoercive.sharpCLM_cont_sub (fun t ↦ mass t u) hm hcsub
    have hr : Continuous (fun t : Icc (0 : ℝ) τ ↦ resid t u) :=
      ((hres_time u hu).mono htime_sub).restrict
    rw [continuousOn_iff_continuous_restrict]
    have happ := hsharp.clm_apply hr
    convert happ using 1
    funext t
    simp only [f, Set.restrict_apply, dif_pos (htime_sub t.2), dif_pos hu,
      hcsub, hco]
  let tzero : Icc (0 : ℝ) τ := ⟨0, by exact ⟨le_rfl, hτ.le⟩⟩
  let aN : ℝ≥0 := ⟨R, hR.le⟩
  have hPL : IsPicardLindelof f tzero (0 : V) aN 0 Lf Kf where
    lipschitzOnWith := hflip
    continuousOn := hftime
    norm_le := fun t _ u _ ↦ hfnorm t u
    mul_max_le := by
      change (Lf : ℝ) * max (τ - 0) (0 - 0) ≤ R - 0
      simpa only [sub_zero, max_eq_left hτ.le] using hLfR
  obtain ⟨γ, hγ0, hγderiv⟩ :=
    hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) τ) :=
    fun t ht ↦ (hγderiv t ht).continuousWithinAt
  have hγball : ∀ t ∈ Icc (0 : ℝ) τ,
      γ t ∈ closedBall (0 : V) R := by
    have hmove := norm_image_sub_le_of_norm_deriv_le_segment'
      hγderiv (fun t ht ↦ hfnorm t (γ t))
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖γ t‖ = ‖γ t - γ 0‖ := by rw [hγ0, sub_zero]
      _ ≤ (Lf : ℝ) * (t - 0) := hmove t ht
      _ ≤ (Lf : ℝ) * τ := by
        apply mul_le_mul_of_nonneg_left _ Lf.coe_nonneg
        simpa only [sub_zero] using ht.2
      _ ≤ R := hLfR
  let vel : ℝ → V := fun t ↦ f t (γ t)
  refine ⟨τ, hτ, hτT, γ, hγ0, hγcont, hγball, vel, ?_, ?_⟩
  · intro t ht
    exact hγderiv t ht
  · intro t ht
    have htT : t ∈ Icc (0 : ℝ) T := htime_sub ht
    have hu : γ t ∈ closedBall (0 : V) R := hγball t ht
    change mass t (γ t) (f t (γ t)) = resid t (γ t)
    rw [show f t (γ t) =
        (hco t htT (γ t) hu).sharpCLM (resid t (γ t)) by
      simp only [f, dif_pos htT, dif_pos hu]]
    simpa only [IsCoercive.sharpCLM_apply] using
      (hco t htT (γ t) hu).apply_sharp (resid t (γ t))

end DifferentialGeometry.Analysis.ODE

end
