import DifferentialGeometry.Analysis.ODE.GeodesicLimits.CommonLocalFlows
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# `C¹` convergence of geodesic sprays (LFR09 kernel, G9.2 input)

For a Christoffel field `Γ : E → E →L E →L E` the geodesic spray is
`q ↦ (q.2, -(Γ q.1 q.2 q.2))` on `E × E` (for `Γ = raisedKoszulOp (g ·) (fderiv g ·)` this is the
tree's `metricSpray g`, definitionally).

* `exists_hasFDerivAt_quadratic`: derivative of `p ↦ B p.1 p.2 p.2` with the bound
  `2 ‖B x‖ ‖v‖ + ‖DB x‖ ‖v‖²`.
* `contDiffOn_spray`: the spray of a field that is `C¹` on `U` is `C¹` on `U ×ˢ univ`.
* `mapCPConvergenceOn_spray`: `C¹` convergence of `Γ i` on the compact subsets of `U` gives `C¹`
  convergence of the sprays on the compact subsets of `U ×ˢ univ`, the hypothesis of CM4.b.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable local instance sprayConvBilinNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance sprayConvBilinNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace
noncomputable local instance sprayConvTriNormedGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance sprayConvTriNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedSpace

/-- Derivative of the quadratic map `p ↦ B p.1 p.2 p.2`, with a norm bound. -/
theorem exists_hasFDerivAt_quadratic {B : E → E →L[ℝ] E →L[ℝ] E} {q : E × E}
    (hB : DifferentiableAt ℝ B q.1) :
    ∃ L : E × E →L[ℝ] E, HasFDerivAt (fun p : E × E => B p.1 p.2 p.2) L q ∧
      ‖L‖ ≤ 2 * ‖B q.1‖ * ‖q.2‖ + ‖fderiv ℝ B q.1‖ * ‖q.2‖ ^ 2 := by
  have h1 : HasFDerivAt (B ∘ Prod.fst)
      ((fderiv ℝ B q.1).comp (ContinuousLinearMap.fst ℝ E E)) q :=
    hB.hasFDerivAt.comp q hasFDerivAt_fst
  have hu : HasFDerivAt (fun p : E × E => p.2) (ContinuousLinearMap.snd ℝ E E) q := hasFDerivAt_snd
  have h2 := h1.clm_apply hu
  have h3 := h2.clm_apply hu
  refine ⟨_, h3, ?_⟩
  simp only [Function.comp_apply]
  have hfst : ‖ContinuousLinearMap.fst ℝ E E‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ E E
  have hsnd : ‖ContinuousLinearMap.snd ℝ E E‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ E E
  set b := ‖B q.1‖
  set d := ‖fderiv ℝ B q.1‖
  set v := ‖q.2‖
  have hb : 0 ≤ b := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  have hc1 : ‖(fderiv ℝ B q.1).comp (ContinuousLinearMap.fst ℝ E E)‖ ≤ d :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith)
  have hA : ‖(B q.1).comp (ContinuousLinearMap.snd ℝ E E)‖ ≤ b :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith)
  have hBv : ‖B q.1 q.2‖ ≤ b * v := (B q.1).le_opNorm q.2
  have hC : ‖(B q.1 q.2).comp (ContinuousLinearMap.snd ℝ E E)‖ ≤ b * v :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans (by nlinarith [norm_nonneg (B q.1 q.2)])
  have hflip1 : ‖((fderiv ℝ B q.1).comp (ContinuousLinearMap.fst ℝ E E)).flip q.2‖ ≤ d * v := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right hc1 hv
  have hD : ‖(B q.1).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderiv ℝ B q.1).comp (ContinuousLinearMap.fst ℝ E E)).flip q.2‖ ≤ b + d * v :=
    (norm_add_le _ _).trans (add_le_add hA hflip1)
  have hflip2 : ‖((B q.1).comp (ContinuousLinearMap.snd ℝ E E) +
      ((fderiv ℝ B q.1).comp (ContinuousLinearMap.fst ℝ E E)).flip q.2).flip q.2‖ ≤
      (b + d * v) * v := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right hD hv
  refine (norm_add_le _ _).trans ?_
  nlinarith [hC, hflip2]

/-- The geodesic spray of a field that is `C¹` on `U` is `C¹` on `U ×ˢ univ`. -/
theorem contDiffOn_spray {U : Set E} {Γ : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ContDiffOn ℝ 1 Γ U) :
    ContDiffOn ℝ 1 (fun q : E × E => (q.2, -(Γ q.1 q.2 q.2))) (U ×ˢ univ) := by
  have h1 : ContDiffOn ℝ 1 (fun q : E × E => Γ q.1) (U ×ˢ univ) :=
    hΓ.comp contDiffOn_fst (fun q hq => hq.1)
  exact contDiffOn_snd.prodMk ((h1.clm_apply contDiffOn_snd).clm_apply contDiffOn_snd).neg

/-- **`C¹` convergence of geodesic sprays.** -/
theorem mapCPConvergenceOn_spray {U : Set E} (hU : IsOpen U) {Γ : ℕ → E → E →L[ℝ] E →L[ℝ] E}
    {ΓInf : E → E →L[ℝ] E →L[ℝ] E} (hΓ : ∀ i, ContDiffOn ℝ 1 (Γ i) U)
    (hΓInf : ContDiffOn ℝ 1 ΓInf U)
    (hconv : ∀ C, IsCompact C → C ⊆ U → MapCPConvergenceOn C 1 Γ ΓInf)
    {C : Set (E × E)} (hC : IsCompact C) (hCU : C ⊆ U ×ˢ univ) :
    MapCPConvergenceOn C 1 (fun i (q : E × E) => (q.2, -(Γ i q.1 q.2 q.2)))
      (fun q => (q.2, -(ΓInf q.1 q.2 q.2))) := by
  have hUo : IsOpen (U ×ˢ (univ : Set E)) := hU.prod isOpen_univ
  have hdiff : ∀ {Θ : E → E →L[ℝ] E →L[ℝ] E}, ContDiffOn ℝ 1 Θ U → ∀ q ∈ C,
      DifferentiableAt ℝ (fun q : E × E => (q.2, -(Θ q.1 q.2 q.2))) q := fun hΘ q hq =>
    ((contDiffOn_spray hΘ).contDiffAt (hUo.mem_nhds (hCU hq))).differentiableAt one_ne_zero
  have hdΓ : ∀ i, ∀ x ∈ U, DifferentiableAt ℝ (Γ i) x := fun i x hx =>
    ((hΓ i).contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  have hdΓInf : ∀ x ∈ U, DifferentiableAt ℝ ΓInf x := fun x hx =>
    (hΓInf.contDiffAt (hU.mem_nhds hx)).differentiableAt one_ne_zero
  -- compact projections
  have hC1 : IsCompact (Prod.fst '' C) := hC.image continuous_fst
  have hC1U : Prod.fst '' C ⊆ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact (hCU hq).1
  obtain ⟨R, hR⟩ := (hC.image continuous_snd).isBounded.exists_norm_le
  have hR0 : ∀ q ∈ C, ‖q.2‖ ≤ R := fun q hq => hR _ ⟨q, hq, rfl⟩
  set R' : ℝ := |R| + 1 with hR'_def
  have hR' : 0 < R' := by positivity
  have hRR' : ∀ q ∈ C, ‖q.2‖ ≤ R' := fun q hq => (hR0 q hq).trans (by linarith [le_abs_self R])
  have hΓc := forall_norm_sub_le_of_mapCPConvergenceOn_one (hconv _ hC1 hC1U)
    (fun i x hx => hdΓ i x (hC1U hx)) (fun x hx => hdΓInf x (hC1U hx))
  -- the difference of the sprays
  have hsub : ∀ i, ((fun p : E × E => (p.2, -(Γ i p.1 p.2 p.2))) -
      fun p : E × E => (p.2, -(ΓInf p.1 p.2 p.2))) =
      fun p : E × E => ((0 : E), -((fun x => Γ i x - ΓInf x) p.1 p.2 p.2)) := by
    intro i
    funext p
    simp only [Pi.sub_apply, Prod.mk_sub_mk, sub_self, sub_apply]
    congr 1
    abel
  refine mapCPConvergenceOn_one_of_forall_norm_sub_le
    (Eventually.of_forall fun i q hq => hdiff (hΓ i) q hq) (fun q hq => hdiff hΓInf q hq) ?_ ?_
  · intro ε hε
    filter_upwards [hΓc (ε / R' ^ 2) (by positivity)] with i hi q hq
    have h := congrFun (hsub i) q
    simp only [Pi.sub_apply] at h
    rw [h, Prod.norm_mk, norm_zero, norm_neg]
    have hq1 : q.1 ∈ Prod.fst '' C := ⟨q, hq, rfl⟩
    have hle : ‖(Γ i q.1 - ΓInf q.1) q.2 q.2‖ ≤ ‖Γ i q.1 - ΓInf q.1‖ * ‖q.2‖ * ‖q.2‖ :=
      ((Γ i q.1 - ΓInf q.1) q.2).le_opNorm q.2 |>.trans
        (mul_le_mul_of_nonneg_right ((Γ i q.1 - ΓInf q.1).le_opNorm q.2) (norm_nonneg _))
    refine max_le hε.le (hle.trans ?_)
    have hq2 := hRR' q hq
    calc ‖Γ i q.1 - ΓInf q.1‖ * ‖q.2‖ * ‖q.2‖ ≤ ε / R' ^ 2 * R' * R' := by
          gcongr
          exact (hi _ hq1).1
      _ = ε := by field_simp
  · intro ε hε
    set c : ℝ := ε / (2 * R' + R' ^ 2) with hc_def
    have hc : 0 < c := by positivity
    filter_upwards [hΓc c hc] with i hi q hq
    have hq1 : q.1 ∈ Prod.fst '' C := ⟨q, hq, rfl⟩
    have hBd : DifferentiableAt ℝ (fun x => Γ i x - ΓInf x) q.1 :=
      (hdΓ i _ (hC1U hq1)).fun_sub (hdΓInf _ (hC1U hq1))
    obtain ⟨L, hL, hLb⟩ := exists_hasFDerivAt_quadratic hBd
    have hpair : HasFDerivAt (fun p : E × E => ((0 : E), -((fun x => Γ i x - ΓInf x) p.1 p.2 p.2)))
        ((0 : E × E →L[ℝ] E).prod (-L)) q :=
      (hasFDerivAt_const (0 : E) q).prodMk hL.neg
    rw [← fderiv_sub (hdiff (hΓ i) q hq) (hdiff hΓInf q hq), hsub i, hpair.fderiv]
    have hfd : fderiv ℝ (fun x => Γ i x - ΓInf x) q.1 = fderiv ℝ (Γ i) q.1 - fderiv ℝ ΓInf q.1 :=
      fderiv_fun_sub (hdΓ i _ (hC1U hq1)) (hdΓInf _ (hC1U hq1))
    rw [hfd] at hLb
    have hq2 := hRR' q hq
    have hb := (hi _ hq1).1
    have hd := (hi _ hq1).2
    have hLle : ‖L‖ ≤ ε := by
      refine hLb.trans ?_
      calc 2 * ‖Γ i q.1 - ΓInf q.1‖ * ‖q.2‖ + ‖fderiv ℝ (Γ i) q.1 - fderiv ℝ ΓInf q.1‖ * ‖q.2‖ ^ 2
          ≤ 2 * c * R' + c * R' ^ 2 := by gcongr
        _ = ε := by rw [hc_def]; field_simp
    refine (ContinuousLinearMap.opNorm_le_bound _ hε.le fun p => ?_)
    rw [ContinuousLinearMap.prod_apply, Prod.norm_mk, _root_.zero_apply, norm_zero,
      _root_.neg_apply, norm_neg]
    exact max_le (by positivity)
      ((L.le_opNorm p).trans (mul_le_mul_of_nonneg_right hLle (norm_nonneg _)))

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
