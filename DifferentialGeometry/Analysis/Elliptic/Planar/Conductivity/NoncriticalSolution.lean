import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.UniformRescaling
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.LocalCoefficient
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.AffineDirichletPerturbation
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.UniformEnergyExcess
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.CampanatoRegularity
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.UniformCampanatoGradient
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.NoncriticalPerturbation
import DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.Divergence.Local

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric InnerProductSpace
open scoped Topology ContDiff ENNReal InnerProductSpace

namespace DifferentialGeometry.Analysis

open DeGiorgi Laplacian.MetricExtension Parabolic.Euclidean

local notation "V" => EuclideanSpace ℝ (Fin 2)

/-- The original locally C1 determinant-one positive conductivity has a
noncritical C1 weak solution after one sufficiently small literal rescaling. -/
theorem exists_noncritical_rescaled_c1_weak_conductivity_solution
    {Ω : Set V} (hΩ : IsOpen Ω) (h0 : (0 : V) ∈ Ω)
    (K : V → Matrix (Fin 2) (Fin 2) ℝ)
    (hK : ∀ i j, ContDiffOn ℝ 1 (fun x => K x i j) Ω)
    (hpos : ∀ x ∈ Ω, (K x).PosDef)
    (hdet : ∀ x ∈ Ω, (K x).det = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (0 : V) ρ ⊆ Ω ∧
      ∃ v : V → ℝ, ContDiffOn ℝ 1 v (Metric.ball (0 : V) (1 / 8)) ∧
        DeGiorgi.HasWeakDiv 0
          (fun x => DeGiorgi.matMulE (K (ρ • x)) (DeGiorgi.smoothGradField v x))
          (Metric.ball (0 : V) (1 / 8)) ∧
        DeGiorgi.smoothGradField v 0 ≠ 0 := by
  classical
  obtain ⟨ρ₀, lam, Λ, L, hρ₀, hρ₀1, hballΩ, hlam, hlamΛ, hΛ1, hb, hosc⟩ :=
    exists_uniform_rescaled_conductivity_bounds hΩ h0 K hK hpos hdet
  let rstar : ℝ := min ρ₀ (lam / (2 * ((L : ℝ) + 1)))
  have hrstar : 0 < rstar := lt_min hρ₀ (by positivity)
  have hrstarρ : rstar ≤ ρ₀ := min_le_left _ _
  let I := {ρ : ℝ // ρ ∈ Ioc (0 : ℝ) rstar}
  have hiρ (i : I) : (i : ℝ) ≤ ρ₀ := i.2.2.trans hrstarρ
  have hi1 (i : I) : (i : ℝ) ≤ 1 := (hiρ i).trans hρ₀1
  have hsmall (i : I) : ((i : ℝ) * (L : ℝ)) / lam ≤ 1 / 2 := by
    have hden : 0 < 2 * ((L : ℝ) + 1) := by positivity
    have ht := (le_div_iff₀ hden).mp
      (i.2.2.trans (min_le_right ρ₀ (lam / (2 * ((L : ℝ) + 1)))))
    apply (div_le_iff₀ hlam).2
    nlinarith [i.2.1]
  have hcoeff (i : I) :
      ∃ A : EllipticCoeff 2 (ball (0 : V) 1),
        A.lam = lam ∧ A.Λ = Λ ∧
        (∀ x ∈ closedBall (0 : V) 1, A.a x = K ((i : ℝ) • x)) ∧
        (∀ x ∉ closedBall (0 : V) 1, A.a x = 1) := by
    refine exists_ellipticCoeff_of_closedBall_continuous
      (fun x => K ((i : ℝ) • x)) ?_ lam Λ hlam hlamΛ ?_ ?_
    · intro j k
      have hs : Continuous (fun x : V => (i : ℝ) • x) :=
        (continuous_id : Continuous (fun x : V => x)).const_smul (i : ℝ)
      exact (hK j k).continuousOn.comp hs.continuousOn
        (fun x hx => (hb i i.2.1 (hiρ i) x hx).1)
    · intro x hx
      exact (hb i i.2.1 (hiρ i) x hx).2.2.2.1
    · intro x hx
      exact (hb i i.2.1 (hiρ i) x hx).2.2.2.2.1
  choose A hAlam hAΛ hAeq hAoff using hcoeff
  have hb0 := hb ρ₀ hρ₀ le_rfl 0 (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))
  have hcoer0 (ξ : V) : lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (K 0) ξ⟫_ℝ := by
    simpa only [smul_zero] using hb0.2.2.2.1 ξ
  have hinv0 (ξ : V) : Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((K 0)⁻¹) ξ⟫_ℝ := by
    simpa only [smul_zero] using hb0.2.2.2.2.1 ξ
  let B : EllipticCoeff 2 (ball (0 : V) 1) :=
    ellipticCoeffOfPointwiseBounds isOpen_ball.measurableSet (fun _ => K 0)
      lam Λ hlam hlamΛ (fun _ _ => measurable_const)
      (fun _ _ => hcoer0) (fun _ _ => hinv0)
  let e : V := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have haffine (i : I) :=
    exists_affine_dirichlet_solution_with_uniform_gradient_error (A i) B (K 0) rfl e he
      (ε := (i : ℝ) * (L : ℝ)) (mul_nonneg i.2.1.le L.coe_nonneg) (hsmall i) (by
        filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
        intro ξ
        have hxc := ball_subset_closedBall hx
        have hzero : (0 : V) ∈ closedBall 0 1 := mem_closedBall_self (by norm_num)
        have hd : dist x 0 ≤ 1 := (mem_ball.mp hx).le
        change ‖matMulE ((A i).a x) ξ - matMulE (K 0) ξ‖ ≤ _
        rw [hAeq i x hxc]
        have hh := hosc i i.2.1 (hiρ i) x hxc 0 hzero ξ
        simp only [smul_zero] at hh
        exact hh.trans (by
          calc
            (i : ℝ) * (L : ℝ) * dist x 0 * ‖ξ‖ ≤
                ((i : ℝ) * (L : ℝ) * 1) * ‖ξ‖ :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hd (mul_nonneg i.2.1.le L.coe_nonneg))
                (norm_nonneg _)
            _ = (i : ℝ) * (L : ℝ) * ‖ξ‖ := by rw [mul_one]))
  choose u w hu htrace herror henergy using haffine
  have hAc (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) : ((A i).a x).PosDef := by
    rw [hAeq i x (ball_subset_closedBall hx)]
    exact (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.1
  have hAdet (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) : ((A i).a x).det = 1 := by
    rw [hAeq i x (ball_subset_closedBall hx)]
    exact (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.2.1
  have hAcoer (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) (ξ : V) :
      lam * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE ((A i).a x) ξ⟫_ℝ := by
    rw [hAeq i x (ball_subset_closedBall hx)]
    exact (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.2.2.1 ξ
  have hAinv (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) (ξ : V) :
      (A i).Λ⁻¹ * ‖ξ‖ ^ 2 ≤ ⟪ξ, matMulE (((A i).a x)⁻¹) ξ⟫_ℝ := by
    rw [hAΛ i, hAeq i x (ball_subset_closedBall hx)]
    exact (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.2.2.2.1 ξ
  have hAosc (i : I) (x : V) (hx : x ∈ ball (0 : V) 1)
      (y : V) (hy : y ∈ ball (0 : V) 1) (ξ : V) :
      ‖matMulE ((A i).a x) ξ - matMulE ((A i).a y) ξ‖ ≤
        (L : ℝ) * dist x y * ‖ξ‖ := by
    rw [hAeq i x (ball_subset_closedBall hx), hAeq i y (ball_subset_closedBall hy)]
    apply (hosc i i.2.1 (hiρ i) x (ball_subset_closedBall hx)
      y (ball_subset_closedBall hy) ξ).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left L.coe_nonneg (hi1 i))
        dist_nonneg) (norm_nonneg _)
  have hMbound (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) :
      ‖(spdSqrtEquiv ((A i).a x) (hAc i x hx) : V →L[ℝ] V)‖ ≤
        max 1 (Real.sqrt Λ) := by
    have hh := (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.2.2.2.2.2
    simpa only [hAeq i x (ball_subset_closedBall hx)] using
      (hh (hpos _ (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).1)).1
  have hNbound (i : I) (x : V) (hx : x ∈ ball (0 : V) 1) :
      ‖((spdSqrtEquiv ((A i).a x) (hAc i x hx)).symm : V →L[ℝ] V)‖ ≤
        max 1 (Real.sqrt lam)⁻¹ := by
    have hh := (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).2.2.2.2.2.2
    simpa only [hAeq i x (ball_subset_closedBall hx)] using
      (hh (hpos _ (hb i i.2.1 (hiρ i) x (ball_subset_closedBall hx)).1)).2
  obtain ⟨E, Kex, hE, hKex, hdecay⟩ := exists_uniform_weakGrad_energy_excess_bounds
    (by norm_num : (0 : ℝ) < 1) A hlam hAlam u hu w L.coe_nonneg
    (le_max_left 1 (Real.sqrt Λ)) (le_max_left 1 (Real.sqrt lam)⁻¹)
    (by positivity : 0 ≤ 4 * volume.real (ball (0 : V) 1))
    hAc hAdet hAcoer hAinv hAosc hMbound hNbound henergy
  have hquarter : ball (0 : V) (1 / 4) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have heighth : ball (0 : V) (1 / 8) ⊆ ball 0 (1 / 4) := ball_subset_ball (by norm_num)
  let wq (i : I) : MemW1pWitness 2 (u i) (ball (0 : V) (1 / 4)) :=
    (w i).restrict isOpen_ball hquarter
  have hrep (i : I) :=
    exists_contDiffOn_one_representative_of_linear_energy_cubic_excess
      (by norm_num : (0 : ℝ) < 1 / 4) (wq i) hE hKex
      (fun b => (hdecay i b.center (b.subset_ball (mem_ball_self b.radius_pos))
        b.radius ⟨b.radius_pos, b.radius_le⟩).1)
      (fun b => (hdecay i b.center (b.subset_ball (mem_ball_self b.radius_pos))
        b.radius ⟨b.radius_pos, b.radius_le⟩).2)
  choose v G C wv hC hvae hwv hGae hvc hGc hDv hGlocal using hrep
  have hhalfquarter : (1 / 4 : ℝ) / 2 = 1 / 8 := by norm_num
  have hvc' (i : I) : ContDiffOn ℝ 1 (v i) (ball (0 : V) (1 / 8)) := by
    simpa only [hhalfquarter] using hvc i
  have hDv' (i : I) (x : V) (hx : x ∈ ball (0 : V) (1 / 8)) :
      HasFDerivAt (v i) (innerSL ℝ (G i x)) x := by
    apply hDv i x
    simpa only [hhalfquarter] using hx
  have hgrad (i : I) (x : V) (hx : x ∈ ball (0 : V) (1 / 8)) :
      smoothGradField (v i) x = G i x := by
    ext j
    change fderiv ℝ (v i) x (EuclideanSpace.single j 1) = G i x j
    rw [(hDv' i x hx).fderiv]
    simp only [innerSL_apply_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  obtain ⟨H, hH, hHolder⟩ :=
    Sobolev.Euclidean.exists_uniform_holder_bound_of_continuous_gradient_excess
      (a := (0 : V)) (R := (1 / 4 : ℝ)) (K := Kex) (by norm_num) hKex
  have hGH := hHolder I (fun i => (wq i).weakGrad) G
    (fun i => (wq i).weakGrad_memLp) hGae hGc (by
      intro i b
      exact (hdecay i b.center (b.subset_ball (mem_ball_self b.radius_pos))
        b.radius ⟨b.radius_pos, b.radius_le⟩).2)
  have hGH' (i : I) : ∀ x ∈ ball (0 : V) (1 / 8), ∀ y ∈ ball 0 (1 / 8),
      ‖G i x - G i y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    simpa only [hhalfquarter] using hGH i
  obtain ⟨ε, hε, hnonzero⟩ :=
    exists_l2_threshold_for_nonzero_at_center_of_uniform_holder
      (1 / 8) (by norm_num) ⟨H, hH⟩ e he
  let err : ℝ → ℝ := fun ρ =>
    4 * (ρ * (L : ℝ) / lam) ^ 2 * volume.real (ball (0 : V) 1)
  have herrc : Continuous err := by
    exact (continuous_const.mul
      (((continuous_id.mul continuous_const).div_const lam).pow 2)).mul continuous_const
  have herr0 : err 0 < ε := by simpa only [err, zero_mul, zero_div, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using hε
  have hnear : ∀ᶠ ρ in 𝓝 (0 : ℝ), err ρ < ε :=
    herrc.continuousAt.eventually (gt_mem_nhds herr0)
  obtain ⟨δ, hδ, hδsmall⟩ := Metric.mem_nhds_iff.mp hnear
  let ρ : ℝ := min δ rstar / 2
  have hρ : 0 < ρ := half_pos (lt_min hδ hrstar)
  have hρstar : ρ ≤ rstar :=
    (half_le_self (le_of_lt (lt_min hδ hrstar))).trans (min_le_right _ _)
  have hρδ : ρ < δ :=
    (half_lt_self (lt_min hδ hrstar)).trans_le (min_le_left _ _)
  let i : I := ⟨ρ, hρ, hρstar⟩
  have herr : err ρ < ε := hδsmall (by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hρ] using hρδ)
  let : IsFiniteMeasure (volume.restrict (ball (0 : V) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure (volume.restrict (ball (0 : V) (1 / 4))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hGmem : MemLp (G i) 2 (volume.restrict (ball (0 : V) (1 / 4))) :=
    (wq i).weakGrad_memLp.ae_eq (Filter.EventuallyEq.symm (hGae i))
  have hGerr : IntegrableOn (fun x => ‖G i x - e‖ ^ 2) (ball (0 : V) (1 / 8)) volume :=
    IntegrableOn.mono_set (hGmem.sub (memLp_const e)).norm.integrable_sq heighth
  have hWerr : IntegrableOn (fun x => ‖(w i).weakGrad x - e‖ ^ 2)
      (ball (0 : V) 1) volume :=
    ((w i).weakGrad_memLp.sub (memLp_const e)).norm.integrable_sq
  have hGsmall : (∫ x in ball (0 : V) (1 / 8), ‖G i x - e‖ ^ 2) < ε := by
    calc
      _ = ∫ x in ball (0 : V) (1 / 8), ‖(w i).weakGrad x - e‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae_restrict_of_subset heighth (hGae i)] with x hx
        change G i x = (w i).weakGrad x at hx
        rw [hx]
      _ ≤ ∫ x in ball (0 : V) 1, ‖(w i).weakGrad x - e‖ ^ 2 :=
        setIntegral_mono_set hWerr (Eventually.of_forall fun _ => sq_nonneg _)
          (Eventually.of_forall fun _ hx => hquarter (heighth hx))
      _ ≤ err ρ := herror i
      _ < ε := herr
  have hG0 : G i 0 ≠ 0 := hnonzero (G i) (hGH' i) hGerr hGsmall
  have hdiv : HasWeakDiv (fun _ : V => -(0 : ℝ))
      (fun x => matMulE ((A i).a x) ((w i).weakGrad x)) (ball (0 : V) 1) := by
    apply (bilinFormOfCoeff_eq_integral_iff_hasWeakDiv isOpen_ball (w i)
      (memLp_const (0 : ℝ))).mp
    intro φ hφ wφ
    simpa only [zero_mul, integral_zero] using (hu i).2 (w i) φ hφ wφ
  have hdivsmall : HasWeakDiv 0
      (fun x => matMulE (K (ρ • x)) (smoothGradField (v i) x))
      (ball (0 : V) (1 / 8)) := by
    apply (hdiv.restrict (heighth.trans hquarter)).congr_ae
      (Eventually.of_forall fun _ => neg_zero)
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae_restrict_of_subset heighth (hGae i)] with x hx hGx
    change G i x = (w i).weakGrad x at hGx
    rw [hAeq i x (ball_subset_closedBall (hquarter (heighth hx))), ← hGx, hgrad i x hx]
  refine ⟨ρ, hρ, (closedBall_subset_closedBall ((hiρ i))).trans hballΩ,
    v i, hvc' i, hdivsmall, ?_⟩
  rw [hgrad i 0 (mem_ball_self (by norm_num))]
  exact hG0

end DifferentialGeometry.Analysis
