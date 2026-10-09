import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientRootLowerTerms
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry MeasureTheory
open DifferentialGeometry.Geometry DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped ContDiff Manifold Topology Interval Matrix.Norms.Elementwise

private def rootMeasurableEntry (i j : Fin 2) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℝ :=
  ((![Complex.reCLM, Complex.imCLM] : Fin 2 → ℂ →L[ℝ] ℝ) i).comp
    (ContinuousLinearMap.apply ℝ ℂ ((![1, Complex.I] : Fin 2 → ℂ) j))

private theorem rootMeasurableEntry_apply (A : Matrix (Fin 2) (Fin 2) ℝ)
    (i j : Fin 2) : rootMeasurableEntry i j (complexPlaneMatrixOperator A) = A i j := by
  fin_cases i <;> fin_cases j <;>
    simp [rootMeasurableEntry, complexPlaneMatrixOperator, Complex.real_smul]

/-- Measurability of the literal lower fields of the original-metric root equation.
The radius is common to all deck roots. Derivatives of one fixed joint graph
residual supply measurable representatives, avoiding any regularity assertion
for the total chart formulas outside their physical neighborhood. -/
theorem DifferentialGeometry.Geometry.chartLeadingPlaneProjection_root_lower_terms_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hsrc : x ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (hb : b ≠ 0)
    (hnull : (∑ i, ∑ j, (chartGramMatrix g p x i j : ℂ) * b i * b j) = 0)
    {N : E} (hN : chartLeadingPlaneProjection g p x b N = 0)
    (hunit : chartGramBilin g p x N N = 1)
    (L : ℂ →L[ℝ] E)
    (hL : ∀ w, L w = (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ)
    {m : ℕ} (hm : 1 ≤ m) {H : ℂ → ℝ}
    (hH : ContDiffAt ℝ 2 H 0) (hH0 : H 0 = 0) (hDH : fderiv ℝ H 0 = 0)
    (hHess : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let Q := chartGramBilin g p x
    let proj := chartLeadingPlaneProjection g p x b
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let Y : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) → E := fun q =>
      extChartAt 𝓘(ℝ, E) p x + L (q.1.1 - c) + q.1.2 • N
    let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
    let G : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y q)) (V q.2 i) (V q.2 j)
    let A : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → Matrix (Fin 2) (Fin 2) ℝ := fun q =>
      Analysis.planarConductivity (G q 0 0) (G q 1 1) (G q 0 1)
    let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => Q N - l.comp proj
    let Phi : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → ℝ :=
      fun T q => ∑ i : Fin 2, ∑ j : Fin 2,
        A q i j * (T (dirs i) (dirs j) +
          theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q)))
    let R : ℂ → (ℂ →L[ℝ] ℝ) := Analysis.complexPowerNormalizedGradient m H
    let P : ℂ → ℂ := fun w => c + w ^ (m + 1) / ((m + 1 : ℕ) : ℂ)
    let T2 : ℂ → ℂ → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) := fun zeta w =>
      (fderiv ℝ R (zeta * w)).comp
        (ContinuousLinearMap.mul ℝ ℂ (((zeta * w) ^ m)⁻¹))
    let Jet : Type := ℝ × (ℂ →L[ℝ] ℝ)
    let J1 : ℂ → Jet := fun w => (H w, R w)
    let J2 : ℂ → ℂ → Jet := fun zeta w => (H (zeta * w), R (zeta * w))
    let J : ℂ → ℂ → ℝ → Jet := fun zeta w t => (1 - t) • J2 zeta w + t • J1 w
    let PhiRoot : ℂ → ℂ → Jet → ℝ := fun zeta w j =>
      Phi (T2 zeta w) ((P w, j.1), j.2)
    let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
    let betaRoot : ℂ → ℂ → Fin 2 → ℝ := fun zeta w i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (0, duals i)
    let cRoot : ℂ → ℂ → ℝ := fun zeta w =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot zeta w) (J zeta w t) (1, 0)
    let A1 : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => A ((P w, H w), R w)
    let K : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun w => if w = 0 then 1 else
      Analysis.planarComplexMulMatrix ((w ^ m)⁻¹) * A1 w *
        Analysis.planarComplexMulMatrix (w ^ m)
    let bTilde : ℂ → ℂ → ℂ := fun zeta w =>
      star (w ^ m) * ((betaRoot zeta w 0 : ℂ) + (betaRoot zeta w 1 : ℂ) * Complex.I) -
        ((m : ℂ) / w) * Analysis.planarMatrixSpin (K w)
    let cTilde : ℂ → ℂ → ℝ := fun zeta w => ‖w ^ m‖ ^ 2 * cRoot zeta w
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ zeta : ℂ, zeta ^ (m + 1) = 1 →
        Measurable (fun w : Metric.ball (0 : ℂ) ε => bTilde zeta w) ∧
        Measurable (fun w : Metric.ball (0 : ℂ) ε => cTilde zeta w) := by
  classical
  intro Q proj dirs Y V G A theta Phi R P T2 Jet J1 J2 J PhiRoot duals betaRoot cRoot A1 K
    bTilde cTilde
  let FullJet := (ℂ × ℝ) × (ℂ →L[ℝ] ℝ)
  let Hessian := ℂ →L[ℝ] ℂ →L[ℝ] ℝ
  let q0 : FullJet := ((c, 0), 0)
  let Aop : FullJet → ℂ →L[ℝ] ℂ := fun q => complexPlaneMatrixOperator (A q)
  let Psi : Hessian × FullJet → ℝ := fun tq => Phi tq.1 tq.2
  obtain ⟨hA, _⟩ :=
    chartLeadingPlaneProjection_conductivity_jet_bounds g hsrc hb hnull hN hunit L hL c
  change ContDiffAt ℝ 2 Aop q0 at hA
  obtain ⟨rΦ, CΦ, hrΦ, _, _, hΦ⟩ :=
    chartLeadingPlaneProjection_graph_residual_jet_bounds g hsrc hb hnull hN hunit L hL c
  have hPhi0 : ∀ q ∈ ball q0 rΦ, ContDiffAt ℝ 1 (Phi 0) q := by
    intro q hq
    exact ((hΦ q hq).2.2 0).1
  obtain ⟨rA, hrA, hrAlocal⟩ := Metric.mem_nhds_iff.mp (hA.eventually (by norm_num))
  let r := min rΦ rA
  have hr : 0 < r := lt_min hrΦ hrA
  have hPsi (T : Hessian) (q : FullJet) (hq : q ∈ ball q0 r) :
      ContDiffAt ℝ 1 Psi (T, q) := by
    have hAq2 : ContDiffAt ℝ 2 Aop q :=
      hrAlocal (ball_subset_ball (min_le_right _ _) hq)
    have hAq : ContDiffAt ℝ 1 Aop q := hAq2.of_le (by norm_num)
    have hentry (i j : Fin 2) : ContDiffAt ℝ 1 (fun tq : Hessian × FullJet =>
        A tq.2 i j) (T, q) := by
      have heq : (fun q => A q i j) = fun q => rootMeasurableEntry i j (Aop q) := by
        funext v
        exact (rootMeasurableEntry_apply (A v) i j).symm
      change ContDiffAt ℝ 1 ((fun q => A q i j) ∘ Prod.snd) (T, q)
      rw [heq]
      exact ((rootMeasurableEntry i j).contDiff.contDiffAt.comp q hAq).comp
        (T, q) contDiffAt_snd
    have hconstant : ContDiffAt ℝ 1 (fun tq : Hessian × FullJet => Phi 0 tq.2)
        (T, q) := by
      exact ContDiffAt.comp
        (f := (Prod.snd : Hessian × FullJet → FullJet)) (g := Phi (0 : Hessian))
        (T, q) (hPhi0 q (ball_subset_ball (min_le_left _ _) hq)) contDiffAt_snd
    have heq : Psi = fun tq =>
        (∑ i : Fin 2, ∑ j : Fin 2, A tq.2 i j * tq.1 (dirs i) (dirs j)) +
          Phi 0 tq.2 := by
      funext tq
      simp only [Psi, Phi, mul_add, Finset.sum_add_distrib, zero_apply, mul_zero,
        Finset.sum_const_zero, zero_add]
    rw [heq]
    refine (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
      (hentry i j).mul ?_).add hconstant
    fun_prop
  obtain ⟨hPζ, CJ, hCJ, hJnear⟩ :=
    chartLeadingPlaneProjection_interpolated_root_slope_bound
      g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  have hJdist : ∀ᶠ w in 𝓝 (0 : ℂ), ∀ ζ : ℂ, ζ ^ (m + 1) = 1 →
      ∀ t ∈ Icc (0 : ℝ) 1,
        ‖((P w, (J ζ w t).1), (J ζ w t).2) - q0‖ ≤ CJ * ‖w‖ := by
    filter_upwards [hJnear] with w hw
    intro ζ hζ t ht
    have hh := (hw ζ hζ t ht).2
    change ‖((1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
      t • ((P w, H w), R w)) - q0‖ ≤ CJ * ‖w‖ at hh
    have heq : (1 - t) • ((P (ζ * w), H (ζ * w)), R (ζ * w)) +
        t • ((P w, H w), R w) = ((P w, (J ζ w t).1), (J ζ w t).2) := by
      apply Prod.ext
      · apply Prod.ext
        · change (1 - t) • P (ζ * w) + t • P w = P w
          have hP : P (ζ * w) = P w := hPζ ζ hζ w
          rw [hP, ← add_smul, sub_add_cancel, one_smul]
        · rfl
      · rfl
    simpa only [heq] using hh
  obtain ⟨_, _, _, hK, _⟩ :=
    chartLeadingPlaneProjection_normalized_conductivity
      g hsrc hb hnull hN hunit L hL c hm hH hH0 hDH hHess
  change ContDiffAt ℝ 1 K 0 at hK
  have hsmall : ∀ᶠ w in 𝓝 (0 : ℂ), CJ * ‖w‖ < r :=
    (show ContinuousAt (fun w : ℂ => CJ * ‖w‖) 0 by fun_prop).eventually
      (gt_mem_nhds (by simpa using hr))
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), ContinuousAt H w ∧ ContinuousAt K w ∧
      CJ * ‖w‖ < r ∧ ∀ ζ : ℂ, ζ ^ (m + 1) = 1 → ∀ t ∈ Icc (0 : ℝ) 1,
        ‖((P w, (J ζ w t).1), (J ζ w t).2) - q0‖ ≤ CJ * ‖w‖ := by
    filter_upwards [hH.eventually (by norm_num), hK.eventually (by norm_num),
      hsmall, hJdist] with w hwH hwK hwsmall hwJ
    exact ⟨hwH.continuousAt, hwK.continuousAt, hwsmall, hwJ⟩
  obtain ⟨ε0, hε0, hεnear⟩ := Metric.mem_nhds_iff.mp hnear
  let ε := min ε0 1
  have hε : 0 < ε := lt_min hε0 zero_lt_one
  have hlocal (w : ball (0 : ℂ) ε) :=
    hεnear (ball_subset_ball (min_le_left ε0 1) w.property)
  have hHcont : ContinuousOn H (ball (0 : ℂ) ε) :=
    fun w hw => (hlocal ⟨w, hw⟩).1.continuousWithinAt
  have hKcont : ContinuousOn K (ball (0 : ℂ) ε) :=
    fun w hw => (hlocal ⟨w, hw⟩).2.1.continuousWithinAt
  have hRmeas : Measurable R := by
    have hcomp : Measurable (fun fg : (ℂ →L[ℝ] ℝ) × (ℂ →L[ℝ] ℂ) =>
        fg.1.comp fg.2) := (continuous_fst.clm_comp continuous_snd).measurable
    exact hcomp.comp ((measurable_fderiv ℝ H).prodMk
      ((ContinuousLinearMap.mul ℝ ℂ).measurable.comp (by fun_prop)))
  refine ⟨ε, hε, min_le_right _ _, ?_⟩
  intro ζ hζ
  have hζnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ (by omega)
  have hζball (w : ball (0 : ℂ) ε) : ζ * (w : ℂ) ∈ ball (0 : ℂ) ε := by
    simpa only [mem_ball, dist_zero_right, norm_mul, hζnorm, one_mul] using w.property
  have hHmeas : Measurable (fun w : ball (0 : ℂ) ε => H w) :=
    hHcont.domRestrict.measurable
  have hHζmeas : Measurable (fun w : ball (0 : ℂ) ε => H (ζ * w)) :=
    (hHcont.comp_continuous (continuous_const.mul continuous_subtype_val)
      (fun w => hζball w)).measurable
  have hTmeas : Measurable (T2 ζ) := by
    have hcomp : Measurable
        (fun fg : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) × (ℂ →L[ℝ] ℂ) => fg.1.comp fg.2) :=
      (continuous_fst.clm_comp continuous_snd).measurable
    exact hcomp.comp (((measurable_fderiv ℝ R).comp (by fun_prop)).prodMk
      ((ContinuousLinearMap.mul ℝ ℂ).measurable.comp (by fun_prop)))
  have hPmeas : Measurable P := by dsimp [P]; fun_prop
  have hJmeas : Measurable (fun wt : ball (0 : ℂ) ε × ℝ => J ζ wt.1 wt.2) := by
    have hJ1 : Measurable (fun w : ball (0 : ℂ) ε => J1 w) :=
      hHmeas.prodMk (hRmeas.comp measurable_subtype_coe)
    have hJ2 : Measurable (fun w : ball (0 : ℂ) ε => J2 ζ w) := by
      exact hHζmeas.prodMk (hRmeas.comp (by fun_prop))
    dsimp [J]
    exact ((measurable_const.sub measurable_snd).smul (hJ2.comp measurable_fst)).add
      (measurable_snd.smul (hJ1.comp measurable_fst))
  let Z : ball (0 : ℂ) ε × ℝ → Hessian × FullJet := fun wt =>
    (T2 ζ wt.1, ((P wt.1, (J ζ wt.1 wt.2).1), (J ζ wt.1 wt.2).2))
  have hZmeas : Measurable Z := by
    exact (hTmeas.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
      (((hPmeas.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
        hJmeas.fst).prodMk hJmeas.snd)
  let liftJet : Jet →L[ℝ] Hessian × FullJet :=
    (0 : Jet →L[ℝ] Hessian).prod
      (((0 : Jet →L[ℝ] ℂ).prod (ContinuousLinearMap.fst ℝ ℝ (ℂ →L[ℝ] ℝ))).prod
        (ContinuousLinearMap.snd ℝ ℝ (ℂ →L[ℝ] ℝ)))
  have hderiv (w : ball (0 : ℂ) ε) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (v : Jet) :
      fderiv ℝ (PhiRoot ζ w) (J ζ w t) v = fderiv ℝ Psi (Z (w, t)) (liftJet v) := by
    have hq : ((P w, (J ζ w t).1), (J ζ w t).2) ∈ ball q0 r := by
      rw [mem_ball, dist_eq_norm]
      exact ((hlocal w).2.2.2 ζ hζ t ht).trans_lt (hlocal w).2.2.1
    have hmap : HasFDerivAt (fun j : Jet => (T2 ζ w, ((P w, j.1), j.2)))
        liftJet (J ζ w t) := by
      exact (hasFDerivAt_const _ _).prodMk
        (((hasFDerivAt_const _ _).prodMk hasFDerivAt_fst).prodMk hasFDerivAt_snd)
    have hd := ((hPsi (T2 ζ w) _ hq).differentiableAt one_ne_zero).hasFDerivAt.comp
      (J ζ w t) hmap
    exact congrArg (fun D => D v) hd.fderiv
  have hint (v : Jet) : Measurable (fun w : ball (0 : ℂ) ε =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (PhiRoot ζ w) (J ζ w t) v) := by
    let B : ball (0 : ℂ) ε × ℝ → ℝ := fun wt => fderiv ℝ Psi (Z wt) (liftJet v)
    have hB : Measurable B := (measurable_fderiv_apply_const ℝ Psi (liftJet v)).comp hZmeas
    have hBi : Measurable (fun w : ball (0 : ℂ) ε =>
        ∫ t, B (w, t) ∂(volume.restrict (Ioc (0 : ℝ) 1))) :=
      (hB.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (Ioc (0 : ℝ) 1))).measurable
    convert hBi using 1
    funext w
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hderiv w t ⟨ht.1.le, ht.2⟩ v
  have hbeta (i : Fin 2) : Measurable (fun w : ball (0 : ℂ) ε => betaRoot ζ w i) :=
    hint (0, duals i)
  have hc : Measurable (fun w : ball (0 : ℂ) ε => cRoot ζ w) := hint (1, 0)
  have hKm : Measurable (fun w : ball (0 : ℂ) ε => K w) :=
    hKcont.domRestrict.measurable
  constructor
  · dsimp only [bTilde]
    have hb0 := (Complex.continuous_ofReal.measurable.comp (hbeta 0))
    have hb1 := (Complex.continuous_ofReal.measurable.comp (hbeta 1))
    have hs : Measurable (fun w : ball (0 : ℂ) ε => Analysis.planarMatrixSpin (K w)) := by
      have hKe (i j : Fin 2) : Measurable (fun w : ball (0 : ℂ) ε => K w i j) :=
        hKm.eval.eval
      dsimp [Analysis.planarMatrixSpin]
      exact (Complex.continuous_ofReal.measurable.comp ((hKe 0 0).sub (hKe 1 1))).add
        ((Complex.continuous_ofReal.measurable.comp ((hKe 0 1).add (hKe 1 0))).mul
          measurable_const)
    fun_prop
  · dsimp only [cTilde]
    exact (by fun_prop : Measurable (fun w : ball (0 : ℂ) ε => ‖(w : ℂ) ^ m‖ ^ 2)).mul hc
