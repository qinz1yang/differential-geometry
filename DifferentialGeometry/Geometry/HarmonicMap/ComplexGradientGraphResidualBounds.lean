import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingConductivityBounds
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

private def residualMatrixEntry (i j : Fin 2) : (ℂ →L[ℝ] ℂ) →L[ℝ] ℝ :=
  ((![Complex.reCLM, Complex.imCLM] : Fin 2 → ℂ →L[ℝ] ℝ) i).comp
    (ContinuousLinearMap.apply ℝ ℂ ((![1, Complex.I] : Fin 2 → ℂ) j))

private theorem residualMatrixEntry_apply (A : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    residualMatrixEntry i j (complexPlaneMatrixOperator A) = A i j := by
  fin_cases i <;> fin_cases j <;>
    simp [residualMatrixEntry, complexPlaneMatrixOperator, Complex.real_smul]

private def residualPrincipal (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    (ℂ →L[ℝ] ℂ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)).comp T).comp
      (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)) +
    ((ContinuousLinearMap.apply ℝ ℝ Complex.I).comp T).comp
      (ContinuousLinearMap.apply ℝ ℂ Complex.I)

private theorem residualPrincipal_norm (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    ‖residualPrincipal T‖ ≤ 2 * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro A
  have h1 : ‖A (1 : ℂ)‖ ≤ ‖A‖ := by simpa using A.le_opNorm (1 : ℂ)
  have hI : ‖A Complex.I‖ ≤ ‖A‖ := by simpa using A.le_opNorm Complex.I
  have hT1 : ‖T (A 1) 1‖ ≤ ‖T‖ * ‖A‖ := by
    calc
      _ ≤ ‖T‖ * ‖A 1‖ := by simpa using T.le_opNorm₂ (A 1) (1 : ℂ)
      _ ≤ ‖T‖ * ‖A‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg T)
  have hTI : ‖T (A Complex.I) Complex.I‖ ≤ ‖T‖ * ‖A‖ := by
    calc
      _ ≤ ‖T‖ * ‖A Complex.I‖ := by simpa using T.le_opNorm₂ (A Complex.I) Complex.I
      _ ≤ ‖T‖ * ‖A‖ := mul_le_mul_of_nonneg_left hI (norm_nonneg T)
  change ‖T (A 1) 1 + T (A Complex.I) Complex.I‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add hT1 hTI).trans_eq (by ring))

private theorem residualPrincipal_matrix (T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    residualPrincipal T (complexPlaneMatrixOperator A) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        A i j * T (![1, Complex.I] i) (![1, Complex.I] j) := by
  simp [residualPrincipal, complexPlaneMatrixOperator, Fin.sum_univ_two,
    map_add, map_smul]
  ring

end DifferentialGeometry.Geometry

theorem DifferentialGeometry.Geometry.chartLeadingPlaneProjection_graph_residual_jet_bounds
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
      (fun i => (2 : ℝ) * (w * b i).re)) (c : ℂ) :
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
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < C ∧
      ∀ q ∈ Metric.ball ((c, (0 : ℝ)), (0 : ℂ →L[ℝ] ℝ)) r,
        Y q ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
        0 < G q 0 0 * G q 1 1 - G q 0 1 ^ 2 ∧
        ∀ T : ℂ →L[ℝ] ℂ →L[ℝ] ℝ,
          ContDiffAt ℝ 1 (Phi T) q ∧
          let D := fderiv ℝ
            (fun j : ℝ × (ℂ →L[ℝ] ℝ) => Phi T ((q.1.1, j.1), j.2)) (q.1.2, q.2)
          ‖D (1, 0)‖ ≤ C * (‖T‖ + 1) ∧
          ‖D.comp (ContinuousLinearMap.inr ℝ ℝ (ℂ →L[ℝ] ℝ))‖ ≤
            C * (‖q - ((c, 0), 0)‖ * ‖T‖ + 1) := by
  classical
  intro Q proj dirs Y V G A theta Phi
  let J0 : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) := ((c, 0), 0)
  let Aop : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → (ℂ →L[ℝ] ℂ) :=
    fun q => complexPlaneMatrixOperator (A q)
  obtain ⟨hA, _hA0, rA, CA, hrA, hrA1, hCA, hAbound, hphysical⟩ :=
    chartLeadingPlaneProjection_conductivity_jet_bounds g hsrc hb hnull hN hunit L hL c
  change ContDiffAt ℝ 2 Aop J0 at hA
  have hAbound' (q : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ))
      (hq : q ∈ ball J0 rA) :
      ‖fderiv ℝ Aop q‖ ≤ CA ∧
      ‖(fderiv ℝ Aop q).comp
        (ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ))‖ ≤ CA * ‖q - J0‖ :=
    ⟨(hAbound q hq).2.1, (hAbound q hq).2.2⟩
  let Curved : ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) → ℝ := fun q =>
    ∑ i : Fin 2, ∑ j : Fin 2, A q i j *
      theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q))
  have hentry (i j : Fin 2) : ContDiffAt ℝ 1 (fun q => A q i j) J0 := by
    have heq : (fun q => A q i j) = fun q => residualMatrixEntry i j (Aop q) := by
      funext q
      exact (residualMatrixEntry_apply (A q) i j).symm
    rw [heq]
    exact (residualMatrixEntry i j).contDiff.contDiffAt.comp J0 (hA.of_le (by norm_num))
  have hY : ContDiff ℝ ∞ Y := by dsimp [Y]; fun_prop
  have hV (i : Fin 2) : ContDiff ℝ ∞
      (fun q : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) => V q.2 i) := by
    dsimp [V]
    fun_prop
  have hY0 : Y J0 ∈ interior (extChartAt 𝓘(ℝ, E) p).target := by
    rw [(isOpen_extChartAt_target p).interior_eq]
    have hx := (extChartAt 𝓘(ℝ, E) p).map_source
      (show x ∈ (extChartAt 𝓘(ℝ, E) p).source from by
        simpa only [extChartAt_source] using hsrc)
    simpa [Y, J0] using hx
  have hGamma (i j : Fin 2) : ContDiffAt ℝ 1
      (fun q : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) =>
        chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y q)) J0 :=
    (((contDiffAt_chartChristoffelContraction g p _ _ _ hY0).comp J0
      ((hV i).contDiffAt.prodMk ((hV j).contDiffAt.prodMk hY.contDiffAt))).of_le
        (by simp))
  have htheta : ContDiffAt ℝ 1
      (fun q : (ℂ × ℝ) × (ℂ →L[ℝ] ℝ) => theta q.2) J0 := by
    exact contDiffAt_const.sub (contDiffAt_snd.clm_comp contDiffAt_const)
  have hCurved : ContDiffAt ℝ 1 Curved J0 :=
    ContDiffAt.sum (fun i (_ : i ∈ Finset.univ) =>
      ContDiffAt.sum (fun j (_ : j ∈ Finset.univ) =>
        (hentry i j).mul (htheta.clm_apply (hGamma i j))))
  let M : ℝ := ‖fderiv ℝ Curved J0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMnear : ∀ᶠ q in 𝓝 J0, ‖fderiv ℝ Curved q‖ < M :=
    (hCurved.continuousAt_fderiv one_ne_zero).norm.eventually
      (gt_mem_nhds (by dsimp [M]; linarith))
  have hnear : ∀ᶠ q in 𝓝 J0,
      ContDiffAt ℝ 1 Aop q ∧ ContDiffAt ℝ 1 Curved q ∧ ‖fderiv ℝ Curved q‖ ≤ M := by
    filter_upwards [hA.eventually (by norm_num), hCurved.eventually (by norm_num), hMnear]
      with q hAq hCq hMq
    exact ⟨hAq.of_le (by norm_num), hCq, hMq.le⟩
  obtain ⟨s, hs, hlocal⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min rA s
  let C := 2 * CA + M + 1
  have hr : 0 < r := lt_min hrA hs
  have hC : 0 < C := by dsimp [C]; positivity
  have hCA2 : 2 * CA ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  refine ⟨r, C, hr, (min_le_left rA s).trans hrA1, hC, ?_⟩
  intro q hq
  have hqA : q ∈ ball J0 rA := ball_subset_ball (min_le_left rA s) hq
  have hqs : q ∈ ball J0 s := ball_subset_ball (min_le_right rA s) hq
  obtain ⟨hAq, hCq, hDCq⟩ := hlocal hqs
  have hAqbound := hAbound' q hqA
  refine ⟨(hphysical q hqA).1, (hphysical q hqA).2, ?_⟩
  intro T
  have hPhi : Phi T = fun q => residualPrincipal T (Aop q) + Curved q := by
    funext q
    dsimp only [Phi, Curved, Aop]
    rw [residualPrincipal_matrix]
    simp only [dirs, mul_add, Finset.sum_add_distrib]
  have hPhismooth : ContDiffAt ℝ 1 (Phi T) q := by
    rw [hPhi]
    exact ((residualPrincipal T).contDiff.contDiffAt.comp q hAq).add hCq
  refine ⟨hPhismooth, ?_⟩
  let J : (ℝ × (ℂ →L[ℝ] ℝ)) →L[ℝ] ((ℂ × ℝ) × (ℂ →L[ℝ] ℝ)) :=
    ((ContinuousLinearMap.inr ℝ ℂ ℝ).comp
      (ContinuousLinearMap.fst ℝ ℝ (ℂ →L[ℝ] ℝ))).prod
        (ContinuousLinearMap.snd ℝ ℝ (ℂ →L[ℝ] ℝ))
  have hJ : HasFDerivAt
      (fun j : ℝ × (ℂ →L[ℝ] ℝ) => ((q.1.1, j.1), j.2)) J (q.1.2, q.2) := by
    have hc : HasFDerivAt (fun _ : ℝ × (ℂ →L[ℝ] ℝ) => q.1.1)
        (0 : (ℝ × (ℂ →L[ℝ] ℝ)) →L[ℝ] ℂ) (q.1.2, q.2) :=
      hasFDerivAt_const q.1.1 (q.1.2, q.2)
    have hf : HasFDerivAt (fun j : ℝ × (ℂ →L[ℝ] ℝ) => j.1)
        (ContinuousLinearMap.fst ℝ ℝ (ℂ →L[ℝ] ℝ)) (q.1.2, q.2) :=
      hasFDerivAt_fst
    have hs : HasFDerivAt (fun j : ℝ × (ℂ →L[ℝ] ℝ) => j.2)
        (ContinuousLinearMap.snd ℝ ℝ (ℂ →L[ℝ] ℝ)) (q.1.2, q.2) :=
      hasFDerivAt_snd
    convert (hc.prodMk hf).prodMk hs using 1
    ext v <;> rfl
  have hDphi : fderiv ℝ (Phi T) q =
      (residualPrincipal T).comp (fderiv ℝ Aop q) + fderiv ℝ Curved q := by
    rw [hPhi]
    exact (((residualPrincipal T).hasFDerivAt.comp q
      (hAq.differentiableAt one_ne_zero).hasFDerivAt).add
        (hCq.differentiableAt one_ne_zero).hasFDerivAt).fderiv
  have hD : fderiv ℝ
      (fun j : ℝ × (ℂ →L[ℝ] ℝ) => Phi T ((q.1.1, j.1), j.2)) (q.1.2, q.2) =
        (fderiv ℝ (Phi T) q).comp J := by
    have hPhiAt : HasFDerivAt (Phi T) (fderiv ℝ (Phi T) q) q :=
      (hPhismooth.differentiableAt one_ne_zero).hasFDerivAt
    simpa only [Function.comp_def] using (hPhiAt.comp (q.1.2, q.2) hJ).fderiv
  dsimp only
  rw [hD]
  have hnT := residualPrincipal_norm T
  have hfull : ‖fderiv ℝ (Phi T) q‖ ≤ 2 * ‖T‖ * CA + M := by
    rw [hDphi]
    exact (norm_add_le _ _).trans (add_le_add
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hnT hAqbound.1 (norm_nonneg _) (by positivity))) hDCq)
  constructor
  · have hunitJ : ‖J (1, 0)‖ = 1 := by simp [J]
    calc
      _ ≤ ‖fderiv ℝ (Phi T) q‖ * ‖J (1, 0)‖ := (fderiv ℝ (Phi T) q).le_opNorm _
      _ ≤ 2 * ‖T‖ * CA + M := by simpa only [hunitJ, mul_one] using hfull
      _ ≤ C * (‖T‖ + 1) := by
        nlinarith [norm_nonneg T, mul_nonneg (sub_nonneg.mpr hCA2) (norm_nonneg T)]
  · let I := ContinuousLinearMap.inr ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ)
    have hcomp : ((fderiv ℝ (Phi T) q).comp J).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℂ →L[ℝ] ℝ)) =
          (residualPrincipal T).comp ((fderiv ℝ Aop q).comp I) +
            (fderiv ℝ Curved q).comp I := by
      rw [hDphi]
      ext v
      rfl
    rw [hcomp]
    have hcurveBound : ‖(fderiv ℝ Curved q).comp I‖ ≤ M :=
      ((ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ (ℂ × ℝ) (ℂ →L[ℝ] ℝ)))).trans hDCq
    calc
      _ ≤ ‖(residualPrincipal T).comp ((fderiv ℝ Aop q).comp I)‖ +
          ‖(fderiv ℝ Curved q).comp I‖ := norm_add_le _ _
      _ ≤ (2 * ‖T‖) * (CA * ‖q - J0‖) + M :=
        add_le_add ((ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul hnT hAqbound.2 (norm_nonneg _) (by positivity))) hcurveBound
      _ ≤ C * (‖q - ((c, 0), 0)‖ * ‖T‖ + 1) := by
        change (2 * ‖T‖) * (CA * ‖q - J0‖) + M ≤ C * (‖q - J0‖ * ‖T‖ + 1)
        nlinarith [norm_nonneg T, norm_nonneg (q - J0),
          mul_nonneg (sub_nonneg.mpr hCA2) (mul_nonneg (norm_nonneg (q - J0)) (norm_nonneg T))]
