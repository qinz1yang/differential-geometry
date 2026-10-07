import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphReparametrization
import DifferentialGeometry.Analysis.Calculus.Hadamard.Within
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral

set_option autoImplicit false

noncomputable section

open Set Metric Filter Manifold MeasureTheory DifferentialGeometry Bundle
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Topology ContDiff Manifold Interval

namespace DifferentialGeometry.Geometry

private abbrev GraphJet := ℝ × (ℂ →L[ℝ] ℝ)

section MetricJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem graph_jet_gram_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hx : x ∈ (chartAt E p).source)
    (L : ℂ →L[ℝ] E) (proj : E →L[ℝ] ℂ) (N : E)
    (hL : ∀ v, proj (L v) = v) (hN : proj N = 0)
    (ell : ℂ →L[ℝ] ℝ) :
    (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => chartGramBilin g p x
      (L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
      (L (![1, Complex.I] j) + ell (![1, Complex.I] j) • N)).PosDef := by
  classical
  let Q : LinearMap.BilinForm ℝ E := (chartGramBilin g p x).toLinearMap₁₂
  have hQmat : Q.toMatrix (chartModelBasis E) = chartGramMatrix g p x := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change chartGramBilin g p x (chartModelBasis E i) (chartModelBasis E j) =
      chartGramMatrix g p x i j
    rw [chartGramBilin_apply]
    simp only [Module.Basis.equivFun_self, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hb : x ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hQmatrix := chartGramMatrix_posDef g p hb
  have hQsym : Q.IsSymm := by
    apply (LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm (chartModelBasis E)).mp
    rw [hQmat]
    exact Matrix.isHermitian_iff_isSymm.mp hQmatrix.1
  have hQpos : Q.toQuadraticMap.PosDef := by
    apply (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
      (chartModelBasis E) Q hQsym).mpr
    rwa [hQmat]
  let K : ℂ →L[ℝ] E := L + ell.smulRight N
  have hK (v : ℂ) : proj (K v) = v := by
    simp only [K, add_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, hN, smul_zero, add_zero, hL]
  let G : LinearMap.BilinForm ℝ ℂ :=
    LinearMap.BilinForm.comp Q K.toLinearMap K.toLinearMap
  have hGsym : G.IsSymm := ⟨fun v w => hQsym.eq (K v) (K w)⟩
  have hGpos : G.toQuadraticMap.PosDef := by
    intro v hv
    apply hQpos
    intro h
    have hzero : K v = 0 := h
    have hc := hK v
    rw [hzero, map_zero] at hc
    exact hv hc.symm
  have hm : G.toMatrix Complex.basisOneI =
      (show Matrix (Fin 2) (Fin 2) ℝ from fun i j => chartGramBilin g p x
        (L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + ell (![1, Complex.I] j) • N)) := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change chartGramBilin g p x (K (Complex.basisOneI i)) (K (Complex.basisOneI j)) =
      chartGramBilin g p x (L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N)
        (L (![1, Complex.I] j) + ell (![1, Complex.I] j) • N)
    simp only [Complex.coe_basisOneI, K, add_apply, ContinuousLinearMap.smulRight_apply]
  rw [← hm]
  exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    Complex.basisOneI G hGsym).mp hGpos

private theorem graph_jet_gram_smooth
    {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {D : Set T} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    {Y : T → E} (hY : ContDiffOn ℝ ∞ Y D)
    (hchart : ∀ t ∈ D, Y t ∈ (extChartAt 𝓘(ℝ, E) p).target)
    {V : T → Fin 2 → E} (hV : ∀ i, ContDiffOn ℝ ∞ (fun t => V t i) D)
    (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun t => chartGramBilin g p
      ((extChartAt 𝓘(ℝ, E) p).symm (Y t)) (V t i) (V t j)) D := by
  have hG (k l : Fin (Module.finrank ℝ E)) :
      ContDiffOn ℝ ∞ (fun t => chartGramMatrix g p
        ((extChartAt 𝓘(ℝ, E) p).symm (Y t)) k l) D :=
    (Operator.chartGramOnE_contDiffOn g p k l).comp hY hchart
  have hcoord (k : Fin (Module.finrank ℝ E)) (i : Fin 2) :
      ContDiffOn ℝ ∞ (fun t => (chartModelBasis E).equivFun (V t i) k) D :=
    (chartCoordCLM E k).contDiff.comp_contDiffOn (hV i)
  have hsum := ContDiffOn.sum (fun k (_ : k ∈ Finset.univ) =>
    ContDiffOn.sum (fun l (_ : l ∈ Finset.univ) =>
      ((hG k l).mul (hcoord k i)).mul (hcoord l j)))
  simpa only [chartGramBilin_apply] using hsum

end MetricJets

private theorem graph_jet_partial_derivative
    {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    {R : ℂ × GraphJet → ℝ} (hR : ContDiffOn ℝ ∞ R D)
    {y : ℂ} {q : GraphJet} (hq : (y, q) ∈ D) :
    fderiv ℝ (fun q' => R (y, q')) q =
      (fderiv ℝ R (y, q)).comp (ContinuousLinearMap.inr ℝ ℂ GraphJet) := by
  have hp : HasFDerivAt (fun q' : GraphJet => (y, q'))
      (ContinuousLinearMap.inr ℝ ℂ GraphJet) q :=
    (hasFDerivAt_const y q).prodMk (hasFDerivAt_id q)
  exact (((hR.contDiffAt (hD.mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt.comp q hp).fderiv

private theorem graph_jet_integral_smooth
    {O : Set ℂ} (hO : IsOpen O) {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    {R : ℂ × GraphJet → ℝ} (hR : ContDiffOn ℝ ∞ R D)
    {J₁ J₂ : ℂ → GraphJet}
    (hJ₁ : ContDiffOn ℝ ∞ J₁ O) (hJ₂ : ContDiffOn ℝ ∞ J₂ O)
    (hsegment : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (y, (1 - t) • J₂ y + t • J₁ y) ∈ D) (v : GraphJet) :
    ContDiffOn ℝ ∞ (fun y => ∫ t in (0 : ℝ)..1,
      fderiv ℝ (fun q => R (y, q)) ((1 - t) • J₂ y + t • J₁ y) v) O := by
  let K : ℂ × ℝ → ℂ × GraphJet :=
    fun t => (t.1, (1 - t.2) • J₂ t.1 + t.2 • J₁ t.1)
  let Ω : Set (ℂ × ℝ) := (O ×ˢ univ) ∩ K ⁻¹' D
  have hK : ContDiffOn ℝ ∞ K (O ×ˢ univ) :=
    contDiffOn_fst.prodMk (((contDiffOn_const.sub contDiffOn_snd).smul
      (hJ₂.comp contDiffOn_fst (fun _ h => h.1))).add
      (contDiffOn_snd.smul (hJ₁.comp contDiffOn_fst (fun _ h => h.1))))
  have hΩ : IsOpen Ω := hK.continuousOn.isOpen_inter_preimage
    (hO.prod isOpen_univ) hD
  have hsub : O ×ˢ Icc (0 : ℝ) 1 ⊆ Ω := by
    intro t ht
    exact ⟨⟨ht.1, mem_univ _⟩, hsegment t.1 ht.1 t.2 ht.2⟩
  let DR : ℂ × GraphJet → GraphJet →L[ℝ] ℝ :=
    fun t => (fderiv ℝ R t).comp (ContinuousLinearMap.inr ℝ ℂ GraphJet)
  have hDR : ContDiffOn ℝ ∞ DR D :=
    (hR.fderiv_of_isOpen (m := ∞) hD (by simp)).clm_comp contDiffOn_const
  have hIntegrand : ContDiffOn ℝ ∞ (fun t => DR (K t) v) Ω :=
    (hDR.comp (hK.mono inter_subset_left) (fun _ h => h.2)).clm_apply contDiffOn_const
  have hIntegral := DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact
    (⊤ : ℕ∞) isCompact_Icc volume hO hΩ hsub hIntegrand
  apply hIntegral.congr
  intro y hy
  rw [integral_subtype measurableSet_Icc (fun t : ℝ => DR (K (y, t)) v),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  exact congrArg (fun T : GraphJet →L[ℝ] ℝ => T v)
    (graph_jet_partial_derivative hD hR (hsegment y hy t ht'))

private theorem graph_jet_integral_difference
    {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    {R : ℂ × GraphJet → ℝ} (hR : ContDiffOn ℝ ∞ R D)
    (y : ℂ) (q₁ q₂ : GraphJet)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (y, (1 - t) • q₂ + t • q₁) ∈ D) :
    R (y, q₁) - R (y, q₂) =
      ∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁) (q₁ - q₂) := by
  let J : ℝ → GraphJet := fun t => (1 - t) • q₂ + t • q₁
  have hJ (t : ℝ) : HasDerivAt J (q₁ - q₂) t := by
    have hd : HasDerivAt (fun x : ℝ => (1 - x) • q₂ + x • q₁)
        ((0 - 1 : ℝ) • q₂ + (1 : ℝ) • q₁) t :=
      (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const q₂).add
        ((hasDerivAt_id t).smul_const q₁)
    exact hd.congr_deriv (by rw [zero_sub, neg_one_smul, one_smul, sub_eq_add_neg, add_comm])
  have hDR : ContinuousOn (fun t =>
      (fderiv ℝ R (y, J t)) (0, q₁ - q₂)) (Icc (0 : ℝ) 1) :=
    (((hR.fderiv_of_isOpen (m := ∞) hD (by simp)).continuousOn.comp
      (continuousOn_const.prodMk (by fun_prop))
      (fun t ht => hsegment t ht)).clm_apply continuousOn_const)
  have hderiv (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t => R (y, J t))
        ((fderiv ℝ R (y, J t)) (0, q₁ - q₂)) t := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hd := ((hR.contDiffAt (hD.mem_nhds (hsegment t ht'))).differentiableAt
      (by simp)).hasFDerivAt
    exact hd.comp_hasDerivAt t ((hasDerivAt_const t y).prodMk (hJ t))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((by simpa using hDR : ContinuousOn (fun t =>
      (fderiv ℝ R (y, J t)) (0, q₁ - q₂)) (uIcc (0 : ℝ) 1)).intervalIntegrable)
  have hend : R (y, q₁) - R (y, q₂) =
      ∫ t in (0 : ℝ)..1, (fderiv ℝ R (y, J t)) (0, q₁ - q₂) := by
    simpa only [J, sub_self, zero_smul, one_smul, zero_add, sub_zero, add_zero]
      using hFTC.symm
  rw [hend]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
  exact (congrArg (fun T : GraphJet →L[ℝ] ℝ => T (q₁ - q₂))
    (graph_jet_partial_derivative hD hR (hsegment t ht'))).symm

section Residual

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
private def graphJetPosition (L : ℂ →L[ℝ] E) (N xa : E) (fa : ℂ)
    (t : ℂ × GraphJet) : E := xa + L (t.1 - fa) + t.2.1 • N

omit [FiniteDimensional ℝ E] in
private def graphJetTangent (L : ℂ →L[ℝ] E) (N : E)
    (ell : ℂ →L[ℝ] ℝ) (i : Fin 2) : E :=
  L (![1, Complex.I] i) + ell (![1, Complex.I] i) • N

private def graphJetGram (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (L : ℂ →L[ℝ] E) (N xa : E) (fa : ℂ) (t : ℂ × GraphJet) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (graphJetPosition L N xa fa t))
    (graphJetTangent L N t.2.2 i) (graphJetTangent L N t.2.2 j)

private def graphJetConductivity (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (L : ℂ →L[ℝ] E) (N xa : E) (fa : ℂ) (t : ℂ × GraphJet) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let H := graphJetGram g p L N xa fa t
  Analysis.planarConductivity (H 0 0) (H 1 1) (H 0 1)

private def graphJetResidual (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (L : ℂ →L[ℝ] E) (proj : E →L[ℝ] ℂ) (eta : E →L[ℝ] ℝ)
    (N xa : E) (fa : ℂ) (h₂ : ℂ → ℝ) (t : ℂ × GraphJet) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    graphJetConductivity g p L N xa fa t i j *
      (fderiv ℝ (fderiv ℝ h₂) t.1 (![1, Complex.I] i) (![1, Complex.I] j) +
        (eta - t.2.2.comp proj)
          (chartChristoffelContraction g p (graphJetTangent L N t.2.2 i)
            (graphJetTangent L N t.2.2 j) (graphJetPosition L N xa fa t)))

private theorem graph_jet_residual_smooth
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (L : ℂ →L[ℝ] E) (proj : E →L[ℝ] ℂ) (eta : E →L[ℝ] ℝ)
    (N xa : E) (fa : ℂ)
    (hL : ∀ v, proj (L v) = v) (hN : proj N = 0)
    {O : Set ℂ} (hO : IsOpen O) {h₂ : ℂ → ℝ} (hh₂ : ContDiffOn ℝ ∞ h₂ O) :
    let D : Set (ℂ × GraphJet) :=
      (O ×ˢ univ) ∩ graphJetPosition L N xa fa ⁻¹' (extChartAt 𝓘(ℝ, E) p).target
    IsOpen D ∧ ContDiffOn ℝ ∞ (graphJetResidual g p L proj eta N xa fa h₂) D := by
  classical
  let Y := graphJetPosition L N xa fa
  let H := graphJetGram g p L N xa fa
  let A := graphJetConductivity g p L N xa fa
  let D : Set (ℂ × GraphJet) :=
    (O ×ˢ univ) ∩ Y ⁻¹' (extChartAt 𝓘(ℝ, E) p).target
  have hY : ContDiff ℝ ∞ Y := by
    change ContDiff ℝ ∞ (fun t : ℂ × GraphJet => xa + L (t.1 - fa) + t.2.1 • N)
    fun_prop
  have hD : IsOpen D := (hO.prod isOpen_univ).inter
    ((isOpen_extChartAt_target p).preimage hY.continuous)
  refine ⟨hD, ?_⟩
  have hV (i : Fin 2) : ContDiff ℝ ∞
      (fun t : ℂ × GraphJet => graphJetTangent L N t.2.2 i) := by
    dsimp [graphJetTangent]
    fun_prop
  have hH (i j : Fin 2) : ContDiffOn ℝ ∞ (fun t => H t i j) D :=
    graph_jet_gram_smooth g p hY.contDiffOn (fun _ ht => ht.2)
      (fun k => (hV k).contDiffOn) i j
  have hHpos (t : ℂ × GraphJet) (ht : t ∈ D) : (H t).PosDef := by
    have hx : (extChartAt 𝓘(ℝ, E) p).symm (Y t) ∈ (chartAt E p).source := by
      simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) p).map_target ht.2
    exact graph_jet_gram_pos g hx L proj N hL hN t.2.2
  have hdet (t : ℂ × GraphJet) (ht : t ∈ D) :
      0 < H t 0 0 * H t 1 1 - H t 0 1 ^ 2 := by
    have hsym : H t 1 0 = H t 0 1 := by
      simpa only [star_trivial] using (hHpos t ht).1.apply 0 1
    simpa only [Matrix.det_fin_two, hsym, pow_two] using (hHpos t ht).det_pos
  have hA (i j : Fin 2) : ContDiffOn ℝ ∞ (fun t => A t i j) D :=
    Analysis.contDiffOn_planarConductivity (hH 0 0) (hH 1 1) (hH 0 1) hdet i j
  have hHess : ContDiffOn ℝ ∞ (fderiv ℝ (fderiv ℝ h₂)) O :=
    (hh₂.fderiv_of_isOpen (m := ∞) hO (by simp)).fderiv_of_isOpen (m := ∞) hO (by simp)
  have hK (i j : Fin 2) : ContDiffOn ℝ ∞ (fun t : ℂ × GraphJet =>
      fderiv ℝ (fderiv ℝ h₂) t.1 (![1, Complex.I] i) (![1, Complex.I] j)) D :=
    ((hHess.comp contDiffOn_fst (fun _ ht => ht.1.1)).clm_apply
      contDiffOn_const).clm_apply contDiffOn_const
  have hGamma (i j : Fin 2) : ContDiffOn ℝ ∞ (fun t =>
      chartChristoffelContraction g p (graphJetTangent L N t.2.2 i)
        (graphJetTangent L N t.2.2 j) (Y t)) D := by
    intro t ht
    have hy : Y t ∈ interior (extChartAt 𝓘(ℝ, E) p).target := by
      rw [(isOpen_extChartAt_target p).interior_eq]
      exact ht.2
    exact ((contDiffAt_chartChristoffelContraction g p _ _ _ hy).comp t
      ((hV i).contDiffAt.prodMk ((hV j).contDiffAt.prodMk hY.contDiffAt))).contDiffWithinAt
  have htheta : ContDiffOn ℝ ∞
      (fun t : ℂ × GraphJet => eta - t.2.2.comp proj) D :=
    contDiffOn_const.sub ((contDiffOn_snd.snd).clm_comp contDiffOn_const)
  exact ContDiffOn.sum (fun i (_ : i ∈ Finset.univ) =>
    ContDiffOn.sum (fun j (_ : j ∈ Finset.univ) =>
      (hA i j).mul ((hK i j).add (htheta.clm_apply (hGamma i j)))))

end Residual

private theorem graph_jet_segment_integrable
    {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    {R : ℂ × GraphJet → ℝ} (hR : ContDiffOn ℝ ∞ R D)
    (y : ℂ) (q₁ q₂ : GraphJet)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (y, (1 - t) • q₂ + t • q₁) ∈ D)
    (v : GraphJet) :
    IntervalIntegrable (fun t =>
      fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁) v) volume 0 1 := by
  have hc : ContinuousOn (fun t : ℝ =>
      (fderiv ℝ R (y, (1 - t) • q₂ + t • q₁)) (0, v)) (Icc (0 : ℝ) 1) :=
    ((hR.fderiv_of_isOpen (m := ∞) hD (by simp)).continuousOn.comp
      (by fun_prop) (fun t ht => hsegment t ht)).clm_apply continuousOn_const
  have hc' : ContinuousOn (fun t =>
      fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁) v) (Icc (0 : ℝ) 1) := by
    apply hc.congr
    intro t ht
    exact congrArg (fun T : GraphJet →L[ℝ] ℝ => T v)
      (graph_jet_partial_derivative hD hR (hsegment t ht))
  have hc'' : ContinuousOn (fun t =>
      fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁) v) (uIcc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hc'
  exact hc''.intervalIntegrable

private theorem graph_real_covector_coordinates (ell : ℂ →L[ℝ] ℝ) :
    ell = ell 1 • Complex.reCLM + ell Complex.I • Complex.imCLM := by
  ext z
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  calc
    ell z = ell (z.re • (1 : ℂ) + z.im • Complex.I) := congrArg ell hz
    _ = (ell 1 • Complex.reCLM + ell Complex.I • Complex.imCLM) z := by
      simp only [map_add, map_smul, add_apply, smul_apply,
        Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
      ring

private theorem graph_jet_difference_coefficients
    {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    {R : ℂ × GraphJet → ℝ} (hR : ContDiffOn ℝ ∞ R D)
    (y : ℂ) (q₁ q₂ : GraphJet)
    (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (y, (1 - t) • q₂ + t • q₁) ∈ D) :
    R (y, q₁) - R (y, q₂) =
      (∑ i : Fin 2,
        (∫ t in (0 : ℝ)..1,
          fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁)
            (0, ![Complex.reCLM, Complex.imCLM] i)) *
          ((q₁.2 - q₂.2) (![1, Complex.I] i))) +
      (∫ t in (0 : ℝ)..1,
        fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁) (1, 0)) *
        (q₁.1 - q₂.1) := by
  let ell := q₁.2 - q₂.2
  have hdelta : q₁ - q₂ =
      ell 1 • (0, Complex.reCLM) + ell Complex.I • (0, Complex.imCLM) +
        (q₁.1 - q₂.1) • (1, (0 : ℂ →L[ℝ] ℝ)) := by
    apply Prod.ext
    · simp
    · change ell = ell 1 • Complex.reCLM + ell Complex.I • Complex.imCLM +
        (q₁.1 - q₂.1) • (0 : ℂ →L[ℝ] ℝ)
      rw [smul_zero, add_zero]
      exact graph_real_covector_coordinates ell
  let T : ℝ → GraphJet →L[ℝ] ℝ := fun t =>
    fderiv ℝ (fun q => R (y, q)) ((1 - t) • q₂ + t • q₁)
  have hpoint (t : ℝ) : T t (q₁ - q₂) =
      ell 1 * T t (0, Complex.reCLM) + ell Complex.I * T t (0, Complex.imCLM) +
        (q₁.1 - q₂.1) * T t (1, 0) := by
    rw [hdelta]
    simp only [map_add, map_smul, smul_eq_mul]
  have hi (v : GraphJet) : IntervalIntegrable (fun t => T t v) volume 0 1 :=
    graph_jet_segment_integrable hD hR y q₁ q₂ hsegment v
  rw [graph_jet_integral_difference hD hR y q₁ q₂ hsegment]
  change (∫ t in (0 : ℝ)..1, T t (q₁ - q₂)) = _
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add
      (((hi (0, Complex.reCLM)).const_mul _).add ((hi (0, Complex.imCLM)).const_mul _))
      ((hi (1, 0)).const_mul _),
    intervalIntegral.integral_add ((hi (0, Complex.reCLM)).const_mul _)
      ((hi (0, Complex.imCLM)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  change ell 1 * (∫ t in (0 : ℝ)..1, T t (0, Complex.reCLM)) +
      ell Complex.I * (∫ t in (0 : ℝ)..1, T t (0, Complex.imCLM)) +
      (q₁.1 - q₂.1) * (∫ t in (0 : ℝ)..1, T t (1, 0)) = _
  ring

private theorem graph_jet_linearization_on
    {O : Set ℂ} (hO : IsOpen O) {h₁ h₂ : ℂ → ℝ}
    (hh₁ : ContDiffOn ℝ ∞ h₁ O) (hh₂ : ContDiffOn ℝ ∞ h₂ O)
    (P : ℂ → GraphJet → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ℝ)
    (A : ℂ → GraphJet → Matrix (Fin 2) (Fin 2) ℝ)
    (hAffine : ∀ y q K₁ K₂, P y q K₁ - P y q K₂ =
      ∑ i : Fin 2, ∑ j : Fin 2, A y q i j *
        (K₁ (![1, Complex.I] i) (![1, Complex.I] j) -
          K₂ (![1, Complex.I] i) (![1, Complex.I] j)))
    {D : Set (ℂ × GraphJet)} (hD : IsOpen D)
    (hR : ContDiffOn ℝ ∞
      (fun t : ℂ × GraphJet => P t.1 t.2 (fderiv ℝ (fderiv ℝ h₂) t.1)) D)
    (hsegment : ∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (y, (1 - t) • (h₂ y, fderiv ℝ h₂ y) + t • (h₁ y, fderiv ℝ h₁ y)) ∈ D)
    {S : Set ℂ} (hSO : S ⊆ O)
    (hEq₁ : ∀ y ∈ S, P y (h₁ y, fderiv ℝ h₁ y) (fderiv ℝ (fderiv ℝ h₁) y) = 0)
    (hEq₂ : ∀ y ∈ S, P y (h₂ y, fderiv ℝ h₂ y) (fderiv ℝ (fderiv ℝ h₂) y) = 0) :
    let w : ℂ → ℝ := fun y => h₁ y - h₂ y
    let J₁ : ℂ → GraphJet := fun y => (h₁ y, fderiv ℝ h₁ y)
    let J₂ : ℂ → GraphJet := fun y => (h₂ y, fderiv ℝ h₂ y)
    let J : ℂ → ℝ → GraphJet := fun y t => (1 - t) • J₂ y + t • J₁ y
    let R : ℂ → GraphJet → ℝ := fun y q => P y q (fderiv ℝ (fderiv ℝ h₂) y)
    let beta : ℂ → Fin 2 → ℝ := fun y i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (0, ![Complex.reCLM, Complex.imCLM] i)
    let c : ℂ → ℝ := fun y => ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (1, 0)
    (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧ ContDiffOn ℝ ∞ c O ∧
      ∀ y ∈ S,
        (∑ i : Fin 2, ∑ j : Fin 2,
          A y (J₁ y) i j * fderiv ℝ (fderiv ℝ w) y (![1, Complex.I] i) (![1, Complex.I] j)) +
          (∑ i : Fin 2, beta y i * fderiv ℝ w y (![1, Complex.I] i)) + c y * w y = 0 := by
  let w : ℂ → ℝ := fun y => h₁ y - h₂ y
  let J₁ : ℂ → GraphJet := fun y => (h₁ y, fderiv ℝ h₁ y)
  let J₂ : ℂ → GraphJet := fun y => (h₂ y, fderiv ℝ h₂ y)
  let J : ℂ → ℝ → GraphJet := fun y t => (1 - t) • J₂ y + t • J₁ y
  let R : ℂ → GraphJet → ℝ := fun y q => P y q (fderiv ℝ (fderiv ℝ h₂) y)
  let beta : ℂ → Fin 2 → ℝ := fun y i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (0, ![Complex.reCLM, Complex.imCLM] i)
  let c : ℂ → ℝ := fun y => ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (1, 0)
  have hJ₁ : ContDiffOn ℝ ∞ J₁ O :=
    hh₁.prodMk (hh₁.fderiv_of_isOpen (m := ∞) hO (by simp))
  have hJ₂ : ContDiffOn ℝ ∞ J₂ O :=
    hh₂.prodMk (hh₂.fderiv_of_isOpen (m := ∞) hO (by simp))
  have hbeta (i : Fin 2) : ContDiffOn ℝ ∞ (fun y => beta y i) O :=
    graph_jet_integral_smooth hO hD hR hJ₁ hJ₂ hsegment (0, ![Complex.reCLM, Complex.imCLM] i)
  have hc : ContDiffOn ℝ ∞ c O :=
    graph_jet_integral_smooth hO hD hR hJ₁ hJ₂ hsegment (1, 0)
  refine ⟨hbeta, hc, ?_⟩
  intro y hyS
  have hy := hSO hyS
  have hDw (q : ℂ) (hq : q ∈ O) :
      fderiv ℝ w q = fderiv ℝ h₁ q - fderiv ℝ h₂ q :=
    fderiv_sub ((hh₁.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp))
      ((hh₂.contDiffAt (hO.mem_nhds hq)).differentiableAt (by simp))
  have hD2w : fderiv ℝ (fderiv ℝ w) y =
      fderiv ℝ (fderiv ℝ h₁) y - fderiv ℝ (fderiv ℝ h₂) y := by
    have hn : fderiv ℝ w =ᶠ[𝓝 y] fun q => fderiv ℝ h₁ q - fderiv ℝ h₂ q := by
      filter_upwards [hO.mem_nhds hy] with q hq using hDw q hq
    rw [hn.fderiv_eq]
    exact fderiv_sub
      (((hh₁.fderiv_of_isOpen (m := ∞) hO (by simp)).contDiffAt (hO.mem_nhds hy)).differentiableAt
        (by simp))
      (((hh₂.fderiv_of_isOpen (m := ∞) hO (by simp)).contDiffAt (hO.mem_nhds hy)).differentiableAt
        (by simp))
  have hdiff := graph_jet_difference_coefficients hD hR y (J₁ y) (J₂ y) (hsegment y hy)
  change R y (J₁ y) - R y (J₂ y) =
    (∑ i : Fin 2, beta y i * (fderiv ℝ h₁ y - fderiv ℝ h₂ y) (![1, Complex.I] i)) + c y * w y
      at hdiff
  rw [← hDw y hy] at hdiff
  have hsplitP : P y (J₁ y) (fderiv ℝ (fderiv ℝ h₁) y) - R y (J₁ y) =
      ∑ i : Fin 2, ∑ j : Fin 2,
        A y (J₁ y) i j * fderiv ℝ (fderiv ℝ w) y (![1, Complex.I] i) (![1, Complex.I] j) := by
    rw [hD2w]
    exact hAffine y (J₁ y) _ _
  have hzero₁ : P y (J₁ y) (fderiv ℝ (fderiv ℝ h₁) y) = 0 := hEq₁ y hyS
  have hzero₂ : R y (J₂ y) = 0 := hEq₂ y hyS
  linarith

/-- Smooth graph-jet coefficients on an ambient neighborhood linearize the
height difference wherever both original graph equations hold. The equation
may hold only on a specified subset: its validity is not extended across the
boundary merely because the two heights extend smoothly. -/
theorem graph_height_difference_on_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M)
    (L : ℂ →L[ℝ] E) (proj : E →L[ℝ] ℂ) (eta : E →L[ℝ] ℝ)
    (N xa : E) (fa : ℂ)
    (hL : ∀ v, proj (L v) = v) (hN : proj N = 0)
    {O S : Set ℂ} (hO : IsOpen O) (hSO : S ⊆ O)
    {h₁ h₂ : ℂ → ℝ} (hh₁ : ContDiffOn ℝ ∞ h₁ O) (hh₂ : ContDiffOn ℝ ∞ h₂ O) :
    let w : ℂ → ℝ := fun y => h₁ y - h₂ y
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
    let Jet := ℝ × (ℂ →L[ℝ] ℝ)
    let J₁ : ℂ → Jet := fun y => (h₁ y, fderiv ℝ h₁ y)
    let J₂ : ℂ → Jet := fun y => (h₂ y, fderiv ℝ h₂ y)
    let J : ℂ → ℝ → Jet := fun y t => (1 - t) • J₂ y + t • J₁ y
    let Y : ℂ → Jet → E := fun y q => xa + L (y - fa) + q.1 • N
    let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
    let H : ℂ → Jet → Matrix (Fin 2) (Fin 2) ℝ := fun y q i j =>
      chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y y q)) (V q.2 i) (V q.2 j)
    let A : ℂ → Jet → Matrix (Fin 2) (Fin 2) ℝ := fun y q =>
      Analysis.planarConductivity (H y q 0 0) (H y q 1 1) (H y q 0 1)
    let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => eta - l.comp proj
    let P : ℂ → Jet → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ℝ := fun y q K =>
      ∑ i : Fin 2, ∑ j : Fin 2, A y q i j *
        (K (dirs i) (dirs j) +
          theta q.2 (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y y q)))
    let R : ℂ → Jet → ℝ := fun y q => P y q (fderiv ℝ (fderiv ℝ h₂) y)
    let beta : ℂ → Fin 2 → ℝ := fun y i =>
      ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (0, duals i)
    let c : ℂ → ℝ := fun y => ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (1, 0)
    (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      Y y (J y t) ∈ (extChartAt 𝓘(ℝ, E) p).target) →
    (∀ y ∈ S, P y (J₁ y) (fderiv ℝ (fderiv ℝ h₁) y) = 0) →
    (∀ y ∈ S, P y (J₂ y) (fderiv ℝ (fderiv ℝ h₂) y) = 0) →
    (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => A y (J₁ y) i j) O) ∧
    (∀ y ∈ O, (A y (J₁ y)).PosDef) ∧
    (∀ i : Fin 2, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧
    ContDiffOn ℝ ∞ c O ∧
    ∀ y ∈ S,
      (∑ i : Fin 2, ∑ j : Fin 2,
        A y (J₁ y) i j * fderiv ℝ (fderiv ℝ w) y (dirs i) (dirs j)) +
        (∑ i : Fin 2, beta y i * fderiv ℝ w y (dirs i)) + c y * w y = 0 := by
  classical
  intro w dirs duals Jet J₁ J₂ J Y V H A theta P R beta c hsegment hEq₁ hEq₂
  let D : Set (ℂ × GraphJet) :=
    (O ×ˢ univ) ∩ graphJetPosition L N xa fa ⁻¹' (extChartAt 𝓘(ℝ, E) p).target
  have hresidual : IsOpen D ∧ ContDiffOn ℝ ∞ (fun t : ℂ × GraphJet => R t.1 t.2) D :=
    graph_jet_residual_smooth g p L proj eta N xa fa hL hN hO hh₂
  obtain ⟨hD, hR⟩ := hresidual
  have hJs (y : ℂ) (hy : y ∈ O) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (y, (1 - t) • J₂ y + t • J₁ y) ∈ D :=
    ⟨⟨hy, mem_univ _⟩, hsegment y hy t ht⟩
  have hAffine (y : ℂ) (q : Jet) (K₁ K₂ : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
      P y q K₁ - P y q K₂ = ∑ i : Fin 2, ∑ j : Fin 2,
        A y q i j * (K₁ (dirs i) (dirs j) - K₂ (dirs i) (dirs j)) := by
    dsimp only [P]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  obtain ⟨hbeta, hc, hlinear⟩ := graph_jet_linearization_on hO hh₁ hh₂ P A hAffine
    hD hR hJs hSO hEq₁ hEq₂
  have hY₁ : ContDiffOn ℝ ∞ (fun y => Y y (J₁ y)) O :=
    (contDiffOn_const.add
      (L.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const))).add
      (hh₁.smul contDiffOn_const)
  have hV₁ (i : Fin 2) : ContDiffOn ℝ ∞ (fun y => V (J₁ y).2 i) O :=
    contDiffOn_const.add
      (((hh₁.fderiv_of_isOpen (m := ∞) hO (by simp)).clm_apply contDiffOn_const).smul
        contDiffOn_const)
  have hchart₁ (y : ℂ) (hy : y ∈ O) :
      Y y (J₁ y) ∈ (extChartAt 𝓘(ℝ, E) p).target := by
    have h := hsegment y hy 1 (by simp)
    simpa only [J, sub_self, zero_smul, one_smul, zero_add] using h
  have hHs (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y => H y (J₁ y) i j) O :=
    graph_jet_gram_smooth g p hY₁ hchart₁ hV₁ i j
  have hHp (y : ℂ) (hy : y ∈ O) : (H y (J₁ y)).PosDef := by
    have hx : (extChartAt 𝓘(ℝ, E) p).symm (Y y (J₁ y)) ∈ (chartAt E p).source := by
      simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ, E) p).map_target (hchart₁ y hy)
    exact graph_jet_gram_pos g hx L proj N hL hN (J₁ y).2
  have hdet (y : ℂ) (hy : y ∈ O) :
      0 < H y (J₁ y) 0 0 * H y (J₁ y) 1 1 - H y (J₁ y) 0 1 ^ 2 := by
    have hsym : H y (J₁ y) 1 0 = H y (J₁ y) 0 1 := by
      simpa only [star_trivial] using (hHp y hy).1.apply 0 1
    simpa only [Matrix.det_fin_two, hsym, pow_two] using (hHp y hy).det_pos
  refine ⟨?_, ?_, hbeta, hc, hlinear⟩
  · intro i j
    exact Analysis.contDiffOn_planarConductivity (hHs 0 0) (hHs 1 1) (hHs 0 1) hdet i j
  · intro y hy
    exact Analysis.planarConductivity_posDef (hHp y hy).diag_pos (hdet y hy)

/-- The actual heights of two distinct original harmonic conformal maps satisfy
one full linear elliptic equation on their common genuine source side. Smooth
extensions of the heights supply smooth coefficients and positive principal
part on the ambient graph neighborhood. Both original source sections, metric,
projection and normal remain fixed; no equation is asserted on the other side. -/
theorem two_original_maps_graph_height_difference_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p p₀ : M)
    (b : Fin (Module.finrank ℝ E) → ℂ) (N : E)
    (hunit : chartGramBilin g p p₀ N N = 1)
    (hprojN : chartLeadingPlaneProjection g p p₀ b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
        (fun i => (2 : ℝ) * (chartLeadingPlaneProjection g p p₀ b v * b i).re) +
        (chartGramBilin g p p₀ N v) • N)
    {U₁ U₂ : ℂ → M} {a₁ a₂ : ℂ}
    (hbase₁ : U₁ a₁ = p₀) (hbase₂ : U₂ a₂ = p₀)
    {s₁ s₂ : Set ℂ} (hs₁ : IsOpen s₁) (hs₂ : IsOpen s₂)
    (hU₁ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₁ s₁)
    (hU₂ : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U₂ s₂)
    (hconf₁ : ∀ z ∈ s₁, DiskMapConformalAt g U₁ z)
    (hconf₂ : ∀ z ∈ s₂, DiskMapConformalAt g U₂ z)
    (hharm₁ : ∀ z ∈ s₁, diskMapTension g U₁ z = 0)
    (hharm₂ : ∀ z ∈ s₂, diskMapTension g U₂ z = 0)
    (hchart₁ : ∀ z ∈ s₁, U₁ z ∈ (chartAt E p).source)
    (hchart₂ : ∀ z ∈ s₂, U₂ z ∈ (chartAt E p).source)
    {O S : Set ℂ} (hO : IsOpen O) (hS : IsOpen S) (hSO : S ⊆ O)
    (hSnonempty : S.Nonempty)
    (h₁ h₂ : ℂ → ℝ) (hh₁ : ContDiffOn ℝ ∞ h₁ O) (hh₂ : ContDiffOn ℝ ∞ h₂ O)
    (r₁ r₂ : ℂ → ℂ) (hr₁ : ContDiffOn ℝ ∞ r₁ S) (hr₂ : ContDiffOn ℝ ∞ r₂ S)
    (hmaps₁ : MapsTo r₁ S s₁) (hmaps₂ : MapsTo r₂ S s₂)
    (hright₁ : ∀ y ∈ S, chartLeadingPlaneProjection g p p₀ b
      (extChartAt 𝓘(ℝ, E) p (U₁ (r₁ y))) = y)
    (hright₂ : ∀ y ∈ S, chartLeadingPlaneProjection g p p₀ b
      (extChartAt 𝓘(ℝ, E) p (U₂ (r₂ y))) = y)
    (hheight₁ : ∀ y ∈ S, h₁ y = chartGramBilin g p p₀ N
      (extChartAt 𝓘(ℝ, E) p (U₁ (r₁ y)) - extChartAt 𝓘(ℝ, E) p p₀))
    (hheight₂ : ∀ y ∈ S, h₂ y = chartGramBilin g p p₀ N
      (extChartAt 𝓘(ℝ, E) p (U₂ (r₂ y)) - extChartAt 𝓘(ℝ, E) p p₀)) :
    let xa := extChartAt 𝓘(ℝ, E) p p₀
    let proj := chartLeadingPlaneProjection g p p₀ b
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    (∀ y ∈ O, ∀ t ∈ Icc (0 : ℝ) 1,
      (1 - t) • (xa + lift (y - proj xa) + h₂ y • N) +
        t • (xa + lift (y - proj xa) + h₁ y • N) ∈
          (extChartAt 𝓘(ℝ, E) p).target) →
    ∃ (A : ℂ → Matrix (Fin 2) (Fin 2) ℝ) (beta : ℂ → Fin 2 → ℝ) (c : ℂ → ℝ),
      (∀ i j, ContDiffOn ℝ ∞ (fun y => A y i j) O) ∧
      (∀ y ∈ O, (A y).PosDef) ∧
      (∀ i, ContDiffOn ℝ ∞ (fun y => beta y i) O) ∧ ContDiffOn ℝ ∞ c O ∧
      ∀ y ∈ S,
        (∑ i : Fin 2, ∑ j : Fin 2,
          A y i j * fderiv ℝ (fderiv ℝ (h₁ - h₂)) y (![1, Complex.I] i) (![1, Complex.I] j)) +
          (∑ i : Fin 2, beta y i * fderiv ℝ (h₁ - h₂) y (![1, Complex.I] i)) +
            c y * (h₁ - h₂) y = 0 := by
  classical
  intro xa proj lift hsegment
  change proj N = 0 at hprojN
  let eta := chartGramBilin g p p₀ N
  let Z : ℂ → E := fun y => extChartAt 𝓘(ℝ, E) p (U₁ (r₁ y))
  have hZ : ContDiffOn ℝ ∞ Z S := by
    have hX : ContDiffOn ℝ ∞ (fun z => extChartAt 𝓘(ℝ, E) p (U₁ z)) s₁ := by
      intro z hz
      exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart₁ z hz)).comp z
        (hU₁.contMDiffAt (hs₁.mem_nhds hz))).contDiffAt).contDiffWithinAt
    exact hX.comp hr₁ hmaps₁
  obtain ⟨y₀, hy₀⟩ := hSnonempty
  let R₀ : ℂ →L[ℝ] E := fderiv ℝ Z y₀
  have hprojR (v : ℂ) : proj (R₀ v) = v := by
    have hn : proj ∘ Z =ᶠ[𝓝 y₀] id := by
      filter_upwards [hS.mem_nhds hy₀] with y hy using hright₁ y hy
    have hd := (proj.hasFDerivAt.comp y₀
      ((hZ.contDiffAt (hS.mem_nhds hy₀)).differentiableAt (by simp)).hasFDerivAt).fderiv
    rw [hn.fderiv_eq, fderiv_id] at hd
    exact (congrArg (fun T : ℂ →L[ℝ] ℂ => T v) hd).symm
  let L : ℂ →L[ℝ] E := R₀ - (eta.smulRight N).comp R₀
  have hL (v : ℂ) : L v = lift v := by
    have hh := hsplit (R₀ v)
    change R₀ v = lift (proj (R₀ v)) + eta (R₀ v) • N at hh
    rw [hprojR] at hh
    change R₀ v - eta (R₀ v) • N = lift v
    exact sub_eq_iff_eq_add.mpr hh
  have hPL (v : ℂ) : proj (L v) = v := by
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, hprojN,
      smul_zero, sub_zero, hprojR]
  let dirs : Fin 2 → ℂ := ![1, Complex.I]
  let duals : Fin 2 → (ℂ →L[ℝ] ℝ) := ![Complex.reCLM, Complex.imCLM]
  let J₁ : ℂ → GraphJet := fun y => (h₁ y, fderiv ℝ h₁ y)
  let J₂ : ℂ → GraphJet := fun y => (h₂ y, fderiv ℝ h₂ y)
  let J : ℂ → ℝ → GraphJet := fun y t => (1 - t) • J₂ y + t • J₁ y
  let Y : ℂ → GraphJet → E := fun y q => xa + L (y - proj xa) + q.1 • N
  let V : (ℂ →L[ℝ] ℝ) → Fin 2 → E := fun l i => L (dirs i) + l (dirs i) • N
  let H : ℂ → GraphJet → Matrix (Fin 2) (Fin 2) ℝ := fun y q i j =>
    chartGramBilin g p ((extChartAt 𝓘(ℝ, E) p).symm (Y y q)) (V q.2 i) (V q.2 j)
  let A : ℂ → GraphJet → Matrix (Fin 2) (Fin 2) ℝ := fun y q =>
    Analysis.planarConductivity (H y q 0 0) (H y q 1 1) (H y q 0 1)
  let theta : (ℂ →L[ℝ] ℝ) → E →L[ℝ] ℝ := fun l => eta - l.comp proj
  let P : ℂ → GraphJet → (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) → ℝ := fun y q K =>
    ∑ i : Fin 2, ∑ j : Fin 2, A y q i j *
      (K (dirs i) (dirs j) + theta q.2
        (chartChristoffelContraction g p (V q.2 i) (V q.2 j) (Y y q)))
  let R : ℂ → GraphJet → ℝ := fun y q => P y q (fderiv ℝ (fderiv ℝ h₂) y)
  let beta : ℂ → Fin 2 → ℝ := fun y i =>
    ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (0, duals i)
  let c : ℂ → ℝ := fun y => ∫ t in (0 : ℝ)..1, fderiv ℝ (R y) (J y t) (1, 0)
  have hJs (y : ℂ) (hy : y ∈ O) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Y y (J y t) ∈ (extChartAt 𝓘(ℝ, E) p).target := by
    have hp : Y y (J y t) =
        (1 - t) • (xa + lift (y - proj xa) + h₂ y • N) +
          t • (xa + lift (y - proj xa) + h₁ y • N) := by
      change xa + L (y - proj xa) + ((1 - t) * h₂ y + t * h₁ y) • N = _
      rw [hL]
      let v := xa + lift (y - proj xa)
      have hv : (1 - t) • v + t • v = v := by
        rw [← add_smul, sub_add_cancel, one_smul]
      change v + ((1 - t) * h₂ y + t * h₁ y) • N =
        (1 - t) • (v + h₂ y • N) + t • (v + h₁ y • N)
      calc
        _ = ((1 - t) • v + t • v) +
            (((1 - t) * h₂ y) • N + (t * h₁ y) • N) := by rw [hv, add_smul]
        _ = (1 - t) • (v + h₂ y • N) + t • (v + h₁ y • N) := by
          simp only [smul_add, smul_smul]
          abel
    rw [hp]
    exact hsegment y hy t ht
  have hEq (U : ℂ → M) (a : ℂ) (s : Set ℂ) (hs : IsOpen s)
      (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
      (hbase : U a = p₀) (hconf : ∀ z ∈ s, DiskMapConformalAt g U z)
      (hharm : ∀ z ∈ s, diskMapTension g U z = 0)
      (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
      (r : ℂ → ℂ) (hr : ContDiffOn ℝ ∞ r S) (hmaps : MapsTo r S s)
      (h : ℂ → ℝ)
      (hright : ∀ y ∈ S, proj (extChartAt 𝓘(ℝ, E) p (U (r y))) = y)
      (hheight : ∀ y ∈ S, h y = eta (extChartAt 𝓘(ℝ, E) p (U (r y)) - xa)) :
      ∀ y ∈ S, P y (h y, fderiv ℝ h y) (fderiv ℝ (fderiv ℝ h) y) = 0 := by
    have hresult := chartLeadingPlaneProjection_graph_equation_of_source_section g hs hU hconf
      hharm (a := a) (p := p) hchart (b := b) N
      (by simpa only [hbase] using hunit)
      (by simpa only [hbase] using hprojN)
      (by simpa only [hbase] using hsplit) hS r hr hmaps h
      (by simpa only [hbase] using hright)
      (by simpa only [hbase] using hheight)
    intro y hy
    obtain ⟨hgraph, _, _, _, hp⟩ := hresult.2 y hy
    have hYeq : Y y (h y, fderiv ℝ h y) = extChartAt 𝓘(ℝ, E) p (U (r y)) := by
      simpa only [Y, hL, hbase] using hgraph.symm
    have hinv : (extChartAt 𝓘(ℝ, E) p).symm (Y y (h y, fderiv ℝ h y)) = U (r y) := by
      rw [hYeq]
      exact (extChartAt 𝓘(ℝ, E) p).left_inv
        (by simpa only [extChartAt_source] using hchart _ (hmaps hy))
    dsimp only [P, A, H]
    rw [hinv]
    simpa only [V, Y, theta, dirs, hL, hbase] using hp
  have hEq₁ := hEq U₁ a₁ s₁ hs₁ hU₁ hbase₁ hconf₁ hharm₁ hchart₁
    r₁ hr₁ hmaps₁ h₁ hright₁ hheight₁
  have hEq₂ := hEq U₂ a₂ s₂ hs₂ hU₂ hbase₂ hconf₂ hharm₂ hchart₂
    r₂ hr₂ hmaps₂ h₂ hright₂ hheight₂
  obtain ⟨hA, hAp, hbeta, hc, hlinear⟩ :=
    graph_height_difference_on_subset g p L proj eta N xa (proj xa) hPL hprojN
      hO hSO hh₁ hh₂ hJs hEq₁ hEq₂
  exact ⟨fun y => A y (J₁ y), beta, c, hA, hAp, hbeta, hc, hlinear⟩

end DifferentialGeometry.Geometry
