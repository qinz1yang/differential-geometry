import DifferentialGeometry.Geometry.HarmonicMap.ComplexGradientLeadingPlane
import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource
import DifferentialGeometry.Analysis.Calculus.Derivative.RankOneContraction
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Coefficients

set_option autoImplicit false

noncomputable section

open Set Filter Manifold Bundle InnerProductSpace DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem graph_gram_eq_inner
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p x : M) (v w : E) :
    chartGramBilin g p x v w = g.inner x
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).symmL ℝ x v)
      ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).symmL ℝ x w) := by
  simpa only [chartGramBilin_apply, chartCoord, Module.Basis.equivFun_apply] using
    (inner_eq_chartGramOnE_bilinear_on_baseSet g p v w).symm

private theorem graph_gram_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {p x : M}
    (hx : x ∈ (chartAt E p).source) {v : E} (hv : v ≠ 0) :
    0 < chartGramBilin g p x v v := by
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hb : x ∈ T.baseSet := by
    simpa only [T, TangentBundle.trivializationAt_baseSet] using hx
  have hne : T.symmL ℝ x v ≠ 0 := by
    intro h
    have hh := congrArg (T.continuousLinearMapAt ℝ x) h
    rw [T.continuousLinearMapAt_symmL hb, map_zero] at hh
    exact hv hh
  rw [graph_gram_eq_inner]
  exact g.pos x _ hne

omit [FiniteDimensional ℝ E] in
private theorem graph_chart_partial
    {U : ℂ → M} {z : ℂ}
    (hU : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z) {p : M}
    (hsrc : U z ∈ (chartAt E p).source) (v : ℂ) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).symmL ℝ (U z)
      (fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z v) = diskMapPartial U z v := by
  let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) p
  have hb : U z ∈ T.baseSet := by
    simpa only [T, TangentBundle.trivializationAt_baseSet] using hsrc
  have hc := contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := 1) hsrc
  have hd : (T.continuousLinearMapAt ℝ (U z)).comp
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) =
        fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z := by
    dsimp only [T]
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hsrc]
    exact (mfderiv_comp (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
      (I'' := 𝓘(ℝ, E)) z (hc.mdifferentiableAt (by norm_num))
      (hU.mdifferentiableAt (by norm_num))).symm.trans mfderiv_eq_fderiv
  have hv : T.continuousLinearMapAt ℝ (U z) (diskMapPartial U z v) =
      fderiv ℝ (extChartAt 𝓘(ℝ, E) p ∘ U) z v :=
    congrArg (fun K => K v) hd
  exact (congrArg (T.symmL ℝ (U z)) hv.symm).trans
    (T.symmL_continuousLinearMapAt hb _)

private theorem mul_transpose_eq_smul_inv_of_conformal
    (D H : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (hD : IsUnit D.det) (hH : IsUnit H.det)
    (hconformal : D.transpose * H * D = t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    D * D.transpose = t • H⁻¹ := by
  have hm := congrArg (fun K : Matrix (Fin 2) (Fin 2) ℝ => D * K * D⁻¹) hconformal
  have hleft : D * D.transpose * H = t • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa only [Matrix.mul_assoc, mul_smul_comm, smul_mul_assoc,
      Matrix.mul_nonsing_inv D hD, Matrix.one_mul, Matrix.mul_one] using hm
  calc
    D * D.transpose = (D * D.transpose * H) * H⁻¹ := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv H hH, Matrix.mul_one]
    _ = t • H⁻¹ := by rw [hleft, smul_mul_assoc, Matrix.one_mul]

private def graph_christoffel_bilin
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (p : M) (x : E) :
    E →L[ℝ] E →L[ℝ] E :=
  (LinearMap.mk₂ ℝ (fun v w => chartChristoffelContraction g p v w x)
    (fun v₁ v₂ w => ChartChristoffel.contraction_add_left v₁ v₂ w)
    (fun c v w => ChartChristoffel.contraction_smul_left c v w)
    (fun v w₁ w₂ => ChartChristoffel.contraction_add_right v w₁ w₂)
    (fun c v w => ChartChristoffel.contraction_smul_right c v w)).toContinuousBilinearMap

theorem chartLeadingPlaneProjection_graph_equation
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s)
    (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconformal : ∀ z ∈ s, DiskMapConformalAt g U z)
    (htension : ∀ z ∈ s, diskMapTension g U z = 0)
    {a : ℂ} {p : M}
    (hchart : ∀ z ∈ s, U z ∈ (chartAt E p).source)
    {b : Fin (Module.finrank ℝ E) → ℂ} (N : E)
    (hunit : chartGramBilin g p (U a) N N = 1)
    (hprojN : chartLeadingPlaneProjection g p (U a) b N = 0)
    (hsplit : ∀ v : E,
      v = (chartModelBasis E).equivFunL.symm
          (fun i => (2 : ℝ) *
            (chartLeadingPlaneProjection g p (U a) b v * b i).re) +
        (chartGramBilin g p (U a) N v) • N)
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hesource : e.source ⊆ s)
    (he : (e : ℂ → ℂ) = fun z => chartLeadingPlaneProjection g p (U a) b
      (extChartAt 𝓘(ℝ, E) p (U z)))
    (heinverse : ContDiffOn ℝ ∞ e.symm e.target) :
    let Q := chartGramBilin g p (U a)
    let proj := chartLeadingPlaneProjection g p (U a) b
    let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
    let F : ℂ → ℂ := fun z => proj (X z)
    let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
      (fun i => (2 : ℝ) * (w * b i).re)
    let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
    ContDiffOn ℝ ∞ h e.target ∧
    (∀ y ∈ e.target, X (e.symm y) = X a + lift (y - F a) + h y • N) ∧
    let Y : ℂ → E := fun y => X a + lift (y - F a) + h y • N
    let dirs : Fin 2 → ℂ := ![1, Complex.I]
    let W : ℂ → Fin 2 → E := fun y i =>
      lift (dirs i) + (fderiv ℝ h y (dirs i)) • N
    let H : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y i j =>
      chartGramBilin g p (U (e.symm y)) (W y i) (W y j)
    let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
      DifferentialGeometry.Analysis.planarConductivity (H y 0 0) (H y 1 1) (H y 0 1)
    let theta : ℂ → E →L[ℝ] ℝ := fun y => Q N - (fderiv ℝ h y).comp proj
    (∀ y ∈ e.target,
      Y y ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      (extChartAt 𝓘(ℝ, E) p).symm (Y y) = U (e.symm y)) ∧
    (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => H y i j) e.target) ∧
    (∀ y ∈ e.target, (H y).PosDef) ∧
    (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => A y i j) e.target) ∧
    ∀ y ∈ e.target,
      (A y).PosDef ∧
      A y = Real.sqrt (H y).det • (H y)⁻¹ ∧
      (∑ i : Fin 2, ∑ j : Fin 2,
        A y i j * (fderiv ℝ (fderiv ℝ h) y (dirs i) (dirs j) +
          theta y (chartChristoffelContraction g p (W y i) (W y j) (Y y)))) = 0 := by
  classical
  let Q := chartGramBilin g p (U a)
  let proj := chartLeadingPlaneProjection g p (U a) b
  let X : ℂ → E := fun z => extChartAt 𝓘(ℝ, E) p (U z)
  let F : ℂ → ℂ := fun z => proj (X z)
  let lift : ℂ → E := fun w => (chartModelBasis E).equivFunL.symm
    (fun i => (2 : ℝ) * (w * b i).re)
  let h : ℂ → ℝ := fun y => Q N (X (e.symm y) - X a)
  let Y : ℂ → E := fun y => X a + lift (y - F a) + h y • N
  let dirs : Fin 2 → ℂ := ![1, Complex.I]
  let W : ℂ → Fin 2 → E := fun y i => lift (dirs i) + (fderiv ℝ h y (dirs i)) • N
  let H : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y i j =>
    chartGramBilin g p (U (e.symm y)) (W y i) (W y j)
  let A : ℂ → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    Analysis.planarConductivity (H y 0 0) (H y 1 1) (H y 0 1)
  let theta : ℂ → E →L[ℝ] ℝ := fun y => Q N - (fderiv ℝ h y).comp proj
  change Q N N = 1 at hunit
  change proj N = 0 at hprojN
  change ∀ v : E, v = lift (proj v) + (Q N v) • N at hsplit
  change (e : ℂ → ℂ) = F at he
  change ContDiffOn ℝ ∞ h e.target ∧
    (∀ y ∈ e.target, X (e.symm y) = Y y) ∧
    (∀ y ∈ e.target, Y y ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      (extChartAt 𝓘(ℝ, E) p).symm (Y y) = U (e.symm y)) ∧
    (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => H y i j) e.target) ∧
    (∀ y ∈ e.target, (H y).PosDef) ∧
    (∀ i j : Fin 2, ContDiffOn ℝ ∞ (fun y => A y i j) e.target) ∧
    ∀ y ∈ e.target, (A y).PosDef ∧ A y = Real.sqrt (H y).det • (H y)⁻¹ ∧
      (∑ i : Fin 2, ∑ j : Fin 2,
        A y i j * (fderiv ℝ (fderiv ℝ h) y (dirs i) (dirs j) +
          theta y (chartChristoffelContraction g p (W y i) (W y j) (Y y)))) = 0
  by_cases hempty : e.target = ∅
  · simp only [hempty, contDiffOn_empty, Set.mem_empty_iff_false, false_implies,
      implies_true, and_self]
  obtain ⟨y₀, hy₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
  have hX : ContDiffOn ℝ ∞ X s := by
    intro z hz
    exact (((contMDiffAt_extChartAt' (I := 𝓘(ℝ, E)) (n := ∞) (hchart z hz)).comp z
      (hU.contMDiffAt (hs.mem_nhds hz))).contDiffAt).contDiffWithinAt
  have hF : ContDiffOn ℝ ∞ F s := proj.contDiff.comp_contDiffOn hX
  have hXe : ContDiffOn ℝ ∞ (fun y => X (e.symm y)) e.target :=
    hX.comp heinverse (fun y hy => hesource (e.map_target hy))
  have hh : ContDiffOn ℝ ∞ h e.target :=
    (Q N).contDiff.comp_contDiffOn (hXe.sub contDiffOn_const)
  have hright (y : ℂ) (hy : y ∈ e.target) : F (e.symm y) = y := by
    rw [← he]
    exact e.right_inv hy
  have hFmap (z : ℂ) (hz : z ∈ e.source) : F z ∈ e.target := by
    rw [← he]
    exact e.map_source hz
  have hleft (z : ℂ) (hz : z ∈ e.source) : e.symm (F z) = z := by
    rw [← he]
    exact e.left_inv hz
  have hgraph (y : ℂ) (hy : y ∈ e.target) : X (e.symm y) = Y y := by
    have hp : proj (X (e.symm y) - X a) = y - F a := by
      rw [map_sub]
      change F (e.symm y) - F a = y - F a
      rw [hright y hy]
    calc
      X (e.symm y) = X a + (X (e.symm y) - X a) := by abel
      _ = X a + (lift (y - F a) + h y • N) := by
        rw [hsplit (X (e.symm y) - X a), hp]
      _ = Y y := (add_assoc _ _ _).symm
  have hYchart (y : ℂ) (hy : y ∈ e.target) :
      Y y ∈ (extChartAt 𝓘(ℝ, E) p).target ∧
      (extChartAt 𝓘(ℝ, E) p).symm (Y y) = U (e.symm y) := by
    have hc : U (e.symm y) ∈ (extChartAt 𝓘(ℝ, E) p).source := by
      simpa only [extChartAt_source] using hchart _ (hesource (e.map_target hy))
    rw [← hgraph y hy]
    exact ⟨(extChartAt 𝓘(ℝ, E) p).map_source hc,
      (extChartAt 𝓘(ℝ, E) p).left_inv hc⟩
  have hDF (z : ℂ) (hz : z ∈ s) :
      fderiv ℝ F z = proj.comp (fderiv ℝ X z) :=
    (proj.hasFDerivAt.comp z
      ((hX.contDiffAt (hs.mem_nhds hz)).differentiableAt (by simp)).hasFDerivAt).fderiv
  have hrightD (y : ℂ) (hy : y ∈ e.target) :
      (fderiv ℝ F (e.symm y)).comp (fderiv ℝ e.symm y) =
        ContinuousLinearMap.id ℝ ℂ := by
    have hnear : F ∘ e.symm =ᶠ[𝓝 y] id := by
      filter_upwards [e.open_target.mem_nhds hy] with q hq using hright q hq
    rw [← fderiv_comp y
      ((hF.contDiffAt (hs.mem_nhds (hesource (e.map_target hy)))).differentiableAt (by simp))
      ((heinverse.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)),
      hnear.fderiv_eq, fderiv_id]
  let R : ℂ →L[ℝ] E := (fderiv ℝ X (e.symm y₀)).comp (fderiv ℝ e.symm y₀)
  have hprojR (w : ℂ) : proj (R w) = w := by
    have hr := congrArg (fun T : ℂ →L[ℝ] ℂ => T w) (hrightD y₀ hy₀)
    rw [hDF _ (hesource (e.map_target hy₀))] at hr
    exact hr
  let L : ℂ →L[ℝ] E := R - ((Q N).smulRight N).comp R
  have hL (w : ℂ) : L w = lift w := by
    have hsplitR := hsplit (R w)
    rw [hprojR] at hsplitR
    change R w - (Q N (R w)) • N = lift w
    exact sub_eq_iff_eq_add.mpr hsplitR
  have hprojL (w : ℂ) : proj (L w) = w := by
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, hprojN, smul_zero,
      sub_zero, hprojR]
  have hEtaL (w : ℂ) : Q N (L w) = 0 := by
    simp only [L, sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, hunit,
      smul_eq_mul, mul_one, sub_self]
  have hY : ContDiffOn ℝ ∞ Y e.target := by
    have hY' : ContDiffOn ℝ ∞
        (fun q : ℂ => X a + L (q - F a) + h q • N) e.target :=
      (contDiffOn_const.add
        (L.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const))).add
        (hh.smul contDiffOn_const)
    exact hY'.congr (fun y _ => by simp only [Y, hL])
  have hDY (y : ℂ) (hy : y ∈ e.target) :
      fderiv ℝ Y y = L + (fderiv ℝ h y).smulRight N := by
    have hhy := ((hh.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by simp)).hasFDerivAt
    have hd := ((hasFDerivAt_const (X a) y).add
      (L.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (F a)))).add
      (hhy.smul_const N)
    have hfun : (fun q : ℂ => X a + L (q - F a) + h q • N) = Y := by
      funext q
      simp only [Y, hL]
    change HasFDerivAt (fun q : ℂ => X a + L (q - F a) + h q • N)
      (0 + L.comp (ContinuousLinearMap.id ℝ ℂ) + (fderiv ℝ h y).smulRight N) y at hd
    rw [hfun] at hd
    simpa only [ContinuousLinearMap.comp_id, zero_add] using hd.fderiv
  have hWderiv (y : ℂ) (hy : y ∈ e.target) (i : Fin 2) :
      fderiv ℝ Y y (dirs i) = W y i := by
    rw [hDY y hy]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, hL, W]
  have hprojDY (y : ℂ) (hy : y ∈ e.target) (v : ℂ) :
      proj (fderiv ℝ Y y v) = v := by
    rw [hDY y hy]
    simp only [add_apply, ContinuousLinearMap.smulRight_apply, map_add,
      map_smul, hprojN, smul_zero, add_zero, hprojL]
  have hDX (z : ℂ) (hz : z ∈ e.source) :
      fderiv ℝ X z = (fderiv ℝ Y (F z)).comp (fderiv ℝ F z) := by
    have hnear : X =ᶠ[𝓝 z] Y ∘ F := by
      filter_upwards [e.open_source.mem_nhds hz] with q hq
      have hqgraph := hgraph (F q) (hFmap q hq)
      rw [hleft q hq] at hqgraph
      exact hqgraph
    rw [hnear.fderiv_eq]
    exact fderiv_comp z
      ((hY.contDiffAt (e.open_target.mem_nhds (hFmap z hz))).differentiableAt (by simp))
      ((hF.contDiffAt (hs.mem_nhds (hesource hz))).differentiableAt (by simp))
  have hHsmooth (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y => H y i j) e.target := by
    have hdh : ContDiffOn ℝ ∞ (fderiv ℝ h) e.target :=
      (contDiffOn_infty_iff_fderiv_of_isOpen e.open_target).mp hh |>.2
    have hWsmooth (k : Fin 2) : ContDiffOn ℝ ∞ (fun y => W y k) e.target :=
      contDiffOn_const.add ((hdh.clm_apply contDiffOn_const).smul contDiffOn_const)
    have hG (k l : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
        (fun y => chartGramMatrix g p (U (e.symm y)) k l) e.target := by
      have hc := (Operator.chartGramOnE_contDiffOn g p k l).comp hY
        (fun y hy => (hYchart y hy).1)
      exact hc.congr (fun y hy =>
        congrArg (fun x : M => chartGramMatrix g p x k l) (hYchart y hy).2.symm)
    have hcoord (k : Fin (Module.finrank ℝ E)) (i : Fin 2) :
        ContDiffOn ℝ ∞ (fun y => (chartModelBasis E).equivFun (W y i) k) e.target :=
      (chartCoordCLM E k).contDiff.comp_contDiffOn (hWsmooth i)
    have hsum := ContDiffOn.sum (fun k (_ : k ∈ Finset.univ) =>
      ContDiffOn.sum (fun l (_ : l ∈ Finset.univ) =>
        ((hG k l).mul (hcoord k i)).mul (hcoord l j)))
    simpa only [H, chartGramBilin_apply] using hsum
  have hHpos (y : ℂ) (hy : y ∈ e.target) : (H y).PosDef := by
    let Qy := chartGramBilin g p (U (e.symm y))
    let G : LinearMap.BilinForm ℝ ℂ := LinearMap.BilinForm.comp Qy.toLinearMap₁₂
      (fderiv ℝ Y y).toLinearMap (fderiv ℝ Y y).toLinearMap
    have hGsym : G.IsSymm := by
      refine ⟨fun v w => ?_⟩
      change Qy (fderiv ℝ Y y v) (fderiv ℝ Y y w) =
        Qy (fderiv ℝ Y y w) (fderiv ℝ Y y v)
      rw [graph_gram_eq_inner, graph_gram_eq_inner]
      exact g.symm _ _ _
    have hGp : G.toQuadraticMap.PosDef := by
      intro v hv
      apply graph_gram_pos g (hchart _ (hesource (e.map_target hy)))
      intro hz
      have hz' : fderiv ℝ Y y v = 0 := hz
      have hc := hprojDY y hy v
      rw [hz', map_zero] at hc
      exact hv hc.symm
    have hm : G.toMatrix Complex.basisOneI = H y := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      change Qy (fderiv ℝ Y y (Complex.basisOneI i))
        (fderiv ℝ Y y (Complex.basisOneI j)) = Qy (W y i) (W y j)
      simp only [Complex.coe_basisOneI]
      rw [hWderiv y hy i, hWderiv y hy j]
    rw [← hm]
    exact (LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
      Complex.basisOneI G hGsym).mp hGp
  have hHsym (y : ℂ) (i j : Fin 2) : H y i j = H y j i := by
    dsimp only [H]
    rw [graph_gram_eq_inner, graph_gram_eq_inner]
    exact g.symm _ _ _
  have hHmat (y : ℂ) : H y = !![H y 0 0, H y 0 1; H y 0 1, H y 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact hHsym y 1 0
    · rfl
  have hHdet (y : ℂ) (hy : y ∈ e.target) :
      0 < H y 0 0 * H y 1 1 - H y 0 1 ^ 2 := by
    have hp := (hHpos y hy).det_pos
    simpa only [Matrix.det_fin_two, ← hHsym y 0 1, pow_two] using hp
  have hAsmooth (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y => A y i j) e.target :=
    Analysis.contDiffOn_planarConductivity (hHsmooth 0 0) (hHsmooth 1 1)
      (hHsmooth 0 1) hHdet i j
  refine ⟨hh, hgraph, hYchart, hHsmooth, hHpos, hAsmooth, ?_⟩
  intro y hy
  have hApos : (A y).PosDef := Analysis.planarConductivity_posDef
    (hHpos y hy).diag_pos (hHdet y hy)
  have hAeq : A y = Real.sqrt (H y).det • (H y)⁻¹ := by
    have hEq := Analysis.planarConductivity_eq_sqrt_det_smul_inv (hHdet y hy)
    simpa only [← hHmat y] using hEq
  refine ⟨hApos, hAeq, ?_⟩
  let z := e.symm y
  have hz : z ∈ e.source := e.map_target hy
  have hzs : z ∈ s := hesource hz
  have hFz : F z = y := hright y hy
  have hXz : X z = Y y := hgraph y hy
  have hX2 : ContDiffAt ℝ 2 X z := (hX.contDiffAt (hs.mem_nhds hzs)).of_le (by norm_num)
  have hF2 : ContDiffAt ℝ 2 F z := (hF.contDiffAt (hs.mem_nhds hzs)).of_le (by norm_num)
  have hh2 : ContDiffAt ℝ 2 h y := (hh.contDiffAt (e.open_target.mem_nhds hy)).of_le (by norm_num)
  have hUz : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) 1 U z :=
    (hU.contMDiffAt (hs.mem_nhds hzs)).of_le (by norm_num)
  have hmetric (v w : ℂ) :
      chartGramBilin g p (U z) (fderiv ℝ X z v) (fderiv ℝ X z w) =
        g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) := by
    rw [graph_gram_eq_inner]
    exact congrArg₂ (fun v w => g.inner (U z) v w)
      (graph_chart_partial hUz (hchart z hzs) v)
      (graph_chart_partial hUz (hchart z hzs) w)
  have hfactorD (v : ℂ) : fderiv ℝ Y y (fderiv ℝ F z v) = fderiv ℝ X z v := by
    have hd := congrArg (fun T : ℂ →L[ℝ] E => T v) (hDX z hz)
    rw [hFz] at hd
    exact hd.symm
  have hsurj : Function.Surjective (fderiv ℝ F z) := by
    intro v
    refine ⟨fderiv ℝ e.symm y v, ?_⟩
    exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v) (hrightD y hy)
  have hinj : Function.Injective (fderiv ℝ F z) :=
    (LinearMap.injective_iff_surjective (f := (fderiv ℝ F z).toLinearMap)).mpr hsurj
  let t := chartGramBilin g p (U z) (fderiv ℝ X z 1) (fderiv ℝ X z 1)
  have ht : 0 < t := by
    apply graph_gram_pos g (hchart z hzs)
    intro hzero
    have hproj := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) (hDF z hzs)
    change fderiv ℝ F z 1 = proj (fderiv ℝ X z 1) at hproj
    rw [hzero, map_zero] at hproj
    exact one_ne_zero (hinj (hproj.trans (map_zero (fderiv ℝ F z)).symm))
  let D := LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
    (fderiv ℝ F z).toLinearMap
  let Di := LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
    (fderiv ℝ e.symm y).toLinearMap
  have hDDi : D * Di = 1 := by
    have hc := congrArg (fun T : ℂ →L[ℝ] ℂ =>
      LinearMap.toMatrix Complex.basisOneI Complex.basisOneI T.toLinearMap) (hrightD y hy)
    change LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      ((fderiv ℝ F z).toLinearMap.comp (fderiv ℝ e.symm y).toLinearMap) =
        LinearMap.toMatrix Complex.basisOneI Complex.basisOneI LinearMap.id at hc
    rw [LinearMap.toMatrix_comp Complex.basisOneI Complex.basisOneI Complex.basisOneI,
      LinearMap.toMatrix_id] at hc
    exact hc
  have hDunit : IsUnit D.det := Matrix.isUnit_det_of_right_inverse hDDi
  let G : LinearMap.BilinForm ℝ ℂ :=
    LinearMap.BilinForm.comp (chartGramBilin g p (U z)).toLinearMap₁₂
    (fderiv ℝ Y y).toLinearMap (fderiv ℝ Y y).toLinearMap
  have hGmat : G.toMatrix Complex.basisOneI = H y := by
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change chartGramBilin g p (U z) (fderiv ℝ Y y (Complex.basisOneI i))
      (fderiv ℝ Y y (Complex.basisOneI j)) =
        chartGramBilin g p (U z) (W y i) (W y j)
    simp only [Complex.coe_basisOneI]
    rw [hWderiv y hy i, hWderiv y hy j]
  have hGapply (v w : ℂ) : G (fderiv ℝ F z v) (fderiv ℝ F z w) =
      g.inner (U z) (diskMapPartial U z v) (diskMapPartial U z w) := by
    change chartGramBilin g p (U z) (fderiv ℝ Y y (fderiv ℝ F z v))
      (fderiv ℝ Y y (fderiv ℝ F z w)) = _
    rw [hfactorD, hfactorD]
    exact hmetric v w
  have hconj : D.transpose * H y * D = t • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← hGmat]
    change (LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
      (fderiv ℝ F z).toLinearMap).transpose * G.toMatrix Complex.basisOneI *
      LinearMap.toMatrix Complex.basisOneI Complex.basisOneI (fderiv ℝ F z).toLinearMap = _
    rw [← LinearMap.BilinForm.toMatrix_comp]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply]
    change G (fderiv ℝ F z (Complex.basisOneI i))
      (fderiv ℝ F z (Complex.basisOneI j)) =
        (t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j
    rw [hGapply]
    have hc := hconformal z hzs
    have htmetric : t = g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) :=
      hmetric 1 1
    fin_cases i <;> fin_cases j
    · simp [Complex.coe_basisOneI, htmetric]
    · simpa [Complex.coe_basisOneI] using hc.1
    · simpa [Complex.coe_basisOneI, g.symm] using hc.1
    · simpa [Complex.coe_basisOneI, htmetric] using hc.2.symm
  have hDDt : D * D.transpose = t • (H y)⁻¹ :=
    mul_transpose_eq_smul_inv_of_conformal D (H y) t hDunit
      (isUnit_iff_ne_zero.mpr (hHpos y hy).det_pos.ne') hconj
  have hT : Laplacian.laplacian X z +
      chartChristoffelContraction g p (fderiv ℝ X z 1) (fderiv ℝ X z 1) (X z) +
      chartChristoffelContraction g p (fderiv ℝ X z Complex.I)
        (fderiv ℝ X z Complex.I) (X z) = 0 := by
    have hp := chart_planarTension g
      ((hU.contMDiffAt (hs.mem_nhds hzs)).of_le (show (2 : ℕ∞ω) ≤ ∞ by norm_num))
      (hchart z hzs)
    dsimp only at hp
    change (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).continuousLinearMapAt ℝ (U z)
      (diskMapTension g U z) = _ at hp
    rw [htension z hzs, map_zero] at hp
    exact hp.symm
  have hEtaT := congrArg (Q N) hT
  have hPiT := congrArg ((fderiv ℝ h y).comp proj) hT
  simp only [map_add, map_zero, ContinuousLinearMap.comp_apply] at hEtaT hPiT
  have hnearHeight : h ∘ F =ᶠ[𝓝 z] (fun q => Q N (X q - X a)) := by
    filter_upwards [e.open_source.mem_nhds hz] with q hq
    have hgr := hgraph (F q) (hFmap q hq)
    rw [hleft q hq] at hgr
    have hEta : Q N (X q) = Q N (X a) + h (F q) := by
      rw [hgr]
      change Q N (X a + lift (F q - F a) + h (F q) • N) = _
      rw [map_add, map_add, ← hL, hEtaL, map_smul, hunit]
      simp only [smul_eq_mul, mul_one, add_zero]
    change h (F q) = Q N (X q - X a)
    rw [map_sub, hEta]
    ring
  have hheightLap : Laplacian.laplacian (h ∘ F) z = Q N (Laplacian.laplacian X z) := by
    rw [(InnerProductSpace.laplacian_congr_nhds hnearHeight).eq_of_nhds]
    have hc := (hX2.sub (contDiffAt_const (c := X a))).laplacian_CLM_comp_left (l := Q N)
    change Laplacian.laplacian (fun q => Q N (X q - X a)) z =
      Q N (Laplacian.laplacian (fun q => X q - X a) z) at hc
    have hsub := hX2.laplacian_sub (contDiffAt_const (c := X a))
    rw [InnerProductSpace.laplacian_const, Pi.zero_apply, sub_zero] at hsub
    exact hc.trans (congrArg (Q N) hsub)
  have hprojectionLap : Laplacian.laplacian F z = proj (Laplacian.laplacian X z) :=
    hX2.laplacian_CLM_comp_left
  let Hess : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ h) y
  let T : LinearMap.BilinForm ℝ ℂ := LinearMap.BilinForm.comp Hess.toLinearMap₁₂
    (fderiv ℝ F z).toLinearMap (fderiv ℝ F z).toLinearMap
  have htrace : (∑ i : Fin (Module.finrank ℝ ℂ),
      Hess (fderiv ℝ F z (stdOrthonormalBasis ℝ ℂ i))
        (fderiv ℝ F z (stdOrthonormalBasis ℝ ℂ i))) =
      Hess (fderiv ℝ F z 1) (fderiv ℝ F z 1) +
        Hess (fderiv ℝ F z Complex.I) (fderiv ℝ F z Complex.I) := by
    change (∑ i, T (stdOrthonormalBasis ℝ ℂ i) (stdOrthonormalBasis ℝ ℂ i)) =
      T 1 1 + T Complex.I Complex.I
    calc
      _ = TensorProduct.lift T (canonicalCovariantTensor ℂ) := by
        rw [canonicalCovariantTensor_eq_sum ℂ (stdOrthonormalBasis ℝ ℂ)]
        simp
      _ = _ := by
        rw [canonicalCovariantTensor_eq_sum ℂ Complex.orthonormalBasisOneI]
        simp
  have hchain := hF2.laplacian_comp (show ContDiffAt ℝ 2 h (F z) from hFz.symm ▸ hh2)
  rw [hFz, hheightLap, hprojectionLap] at hchain
  change Q N (Laplacian.laplacian X z) =
    fderiv ℝ h y (proj (Laplacian.laplacian X z)) +
      ∑ i : Fin (Module.finrank ℝ ℂ),
        Hess (fderiv ℝ F z (stdOrthonormalBasis ℝ ℂ i))
          (fderiv ℝ F z (stdOrthonormalBasis ℝ ℂ i)) at hchain
  rw [htrace] at hchain
  let J := graph_christoffel_bilin g p (Y y)
  let K : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
    (LinearMap.mk₂ ℝ (fun v w => Hess v w + theta y (J (fderiv ℝ Y y v) (fderiv ℝ Y y w)))
      (by intro v₁ v₂ w; simp only [map_add, add_apply]; ring)
      (by intro c v w; simp only [map_smul, smul_apply, smul_eq_mul]; ring)
      (by intro v w₁ w₂; simp only [map_add]; ring)
      (by intro c v w; simp only [map_smul, smul_eq_mul]; ring)).toContinuousBilinearMap
  have hKapply (v w : ℂ) : K v w = Hess v w +
      theta y (chartChristoffelContraction g p (fderiv ℝ Y y v) (fderiv ℝ Y y w) (Y y)) := rfl
  have hKzero : K (fderiv ℝ F z 1) (fderiv ℝ F z 1) +
      K (fderiv ℝ F z Complex.I) (fderiv ℝ F z Complex.I) = 0 := by
    simp only [hKapply, hfactorD, ← hXz]
    simp only [theta, sub_apply, ContinuousLinearMap.comp_apply]
    linarith only [hEtaT, hPiT, hchain]
  have hcontract := ContinuousLinearMap.sum_mul_apply_diagonal_eq_sum_coordinates K
    Complex.basisOneI Finset.univ (fun _ : Fin 2 => (1 : ℝ))
    (fun i => fderiv ℝ F z (dirs i)) (fun i j => (D * D.transpose) i j)
    (by
      intro i j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, D, LinearMap.toMatrix_apply,
        Complex.coe_basisOneI, dirs, one_mul, ContinuousLinearMap.coe_coe])
  have hzero : t * (∑ i : Fin 2, ∑ j : Fin 2,
      (H y)⁻¹ i j * K (dirs i) (dirs j)) = 0 := by
    rw [hDDt] at hcontract
    have hhcontract : (∑ i : Fin 2,
        K (fderiv ℝ F z (dirs i)) (fderiv ℝ F z (dirs i))) =
      t * (∑ i : Fin 2, ∑ j : Fin 2, (H y)⁻¹ i j * K (dirs i) (dirs j)) := by
      simpa only [Complex.coe_basisOneI, dirs, one_mul, Matrix.smul_apply,
        smul_eq_mul, Finset.mul_sum, mul_assoc] using hcontract
    rw [← hhcontract]
    simpa only [Fin.sum_univ_two, dirs, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hKzero
  have hzero' : (∑ i : Fin 2, ∑ j : Fin 2, (H y)⁻¹ i j * K (dirs i) (dirs j)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left ht.ne'
  have hKbasis (i j : Fin 2) : K (dirs i) (dirs j) =
      fderiv ℝ (fderiv ℝ h) y (dirs i) (dirs j) +
        theta y (chartChristoffelContraction g p (W y i) (W y j) (Y y)) := by
    rw [hKapply, hWderiv y hy i, hWderiv y hy j]
  simp_rw [← hKbasis]
  rw [hAeq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hscaled : (∑ i : Fin 2, ∑ j : Fin 2,
      (Real.sqrt (H y).det * (H y)⁻¹ i j) * K (dirs i) (dirs j)) =
      Real.sqrt (H y).det * (∑ i : Fin 2, ∑ j : Fin 2,
        (H y)⁻¹ i j * K (dirs i) (dirs j)) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hscaled, hzero', mul_zero]

end DifferentialGeometry.Geometry
