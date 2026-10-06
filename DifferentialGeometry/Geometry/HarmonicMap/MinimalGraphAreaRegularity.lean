import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Geometry.Operator.Hessian.Trace.ChartGramRegularity
import DifferentialGeometry.Geometry.HarmonicMap.MinimalGraphAreaEquation

set_option autoImplicit false
noncomputable section

open Set Metric Filter Manifold Bundle DifferentialGeometry
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open scoped Topology ContDiff Manifold Matrix

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Smoothness of the actual original metric evaluated on varying chart vectors. -/
private theorem chartMetricBilin_contDiffOn
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M)
    {n : ℕ∞ω} (hn : n ≤ ∞) {s : Set Z} {X V W : Z → E}
    (hX : ContDiffOn ℝ n X s) (hV : ContDiffOn ℝ n V s)
    (hW : ContDiffOn ℝ n W s)
    (hchart : MapsTo X s (extChartAt 𝓘(ℝ, E) a).target) :
    ContDiffOn ℝ n (fun z => chartMetricBilin g a (X z) (V z) (W z)) s := by
  classical
  have heq (z : Z) : chartMetricBilin g a (X z) (V z) (W z) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Operator.chartGramOnE g a i j (X z) * chartCoord (E := E) i (V z) *
          chartCoord (E := E) j (W z) :=
    inner_eq_chartGramOnE_bilinear_on_baseSet g a (V z) (W z)
  simp_rw [heq]
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  have hG := ((Operator.chartGramOnE_contDiffOn g a i j).of_le hn).comp hX hchart
  have hVi := ((chartModelBasis E).coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hV
  have hWj := ((chartModelBasis E).coord j).toContinuousLinearMap.contDiff.comp_contDiffOn hW
  exact (hG.mul hVi).mul hWj

/-- Smoothness of the original metric's Christoffel contraction on its actual chart. -/
private theorem chartChristoffelContraction_contDiffOn
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M)
    {n : ℕ∞ω} (hn : n ≤ ∞) {s : Set Z} {X V W : Z → E}
    (hX : ContDiffOn ℝ n X s) (hV : ContDiffOn ℝ n V s)
    (hW : ContDiffOn ℝ n W s)
    (hchart : MapsTo X s (extChartAt 𝓘(ℝ, E) a).target) :
    ContDiffOn ℝ n (fun z => chartChristoffelContraction g a (V z) (W z) (X z)) s := by
  classical
  unfold chartChristoffelContraction
  refine ContDiffOn.sum fun k _ => ContDiffOn.smul ?_ contDiffOn_const
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  have hΓ := ((Operator.chartChristoffel_contDiffOn_interior g a i j k).of_le hn).comp hX
    (fun z hz => by rw [(isOpen_extChartAt_target a).interior_eq]; exact hchart hz)
  have hVi := ((chartModelBasis E).coord i).toContinuousLinearMap.contDiff.comp_contDiffOn hV
  have hWj := ((chartModelBasis E).coord j).toContinuousLinearMap.contDiff.comp_contDiffOn hW
  exact (hΓ.mul hVi).mul hWj

omit [FiniteDimensional ℝ E] in
/-- Projection supplies graph rank for every first jet, including the center.
The determinant is positive for the original metric, without a current-normal
assumption on the fixed vector `N`. -/
theorem chartGraphArea_determinant_pos
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M)
    (x : E) (hx : x ∈ (extChartAt 𝓘(ℝ, E) a).target)
    (proj : E →L[ℝ] ℂ) (L : ℂ →L[ℝ] E) (N : E)
    (hL : ∀ w : ℂ, proj (L w) = w) (hN : proj N = 0)
    (slope : ℂ →L[ℝ] ℝ) :
    let V := L 1 + slope 1 • N
    let W := L Complex.I + slope Complex.I • N
    let B := chartMetricBilin g a x
    0 < B V V * B W W - (B V W) ^ 2 := by
  let B := chartMetricBilin g a x
  let D : ℂ →L[ℝ] E := L + slope.smulRight N
  have hprojD (w : ℂ) : proj (D w) = w := by
    simp only [D, add_apply, ContinuousLinearMap.smulRight_apply,
      map_add, map_smul, hN, smul_zero, add_zero, hL]
  have hBpos (v : E) (hv : v ≠ 0) : 0 < B v v := by
    let b := (extChartAt 𝓘(ℝ, E) a).symm x
    let T := trivializationAt E (TangentSpace 𝓘(ℝ, E)) a
    have hb : b ∈ T.baseSet := by
      simpa only [b, T, TangentBundle.trivializationAt_baseSet, extChartAt_source]
        using (extChartAt 𝓘(ℝ, E) a).map_target hx
    have hne : T.symmL ℝ b v ≠ 0 := by
      intro h
      have hh := congrArg (T.continuousLinearMapAt ℝ b) h
      rw [T.continuousLinearMapAt_symmL hb, map_zero] at hh
      exact hv hh
    exact g.pos b _ hne
  let G : LinearMap.BilinForm ℝ ℂ :=
    LinearMap.BilinForm.comp B.toLinearMap₁₂ D.toLinearMap D.toLinearMap
  have hsym : G.IsSymm := by
    refine ⟨fun v w => ?_⟩
    exact g.symm _ _ _
  have hGp : G.toQuadraticMap.PosDef := by
    intro v hv
    apply hBpos (D v)
    intro h
    have hh := hprojD v
    rw [h, map_zero] at hh
    exact hv hh.symm
  have hp := ((LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix
    Complex.basisOneI G hsym).mp hGp).det_pos
  have he (i j : Fin 2) : G.toMatrix Complex.basisOneI i j =
      B (D (Complex.basisOneI i)) (D (Complex.basisOneI j)) := by
    rw [LinearMap.BilinForm.toMatrix_apply]
    rfl
  rw [Matrix.det_fin_two] at hp
  simp only [he, Complex.coe_basisOneI, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hp
  have hsymB : B (D Complex.I) (D 1) = B (D 1) (D Complex.I) := g.symm _ _ _
  rw [hsymB] at hp
  simpa only [B, D, add_apply, ContinuousLinearMap.smulRight_apply,
    pow_two] using hp

/-- The original graph-area flux and height source depend smoothly on the first
jet whenever the retained projection splits it and the graph stays in its chart.
No PDE or variable-normal assumption is used for this regularity assertion. -/
theorem chartGraphArea_firstJet_contDiffOn
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M)
    (x₀ : E) (c : ℂ) (proj : E →L[ℝ] ℂ) (L : ℂ →L[ℝ] E) (N : E)
    (hL : ∀ w : ℂ, proj (L w) = w) (hN : proj N = 0)
    {n : ℕ∞ω} (hn : n ≤ ∞) {s : Set ℂ}
    {h : ℂ → ℝ} {slope : ℂ → ℂ →L[ℝ] ℝ}
    (hh : ContDiffOn ℝ n h s) (hslope : ContDiffOn ℝ n slope s)
    (hchart : ∀ y ∈ s,
      x₀ + L (y - c) + h y • N ∈ (extChartAt 𝓘(ℝ, E) a).target) :
    ContDiffOn ℝ n
      (fun y => chartGraphAreaFlux g a x₀ c L N y (h y)
        (slope y 1, slope y Complex.I)) s ∧
    ContDiffOn ℝ n
      (fun y => chartGraphAreaSource g a x₀ c L N y (h y)
        (slope y 1, slope y Complex.I)) s := by
  let Y : ℂ → E := fun y => x₀ + L (y - c) + h y • N
  let V : ℂ → E := fun y => L 1 + slope y 1 • N
  let W : ℂ → E := fun y => L Complex.I + slope y Complex.I • N
  let B : ℂ → E →L[ℝ] E →L[ℝ] ℝ := fun y => chartMetricBilin g a (Y y)
  let J : ℂ → ℝ := fun y => Real.sqrt
    (B y (V y) (V y) * B y (W y) (W y) - (B y (V y) (W y)) ^ 2)
  have hY : ContDiffOn ℝ n Y s :=
    (contDiffOn_const.add
      (L.contDiff.comp_contDiffOn (contDiffOn_id.sub contDiffOn_const))).add
        (hh.smul contDiffOn_const)
  have hV : ContDiffOn ℝ n V s :=
    contDiffOn_const.add ((hslope.clm_apply contDiffOn_const).smul contDiffOn_const)
  have hW : ContDiffOn ℝ n W s :=
    contDiffOn_const.add ((hslope.clm_apply contDiffOn_const).smul contDiffOn_const)
  have hpair {P Q : ℂ → E} (hP : ContDiffOn ℝ n P s)
      (hQ : ContDiffOn ℝ n Q s) :
      ContDiffOn ℝ n (fun y => B y (P y) (Q y)) s :=
    chartMetricBilin_contDiffOn g a hn hY hP hQ hchart
  have hVV := hpair hV hV
  have hWW := hpair hW hW
  have hVW := hpair hV hW
  have hNV := hpair (P := fun _ => N) contDiffOn_const hV
  have hNW := hpair (P := fun _ => N) contDiffOn_const hW
  have hdet (y : ℂ) (hy : y ∈ s) :
      0 < B y (V y) (V y) * B y (W y) (W y) - (B y (V y) (W y)) ^ 2 :=
    chartGraphArea_determinant_pos g a (Y y) (hchart y hy)
      proj L N hL hN (slope y)
  have hJ : ContDiffOn ℝ n J s :=
    ((hVV.mul hWW).sub (hVW.pow 2)).sqrt (fun y hy => (hdet y hy).ne')
  have hJne (y : ℂ) (hy : y ∈ s) : J y ≠ 0 :=
    (Real.sqrt_pos.mpr (hdet y hy)).ne'
  have hflux := (((hWW.mul hNV).sub (hVW.mul hNW)).div hJ hJne).prodMk
    (((hVV.mul hNW).sub (hVW.mul hNV)).div hJ hJne)
  have hCV : ContDiffOn ℝ n
      (fun y => chartChristoffelContraction g a N (V y) (Y y)) s :=
    chartChristoffelContraction_contDiffOn g a hn hY contDiffOn_const hV hchart
  have hCW : ContDiffOn ℝ n
      (fun y => chartChristoffelContraction g a N (W y) (Y y)) s :=
    chartChristoffelContraction_contDiffOn g a hn hY contDiffOn_const hW hchart
  have hsource :=
    (((hWW.mul (hpair hCV hV)).add (hVV.mul (hpair hCW hW))).sub
      (hVW.mul ((hpair hCV hW).add (hpair hCW hV)))).div hJ hJne
  constructor
  · simpa only [chartGraphAreaFlux, chartGraphAreaLagrangian, Y, V, W, B, J, Pi.div_apply, Pi.div_def] using hflux
  · simpa only [chartGraphAreaSource, chartGraphAreaLagrangian, Y, V, W, B, J, Pi.div_apply, Pi.div_def] using hsource

/-- The original graph area integrand is smooth on the complete Euclidean first-jet
chart domain, including slope directions away from the actual graph. -/
theorem chartGraphAreaLagrangian_euclideanJet_regular
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (a : M)
    (x₀ : E) (c : ℂ) (L : ℂ →L[ℝ] E) (proj : E →L[ℝ] ℂ) (N : E)
    (hL : ∀ w : ℂ, proj (L w) = w) (hN : proj N = 0) :
    let J := EuclideanSpace ℝ (Fin 2) × (ℝ × EuclideanSpace ℝ (Fin 2))
    let Y : J → E := fun j => x₀ + L (Complex.orthonormalBasisOneI.repr.symm j.1 - c) + j.2.1 • N
    let U := Y ⁻¹' (extChartAt 𝓘(ℝ, E) a).target
    IsOpen U ∧ ContDiffOn ℝ ∞ (fun j : J =>
      chartGraphAreaLagrangian g a x₀ c L N
        (Complex.orthonormalBasisOneI.repr.symm j.1) j.2.1 (j.2.2 0, j.2.2 1)) U := by
  intro J Y U
  let V : J → E := fun j => L 1 + (j.2.2 0) • N
  let W : J → E := fun j => L Complex.I + (j.2.2 1) • N
  have hY : ContDiff ℝ ∞ Y := by dsimp only [Y, J]; fun_prop
  have hV : ContDiff ℝ ∞ V := by dsimp only [V, J]; fun_prop
  have hW : ContDiff ℝ ∞ W := by dsimp only [W, J]; fun_prop
  have hU : IsOpen U := (isOpen_extChartAt_target a).preimage hY.continuous
  have hpair {P Q : J → E} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) :
      ContDiffOn ℝ ∞ (fun j => chartMetricBilin g a (Y j) (P j) (Q j)) U :=
    chartMetricBilin_contDiffOn g a le_rfl hY.contDiffOn hP.contDiffOn hQ.contDiffOn
      (fun _ hj => hj)
  refine ⟨hU, ?_⟩
  have hd : ContDiffOn ℝ ∞ (fun j =>
      chartMetricBilin g a (Y j) (V j) (V j) * chartMetricBilin g a (Y j) (W j) (W j) -
        (chartMetricBilin g a (Y j) (V j) (W j)) ^ 2) U :=
    ((hpair hV hV).mul (hpair hW hW)).sub ((hpair hV hW).pow 2)
  apply hd.sqrt
  intro j hj
  have hp := chartGraphArea_determinant_pos g a (Y j) hj proj L N hL hN
    ((j.2.2 0) • Complex.reCLM + (j.2.2 1) • Complex.imCLM)
  have he : 0 < chartMetricBilin g a (Y j) (V j) (V j) *
      chartMetricBilin g a (Y j) (W j) (W j) -
        (chartMetricBilin g a (Y j) (V j) (W j)) ^ 2 := by
    simpa [V, W] using hp
  exact he.ne'

end DifferentialGeometry.Geometry
