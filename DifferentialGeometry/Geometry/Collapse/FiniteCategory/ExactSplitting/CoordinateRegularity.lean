import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SquaredDistanceCoordinate
import DifferentialGeometry.Geometry.Comparison.FiniteMetric.SquaredDistanceGeodesic
import DifferentialGeometry.Geometry.Metric.L2ProductSegment
import DifferentialGeometry.Geometry.Geodesic.Flow.FiniteMetric
import DifferentialGeometry.Geometry.Geodesic.Equation.MetricSprayFiniteRegularity
import DifferentialGeometry.Geometry.Metric.Pullback.FiniteCoefficients
import DifferentialGeometry.Analysis.Calculus.ContDiff.ConnectionBootstrap
import DifferentialGeometry.Analysis.Calculus.ContDiff.AffineGeodesicHessian

/-!
# LFR11, tier T1: the Euclidean coordinate of an exact splitting is `C^{K+1}`

Blueprint LFR11 (A:25566–25672). Let `g` be a complete finite metric of class `C^K`, `K = r + 1`,
`2 ≤ r` (tree convention), whose length distance is the ambient distance, and let
`e : M ≃ᵢ F ×₂ Y` be a distance isometry onto an `ℓ²` product with a finite-dimensional real
inner-product factor `F`. Then `t = (e ·).fst` is `C^{K+1}` (`contMDiff_splitting_fst`).

Steps (sheet `build-logs/resume/sheet-F7-LFR11.md`, section 3):
* S1 `contMDiff_inner_fst`: every coordinate `⟪t, v⟫` is `C²` (squared distances);
* S5 `exists_affine_inner_fst_geodesicFlow`: `⟪t, v⟫` is affine along every unit geodesic, near
  every time (short geodesics are segments, CM5; kernel K4 for `ℓ²` segments);
* S6 `fderiv_fderiv_inner_fst_chart_apply_self`: in the chart at `x₀`, with
  `Γ(y) = raisedKoszulOp (G y) (DG y)` (`G = chartInner x₀`), `D²f(y)(w,w) = Df(y)(Γ(y)(w,w))`
  (kernel K3 along the chart geodesic, then quadratic scaling);
* S7 `contDiffOn_inner_fst_chart`: polarization (K2) and the bootstrap (K1, `B = 0`) with
  `Γ ∈ C^{K-1}` give `f ∈ C^{K+1}` on the chart target.
No intrinsic connection, parallel vector field or flow is used: the parallel equation is the
chart identity for the differential of `t`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]
  {r : ℕ∞} {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MetricSpace Y]

local instance splittingDualEquiv : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional

/-- **LFR11 S5.** A coordinate of an exact splitting is affine along every unit-speed geodesic,
near every time. -/
theorem exists_affine_inner_fst_geodesicFlow
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) (P : TangentBundle I M)
    (hP : g.inner P.proj P.snd P.snd = 1) (t₀ : ℝ) :
    ∃ a b : ℝ, ∀ᶠ s in 𝓝 t₀, inner ℝ (e (g.geodesicFlow P s).proj).fst v = a + b * s := by
  obtain ⟨ε, hε, hiso⟩ := FiniteComparison.isometric_proj_geodesicFlow_near g hr hnorm P hP t₀
  set c : ℝ → WithLp 2 (F × Y) := fun s => e (g.geodesicFlow P s).proj with hc
  have hseg : ∀ s ∈ Icc (t₀ - ε) (t₀ + ε), ∀ s' ∈ Icc (t₀ - ε) (t₀ + ε),
      dist (c s) (c s') = 1 * |s - s'| := by
    intro s hs s' hs'
    simp only [hc, e.dist_eq, one_mul]
    exact hiso s hs s' hs'
  have hab : t₀ - ε < t₀ + ε := by linarith
  set B : ℝ := inner ℝ ((c (t₀ + ε)).fst - (c (t₀ - ε)).fst) v / ((t₀ + ε) - (t₀ - ε)) with hB
  refine ⟨inner ℝ (c (t₀ - ε)).fst v - (t₀ - ε) * B, B, ?_⟩
  filter_upwards [Icc_mem_nhds (by linarith : t₀ - ε < t₀) (by linarith : t₀ < t₀ + ε)] with s hs
  have h := GC.MetricGeometry.fst_eq_affine_of_dist_eq_mul hab hseg hs
  change inner ℝ (c s).fst v = _
  rw [h, inner_add_left, real_inner_smul_left, hB]
  have hne : (t₀ + ε) - (t₀ - ε) ≠ 0 := by linarith
  field_simp
  ring

/-- **LFR11 S6, unit vectors.** -/
theorem fderiv_fderiv_inner_fst_chart_apply_self_of_unit
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    {w : E} (hw : g.inner ((extChartAt I x₀).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w) = 1) :
    fderiv ℝ (fderiv ℝ (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v)) y w w =
      fderiv ℝ (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v) y
        (MetricKoszul.raisedKoszulOp (g.chartInner x₀ y) (fderiv ℝ (g.chartInner x₀) y) w w) := by
  have hr1 : 1 ≤ r := one_le_two.trans hr
  set κ := extChartAt I x₀ with hκ
  set f : E → ℝ := fun y => inner ℝ (e (κ.symm y)).fst v with hf
  set G := g.chartInner x₀ with hG
  set x : M := κ.symm y with hx
  have hxs : x ∈ κ.source := κ.map_target hy
  have hxc : x ∈ (chartAt H x₀).source := by rwa [hκ, extChartAt_source] at hxs
  have hκx : κ x = y := κ.right_inv hy
  set w' : TangentSpace I x := mfderiv 𝓘(ℝ, E) I κ.symm y w with hw'
  set P : TangentBundle I M := ⟨x, w'⟩ with hP
  set q : TangentBundle I M := ⟨x₀, 0⟩ with hq
  set Z : ℝ → E × E := fun s => extChartAt I.tangent q (g.geodesicFlow P s) with hZ
  have hD : ∀ s : ℝ, (P, s) ∈ g.geodesicFlowDomain := by
    rw [g.geodesicFlowDomain_eq_univ hr hnorm]
    exact fun _ => mem_univ _
  -- `Z 0 = (y, w)`
  have hcomp : (mfderiv I 𝓘(ℝ, E) κ x).comp (mfderiv 𝓘(ℝ, E) I κ.symm y) =
      ContinuousLinearMap.id ℝ E := by
    have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀) hy
    rw [I.range_eq_univ, mfderivWithin_univ] at h
    exact h
  have hZ0 : Z 0 = (y, w) := by
    simp only [hZ, g.geodesicFlow_zero hr1]
    rw [Bundle.ContMDiffRiemannianMetric.extChartAt_tangent_mk x₀ hxc w', hκx]
    congr 1
    exact congrArg (fun L : E →L[ℝ] E => L w) hcomp
  -- the chart curve is in the chart near `0` and solves the chart geodesic equation
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (g.geodesicFlow P s).proj ∈ (chartAt H x₀).source := by
    have hcont := (g.hasMFDerivAt_geodesicFlow_proj hr1 (hD 0)).continuousAt
    have h0 : (g.geodesicFlow P 0).proj = x := by rw [g.geodesicFlow_zero hr1]
    exact hcont.preimage_mem_nhds (by rw [h0]; exact (chartAt H x₀).open_source.mem_nhds hxc)
  have hderZ : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt Z (MetricKoszul.metricSpray G (Z s)) s := by
    filter_upwards [hev] with s hs
    exact g.hasDerivAt_geodesicFlow_chart hr1 (hD s) q hs
  have hc : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun s => (Z s).1) (Z s).2 s := by
    filter_upwards [hderZ] with s hs
    exact (hasFDerivAt_fst (p := Z s)).comp_hasDerivAt s hs
  have hv : HasDerivAt (fun s => (Z s).2)
      (-MetricKoszul.raisedKoszulOp (G y) (fderiv ℝ G y) (Z 0).2 (Z 0).2) 0 := by
    have h := (hasFDerivAt_snd (p := Z 0)).comp_hasDerivAt (0 : ℝ) hderZ.self_of_nhds
    have h1 : (Z 0).1 = y := by rw [hZ0]
    simp only [MetricKoszul.metricSpray, h1] at h
    exact h
  -- the coordinate is `C²` at `y`
  have hfC2 : ContDiffAt ℝ 2 f (Z 0).1 := by
    rw [hZ0]
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f y :=
      (contMDiff_inner_fst g hr hnorm e v x).comp y
        ((contMDiffOn_extChartAt_symm (n := 2) x₀).contMDiffAt
          ((isOpen_extChartAt_target x₀).mem_nhds hy))
    exact h1.contDiffAt
  -- affine along the curve
  obtain ⟨a, b, hab⟩ := exists_affine_inner_fst_geodesicFlow g hr hnorm e v P hw 0
  have haff : ∀ᶠ s in 𝓝 (0 : ℝ), f (Z s).1 = a + b * s := by
    filter_upwards [hab, hev] with s hs hsc
    have hsrc : (g.geodesicFlow P s).proj ∈ κ.source := by rwa [hκ, extChartAt_source]
    have h1 : (Z s).1 = κ (g.geodesicFlow P s).proj :=
      TangentBundle.extChartAt_tangent_apply_fst q
    simp only [hf, h1, κ.left_inv hsrc]
    exact hs
  have hK3 := DifferentialGeometry.Analysis.fderiv_fderiv_apply_self_eq_of_comp_affine
    (Γ := MetricKoszul.raisedKoszulOp (G y) (fderiv ℝ G y)) hfC2 hc hv haff
  rw [hZ0] at hK3
  exact hK3

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] in
/-- The chart differential of `κ.symm` is injective on the chart target. -/
theorem mfderiv_extChartAt_symm_injective (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    Function.Injective (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y) := by
  intro a b hab
  have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) (x := x₀) hy
  rw [I.range_eq_univ, mfderivWithin_univ] at h
  have ha : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) ((extChartAt I x₀).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y a) = a := DFunLike.congr_fun h a
  have hb : mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) ((extChartAt I x₀).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y b) = b := DFunLike.congr_fun h b
  rw [← ha, ← hb, hab]

/-- **LFR11 S6.** In the chart at `x₀`, `D²f(y)(w, w) = Df(y)(Γ(y)(w, w))` for every `w`. -/
theorem fderiv_fderiv_inner_fst_chart_apply_self
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (w : E) :
    fderiv ℝ (fderiv ℝ (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v)) y w w =
      fderiv ℝ (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v) y
        (MetricKoszul.raisedKoszulOp (g.chartInner x₀ y) (fderiv ℝ (g.chartInner x₀) y) w w) := by
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hinj := mfderiv_extChartAt_symm_injective (I := I) x₀ hy
  have hAw : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w ≠ 0 := by
    intro h
    apply hw0
    apply hinj
    rw [h]
    exact (map_zero (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y)).symm
  set lam : ℝ := g.inner ((extChartAt I x₀).symm y)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w)
    (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w) with hlam
  have hlam0 : 0 < lam := g.pos _ _ hAw
  set μ : ℝ := (Real.sqrt lam)⁻¹ with hμ
  have hμ0 : μ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hlam0).ne'
  have hsm : mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y (μ • w) =
      μ • mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y w :=
    map_smul (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y) μ w
  have hunit : g.inner ((extChartAt I x₀).symm y)
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y (μ • w))
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x₀).symm y (μ • w)) = 1 := by
    rw [hsm, Bundle.ContMDiffRiemannianMetric.inner_smul_self_smul, ← hlam, hμ, inv_pow,
      Real.sq_sqrt hlam0.le, inv_mul_cancel₀ hlam0.ne']
  have h := fderiv_fderiv_inner_fst_chart_apply_self_of_unit g hr hnorm e v x₀ hy hunit
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  have hμ2 : μ * μ ≠ 0 := mul_ne_zero hμ0 hμ0
  apply mul_left_cancel₀ hμ2
  linarith

/-- **LFR11 S7, chart form.** In every chart, the coordinate `⟪t, v⟫` is `C^{K+1}` on the chart
target (`K = r + 1`). -/
theorem contDiffOn_inner_fst_chart
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) (x₀ : M) :
    ContDiffOn ℝ ((r : ℕ∞ω) + 2) (fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v)
      (extChartAt I x₀).target := by
  set κ := extChartAt I x₀ with hκ
  set f : E → ℝ := fun y => inner ℝ (e (κ.symm y)).fst v with hf
  set G := g.chartInner x₀ with hG
  have hU : IsOpen κ.target := isOpen_extChartAt_target x₀
  have hfC2 : ContDiffOn ℝ 2 f κ.target := by
    intro y hy
    have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 f y :=
      (contMDiff_inner_fst g hr hnorm e v (κ.symm y)).comp y
        ((contMDiffOn_extChartAt_symm (n := 2) x₀).contMDiffAt (hU.mem_nhds hy))
    exact h1.contDiffAt.contDiffWithinAt
  have hGC : ContDiffOn ℝ ((r : ℕ∞ω) + 1) G κ.target := by
    have hrs : (r : ℕ∞ω) + 1 + 1 ≤ ∞ := by exact_mod_cast le_top
    exact g.contDiffOn_pullback_inner (r := (r : ℕ∞ω) + 1) (s := ∞) le_rfl hrs hU
      (contMDiffOn_extChartAt_symm x₀)
  have hΓ : ContDiffOn ℝ (r : ℕ∞ω)
      (fun y => MetricKoszul.raisedKoszulOp (G y) (fderiv ℝ G y)) κ.target :=
    MetricKoszul.raisedOp_contDiffOn_succ hU hGC
      (fun y hy => g.isCoercive_chartInner x₀ hy)
  have hA := DifferentialGeometry.Analysis.contDiffOn_symmBilin hΓ
  have hB : ContDiffOn ℝ (r : ℕ∞ω) (fun _ : ℝ => (0 : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)) univ :=
    contDiffOn_const
  refine DifferentialGeometry.Analysis.contDiffOn_of_fderiv_fderiv_eq_enat hU hfC2
    (mapsTo_univ _ _) hA hB ?_
  intro y hy w₁ w₂
  have hfy : ContDiffAt ℝ 2 f y := (hfC2 y hy).contDiffAt (hU.mem_nhds hy)
  have h := DifferentialGeometry.Analysis.fderiv_fderiv_eq_of_apply_self hfy
    (MetricKoszul.raisedKoszulOp (G y) (fderiv ℝ G y))
    (fun w => fderiv_fderiv_inner_fst_chart_apply_self g hr hnorm e v x₀ hy w) w₁ w₂
  rw [h]
  simp


/-- **LFR11 S7.** Every coordinate `⟪t, v⟫` of an exact splitting is `C^{K+1}` (`K = r + 1`). -/
theorem contMDiff_inner_splitting_fst
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (v : F) :
    ContMDiff I 𝓘(ℝ, ℝ) ((r : ℕ∞ω) + 2) (fun x => inner ℝ (e x).fst v) := by
  intro x₀
  have hU := contDiffOn_inner_fst_chart g hr hnorm e v x₀
  have h1 : ContMDiffAt I 𝓘(ℝ, ℝ) ((r : ℕ∞ω) + 2)
      ((fun y => inner ℝ (e ((extChartAt I x₀).symm y)).fst v) ∘ extChartAt I x₀) x₀ :=
    ((hU.contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds
      (mem_extChartAt_target x₀))).contMDiffAt).comp x₀ (contMDiffAt_extChartAt)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with x hx
  simp only [Function.comp_apply, (extChartAt I x₀).left_inv hx]

/-- **LFR11, tier T1 headline (T1.a).** For a complete finite metric of class `C^K` (`K = r + 1 ≥ 3`)
and a distance isometry `e : M ≃ᵢ F ×₂ Y` onto an `ℓ²` product with a finite-dimensional real
inner-product factor, the Euclidean coordinate `t = (e ·).fst` is `C^{K+1}`. -/
theorem contMDiff_splitting_fst [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) :
    ContMDiff I 𝓘(ℝ, F) ((r : ℕ∞ω) + 2) (fun x => (e x).fst) := by
  set b := stdOrthonormalBasis ℝ F with hb
  have hsum : (fun x => (e x).fst) = fun x => ∑ i, inner ℝ (e x).fst (b i) • b i := by
    funext x
    conv_lhs => rw [← b.sum_repr' (e x).fst]
    simp only [real_inner_comm]
  rw [hsum]
  exact contMDiff_finsetSum fun i _ =>
    (contMDiff_inner_splitting_fst g hr hnorm e (b i)).smul contMDiff_const

end DifferentialGeometry.Geometry.ExactSplitting
