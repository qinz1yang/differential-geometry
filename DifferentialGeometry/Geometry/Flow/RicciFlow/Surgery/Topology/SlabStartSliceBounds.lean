import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.DerivativeBoundExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.ChartCurvatureRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Curvature.TowerBridge

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private theorem derivWithin_Ici_eq_fderivWithin {F : ℝ × ThreeSpace → ℝ} {T : Set ℝ}
    {W : Set ThreeSpace} (hF : ContDiffOn ℝ ∞ F (T ×ˢ W)) {t : ℝ} {e : ThreeSpace}
    (ht : t ∈ T) (he : e ∈ W) (hT : T ∈ 𝓝[≥] t) :
    derivWithin (fun v => F (v, e)) (Ici t) t = fderivWithin ℝ F (T ×ˢ W) (t, e) (1, 0) := by
  have hd : HasFDerivWithinAt F (fderivWithin ℝ F (T ×ˢ W) (t, e)) (T ×ˢ W) (t, e) :=
    ((hF.differentiableOn (by simp)) _ ⟨ht, he⟩).hasFDerivWithinAt
  have hc : HasDerivWithinAt (fun v : ℝ => (v, e)) ((1 : ℝ), (0 : ThreeSpace)) T t :=
    (hasDerivWithinAt_id t T).prodMk (hasDerivWithinAt_const t T e)
  have hcomp := hd.comp_hasDerivWithinAt t hc
    (show MapsTo (fun v : ℝ => (v, e)) T (T ×ˢ W) from fun v hv => ⟨hv, he⟩)
  exact (hcomp.mono_of_mem_nhdsWithin hT).derivWithin (uniqueDiffWithinAt_Ici t)

theorem chartGramFamilySmoothWithinOn_Ico (p : P.Carrier) :
    chartGramFamilySmoothWithinOn (I := ThreeModel) G.flow.base.metric p (Ico a s) :=
  G.flow.chartGramFamilySmoothWithinOn_of_jointContMDiffOn G.smoothUpTo.jointContMDiffOn p

theorem continuousWithinAt_derivWithin_Ici_scalar_at_start (y : P.Carrier) :
    ContinuousWithinAt (fun z : ℝ × P.Carrier =>
      derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1) (Ici a ×ˢ univ) (a, y) := by
  set φ := extChartAt ThreeModel y with hφ
  set W := interior φ.target with hWdef
  let F : ℝ × ThreeSpace → ℝ := fun z =>
    DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
      (metricScalarAt (G.flow.base.metric z.1)) z.2
  have hF : ContDiffOn ℝ ∞ F (Ico a s ×ˢ W) :=
    scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn _ y
      (G.chartGramFamilySmoothWithinOn_Ico y)
  have hW : W = φ.target := (isOpen_extChartAt_target y).interior_eq
  have huniq : UniqueDiffOn ℝ (Ico a s ×ˢ W) :=
    (uniqueDiffOn_Ico a s).prod isOpen_interior.uniqueDiffOn
  have hcont : ContinuousOn (fun z => fderivWithin ℝ F (Ico a s ×ˢ W) z ((1 : ℝ), (0 : ThreeSpace)))
      (Ico a s ×ˢ W) :=
    (hF.continuousOn_fderivWithin huniq (by simp)).clm_apply continuousOn_const
  have hmap : ContinuousWithinAt (fun z : ℝ × P.Carrier => (z.1, φ z.2))
      (Ico a s ×ˢ φ.source) (a, y) :=
    (continuous_fst.continuousAt.prodMk
      ((continuousAt_extChartAt (I := ThreeModel) y).comp (x := (a, y))
        continuous_snd.continuousAt)).continuousWithinAt
  have hya : ((a, y).1, φ (a, y).2) ∈ Ico a s ×ˢ W :=
    ⟨⟨le_rfl, G.lt⟩, by rw [hW]; exact mem_extChartAt_target y⟩
  have hc := ContinuousWithinAt.comp (f := fun z : ℝ × P.Carrier => (z.1, φ z.2))
    (hcont _ hya) hmap (fun z (hz : z ∈ Ico a s ×ˢ φ.source) => ⟨hz.1, by
      rw [hW]; exact φ.map_source hz.2⟩)
  have hnhds : Ico a s ×ˢ φ.source ∈ 𝓝[Ici a ×ˢ univ] (a, y) :=
    mem_nhdsWithin.mpr ⟨Iio s ×ˢ φ.source, isOpen_Iio.prod (isOpen_extChartAt_source y),
      ⟨G.lt, mem_extChartAt_source y⟩, fun z hz => ⟨⟨hz.2.1, hz.1.1⟩, hz.1.2⟩⟩
  have heq : ∀ z ∈ Ico a s ×ˢ φ.source,
      derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1 =
        fderivWithin ℝ F (Ico a s ×ˢ W) (z.1, φ z.2) ((1 : ℝ), (0 : ThreeSpace)) := by
    intro z hz
    have hfun : (fun v => G.flow.scalar v z.2) = fun v => F (v, φ z.2) := by
      funext v
      exact (DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt y _ hz.2).symm
    rw [hfun]
    exact derivWithin_Ici_eq_fderivWithin hF hz.1 (by rw [hW]; exact φ.map_source hz.2)
      (mem_of_superset (Ico_mem_nhdsGE hz.1.2) (Ico_subset_Ico_left hz.1.1))
  refine (hc.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnhds] with z hz
    exact heq z hz
  · exact heq (a, y) ⟨⟨le_rfl, G.lt⟩, mem_extChartAt_source y⟩

theorem curvDerivNormSq_continuousOn (k : ℕ) :
    ContinuousOn (fun z : ℝ × P.Carrier => curvDerivNormSq k (G.flow.base.metric z.1) z.2)
      (Ico a s ×ˢ univ) := by
  have hgram := chartGramMatrix_joint_contMDiffOn G.flow.base.metric (Ico a s)
    G.smoothUpTo.jointContMDiffOn
  have h := normSq0S_jointContMDiffOn G.flow.base.metric
    (fun t x => nablaKRm04Field
      (solutionOfMetric (D := RealTimeInterval.univ 0) G.flow.base.metric) t k x)
    hgram (fun x₀ K _ ht => nablaKRmChartJoint G.flow.base.metric x₀ (hgram x₀) k K ht)
  refine h.continuousOn.congr fun z _ => ?_
  exact curvNormSq_eq (solutionOfMetric (D := RealTimeInterval.univ 0) G.flow.base.metric) k
    z.1 z.2

private theorem tendsto_nhdsGT_of_continuousWithinAt_start {f : ℝ × P.Carrier → ℝ}
    {T : Set ℝ} (hT : T ∈ 𝓝[>] a) (y : P.Carrier)
    (hf : ContinuousWithinAt f (T ×ˢ univ) (a, y)) :
    Tendsto (fun t => f (t, y)) (𝓝[>] a) (𝓝 (f (a, y))) := by
  have hpath : ContinuousWithinAt (fun t : ℝ => (t, y)) T a :=
    (continuous_id.prodMk continuous_const).continuousWithinAt
  exact (ContinuousWithinAt.comp (f := fun t : ℝ => (t, y)) hf hpath
    fun t ht => ⟨ht, mem_univ y⟩).mono_of_mem_nhdsWithin hT

theorem abs_derivWithin_Ici_scalar_le_curvature_jets_at_start (y : P.Carrier) :
    |derivWithin (fun v => G.flow.scalar v y) (Ici a) a| ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 6 *
          Real.sqrt (curvDerivNormSq 2 (G.flow.base.metric a) y) +
        2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 *
          curvDerivNormSq 0 (G.flow.base.metric a) y := by
  have hIoo : Ioo a s ∈ 𝓝[>] a := Ioo_mem_nhdsGT G.lt
  have hL := tendsto_nhdsGT_of_continuousWithinAt_start (self_mem_nhdsWithin (s := Ioi a)) y
    ((G.continuousWithinAt_derivWithin_Ici_scalar_at_start y).mono
      (prod_mono Ioi_subset_Ici_self subset_rfl))
  have hJ (k : ℕ) := tendsto_nhdsGT_of_continuousWithinAt_start
    (mem_of_superset hIoo Ioo_subset_Ico_self) y
    ((G.curvDerivNormSq_continuousOn k) (a, y) ⟨⟨le_rfl, G.lt⟩, mem_univ y⟩)
  refine le_of_tendsto_of_tendsto hL.abs
    ((((hJ 2).sqrt).const_mul _).add ((hJ 0).const_mul _)) ?_
  filter_upwards [hIoo] with t ht
  have hd := (G.equation.scalarTime
    (show t ∈ (RealTimeInterval.closedOpen a s G.lt).carrier from ⟨ht.1.le, ht.2⟩)
    Subset.rfl y).differentiableAt
    ((RealTimeInterval.closedOpen a s G.lt).regular_mem_nhds ht)
  change |derivWithin (fun v => G.flow.scalar v y) (Ici t) t| ≤ _
  rw [hd.derivWithin (uniqueDiffWithinAt_Ici t)]
  exact abs_deriv_scalar_le_of_curvature_jets G.flow G.equation
    (show t ∈ (RealTimeInterval.closedOpen a s G.lt).regular from ht) y le_rfl le_rfl

theorem abs_derivWithin_Ici_scalar_le_at_start_of_curvature_jets {K : ℝ} (hK : 0 ≤ K)
    {y : P.Carrier}
    (h0 : curvDerivNormSq 0 (G.flow.base.metric a) y ≤ K * G.flow.scalar a y ^ 2)
    (h2 : curvDerivNormSq 2 (G.flow.base.metric a) y ≤ K * G.flow.scalar a y ^ 4) :
    |derivWithin (fun v => G.flow.scalar v y) (Ici a) a| ≤
      ((Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt K +
        2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * K) * G.flow.scalar a y ^ 2 := by
  refine (G.abs_derivWithin_Ici_scalar_le_curvature_jets_at_start y).trans ?_
  have hsq : Real.sqrt (K * G.flow.scalar a y ^ 4) = Real.sqrt K * G.flow.scalar a y ^ 2 := by
    rw [Real.sqrt_mul hK, show G.flow.scalar a y ^ 4 = (G.flow.scalar a y ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hs : Real.sqrt (curvDerivNormSq 2 (G.flow.base.metric a) y) ≤
      Real.sqrt K * G.flow.scalar a y ^ 2 := hsq ▸ Real.sqrt_le_sqrt h2
  have hn : (0 : ℝ) ≤ (Module.finrank ℝ ThreeSpace : ℝ) := Nat.cast_nonneg _
  have h6 := mul_le_mul_of_nonneg_left hs (pow_nonneg hn 6)
  have h4 := mul_le_mul_of_nonneg_left h0 (by positivity :
    (0 : ℝ) ≤ 2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4)
  nlinarith

theorem abs_scalarDifferential_le_at_start_of_curvature_jet {K : ℝ} (hK : 0 ≤ K)
    {y : P.Carrier} (hR : 0 ≤ G.flow.scalar a y)
    (h1 : curvDerivNormSq 1 (G.flow.base.metric a) y ≤ K * G.flow.scalar a y ^ 3)
    (v : TangentSpace ThreeModel y) :
    |Perelman.CanonicalNeighborhood.scalarDifferential G.flow a y v| ≤
      (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt K * G.flow.scalar a y *
        Real.sqrt (G.flow.scalar a y) * Real.sqrt ((G.flow.base.metric a).inner y v v) := by
  have hsq : Real.sqrt (K * G.flow.scalar a y ^ 3) =
      Real.sqrt K * G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) := by
    rw [Real.sqrt_mul hK, show G.flow.scalar a y ^ 3 = G.flow.scalar a y ^ 2 *
      G.flow.scalar a y by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR, mul_assoc]
  have h := abs_scalarDifferential_le_of_curvature_jet G.flow y h1 v
  rw [hsq] at h
  calc _ ≤ _ := h
    _ = _ := by ring

theorem continuousWithinAt_gradient_normSq_at_start (y : P.Carrier) :
    ContinuousWithinAt (fun z : ℝ × P.Carrier => (G.flow.base.metric z.1).inner z.2
      (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
      (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)) (Ici a ×ˢ univ) (a, y) := by
  set φ := extChartAt ThreeModel y with hφ
  set W := interior φ.target with hWdef
  set U := (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).baseSet with hU
  have hUsrc : ∀ x ∈ U, x ∈ φ.source := fun x hx => by
    rwa [hφ, extChartAt_source,
      ← DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source
        (I := ThreeModel)]
  have hW : W = φ.target := (isOpen_extChartAt_target y).interior_eq
  have hG := G.chartGramFamilySmoothWithinOn_Ico y
  have hF : ContDiffOn ℝ ∞ (fun z : ℝ × ThreeSpace =>
      DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
        (metricScalarAt (G.flow.base.metric z.1)) z.2) (Ico a s ×ˢ W) :=
    scalarOnE_contDiffOn_of_chartGramFamilySmoothWithinOn _ y hG
  have hya : ((a, y).1, φ (a, y).2) ∈ Ico a s ×ˢ W :=
    ⟨⟨le_rfl, G.lt⟩, by rw [hW]; exact mem_extChartAt_target y⟩
  have hΦ : ContinuousWithinAt (fun z : ℝ × ThreeSpace =>
      ∑ k : Fin (Module.finrank ℝ ThreeSpace), ∑ i : Fin (Module.finrank ℝ ThreeSpace),
        chartInvGramOnE (I := ThreeModel) (G.flow.base.metric z.1) y k i z.2 *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := ThreeSpace) i
            (fun e => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
              (metricScalarAt (G.flow.base.metric z.1)) e) z.2 *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := ThreeSpace) k
            (fun e => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
              (metricScalarAt (G.flow.base.metric z.1)) e) z.2)
      (Ico a s ×ˢ W) ((a, y).1, φ (a, y).2) := by
    have hd (i : Fin (Module.finrank ℝ ThreeSpace)) := partialDeriv_joint_contDiffWithinAt
      (fun t e => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
        (metricScalarAt (G.flow.base.metric t)) e) i isOpen_interior hya.1 hya.2
      (hF _ hya)
    refine (ContDiffWithinAt.sum fun k _ => ContDiffWithinAt.sum fun i _ =>
      ((chartInvGramOnE_contDiffWithinAt _ y hG k i hya.1 hya.2).mul (hd i)).mul
        (hd k)).continuousWithinAt
  have hmap : ContinuousWithinAt (fun z : ℝ × P.Carrier => (z.1, φ z.2))
      (Ico a s ×ˢ U) (a, y) :=
    (continuous_fst.continuousAt.prodMk
      ((continuousAt_extChartAt (I := ThreeModel) y).comp (x := (a, y))
        continuous_snd.continuousAt)).continuousWithinAt
  have hc := ContinuousWithinAt.comp (f := fun z : ℝ × P.Carrier => (z.1, φ z.2))
    hΦ hmap (fun z (hz : z ∈ Ico a s ×ˢ U) => ⟨hz.1, by
      rw [hW]; exact φ.map_source (hUsrc _ hz.2)⟩)
  have hyU : y ∈ U := FiberBundle.mem_baseSet_trivializationAt' y
  have hnhds : Ico a s ×ˢ U ∈ 𝓝[Ici a ×ˢ univ] (a, y) :=
    mem_nhdsWithin.mpr ⟨Iio s ×ˢ U, isOpen_Iio.prod
      (trivializationAt ThreeSpace (TangentSpace ThreeModel) y).open_baseSet,
      ⟨G.lt, hyU⟩, fun z hz => ⟨⟨hz.2.1, hz.1.1⟩, hz.1.2⟩⟩
  have heq : ∀ z ∈ Ico a s ×ˢ U,
      (G.flow.base.metric z.1).inner z.2
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
        (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2) =
      ∑ k : Fin (Module.finrank ℝ ThreeSpace), ∑ i : Fin (Module.finrank ℝ ThreeSpace),
        chartInvGramOnE (I := ThreeModel) (G.flow.base.metric z.1) y k i (φ z.2) *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := ThreeSpace) i
            (fun e => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
              (metricScalarAt (G.flow.base.metric z.1)) e) (φ z.2) *
          DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := ThreeSpace) k
            (fun e => DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := ThreeModel) y
              (metricScalarAt (G.flow.base.metric z.1)) e) (φ z.2) := by
    intro z hz
    have hxint : φ z.2 ∈ interior φ.target := by
      rw [← hWdef, hW]; exact φ.map_source (hUsrc _ hz.2)
    have h := normGradSqFun_eq_chartInvGram_sum (G.flow.base.metric z.1) y
      (f := G.flow.scalar z.1) hz.2 hxint
    simp only [chartInvGramOnE]
    rw [show (extChartAt ThreeModel y).symm (φ z.2) = z.2 from φ.left_inv (hUsrc _ hz.2)]
    exact h
  refine (hc.mono_of_mem_nhdsWithin hnhds).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hnhds] with z hz
    exact heq z hz
  · exact heq (a, y) ⟨⟨le_rfl, G.lt⟩, hyU⟩

theorem exists_slice_bounds_at_slab_start (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {P : OrientedThreeStage.{u}} {a s q : ℝ} (G : P.IncomingSlab a s),
      0 ≤ q → (∀ y : P.Carrier, q < G.flow.scalar a y → ∀ k ≤ 2,
        curvDerivNormSq k (G.flow.base.metric a) y ≤ K * G.flow.scalar a y ^ (k + 2)) →
      (∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
        derivWithin (fun v => G.flow.scalar v z.2) (Ici z.1) z.1) (Ici a ×ˢ univ) (a, y)) ∧
      (∀ y : P.Carrier, q < G.flow.scalar a y →
        |derivWithin (fun v => G.flow.scalar v y) (Ici a) a| ≤ C * G.flow.scalar a y ^ 2) ∧
      (∀ y : P.Carrier, ContinuousWithinAt (fun z : ℝ × P.Carrier =>
        (G.flow.base.metric z.1).inner z.2
          (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2)
          (gradientFun (G.flow.base.metric z.1) (G.flow.scalar z.1) z.2))
        (Ici a ×ˢ univ) (a, y)) ∧
      (∀ y : P.Carrier, q < G.flow.scalar a y → ∀ v : TangentSpace ThreeModel y,
        |Perelman.CanonicalNeighborhood.scalarDifferential G.flow a y v| ≤
          C * G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
            Real.sqrt ((G.flow.base.metric a).inner y v v)) := by
  set n : ℝ := (Module.finrank ℝ ThreeSpace : ℝ)
  set D : ℝ := n ^ 6 * Real.sqrt K + 2 * n ^ 4 * K
  set E : ℝ := n ^ 2 * Real.sqrt K
  have hD : 0 ≤ D := by positivity
  have hE : 0 ≤ E := by positivity
  refine ⟨⟨D + E + 1, by positivity⟩, by
    change (0 : ℝ) < D + E + 1
    positivity, ?_⟩
  intro P a s q G hq hjets
  refine ⟨G.continuousWithinAt_derivWithin_Ici_scalar_at_start, fun y hy => ?_,
    G.continuousWithinAt_gradient_normSq_at_start, fun y hy v => ?_⟩
  · have h := G.abs_derivWithin_Ici_scalar_le_at_start_of_curvature_jets hK
      (hjets y hy 0 (by norm_num)) (hjets y hy 2 le_rfl)
    change _ ≤ (D + E + 1) * _
    have hsq := sq_nonneg (G.flow.scalar a y)
    nlinarith
  · have hR : 0 ≤ G.flow.scalar a y := hq.trans hy.le
    have h := G.abs_scalarDifferential_le_at_start_of_curvature_jet hK hR
      (hjets y hy 1 (by norm_num)) v
    change _ ≤ (D + E + 1) * _ * _ * _
    have hm : 0 ≤ G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
        Real.sqrt ((G.flow.base.metric a).inner y v v) := by positivity
    calc _ ≤ E * (G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
          Real.sqrt ((G.flow.base.metric a).inner y v v)) := by
          refine h.trans_eq ?_
          ring
      _ ≤ (D + E + 1) * (G.flow.scalar a y * Real.sqrt (G.flow.scalar a y) *
          Real.sqrt ((G.flow.base.metric a).inner y v v)) :=
          mul_le_mul_of_nonneg_right (by linarith) hm
      _ = _ := by ring

theorem exists_derivativeBoundBefore_extend_at_start (K : ℝ) (hK : 0 ≤ K) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ {P : OrientedThreeStage.{u}} {a s q : ℝ} (G : P.IncomingSlab a s),
      0 < q → (∀ y : P.Carrier, q < G.flow.scalar a y → ∀ k ≤ 2,
        curvDerivNormSq k (G.flow.base.metric a) y ≤ K * G.flow.scalar a y ^ (k + 2)) →
      ∃ η : ℝ, 0 < η ∧ a + η < s ∧ G.DerivativeBoundBefore (2 * C) (2 * q) (a + η) ∧
        G.GradientBoundBefore (2 * C) (2 * q) (a + η) := by
  obtain ⟨C, hC, hslice⟩ := exists_slice_bounds_at_slab_start.{u} K hK
  refine ⟨C, hC, fun {P a s q} G hq hjets => ?_⟩
  obtain ⟨hreg, hstart, hgreg, hgstart⟩ := hslice G hq.le hjets
  have hmem : a ∈ Ico a s := ⟨le_rfl, G.lt⟩
  obtain ⟨η₁, hη₁, hs₁, h₁⟩ := G.exists_derivativeBoundBefore_extend_of_slice hC hq hmem
    (fun _ => hreg) (fun _ => hstart) (fun _ t ht => (lt_irrefl a (ht.1.trans ht.2)).elim)
  obtain ⟨η₂, hη₂, -, h₂⟩ := G.exists_gradientBoundBefore_extend_of_slice hC hq hmem
    (fun _ => hgreg) (fun _ => hgstart) (fun _ t ht => (lt_irrefl a (ht.1.trans ht.2)).elim)
  refine ⟨min η₁ η₂, lt_min hη₁ hη₂, by linarith [min_le_left η₁ η₂], ?_, ?_⟩
  · exact G.derivativeBoundBefore_mono (by linarith [min_le_left η₁ η₂]) h₁
  · exact G.gradientBoundBefore_mono (by linarith [min_le_right η₁ η₂]) h₂

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
