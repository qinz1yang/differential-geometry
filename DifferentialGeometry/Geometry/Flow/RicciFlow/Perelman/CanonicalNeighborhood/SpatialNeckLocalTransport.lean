import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialErrorTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.ForwardApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticMetricApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.StaticRescalingComparison
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Scalar

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
def StrongNeck.toSpatialNeck
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    SpatialNeck (S.base.metric t) eps x := by
  let C := nk.comparison.singleton (show (0 : ℝ) ∈ Set.Icc (-1) 0 by norm_num)
  refine {
    eps_pos := nk.eps_pos
    eps_small := nk.eps_small
    Q_pos := nk.Q_pos
    cylinder := nk.cylinder
    map := nk.map
    center := nk.center
    center_eq := nk.center_eq
    domain := nk.domain
    comparison := {
      pullback := fun _ => C.pullback 0
      pullback_eq := ?_
      jet := fun b _ => C.jet b 0
      jet_zero := ?_
      jet_succ := ?_
      equivalence := ?_
      close := ?_ } }
  · intro s y hy v
    have hscale : S.scalar t x = metricScalarAt (S.base.metric t) x := rfl
    simpa only [rescaledMetric, parabolicTime_zero, hscale] using C.pullback_eq 0 y hy v
  · intro s y v
    exact C.jet_zero 0 y v
  · intro b s hs y hy v
    have h := C.jet_succ b 0 (by simp) y hy v
    have hz : derivWithin (fun a => C.jet b a y v) ({0} : Set ℝ) 0 = 0 := by
      apply derivWithin_zero_of_not_accPt
      rw [accPt_iff_clusterPt, Filter.inf_principal]
      simp [ClusterPt]
    rw [hz] at h
    simpa only [derivWithin_fun_const, Pi.zero_apply] using h
  · intro s hs y hy v
    exact C.equivalence 0 (by simp) y hy v
  · intro a b hab s hs y hy
    exact C.close a b hab 0 (by simp) y hy

omit [T2Space M] [SigmaCompactSpace M] in
theorem StrongNeck.toSpatialNeck_map
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t) :
    nk.toSpatialNeck.map = nk.map := rfl

omit [T2Space M] [SigmaCompactSpace M] in
theorem SpatialNeck.exists_transport_of_local_comparisons
    {gm : SmoothRiemannianMetric I3 P} {p : P}
    {g : SmoothRiemannianMetric I3 M} {x : M} {alpha eps : ℝ}
    {V : Set P} {order' : ℕ}
    (nk : SpatialNeck gm (neckModelTolerance alpha) p)
    (hQ : 0 < metricScalarAt g x)
    (Fmap : PartialDiffeomorph I3 I3 P M ∞)
    (cmp : MetricComparisonOn (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => DifferentialGeometry.scaleMetric (metricScalarAt g x) hQ g) Fmap V {0} order' eps)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : 0 ≤ eps) (heps' : eps ≤ neckSourceTolerance alpha)
    (horder : ⌈(2 * alpha)⁻¹⌉₊ ≤ order')
    (hbase : Fmap p = x)
    (houter : ∀ y ∈ Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ V)
    (hVsource : V ⊆ Fmap.source) :
    ∃ nk' : SpatialNeck g (2 * alpha) x,
      nk'.map = partialDiffeomorphTransMixed nk.map Fmap := by
  let U : TopologicalSpace.Opens Cylinder :=
    ⟨Set.univ ×ˢ Set.Ioo (-alpha⁻¹) alpha⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let W : TopologicalSpace.Opens Cylinder :=
    ⟨Set.univ ×ˢ Set.Ioo (-(2 * alpha)⁻¹) (2 * alpha)⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let K : Set Cylinder := Set.univ ×ˢ Set.Icc (-(2 * alpha)⁻¹) (2 * alpha)⁻¹
  have hrad : (2 * alpha)⁻¹ < alpha⁻¹ := inv_strictAnti₀ ha (by linarith)
  have hKU : K ⊆ U := by
    intro y hy
    exact ⟨hy.1, lt_of_lt_of_le (neg_lt_neg hrad) hy.2.1,
      lt_of_le_of_lt hy.2.2 hrad⟩
  have hWK : (W : Set Cylinder) ⊆ K :=
    Set.prod_mono (subset_refl _) Set.Ioo_subset_Icc_self
  have hWU : (W : Set Cylinder) ⊆ U := hWK.trans hKU
  have hK : IsCompact K := isCompact_univ.prod isCompact_Icc
  obtain ⟨chi, hchi, _hcompact, hone, hsupp, _hrange⟩ :=
    DifferentialGeometry.Analysis.exists_mfd_bump (I := IC) hK U.isOpen hKU
  have hchiW : EqOn chi (fun _ => 1) W := by
    intro y hy
    exact subset_of_mem_nhdsSet hone (hWK hy)
  have hU : (U : Set Cylinder) ⊆ nk.map.source := by
    apply Set.Subset.trans ?_ nk.domain
    have hr := inv_anti₀ (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
    exact Set.prod_mono (subset_refl _) (Set.Ioo_subset_Ioo (neg_le_neg hr) hr)
  have hsub : (W : Set Cylinder) ⊆
      Set.univ ×ˢ Set.Ioo (-(neckModelTolerance alpha)⁻¹) (neckModelTolerance alpha)⁻¹ :=
    neck_window_subset_of_le (neckModelTolerance_pos ha) (neckModelTolerance_le alpha)
  have hord : ⌈(2 * alpha)⁻¹⌉₊ ≤ ⌈(neckModelTolerance alpha)⁻¹⌉₊ :=
    Nat.ceil_mono (inv_anti₀ (neckModelTolerance_pos ha)
      ((neckModelTolerance_le alpha).trans (by linarith)))
  obtain ⟨T⟩ := TransportedErrorTower.nonempty_of_partial_pullback cmp
    (fun _ => nk.cylinder.metric 0) nk.map U W hU hWU houter chi hchi hsupp hchiW
    (nk.comparison.mono hsub hord le_rfl) horder heps
    (neckModelTolerance_pos ha) (neckModelTolerance_le_smallness alpha)
    (fun _ _ _ _ _ _ => DifferentiableWithinAt.singleton)
  exact ⟨SpatialNeck.transport' nk hQ Fmap cmp T hsmall (neckModelTolerance_le alpha)
    (backgroundJetConstant_mul_le_of_le_neckSourceTolerance ha heps') hbase
    (fun y hy => houter y (hWU hy)) hVsource, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

variable {X : PointedRiemannianSeq.{u, 0, 0} I3}
  {L : PointedRiemannianManifold.{u, 0, 0} I3} {subseq : ℕ → ℕ}
  {Phi : PointedRiemannianConvergenceMaps X L subseq}

private theorem eventually_scalar_normalized_forward_comparison
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (K : Set L.M) (hK : IsCompact K) (order : ℕ) {eps : ℝ} (heps : 0 < eps)
    (p : L.M) (hq : 0 < metricScalarAt L.metric p) :
    ∀ᶠ k in atTop, K ⊆ Phi.source k ∧
      ∃ hc : 0 < metricScalarAt (X.obj (subseq k)).metric (Phi.map k p),
        ∀ A : Set L.M, A ⊆ interior K → Nonempty (MetricComparisonOn
          (fun _ => scaleMetric (metricScalarAt L.metric p) hq L.metric)
          (fun _ => scaleMetric (metricScalarAt (X.obj (subseq k)).metric (Phi.map k p))
            hc (X.obj (subseq k)).metric)
          (Phi.map k) A {0} order eps) := by
  let q := metricScalarAt L.metric p
  let c (k : ℕ) := metricScalarAt (X.obj (subseq k)).metric (Phi.map k p)
  let n : ℝ := Real.sqrt (Module.finrank ℝ ThreeSpace : ℝ)
  have hn : 0 ≤ n := Real.sqrt_nonneg _
  let B : ℝ := (∑ a ∈ Finset.range (order + 1), Real.sqrt (q⁻¹ ^ (a + 2))) + 1
  have hBsum : 0 ≤ ∑ a ∈ Finset.range (order + 1), Real.sqrt (q⁻¹ ^ (a + 2)) := by
    exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hweight (a : ℕ) (ha : a ≤ order) : Real.sqrt (q⁻¹ ^ (a + 2)) ≤ B := by
    have h := Finset.single_le_sum (fun b (_hb : b ∈ Finset.range (order + 1)) =>
      Real.sqrt_nonneg (q⁻¹ ^ (b + 2))) (Finset.mem_range.mpr (by omega : a < order + 1))
    exact h.trans (by dsimp only [B]; linarith)
  let eta := min (q / 2) (q * eps / (4 * (n + 1)))
  have heta : 0 < eta := lt_min (by positivity) (by positivity)
  let delta := min (1 / 2) (eps / (8 * q * B))
  have hd : 0 < delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hdbudget : 2 * q * B * delta ≤ eps / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * q * B)).mp
      (min_le_right (1 / 2) (eps / (8 * q * B)))
    change delta * (8 * q * B) ≤ eps at h
    nlinarith
  have hnear : ∀ᶠ k in atTop, |c k - q| < eta := by
    have ht := KappaSolutions.pointedScalar_tendsto_of_metricCG_canonical_domains C hcanonical p
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp ht) eta heta
  filter_upwards [C.eventually_map_metric_approximation hcanonical K hK order hd hd1,
    hnear] with k hk hck
  have hc : 0 < c k := by
    have hhalf : eta ≤ q / 2 := min_le_left _ _
    have hlow := (abs_lt.mp hck).1
    linarith
  have hcupper : c k ≤ 2 * q := by
    have hhalf : eta ≤ q / 2 := min_le_left _ _
    have hupper := (abs_lt.mp hck).2
    linarith
  have hratio : |c k / q - 1| ≤ eps / (4 * (n + 1)) := by
    rw [show c k / q - 1 = (c k - q) / q by rw [sub_div, div_self (show q ≠ 0 from hq.ne')], abs_div, abs_of_pos hq]
    apply (div_le_iff₀ hq).mpr
    have hsmall := hck.le.trans (min_le_right (q / 2) (q * eps / (4 * (n + 1))))
    exact hsmall.trans_eq (by ring)
  have hrbudget : |c k / q - 1| * n ≤ eps / 4 := by
    have h := (le_div_iff₀ (by positivity : 0 < 4 * (n + 1))).mp hratio
    nlinarith [abs_nonneg (c k / q - 1)]
  refine ⟨hk.1, hc, ?_⟩
  intro A hA
  obtain ⟨D⟩ := hk.2 A hA
  refine ⟨(MetricComparisonOn.ofMapMetricApproximation D ({0} : Set ℝ)).staticRescale
    (t := 0) (by simp) q (c k) hq hc heps.le ?_⟩
  intro a ha
  have hprod : Real.sqrt (q⁻¹ ^ (a + 2)) * c k * delta ≤ eps / 4 := by
    calc
      _ ≤ B * (2 * q) * delta :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hweight a ha) hcupper hc.le hB.le) hd.le
      _ = 2 * q * B * delta := by ring
      _ ≤ eps / 4 := hdbudget
  change _ + |c k / q - 1| * n ≤ eps
  linarith

theorem SpatialNeck.eventually_transport_of_metric_convergence
    (C : MetricConvergenceData Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    {alpha : ℝ} (ha : 0 < alpha) (hsmall : alpha < 1 / 32)
    {p : L.M} (nk : SpatialNeck L.metric (neckModelTolerance alpha) p) :
    ∀ᶠ k in atTop,
      ∃ nk' : SpatialNeck (X.obj (subseq k)).metric (2 * alpha) (Phi.map k p),
        nk'.map = partialDiffeomorphTransMixed nk.map (Phi.partialDiffeomorph k) := by
  let _ : LocallyCompactSpace L.M := ChartedSpace.locallyCompactSpace ThreeSpace L.M
  have htol : neckModelTolerance alpha < alpha :=
    (neckModelTolerance_le_smallness alpha).trans_lt
      (backgroundJetSmallness_ceil_lt_self _ ha hsmall)
  have hrad : alpha⁻¹ < (neckModelTolerance alpha)⁻¹ :=
    inv_strictAnti₀ (neckModelTolerance_pos ha) htol
  let K0 : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have hK0 : IsCompact K0 := isCompact_univ.prod isCompact_Icc
  have hKsource : K0 ⊆ nk.map.source := by
    intro z hz
    apply nk.domain
    exact ⟨hz.1, (neg_lt_neg hrad).trans_le hz.2.1, hz.2.2.trans_lt hrad⟩
  let A : Set L.M := nk.map '' K0
  have hA : IsCompact A :=
    hK0.image_of_continuousOn (nk.map.contMDiffOn_toFun.continuousOn.mono hKsource)
  obtain ⟨K, hK, hAK⟩ := exists_compact_superset hA
  have houter : ∀ z ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map z ∈ A := by
    intro z hz
    exact ⟨z, ⟨hz.1, hz.2.1.le, hz.2.2.le⟩, rfl⟩
  filter_upwards [eventually_scalar_normalized_forward_comparison C hcanonical K hK
    (⌈(2 * alpha)⁻¹⌉₊) (neckSourceTolerance_pos ha) p nk.Q_pos] with k hk
  obtain ⟨hc, hcmp⟩ := hk.2
  obtain ⟨cmp⟩ := hcmp A hAK
  exact nk.exists_transport_of_local_comparisons hc (Phi.partialDiffeomorph k) cmp
    ha (by linarith) (neckSourceTolerance_pos ha).le le_rfl le_rfl rfl houter
    ((hAK.trans interior_subset).trans hk.1)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
