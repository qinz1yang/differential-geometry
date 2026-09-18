import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PartialErrorTower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckTransportDecoupled
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact

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
    (cmp : MetricComparisonOn (fun _ => scaleMetric (metricScalarAt gm p) nk.Q_pos gm)
      (fun _ => scaleMetric (metricScalarAt g x) hQ g) Fmap V {0} order' eps)
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
