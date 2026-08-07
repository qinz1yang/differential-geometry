import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.ScalarNonautTame
import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLapDiffTime
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.MetricDiffJoint
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.InverseMetricRaisedEndomorphismJetBound
import DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ParametricJetBound
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciDifferenceMeanValue
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricFamilyConnDiff
import DifferentialGeometry.Analysis.Parabolic.RicciLinearization.RicciArmResidualCoefficientFields
import DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.RealizedGramDiff
import DifferentialGeometry.Geometry.Curvature.Realized.MetricFamilyPair
import DifferentialGeometry.Tensor.RSTensor.Metric
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection









noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral


open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance scalarFluxTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedAddCommGroup r s

private local instance scalarFluxTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModel_normedSpace r s

private local instance scalarFluxTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundle_topology r s

private local instance scalarFluxTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundle_fiber r s

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
theorem metricDiff_bilin (q h : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x v w =
      h.inner x v w - q.inner x v w :=
  metricDiff_symVal (I := I) (M := M) q h x v w

private lemma grid_mono {a b : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) (i : ℕ) :
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid a i ≤
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid b i := by
  classical
  rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid,
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun e _ => ?_))
  exact Finset.prod_le_prod (fun m _ => ha (e m)) (fun m _ => hab (e m))

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
private theorem joint0S_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  letI := tensor0SBundle_topology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀
        ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hp
    exact ((e.linear ℝ hp).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by
      rw [he, ← hx₀]
      exact mem_baseSet_trivializationAt _ _ x₀)).map_sub
        (A p₀) (B p₀)).symm




omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff_small
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ)) 0 (2 + i) x
        ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 2 i
          (metricDifferenceCcTensor (I := I) (M := M)
            (G.metric (T : ℝ)) (G.metric t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  have hPzero : P (T : ℝ) = 0 := by
    simp only [P, q, metricDifferenceCcTensor_self]
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun y : M => TensorRSSpace 0 2 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using metricDiff_joint (I := I) (M := M) G hG q
  simpa only [P, q] using
    joint_jet_small (I := I) (M := M) q 0 2 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem scalarTrace_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q (G.metric p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 0 ℝ E) (V₂ := fun x : M => Tensor0SSpace 0 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 0 I p.1 from
        (scalarTraceCoeff (I := I) (M := M) q (G.metric p.2)).toSection p.1))
    (S := D.regular)
  intro W
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) p.1 (W p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact W.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hmove := comTrace_of_family (I := I) 0 G hG
    (fun p : M × ℝ => W p.1) hW
  have hfixedOp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        (cometricDoubleTraceFib (I := I) q 0 p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact (cometricDoubleTraceFib_contMDiff (I := I) q 0).comp_contMDiffOn
      contMDiffOn_fst
  have hfixed := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hfixedOp hW
  have hsub := joint0S_sub (I := I) (M := M) (d := 0)
    (fun p : M × ℝ =>
      cometricDoubleTraceFib (I := I) (G.metric p.2) 0 p.1 (W p.1))
    (fun p : M × ℝ => cometricDoubleTraceFib (I := I) q 0 p.1 (W p.1))
    hmove hfixed
  refine hsub.congr (fun p _ => ?_)
  congr 1



omit [NeZero (Module.finrank ℝ E)] in
theorem connTrace_joint
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q (G.metric p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_pointwise_joint_manifold_time (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 0 ℝ E) (V₂ := fun x : M => Tensor0SSpace 0 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 0 I p.1 from
        (connTraceCoeff (I := I) (M := M) q (G.metric p.2)).toSection p.1))
    (S := D.regular)
  intro W
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun x : M => Tensor0SSpace 1 I x) p.1 (W p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact W.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hconn := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (connDiff_joint (I := I) G hG q) hW
  have htrace := comTrace_of_family (I := I) 0 G hG
    (fun p : M × ℝ =>
      (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        connDiffFib (I := I) (G.metric p.2) q p.1) (W p.1)) hconn
  refine htrace.congr (fun p _ => ?_)
  congr 1



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem scalarTrace_rev
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) (T : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q
          (G.metric (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, T - p.2))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk contMDiffOn_fst
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
  simpa only [Function.comp_apply] using
    (scalarTrace_joint (I := I) (M := M) G hG q).comp hmove
      (fun p hp => ⟨Set.mem_univ p.1, hp.2⟩)



omit [NeZero (Module.finrank ℝ E)] in
theorem connTrace_rev
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) (T : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q
          (G.metric (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, T - p.2))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk contMDiffOn_fst
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
  simpa only [Function.comp_apply] using
    (connTrace_joint (I := I) (M := M) G hG q).comp hmove
      (fun p hp => ⟨Set.mem_univ p.1, hp.2⟩)



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem scalarTrace_rev_on
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) (T : ℝ) {S : Set ℝ}
    (hS : S ⊆ {s : ℝ | T - s ∈ D.regular}) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q
          (G.metric (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
  (scalarTrace_rev (I := I) (M := M) G hG q T).mono
    (Set.prod_mono (Set.Subset.rfl) hS)



omit [NeZero (Module.finrank ℝ E)] in
theorem connTrace_rev_on
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (q : SmoothRiemannianMetric I M) (T : ℝ) {S : Set ℝ}
    (hS : S ⊆ {s : ℝ | T - s ∈ D.regular}) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q
          (G.metric (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
  (connTrace_rev (I := I) (M := M) G hG q T).mono
    (Set.prod_mono (Set.Subset.rfl) hS)



omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTrace_small
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ)) 2 (0 + i) x
        ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 2 0 i
          (scalarTraceCoeff (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 2 0 := fun t =>
    scalarTraceCoeff (I := I) (M := M) q (G.metric t)
  have hPzero : P (T : ℝ) = 0 := by
    simp only [P, q, scalarTraceCoeff, traceCast_self, sub_self]
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun y : M => TensorRSSpace 2 0 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using scalarTrace_joint (I := I) (M := M) G hG q
  simpa only [P, q, Nat.zero_add] using
    joint_jet_small (I := I) (M := M) q 2 0 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε

omit [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
private theorem connFib_self [SigmaCompactSpace M] (q : SmoothRiemannianMetric I M) (x : M) :
    connDiffFib (I := I) q q x = 0 := by
  apply ContinuousLinearMap.ext
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  rw [connDiffFib_apply_eval, PDE.DeTurck.connDiff_self]
  change om (0 : Fin 1 → TangentSpace I x) = 0
  exact ContinuousMultilinearMap.map_zero om




omit [NeZero (Module.finrank ℝ E)] in
theorem connTrace_small
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ)) 1 (0 + i) x
        ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 1 0 i
          (connTraceCoeff (I := I) (M := M) (G.metric (T : ℝ))
            (G.metric t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 1 0 := fun t =>
    connTraceCoeff (I := I) (M := M) q (G.metric t)
  have hPzero : P (T : ℝ) = 0 := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    dsimp only [P, q]
    rw [connTraceCoeff, appCcRS_toSection, traceCast,
      SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection,
      connDiffSection_toSection, connFib_self (I := I) (M := M),
      ContinuousLinearMap.comp_zero, SmoothCcTensor.toSection_zero]
    rfl
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun y : M => TensorRSSpace 1 0 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using connTrace_joint (I := I) (M := M) G hG q
  simpa only [P, q, Nat.zero_add] using
    joint_jet_small (I := I) (M := M) q 1 0 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε



omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
theorem scalarFlux_eq_slot (q h : SmoothRiemannianMetric I M) :
    scalarFluxCoeff (I := I) (M := M) q h =
      endoSlotZeroCcTensor (I := I) (M := M) q 0
      (gInvDiffRaisedEndoField (I := I) (M := M) q h) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [scalarFlux_eval (I := I) (M := M), slotInsertEndoCc_toSection,
    cotangent_slot_apply (I := I) (M := M)]
  rfl



theorem scalarFlux_jet_grid
    (q : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (h : SmoothRiemannianMetric I M) (T : SmoothCcTensor q 0 2)
        (_htie : ∀ y v w, h.inner y v w =
          q.inner y v w + ccTensorBilinSymm (I := I) q T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) q
          (ccTensorBilinSymm (I := I) q T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
            ((iteratedCovGrad (I := I) q 1 1 i
              (scalarFluxCoeff (I := I) (M := M) q h)).toSection x) ≤
          C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
              ((iteratedCovGrad (I := I) q 0 2 j T).toSection x)) i := by
  obtain ⟨C, hC, hjet⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_gInvDiffRaisedEndo_diagGrid_le
      (I := I) (M := M) q hδ₀
  refine ⟨C, hC, ?_⟩
  intro h T htie δ hδ_le hδ0 hbound i x
  rw [scalarFlux_eq_slot (I := I) (M := M)]
  simpa only [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid] using
    hjet h T htie hδ_le hδ0 hbound i x



omit [NeZero (Module.finrank ℝ E)] in
theorem metricDiff_slab
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ((T : ℝ) - s ∈ D.regular) ∧
          metricCauchySchwarzBound (I := I) (G.metric (T : ℝ))
            (ccTensorBilinSymm (I := I) (G.metric (T : ℝ))
              (metricDifferenceCcTensor (I := I) (M := M)
                (G.metric (T : ℝ)) (G.metric ((T : ℝ) - s)))) (1 / 4 : ℝ) ∧
          ∀ i x,
            riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ)) 0 (2 + i) x
              ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 0 2 i
                (metricDifferenceCcTensor (I := I) (M := M)
                  (G.metric (T : ℝ)) (G.metric ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨tau, htau, htau_one, hshort⟩ :=
    lapDiff_short (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let K : Set ℝ := Set.Icc ((T : ℝ) - tau) (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_Icc
  have hKreg : K ⊆ D.regular := by
    intro t ht
    have hs : (T : ℝ) - t ∈ Set.Icc (0 : ℝ) tau := by
      constructor <;> dsimp only [K] at ht <;> linarith [ht.1, ht.2]
    have hreg := (hshort ((T : ℝ) - t) hs).1
    convert hreg using 1
    all_goals ring
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) p.1
        ((P p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using metricDiff_joint (I := I) (M := M) G hG q
  obtain ⟨B, hB, hjet⟩ := joint_jet_bdd (I := I) (M := M) q 0 2 P
    hK hKreg hPjoint
  refine ⟨tau, htau, htau_one, B, hB, ?_⟩
  intro s hs
  have htK : (T : ℝ) - s ∈ K := by
    constructor <;> dsimp only [K] <;> linarith [hs.1, hs.2]
  have hbound : metricCauchySchwarzBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    simpa only [q, ContinuousLinearMap.sub_apply] using
      (hshort s hs).2 y v w
  refine ⟨(hshort s hs).1, ?_, ?_⟩
  · simpa only [q, P] using hbound
  · intro i x
    simpa only [q, P] using hjet i ((T : ℝ) - s) htK x



theorem scalarFlux_slab
    {D : RealTimeInterval}
    (G : RealizedMetricFamilyOn (I := I) (M := M) D)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D G)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ i x,
          riemannianFiberNormSq (I := I) (M := M) (G.metric (T : ℝ))
              1 (1 + i) x
              ((iteratedCovGrad (I := I) (G.metric (T : ℝ)) 1 1 i
                (scalarFluxCoeff (I := I) (M := M) (G.metric (T : ℝ))
                  (G.metric ((T : ℝ) - s)))).toSection x) ≤
            B i := by
  classical
  obtain ⟨tau, htau, htau_one, J, hJ, hdata⟩ :=
    metricDiff_slab (I := I) (M := M) G hG T
  let q : SmoothRiemannianMetric I M := G.metric (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (G.metric t)
  obtain ⟨C, hC, hflux⟩ :=
    scalarFlux_jet_grid (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨tau, htau, htau_one, fun i =>
    C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i,
    fun i => mul_nonneg (hC i)
      (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ i), ?_⟩
  intro s hs i x
  have hsdata := hdata s hs
  have htie : ∀ y v w,
      (G.metric ((T : ℝ) - s)).inner y v w =
        q.inner y v w + ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s)) y v w := by
    intro y v w
    rw [metricDiff_bilin (I := I) (M := M)]
    ring
  have hbound : metricCauchySchwarzBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    simpa only [q, P] using hsdata.2.1
  have hlocal := hflux (G.metric ((T : ℝ) - s)) (P ((T : ℝ) - s)) htie
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hbound i x
  have hgrid :
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
            ((iteratedCovGrad (I := I) q 0 2 j (P ((T : ℝ) - s))).toSection x)) i ≤
        DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i := by
    apply grid_mono
    · intro j
      exact riemannianFiberNormSq_nonneg (I := I) (M := M) q 0 (2 + j) x _
    · intro j
      simpa only [q, P] using hsdata.2.2 j x
  exact hlocal.trans (mul_le_mul_of_nonneg_left hgrid (hC i))

end DifferentialGeometry.Analysis.Spectral

end
