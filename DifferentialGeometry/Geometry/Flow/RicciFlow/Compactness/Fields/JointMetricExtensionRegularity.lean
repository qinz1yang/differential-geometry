import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.MetricExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Solution.TimeRegularity
import DifferentialGeometry.Geometry.Metric.Convergence.Compactness.Precompactness
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype


noncomputable section

open Bundle Filter Manifold
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : Nat → Nat} (Φ : PointedCGHMaps (I := I) X P subseq)

theorem contDiffAt_gSeqExt_chartGramOnE_of_solution
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (k : Nat)
    {D : RealTimeInterval}
    (S : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
      SolutionOn (I := I) (M := SourceDomain (I := I) Φ k) D)
    (hS : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
      letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I) S)
    (hmetric : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) :=
          sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
      letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
      ∀ (t : Real) (x : SourceDomain (I := I) Φ k)
        (v w : TangentSpace I x),
        (sourceMetric (I := I) Φ hsrc htgt k t).inner x v w =
          (S.family.metric t).inner x v w)
    (x₀ : P.M) (i j : Fin (Module.finrank Real E)) (q : Real × E)
    (hqt : q.1 ∈ D.regular)
    (hqtarget : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      q.2 ∈ (extChartAt I x₀).target)
    (hqgrow : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      (extChartAt I x₀).symm q.2 ∈ bf.grow k) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    ContDiffAt Real ∞
      (fun p : Real × E =>
        chartGramOnE (I := I)
          (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j p.2) q := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let : IsManifold I 1 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I 2 P.M :=
    IsManifold.of_le (I := I) (M := P.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
    change IsManifold I ∞ P.M
    infer_instance
  classical
  set y : E := q.2 with hy
  have hytarget : y ∈ (extChartAt I x₀).target := hqtarget
  set x : P.M := (extChartAt I x₀).symm y with hx
  have hxchart : x ∈ (extChartAt I x₀).source := (extChartAt I x₀).map_target hytarget
  have hxy : extChartAt I x₀ x = y := by
    simpa only [x] using (extChartAt I x₀).right_inv hytarget
  have hxgrow : x ∈ bf.grow k := hqgrow
  have hxsource : x ∈ Φ.source k := bf.grow_subset k hxgrow
  obtain ⟨σi, hσi⟩ := exists_section_eqOn_compact (I := I) x₀
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) isCompact_singleton
    (Set.singleton_subset_iff.mpr (by simpa only [extChartAt_source] using hxchart))
  obtain ⟨σj, hσj⟩ := exists_section_eqOn_compact (I := I) x₀
    ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) isCompact_singleton
    (Set.singleton_subset_iff.mpr (by simpa only [extChartAt_source] using hxchart))
  let : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
  let : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
  let : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
  let : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
  let : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceSigma : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
    sourceDomSigmaOf (I := I) Φ k (hsrc k)
  let sourceT2 : T2Space ↥(sourceOpen (I := I) Φ k) :=
    sourceDomT2 (I := I) Φ k
  let Vi := @DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection E inferInstance
    inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.smooth
    (sourceOpen (I := I) Φ k) σi
  let Vj := @DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection E inferInstance
    inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.smooth
    (sourceOpen (I := I) Φ k) σj
  let : IsManifold I 1 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I 2 (SourceDomain (I := I) Φ k) :=
    IsManifold.of_le (I := I) (M := SourceDomain (I := I) Φ k)
      (n := (∞ : WithTop ℕ∞)) (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (SourceDomain (I := I) Φ k) := by
    change IsManifold I ∞ (SourceDomain (I := I) Φ k)
    infer_instance
  let V : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : SourceDomain (I := I) Φ k → Type _) := ![Vi, Vj]
  let xU : SourceDomain (I := I) Φ k := ⟨x, hxsource⟩
  let core : E → SourceDomain (I := I) Φ k := fun z =>
    if hz : (extChartAt I x₀).symm z ∈ Φ.source k then
      ⟨(extChartAt I x₀).symm z, hz⟩
    else xU
  have htend : Filter.Tendsto (extChartAt I x₀).symm (𝓝 y) (𝓝 x) := by
    have h := (continuousAt_extChartAt_symm'' (I := I) (x := x₀) hytarget).tendsto
    rwa [show (extChartAt I x₀).symm y = x by rfl] at h
  have hevSource : ∀ᶠ z in 𝓝 y, (extChartAt I x₀).symm z ∈ Φ.source k :=
    htend.eventually ((Φ.source_open k).mem_nhds hxsource)
  have hcoreEq : (fun z : E => ((core z : SourceDomain (I := I) Φ k) : P.M)) =ᶠ[𝓝 y]
      (extChartAt I x₀).symm := by
    filter_upwards [hevSource] with z hz
    simp only [core, dite_eq_left hz]
  have hsymm : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := (∞ : WithTop ℕ∞)) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hytarget)
  have hcoreVal : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞)
      (fun z : E => ((core z : SourceDomain (I := I) Φ k) : P.M)) y :=
    hsymm.congr_of_eventuallyEq hcoreEq
  have hcore : ContMDiffAt 𝓘(Real, E) I (∞ : WithTop ℕ∞) core y := by
    rw [contMDiffAt_iff] at hcoreVal ⊢
    obtain ⟨hcont, hdiff⟩ := hcoreVal
    refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr
      (by simpa [Function.comp_def] using hcont), ?_⟩
    convert hdiff using 2
    funext z
    rfl
  have hmap : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
      (𝓘(Real, Real).prod I) (∞ : WithTop ℕ∞)
      (fun p : Real × E => (p.1, core p.2)) q := by
    exact contMDiffAt_fst.prodMk (hcore.comp q contMDiffAt_snd)
  have hsrcSmooth := solutionMetricJointAt (I := I) (x := core y) S
    hS (D.regular_isOpen.mem_nhds hqt) V
  have hlocalMD := hsrcSmooth.comp q hmap
  let G : Real × E → Real := fun p =>
    (S.family.metric p.1).inner (core p.2)
      (V 0 (core p.2)) (V 1 (core p.2))
  have hlocalMD' : ContMDiffAt (𝓘(Real, Real).prod 𝓘(Real, E))
      𝓘(Real, Real) (∞ : WithTop ℕ∞) G q := by
    apply hlocalMD.congr_of_eventuallyEq
    filter_upwards [] with p
    simp only [G, solutionMetricField, Tensor0SBundle.metricTensorField_apply,
      Function.comp_apply]
  have hlocal : ContDiffAt Real (∞ : WithTop ℕ∞) G q := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hlocalMD'
  obtain ⟨W, hWopen, hgrowW, hWone⟩ := bf.chi_one k
  have hσi0 : ∀ᶠ z in 𝓝 x,
      σi z = TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
        x₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) z :=
    hσi.filter_mono (nhds_le_nhdsSet (Set.mem_singleton x))
  have hσj0 : ∀ᶠ z in 𝓝 x,
      σj z = TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
        x₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) z :=
    hσj.filter_mono (nhds_le_nhdsSet (Set.mem_singleton x))
  have hevY : ∀ᶠ z in 𝓝 y,
      z ∈ (extChartAt I x₀).target ∧
      (extChartAt I x₀).symm z ∈ Φ.source k ∧
      (extChartAt I x₀).symm z ∈ W ∧
      σi ((extChartAt I x₀).symm z) =
        TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
          x₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i)
          ((extChartAt I x₀).symm z) ∧
      σj ((extChartAt I x₀).symm z) =
        TensorLieDeriv.tangentConstInChart (𝕜 := Real) (I := I)
          x₀ ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)
          ((extChartAt I x₀).symm z) := by
    filter_upwards [
      (isOpen_extChartAt_target (I := I) x₀).mem_nhds hytarget,
      hevSource, htend.eventually (hWopen.mem_nhds (hgrowW hxgrow)),
      htend.eventually hσi0, htend.eventually hσj0] with z hzt hzs hzW hzi hzj
    exact ⟨hzt, hzs, hzW, hzi, hzj⟩
  let F : Real × E → Real := fun p =>
    chartGramOnE (I := I) (gSeqExt (I := I) Φ R bf hsrc htgt k p.1) x₀ i j p.2
  have hFG : F =ᶠ[𝓝 q] G := by
    filter_upwards [(continuous_snd.tendsto q).eventually hevY] with p hp
    rcases hp with ⟨hpt, hps, hpW, hpi, hpj⟩
    set z : P.M := (extChartAt I x₀).symm p.2 with hz
    have hcorez : core p.2 = (⟨z, hps⟩ : SourceDomain (I := I) Φ k) := by
      simp only [core, dite_eq_left hps, z]
    have hViz : Vi (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σi z := by
      exact @DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection_apply E
        inferInstance
        inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.smooth
        (sourceOpen (I := I) Φ k) σi ⟨z, hps⟩
    have hVjz : Vj (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σj z := by
      exact @DifferentialGeometry.Geometry.Curvature.restrictOpenTangentSection_apply E
        inferInstance
        inferInstance inferInstance H inferInstance I P.M P.topology P.charted P.smooth
        (sourceOpen (I := I) Φ k) σj ⟨z, hps⟩
    have hV0 : V 0 (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σi z := by
      simpa only [V, Matrix.cons_val_zero] using hViz
    have hV1 : V 1 (⟨z, hps⟩ : SourceDomain (I := I) Φ k) = σj z := by
      simpa only [V, Matrix.cons_val_one, Matrix.cons_val_zero] using hVjz
    simp only [F, G, chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
    rw [hcorez]
    rw [gSeqExt_inner_of_mem (I := I) Φ R bf hsrc htgt k p.1 z hps
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ i z) (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) x₀ j z),
      hWone z hpW, hV0, hV1]
    simp only [one_smul, sub_self, zero_smul, add_zero]
    rw [hpi, hpj]
    exact hmetric p.1 ⟨z, hps⟩ _ _
  have hF : ContDiffAt Real (∞ : WithTop ℕ∞) F q :=
    hlocal.congr_of_eventuallyEq hFG
  exact hF

end DifferentialGeometry.CheegerGromovCompactness
