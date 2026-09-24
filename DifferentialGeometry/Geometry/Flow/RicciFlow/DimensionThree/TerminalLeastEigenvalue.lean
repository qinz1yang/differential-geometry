import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureUpperSupport
import DifferentialGeometry.Topology.Manifold.SmallDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Curvature.OperatorNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientLocalCubicCutoff
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.TerminalCubicBarrier

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped _root_.Manifold ContDiff _root_.Topology

section InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private theorem positive_at_terminal_of_upperSupport
    [NeZero (Module.finrank ℝ E)]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T : ℝ} (hT : 0 < T)
    (hcarrier : D.carrier = Iic T) (hregular : D.regular = Iio T)
    {u : ℝ → M → ℝ}
    (hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2) (Icc 0 T ×ˢ (univ : Set M)))
    (hunonneg : ∀ t ∈ Icc 0 T, ∀ y, 0 ≤ u t y)
    (hsupport : ∀ B ∈ Ioo 0 T, ∀ t ∈ Ioc 0 B, ∀ y,
      Nonempty (DifferentialGeometry.Analysis.Parabolic.ParabolicUpperSupportAt
        (flowG S) B (fun _ _ => 0) u t y))
    (x : M) (hux : 0 < u 0 x) : 0 < u T x := by
  have hu0 : Continuous (u 0) := by
    apply continuousOn_univ.mp
    exact hu.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y _ => ⟨⟨le_rfl, hT.le⟩, mem_univ y⟩)
  obtain ⟨K, hK, hKU, hxK, f, hf, hfx, hfout, C, ℓ, ρ, -, hℓ, hρ, hcutoff⟩ :=
    exists_ancient_local_cubic_cutoff (a := 0) S hS hcarrier hregular x
      (hu0.continuousAt.eventually (Ioi_mem_nhds hux))
  obtain ⟨ε, hε, hinit⟩ := exists_initial_cubic_barrier K hK ⟨x, hxK⟩
    hf.continuous.continuousOn hu0.continuousOn (fun y hy => hKU hy)
    (fun y _ => hunonneg 0 ⟨le_rfl, hT.le⟩ y) hfout
  have hutime : ContinuousOn (fun s => u s x) (Icc 0 T) :=
    hu.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun s hs => ⟨hs, mem_univ x⟩)
  have huend : ContinuousWithinAt (fun s => u s x) (Iio T) T := by
    have hend := hutime T ⟨hT.le, le_rfl⟩
    rw [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsLE hT] at hend
    exact hend.mono_left (nhdsWithin_mono T Iio_subset_Iic_self)
  exact (local_cubic_barrier_positive_at_terminal (flowG S) (fun _ _ => 0)
    hT hε hℓ hρ hf K hK hfout
    (hu.mono (prod_mono Ico_subset_Icc_self (subset_univ K)))
    (fun t ht => hunonneg t ⟨ht.1, ht.2.le⟩) hinit hsupport
    (fun t ht y hy => (hcutoff t ⟨ht.1.le, ht.2.le⟩ y hy).1)
    (fun t ht y hy => (hcutoff t ⟨ht.1.le, ht.2.le⟩ y hy).2)
    hfx huend).2

private theorem least_eigenvalue_pos_at_terminal_inner
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T : ℝ} (hT : 0 < T)
    (hcarrier : D.carrier = Iic T) (hregular : D.regular = Iio T)
    (hR : ∀ t ∈ Icc 0 T, ∀ x,
      (⟨metricRm04At (S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hpos : 0 < leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      ⟨S.base.rm04 0 x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric 0) x⟩) :
    0 < leastCurvatureOperatorEigenvalueAt (S.base.metric T) x
      ⟨S.base.rm04 T x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric T) x⟩ := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  let u : ℝ → M → ℝ := fun t y =>
    2 * leastCurvatureOperatorEigenvalueAt (S.base.metric t) y
      ⟨S.base.rm04 t y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) y⟩
  have hslab : Icc 0 T ⊆ D.carrier := by
    rw [hcarrier]
    exact fun _ ht => ht.2
  have hreg : Ioo 0 T ⊆ D.regular := by
    rw [hregular]
    exact fun _ ht => ht.2
  have hclosed : IsSolutionOn (S.timeRestrict (RealTimeInterval.closed 0 T hT.le)) :=
    isSolutionOn_timeRestrict hS hslab hreg
  have hu : ContinuousOn (fun p : ℝ × M => u p.1 p.2)
      (Icc 0 T ×ˢ (univ : Set M)) :=
    (continuousOn_leastCurvatureOperatorEigenvalueAt_rm04 hT
      (S.timeRestrict (RealTimeInterval.closed 0 T hT.le)) hclosed
      (fun y => (VectorBundle.finrank_eq ℝ E (TangentSpace I) y).trans hdim)).const_mul 2
  have hunonneg : ∀ t ∈ Icc 0 T, ∀ y, 0 ≤ u t y := by
    intro t ht y
    apply mul_nonneg (by norm_num)
    exact (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      (S.base.metric t) ((VectorBundle.finrank_eq ℝ E (TangentSpace I) y).trans hdim)).mpr
      (hR t ht y)
  have hsupport : ∀ B ∈ Ioo 0 T, ∀ t ∈ Ioc 0 B, ∀ y,
      Nonempty (DifferentialGeometry.Analysis.Parabolic.ParabolicUpperSupportAt
        (flowG S) B (fun _ _ => 0) u t y) := by
    intro B hB t ht y
    exact nonempty_parabolicUpperSupportAt_twice_leastCurvatureOperatorEigenvalueAt
      S hS hdim hB.1 ⟨ht.1.le, ht.2⟩
      (by rw [hregular]; exact ht.2.trans_lt hB.2) y
      (hR t ⟨ht.1.le, ht.2.trans hB.2.le⟩ y)
  have hterminal := positive_at_terminal_of_upperSupport S hS hT hcarrier hregular
    hu hunonneg hsupport x (mul_pos (by norm_num) hpos)
  exact pos_of_mul_pos_right hterminal (by norm_num : (0 : ℝ) ≤ 2)

end InnerProductModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem leastCurvatureOperatorEigenvalueAt_pos_at_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T : ℝ} (hT : 0 < T)
    (hcarrier : D.carrier = Iic T) (hregular : D.regular = Iio T)
    (hR : ∀ t ∈ Icc 0 T, ∀ x,
      (⟨metricRm04At (S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (x : M)
    (hpos : 0 < leastCurvatureOperatorEigenvalueAt (S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric 0) x)) :
    0 < leastCurvatureOperatorEigenvalueAt (S.base.metric T) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric T) x) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let L : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := ContinuousLinearEquiv.ofFinrankEq (by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using hdim)
  obtain ⟨P, htop, hcs, hman, ⟨e⟩⟩ :=
    DifferentialGeometry.Manifold.exists_small_diffeomorph (M := M) (I := I) L
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ : T2Space P := e.toHomeomorph.isEmbedding.t2Space
  let _ : SigmaCompactSpace P := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let U := S.pullback e
  have hU : IsSolutionOn U := hS.pullback S e
  have hdimP : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have heigen (t : ℝ) (y : P) :
      leastCurvatureOperatorEigenvalueAt (U.base.metric t) y
        (metricAlgebraicCurvatureTensorAt (U.base.metric t) y) =
      leastCurvatureOperatorEigenvalueAt (S.base.metric t) (e y)
        (metricAlgebraicCurvatureTensorAt (S.base.metric t) (e y)) :=
    leastCurvatureOperatorEigenvalueAt_pullbackMetricCross (S.base.metric t) e y
  have hRU : ∀ t ∈ Icc 0 T, ∀ y : P,
      (⟨metricRm04At (U.base.metric t) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (U.base.metric t) y⟩ :
          algebraicCurvatureTensorSubmodule (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
            (M := P) y) ∈ algebraicCurvatureOperatorNonnegativeCone := by
    intro t ht y
    change metricAlgebraicCurvatureTensorAt (U.base.metric t) y ∈
      algebraicCurvatureOperatorNonnegativeCone
    apply (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      (U.base.metric t) hdimP).mp
    rw [heigen]
    exact (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      (S.base.metric t) hdim).mpr (hR t ht (e y))
  have hposU : 0 < leastCurvatureOperatorEigenvalueAt (U.base.metric 0) (e.symm x)
      (metricAlgebraicCurvatureTensorAt (U.base.metric 0) (e.symm x)) := by
    rw [heigen, e.apply_symm_apply]
    exact hpos
  have hp := least_eigenvalue_pos_at_terminal_inner U hU hdimP hT hcarrier hregular
    hRU (e.symm x) hposU
  change 0 < leastCurvatureOperatorEigenvalueAt (U.base.metric T) (e.symm x)
    (metricAlgebraicCurvatureTensorAt (U.base.metric T) (e.symm x)) at hp
  rw [heigen, e.apply_symm_apply] at hp
  exact hp

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
