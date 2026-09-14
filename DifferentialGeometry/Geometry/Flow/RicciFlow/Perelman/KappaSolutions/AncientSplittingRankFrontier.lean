import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientSplittingNegativeTime
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalCurvatureTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Kernel

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold ContDiff

universe u uE uH

section AncientSplitting

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance ancientSplittingRankFrontierTopology : TopologicalSpace F.M := F.topology
local instance ancientSplittingRankFrontierCharted : ChartedSpace H F.M := F.charted
local instance ancientSplittingRankFrontierSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientSplittingRankFrontierC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientSplittingRankFrontierC2 : IsManifold I 2 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance ancientSplittingRankFrontierT2 : T2Space F.M := F.t2
local instance ancientSplittingRankFrontierSigma : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientSplittingRankFrontierTangentT2 :
    T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance ancientSplittingRankFrontierInhabited : Inhabited F.M := ⟨F.basepoint⟩

local instance ancientSplittingRankFrontierLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M

local instance ancientSplittingRankFrontierSemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)

def ancientCurvatureOperatorImageRank (t : ℝ) (x : F.M) : ℕ :=
  Module.finrank ℝ
    (curvatureOperatorImageAt (I := I) (F.S.base.metric t) x
      ⟨metricRm04At (I := I) (F.S.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) (F.S.base.metric t) x⟩)

def AncientCurvatureOperatorConstantRank (q : ℕ) : Prop :=
  ∀ t : ℝ, t ≤ 0 → ∀ x : F.M, ancientCurvatureOperatorImageRank (I := I) F t x = q

def AncientCurvatureOperatorKernelParallel : Prop :=
  ∀ t : ℝ, t ≤ 0 →
    IsParallelContinuousAlternatingSubmoduleFamily (F.S.base.metric t)
      (fun x : F.M =>
        curvatureOperatorKernelAt (I := I) (F.S.base.metric t) x
          ⟨metricRm04At (I := I) (F.S.base.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule
              (I := I) (F.S.base.metric t) x⟩)

def AncientCurvatureOperatorConstantRankParallelKernel : Prop :=
  ∃ q : ℕ, (q = 0 ∨ q = 1) ∧
    AncientCurvatureOperatorConstantRank (I := I) F q ∧
    AncientCurvatureOperatorKernelParallel (I := I) F

def AncientNullPlaneSplittingFrontier : Prop :=
  AncientCurvatureOperatorConstantRankParallelKernel (I := I) F ∧
    NegativeTimeUniversalCoverSplitting (I := I) F

open DifferentialGeometry.Geometry.Curvature.DimensionThree in
omit [I.Boundaryless] in
theorem scalar_pos_at_zero_of_constantRank_one
    (hdim : Module.finrank ℝ E = 3)
    (hcurvature : ∀ t : ℝ, t ≤ 0 →
      PointedFlowNonnegativeCurvatureOperator (I := I) F t)
    (hrank : AncientCurvatureOperatorConstantRank (I := I) F 1) :
    ∀ x : F.M, 0 < F.S.scalar 0 x := by
  intro x
  have hcone : metricAlgebraicCurvatureTensorAt (I := I) (M := F.M)
      (F.S.base.metric 0) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hcurvature 0 le_rfl x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  exact metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
    (I := I) hdim (F.S.base.metric 0) x hcone (hrank 0 le_rfl x)

theorem ancient_fixed_universal_cover_product_of_null_plane_of_frontier
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hfrontier : AncientNullPlaneSplittingFrontier (I := I) F) :
    let _ : ConnectedSpace F.M := hconnected
    ∃ G : PointedFlowData.{u, 0, 0} (I := 𝓡 2) ancientTimeInterval,
      let _ : TopologicalSpace G.M := G.topology
      let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
      let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
      let _ : IsManifold (𝓡 2) 1 G.M :=
        IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
      let _ : T2Space G.M := G.t2
      let _ : SigmaCompactSpace G.M := G.sigmaCompact
      ConnectedSpace G.M ∧ SimplyConnectedSpace G.M ∧
      (∀ t : ℝ, t ≤ 0 → MetricComplete (I := 𝓡 2) (G.atTime t)) ∧
      (∀ t : ℝ, t ≤ 0 → ∀ y : G.M, 0 < G.S.scalar t y) ∧
      ∃ Phi : (G.M × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M,
        ∀ (t : ℝ), t ≤ 0 → ∀ (y : G.M) (s : ℝ)
          (v w : TangentSpace (𝓡 2) y) (a c : ℝ),
          (UniversalCover.liftedMetric (I := I) (F.S.family.metric t)).inner (Phi (y, s))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (v, a))
              (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Phi (y, s) (w, c)) =
            (G.S.family.metric t).inner y v w + a * c :=
  ancient_fixed_universal_cover_product_of_negative_time_splitting F hconnected hcomplete
    hfrontier.2

open DifferentialGeometry.Geometry.Riemannian in
theorem nonempty_terminalSurfaceProduct_of_frontier
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hfrontier : AncientNullPlaneSplittingFrontier (I := I) F) :
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  let _ : ConnectedSpace F.M := hconnected
  obtain ⟨G, hG⟩ :=
    ancient_fixed_universal_cover_product_of_null_plane_of_frontier F hconnected hcomplete
      hfrontier
  let _ : TopologicalSpace G.M := G.topology
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) G.M := G.charted
  let _ : IsManifold (𝓡 2) ∞ G.M := G.smooth
  let _ : IsManifold (𝓡 2) 1 G.M :=
    IsManifold.of_le (I := 𝓡 2) (M := G.M) (n := ∞) (by decide)
  let _ : T2Space G.M := G.t2
  let _ : SigmaCompactSpace G.M := G.sigmaCompact
  obtain ⟨hconnG, -, hcompleteG, hscalarG, Phi, hprod⟩ := hG
  have hdim2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  refine ⟨{
    S := G.M
    topology := G.topology
    charted := G.charted
    smooth := G.smooth
    t2 := G.t2
    sigmaCompact := G.sigmaCompact
    connected := hconnG
    h := G.S.family.metric 0
    Phi := Phi
    product := fun y s v w a c => hprod 0 le_rfl y s v w a c
    complete := ⟨hcompleteG 0 le_rfl⟩
    positive :=
      hasPositiveSectionalCurvature_of_forall_metricScalarAt_pos_of_finrank_eq_two
        (G.S.family.metric 0) hdim2 (fun y => hscalarG 0 le_rfl y) }⟩

theorem terminalNullPlaneSplitting_of_frontier
    (hconnected : ConnectedSpace F.M)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (I := I) (F.atTime t))
    (hfrontier : AncientNullPlaneSplittingFrontier (I := I) F) :
    TerminalNullPlaneSplitting (I := I) F :=
  fun _ _ _ _ _ =>
    Or.inr (nonempty_terminalSurfaceProduct_of_frontier F hconnected hcomplete hfrontier)

end AncientSplitting

section PointwiseInsufficiency

private def degenerateCurvatureOperatorFamily (t : ℝ) :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := fun i => (if i = 0 then 1 else t) * x i
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

private theorem degenerateCurvatureOperatorFamily_nonneg (t : ℝ) (ht : 0 ≤ t)
    (x : Fin 3 → ℝ) :
    0 ≤ ∑ i, x i * (degenerateCurvatureOperatorFamily t x) i := by
  have h1 : (1 : Fin 3) ≠ 0 := by decide
  have h2 : (2 : Fin 3) ≠ 0 := by decide
  simp only [degenerateCurvatureOperatorFamily, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_three, h1, h2, if_false, if_true, one_mul]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

private theorem degenerateCurvatureOperatorFamily_ker_zero :
    (degenerateCurvatureOperatorFamily 0).ker ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  refine ⟨(fun i : Fin 3 => if i = 0 then (0 : ℝ) else 1), ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    funext i
    by_cases hi : i = 0 <;> simp [degenerateCurvatureOperatorFamily, hi]
  · intro h
    have h1 := congrFun h 1
    simp at h1

private theorem degenerateCurvatureOperatorFamily_ker_one :
    (degenerateCurvatureOperatorFamily 1).ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  funext i
  have h := congrFun (LinearMap.mem_ker.mp hx) i
  simpa [degenerateCurvatureOperatorFamily] using h

theorem exists_posSemidefinite_family_with_nonconstant_kernel :
    ∃ A : ℝ → ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin 3 → ℝ,
        0 ≤ ∑ i, x i * (A t x) i) ∧
      (A 0).ker ≠ ⊥ ∧ (A 1).ker = ⊥ :=
  ⟨degenerateCurvatureOperatorFamily,
    fun t ht x => degenerateCurvatureOperatorFamily_nonneg t ht.1 x,
    degenerateCurvatureOperatorFamily_ker_zero,
    degenerateCurvatureOperatorFamily_ker_one⟩

theorem exists_posSemidefinite_family_with_constant_kernel :
    ∃ A : ℝ → ((Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : Fin 3 → ℝ,
        0 ≤ ∑ i, x i * (A t x) i) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, (A t).ker = (A 0).ker :=
  ⟨fun _ => degenerateCurvatureOperatorFamily 0,
    fun _ _ x => degenerateCurvatureOperatorFamily_nonneg 0 le_rfl x,
    fun _ _ => rfl⟩

end PointwiseInsufficiency

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
