import DifferentialGeometry.Geometry.Metric.Family.ProductSlice
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.AncientNullRank
import DifferentialGeometry.Geometry.Metric.Product.Completeness
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.GlobalCurvatureSurface
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProductEuclidean
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.UniversalCover
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Curvature.DimensionThree.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Topology.Manifold.SmallDiffeomorph
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalSurfaceProduct
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.HarnackLimit
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalTrichotomyTopology : TopologicalSpace F.M := F.topology
local instance terminalTrichotomyCharted : ChartedSpace H F.M := F.charted
local instance terminalTrichotomySmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalTrichotomyC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance terminalTrichotomyT2 : T2Space F.M := F.t2
local instance terminalTrichotomySigma : SigmaCompactSpace F.M := F.sigmaCompact


local instance terminalTrichotomyInhabited : Inhabited F.M := ⟨F.basepoint⟩


local instance terminalTrichotomyLocallyPathConnected :
    LocallyPathConnectedSpace F.M := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H F.M


local instance terminalTrichotomySemilocallySimplyConnected :
    SemilocallySimplyConnectedSpace F.M :=
  manifold_semilocallySimplyConnectedSpace (I := I) (M := F.M)



section TerminalNullPlaneDichotomy

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) g ↔
      ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x := by
  constructor
  · intro hsec x
    rw [curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim]
    intro a b hgram
    exact hsec x a b
      (Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
        (I := I) (M := M) g x a b (by
          simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram))
  · intro hpos x a b hab
    have hgram : 0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 := by
      simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using
        Geometry.Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := I) (M := M) g x a b hab
    exact ((curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim).mp
      (hpos x) a b hgram)

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3)
    (hnonneg : ∀ x : M, metricAlgebraicCurvatureTensorAt (I := I) (M := M) g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hnot : ¬ ∀ x : M, CurvatureOperatorPositiveAt (I := I) (M := M) g x) :
    ∃ x : M, ∃ a b : TangentSpace I x,
      0 < g.inner x a a * g.inner x b b - (g.inner x a b) ^ 2 ∧
      metricRm04StandardAt (I := I) (M := M) g x a b b a = 0 := by
  push Not at hnot
  obtain ⟨x, hx⟩ := hnot
  have hplanes := (not_congr
    (curvatureOperatorPositiveAt_iff_sectional (I := I) (M := M) g x hdim)).mp hx
  push Not at hplanes
  obtain ⟨a, b, hgram, hnonpos⟩ := hplanes
  refine ⟨x, a, b, ?_, ?_⟩
  · simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram
  · have hnonneg' : 0 ≤ metricRm04StandardAt (I := I) (M := M) g x a b b a := by
      have h := mem_algebraicCurvatureOperatorNonnegativeCone.mp (hnonneg x)
        1 (fun _ : Fin 1 => 1) (fun _ : Fin 1 => a) (fun _ : Fin 1 => b)
      simpa only [algebraicCurvatureOperatorQuadraticEval, Fin.sum_univ_one, one_mul,
        metricAlgebraicCurvatureTensorAt_coe, metricRm04StandardAt] using h
    exact le_antisymm hnonpos hnonneg'

end TerminalNullPlaneDichotomy

def TerminalNullPlaneSplitting (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ∀ x : F.M, ∀ a b : TangentSpace I x,
    0 < (F.S.base.metric 0).inner x a a * (F.S.base.metric 0).inner x b b -
        ((F.S.base.metric 0).inner x a b) ^ 2 →
      metricRm04StandardAt (I := I) (M := F.M) (F.S.base.metric 0) x a b b a = 0 →
        (∀ y : F.M, F.rmNormSq (I := I) 0 y = 0) ∨
          Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0))

theorem klim_terminal_curvature_trichotomy_of_nullPlaneSplitting
    (hsplit : TerminalNullPlaneSplitting (I := I) F)
    {kappa : ℝ} (hK : KLim (I := I) kappa F) (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  by_cases hpos : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I)
    (F.S.base.metric 0)
  · exact Or.inl hpos
  · refine Or.inr ?_
    have hnot : ¬ ∀ x : F.M,
        CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
      fun h => hpos ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
        (I := I) (M := F.M) (F.S.base.metric 0) hdim).mpr h)
    have hnonneg : ∀ x : F.M,
        metricAlgebraicCurvatureTensorAt (I := I) (M := F.M) (F.S.base.metric 0) x ∈
          algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      intro x
      apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
      intro n c v w
      have h0 : (0 : ℝ) ∈ D.carrier := by
        simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)
      have h := hK.nonnegativeCurvatureOperator 0 h0 x n c v w
      simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
        tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
    obtain ⟨x, a, b, hgram, hnull⟩ :=
      exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt (I := I) (M := F.M)
        (F.S.base.metric 0) hdim hnonneg hnot
    exact hsplit x a b hgram hnull

set_option backward.isDefEq.respectTransparency false in
private theorem terminal_surface_product_of_morse_product
    (N : Type) [TopologicalSpace N]
    [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
    [IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞ N]
    [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]
    (h : SmoothRiemannianMetric 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N)
    (Phi : (N × ℝ) ≃ₘ⟮(𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
      𝓘(ℝ, ℝ), I⟯ UniversalCover F.M)
    (hproduct : Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (F.S.base.metric 0)) Phi =
        h.prod (euclideanMetric (E := ℝ)))
    (hcomplete : RiemannianMetricComplete h)
    (hscalar : ∀ y : N, 0 < metricScalarAt h y) :
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) (ULift.{u} N) :=
    DifferentialGeometry.Topology.uliftChartedSpace
      (DifferentialGeometry.Topology.Morse.MorseModel 2) N
  let _ : IsManifold 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) ∞
      (ULift.{u} N) :=
    DifferentialGeometry.Topology.isManifold_ulift
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N
  let PsiU : (ULift.{u} N) ≃ₘ⟮
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ N :=
    (DifferentialGeometry.Topology.uliftDiffeomorph
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) N).symm
  let e := (morseModelEuclideanModelEquiv 2).toHomeomorph
  let L := morseModelEuclideanModelEquiv 2
  have hcompat : ∀ y : DifferentialGeometry.Topology.Morse.MorseModel 2,
      (𝓡 2) (e y) = L (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) y) :=
    fun _ => rfl
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 2)) (ULift.{u} N) :=
    DifferentialGeometry.Manifold.chartedSpaceTransHomeomorph (M := ULift.{u} N) e
  let _ : IsManifold (𝓡 2) ∞ (ULift.{u} N) :=
    DifferentialGeometry.Manifold.isManifold_transHomeomorph (M := ULift.{u} N)
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2) (𝓡 2) e L hcompat
  let PsiM : (ULift.{u} N) ≃ₘ⟮(𝓡 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ (ULift.{u} N) :=
    DifferentialGeometry.Manifold.diffeomorphChartedSpaceTransHomeomorph
      (M := ULift.{u} N) 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)
      (𝓡 2) e L hcompat
  let PsiN : (ULift.{u} N) ≃ₘ⟮(𝓡 2),
      𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)⟯ N := PsiM.trans PsiU
  let Psi : ((ULift.{u} N) × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover F.M :=
    (PsiN.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans Phi
  let _ : ConnectedSpace (ULift.{u} N) :=
    PsiN.symm.surjective.connectedSpace PsiN.symm.continuous
  let k := Diffeomorph.pullbackMetricCross h PsiN
  have heq : Diffeomorph.pullbackMetricCross
      (UniversalCover.liftedMetric (F.S.base.metric 0)) Psi =
        k.prod (euclideanMetric (E := ℝ)) := by
    rw [show Psi = (PsiN.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)).trans Phi from rfl,
      ← Diffeomorph.pullbackMetricCross_trans, hproduct,
      Diffeomorph.pullbackMetricCross_prodCongr, Diffeomorph.pullbackMetricCross_refl]
  refine ⟨{
    S := ULift.{u} N
    h := k
    Phi := Psi
    product := ?_
    complete := RiemannianMetricComplete.pullbackCross h PsiN hcomplete
    positive := ?_ }⟩
  · intro y s v w a c
    have hp := congrArg (fun m => m.inner (y, s) (v, a) (w, c)) heq
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner] at hp
    have hf : (euclideanMetric (E := ℝ)).inner s a c = a * c := by
      change inner ℝ a c = a * c
      rw [RCLike.inner_apply, conj_trivial, mul_comm]
    rw [hf] at hp
    exact hp
  · apply hasPositiveSectionalCurvature_of_forall_metricScalarAt_pos_of_finrank_eq_two
      k (by simp)
    intro y
    change 0 < metricScalarAt (Diffeomorph.pullbackMetricCross h PsiN) y
    rw [metricScalar_cross]
    exact hscalar (PsiN y)

set_option backward.isDefEq.respectTransparency false in
private theorem terminal_surface_product_of_rank_one_on_interval
    {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3)
    {s : ℝ} (hs : s < 0)
    (hrank : ∀ t ∈ Set.Ioo s 0, ∀ x : F.M,
      Module.finrank ℝ (curvatureOperatorImageAt (F.S.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (F.S.base.metric t) x)) = 1) :
    let _ : ConnectedSpace F.M := hK.connected
    Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  let _ : ConnectedSpace F.M := hK.connected
  let _ : SecondCountableTopology H := ModelWithCorners.secondCountableTopology I
  let _ : SecondCountableTopology F.M := ChartedSpace.secondCountable_of_sigmaCompact H F.M
  let U := F.S.universalCover
  have hU : IsSolutionOn U := F.isSolution.universalCover F.S
  have hUc (t : ℝ) (ht : t ≤ 0) : RiemannianMetricComplete (U.base.metric t) :=
    F.S.universalCover_complete t
      ⟨hK.complete t (by simpa only [hK.carrier_eq, Set.mem_Iic] using ht)⟩
  let L : E ≃L[ℝ] DifferentialGeometry.Topology.Morse.MorseModel 3 :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simpa only [DifferentialGeometry.Topology.Morse.MorseModel,
        Module.finrank_fin_fun] using hdim)
  obtain ⟨P, htopP, hcsP, hmanP, ⟨e⟩⟩ :=
    DifferentialGeometry.Manifold.exists_small_diffeomorph
      (M := UniversalCover F.M) (I := I) L
  let _ := htopP
  let _ := hcsP
  let _ := hmanP
  let _ : T2Space P := e.toHomeomorph.isEmbedding.t2Space
  let _ : SigmaCompactSpace P := e.toHomeomorph.isClosedEmbedding.sigmaCompactSpace
  let _ : SimplyConnectedSpace P := e.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  let V := U.pullback e
  have hV : IsSolutionOn V := hU.pullback U e
  have hVc (t : ℝ) (ht : t ≤ 0) : RiemannianMetricComplete (V.base.metric t) :=
    RiemannianMetricComplete.pullbackCross (U.base.metric t) e (hUc t ht)
  have hdimP : Module.finrank ℝ (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hVR (t : ℝ) (ht : t < 0) (x : P) :
      metricAlgebraicCurvatureTensorAt (V.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    exact curvatureOperator_nonnegative_of_complete_ancient V hV
      (fun r hr => by rw [hK.carrier_eq]; exact hr.trans ht.le)
      (fun r hr => by rw [hK.regular_eq]; exact hr.trans ht)
      (fun r hr => hVc r (hr.trans ht.le)) hdimP x
  have hrV (t : ℝ) (ht : t ∈ Set.Ioo s 0) (x : P) :
      Module.finrank ℝ (curvatureOperatorImageAt (V.base.metric t) x
        (metricAlgebraicCurvatureTensorAt (V.base.metric t) x)) = 1 := by
    change Module.finrank ℝ (curvatureOperatorImageAt (V.base.metric t) x
      ⟨metricRm04At (V.base.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (V.base.metric t) x⟩) = 1
    rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank
      _ _ hdimP]
    change DimensionThree.metricCurvatureOperatorRankAt
      (Diffeomorph.pullbackMetricCross (U.base.metric t) e) x hdimP = 1
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      DimensionThree.metricCurvatureOperatorRankAt_localPull _ _ _ _ hdimP hdim,
      metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
    exact (UniversalCover.curvatureOperatorImageAt_finrank_liftedMetric
      (F.S.base.metric t) (e x) hdim).trans (hrank t ht (UniversalCover.proj (e x)))
  have hm : s / 2 ∈ Set.Ioo s (0 : ℝ) := ⟨by linarith, by linarith⟩
  obtain ⟨N, htop, hcs, hman, ht2, hσ, h, Phi₀, hconn, _, _, hprod₀,
      _, _, hpositive, _⟩ :=
    exists_positive_surface_global_product_of_curvatureOperatorImage_rank_eq_one
      V hV isOpen_Iio (by rw [hK.regular_eq]) Set.ordConnected_Ioo
      (fun _ ht => ht.2) hm (hVc _ hm.2.le) hVR hrV
  let _ := htop
  let _ := hcs
  let _ := hman
  let _ := ht2
  let _ := hσ
  let _ : ConnectedSpace N := hconn
  let Phi := Phi₀.trans e
  let W := U.pullback Phi
  have hW : IsSolutionOn W := hU.pullback U Phi
  let g := fun t => (W.base.metric t).sliceFst (0 : ℝ)
  have hproduct (t : ℝ) (ht : t ∈ Set.Ioo s 0) :
      W.base.metric t = (h t).prod (euclideanMetric (E := ℝ)) := by
    change Diffeomorph.pullbackMetricCross (U.base.metric t) (Phi₀.trans e) = _
    rw [← Diffeomorph.pullbackMetricCross_trans]
    exact hprod₀ t ht
  have hslice (t : ℝ) (ht : t ∈ Set.Ioo s 0) : g t = h t := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    change ((W.base.metric t).sliceFst (0 : ℝ)).inner y v w = _
    rw [SmoothRiemannianMetric.sliceFst_inner, hproduct t ht,
      SmoothRiemannianMetric.prod_inner]
    simp
  have hprod (t : ℝ) (ht : t ∈ Set.Ioo s 0) :
      W.base.metric t = (g t).prod (euclideanMetric (E := ℝ)) := by
    rw [hslice t ht]
    exact hproduct t ht
  have hprod0 : W.base.metric 0 = (g 0).prod (euclideanMetric (E := ℝ)) := by
    apply hW.smoothMetric.eq_sliceFst_prod_at_terminal_of_eventually
      (by rw [hK.carrier_eq]; exact Set.mem_Iic.mpr le_rfl)
      (by
        rw [hK.carrier_eq]
        exact Filter.mem_of_superset self_mem_nhdsWithin fun _ ht => Set.mem_Iic.mpr ht.le)
      (euclideanMetric (E := ℝ)) (0 : ℝ)
    filter_upwards [Ioo_mem_nhdsLT hs] with t ht
    exact hprod t ht
  have hgc : RiemannianMetricComplete (g 0) := by
    have hc : RiemannianMetricComplete (W.base.metric 0) :=
      RiemannianMetricComplete.pullbackCross (U.base.metric 0) Phi (hUc 0 le_rfl)
    rw [hprod0] at hc
    exact hc.fst_of_prod (0 : ℝ)
  have hscalar (t : ℝ) (ht : W.base.metric t = (g t).prod (euclideanMetric (E := ℝ)))
      (y : N) : metricScalarAt (g t) y =
        F.S.scalar t (UniversalCover.proj (Phi (y, 0))) := by
    have hc := metricScalar_cross (U.base.metric t) Phi (y, 0)
    change metricScalarAt (W.base.metric t) (y, 0) = _ at hc
    rw [ht, metricScalarAt_productMetric,
      metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hc
    exact hc.trans (F.S.universalCover_scalar t (Phi (y, 0)))
  have hpositive0 (y : N) : 0 < metricScalarAt (g 0) y := by
    rw [hscalar 0 hprod0]
    have hp : 0 < metricScalarAt (g (s / 2)) y := by
      rw [hslice _ hm]
      exact hpositive _ hm y
    rw [hscalar _ (hprod _ hm)] at hp
    exact hp.trans_le (hK.scalar_le_terminal hm.2.le _)
  exact terminal_surface_product_of_morse_product F N (g 0) Phi
    hprod0 hgc hpositive0

theorem klim_terminal_curvature_trichotomy {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    DifferentialGeometry.Geometry.HasPositiveSectionalCurvature (I := I) (F.S.base.metric 0) ∨
      (∀ x : F.M, F.rmNormSq (I := I) 0 x = 0) ∨
      Nonempty (TerminalSurfaceProduct (I := I) (F.S.base.metric 0)) := by
  let _ : ConnectedSpace F.M := hK.connected
  by_cases hpos : DifferentialGeometry.Geometry.HasPositiveSectionalCurvature
      (I := I) (F.S.base.metric 0)
  · exact Or.inl hpos
  have hR : ∀ t ≤ 0, ∀ x : F.M,
      metricAlgebraicCurvatureTensorAt (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := by
    intro t ht x
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have htcar : t ∈ D.carrier := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht
    have h := hK.nonnegativeCurvatureOperator t htcar x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hnot : ¬ ∀ x : F.M,
      CurvatureOperatorPositiveAt (I := I) (M := F.M) (F.S.base.metric 0) x :=
    fun h => hpos ((hasPositiveSectionalCurvature_iff_forall_curvatureOperatorPositiveAt
      (I := I) (M := F.M) (F.S.base.metric 0) hdim).mpr h)
  obtain ⟨x, a, b, hgram, hnull⟩ :=
    exists_nullPlane_of_not_forall_curvatureOperatorPositiveAt
      (F.S.base.metric 0) hdim (hR 0 le_rfl) hnot
  have hpair : LinearIndependent ℝ ![a, b] :=
    Geometry.Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      (F.S.base.metric 0) x a b
      (by simpa only [Geometry.Riemannian.sectionalCurvatureDenominator_def] using hgram)
  have hzero : leastCurvatureOperatorEigenvalueAt (F.S.base.metric 0) x
      (metricAlgebraicCurvatureTensorAt (F.S.base.metric 0) x) = 0 := by
    apply DimensionThree.leastCurvatureOperatorEigenvalueAt_eq_zero_of_sectionalCurvature_eq_zero
        (F.S.base.metric 0) x hdim (hR 0 le_rfl x) a b hpair
    exact Geometry.Riemannian.sectionalCurvature_eq_zero_of_metricRm04At_vec4_eq_zero
      (F.S.base.metric 0) x a b hnull
  have hnotflat : ∃ t ≤ (0 : ℝ), ∃ y : F.M, metricRm04At (F.S.base.metric t) y ≠ 0 := by
    obtain ⟨t, ht, y, hy⟩ := hK.notFlat
    refine ⟨t, by simpa only [hK.carrier_eq, Set.mem_Iic] using ht, y, ?_⟩
    intro hz
    apply hy
    change DifferentialGeometry.Tensor0SBundle.normSq0S (F.S.base.metric t) y 4
      (metricRm04At (F.S.base.metric t) y) = 0
    rw [hz]
    simp [DifferentialGeometry.Tensor0SBundle.normSq0S,
      DifferentialGeometry.Tensor0SBundle.inner0S]
  obtain ⟨s, hs, hrank⟩ :=
    exists_curvatureOperatorImageAt_finrank_eq_one_on_terminal_interval
      F.S F.isSolution hdim hK.carrier_eq hK.regular_eq hR hnotflat x hzero
  exact Or.inr (Or.inr (terminal_surface_product_of_rank_one_on_interval F hK hdim hs hrank))

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
