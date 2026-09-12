import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance harnackLimitTopology : TopologicalSpace F.M := F.topology
local instance harnackLimitCharted : ChartedSpace H F.M := F.charted
local instance harnackLimitSmooth : IsManifold I ∞ F.M := F.smooth
local instance harnackLimitC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide)
local instance harnackLimitSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance harnackLimitT2 : T2Space F.M := F.t2

structure KLim (kappa : ℝ) (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop where
  dimension_ge_two : 2 ≤ Module.finrank ℝ E
  kappa_pos : 0 < kappa
  carrier_eq : D.carrier = Set.Iic 0
  regular_eq : D.regular = Set.Iio 0
  connected : ConnectedSpace F.M
  complete : ∀ t ∈ D.carrier, MetricComplete (I := I) (F.atTime (I := I) t)
  nonnegativeCurvatureOperator :
    ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t
  noncollapsed : PointedFlowNoncollapsedAllScales (I := I) F kappa
  notFlat : PointedFlowNotFlat (I := I) F
  traceHarnack : ∀ t ∈ D.carrier, ∀ (x : F.M) (V : TangentSpace I x),
    0 ≤ derivWithin (fun s : ℝ => F.S.scalar s x) D.carrier t +
      2 * (F.S.base.metric t).inner x
        (gradientAt (I := I) (flowG (I := I) F.S) t (F.S.scalar t) x) V +
      2 * metricRicci (I := I) (M := F.M) (F.S.base.metric t) x (vec2 V V)

namespace KLim

variable {F} {kappa : ℝ}

theorem scalar_nonneg (hK : KLim kappa F) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    0 ≤ F.S.scalar t x := by
  have htcar : t ∈ D.carrier := by
    simpa only [hK.carrier_eq, Set.mem_Iic] using ht
  have hR : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hK.nonnegativeCurvatureOperator t htcar x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval,
      metricAlgebraicCurvatureTensorAt, tensor04StandardAt, SolutionFamily.rm04,
      metricRm04_apply] using h
  exact metricScalarAt_nonnegative_of_curvatureOperator_nonnegative
    (I := I) (F.S.base.metric t) x hR

theorem scalar_derivWithin_nonneg (hK : KLim kappa F)
    {t : ℝ} (ht : t ∈ D.carrier) (x : F.M) :
    0 ≤ derivWithin (fun s : ℝ => F.S.scalar s x) D.carrier t := by
  have htrace := hK.traceHarnack t ht x (0 : TangentSpace I x)
  have hRicZero : metricRicci (I := I) (M := F.M) (F.S.base.metric t) x
      (vec2 (0 : TangentSpace I x) 0) = 0 := by
    exact (metricRicci (I := I) (M := F.M) (F.S.base.metric t) x).map_coord_zero
      (i := 0) (by simp [vec2])
  rw [hRicZero] at htrace
  simpa using htrace

theorem scalar_deriv_nonneg (hK : KLim kappa F)
    {t : ℝ} (ht : t ∈ D.regular) (x : F.M) :
    0 ≤ deriv (fun s : ℝ => F.S.scalar s x) t := by
  have h := hK.scalar_derivWithin_nonneg (D.regular_subset ht) x
  rw [derivWithin_of_mem_nhds (D.regular_mem_nhds ht)] at h
  exact h

theorem scalar_monotoneOn (hK : KLim kappa F) (x : F.M) :
    MonotoneOn (fun t : ℝ => F.S.scalar t x) (Set.Iic 0) := by
  have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  have hcont : ContinuousOn (fun t : ℝ => F.S.scalar t x) (Set.Iic 0) := by
    have h := F.isSolution.scalarCont.comp hmap.continuousOn
      (fun t (ht : t ∈ Set.Iic (0 : ℝ)) =>
        ⟨by simpa only [hK.carrier_eq] using ht, Set.mem_univ x⟩)
    simpa only [Function.comp_def] using h
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont
  · intro t ht
    have htreg : t ∈ D.regular := by
      simpa only [hK.regular_eq, interior_Iic, Set.mem_Iio] using ht
    exact ((F.isSolution.scalarTime (K := D.carrier) (D.regular_subset htreg)
      (fun _ hs => hs) x).differentiableAt
        (D.regular_mem_nhds htreg)).differentiableWithinAt
  · intro t ht
    have htreg : t ∈ D.regular := by
      simpa only [hK.regular_eq, interior_Iic, Set.mem_Iio] using ht
    exact hK.scalar_deriv_nonneg htreg x

theorem scalar_le_terminal (hK : KLim kappa F) {t : ℝ} (ht : t ≤ 0) (x : F.M) :
    F.S.scalar t x ≤ F.S.scalar 0 x :=
  hK.scalar_monotoneOn x ht (by change (0 : ℝ) ≤ 0; exact le_rfl) ht

theorem scalarBounded_of_terminal_bound (hK : KLim kappa F) {C : ℝ}
    (hC : ∀ x : F.M, F.S.scalar 0 x ≤ C) :
    PointedFlowScalarBounded (I := I) F C := by
  intro t ht x
  have ht0 : t ≤ 0 := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht
  exact ⟨hK.scalar_nonneg ht0 x, (hK.scalar_le_terminal ht0 x).trans (hC x)⟩

theorem toIsAncientKappaSolution (hK : KLim kappa F) {C : ℝ}
    (hC : ∀ x : F.M, F.S.scalar 0 x ≤ C) : IsAncientKappaSolution kappa F where
  kappa_pos := hK.kappa_pos
  carrier_eq := hK.carrier_eq
  regular_eq := hK.regular_eq
  connected := hK.connected
  complete := hK.complete
  nonnegativeCurvatureOperator := hK.nonnegativeCurvatureOperator
  globalScalarBound := ⟨C, hK.scalarBounded_of_terminal_bound hC⟩
  noncollapsed := hK.noncollapsed
  notFlat := hK.notFlat

theorem isAncientKappaSolution_iff_terminal_bounded (hK : KLim kappa F) :
    IsAncientKappaSolution kappa F ↔ ∃ C : ℝ, ∀ x : F.M, F.S.scalar 0 x ≤ C := by
  constructor
  · intro hF
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    refine ⟨C, fun x => ?_⟩
    exact (hC 0 (by
      simpa only [hK.carrier_eq, Set.mem_Iic] using (le_rfl : (0 : ℝ) ≤ 0)) x).2
  · rintro ⟨C, hC⟩
    exact hK.toIsAncientKappaSolution hC

end KLim

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
