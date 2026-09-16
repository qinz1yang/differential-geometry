import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MaximalPointSlabLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.ScalarPositive
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.DifferentialGeometry.Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
variable (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance ancientLimitScalarBarrierTopology : TopologicalSpace F.M := F.topology
local instance ancientLimitScalarBarrierCharted : ChartedSpace H F.M := F.charted
local instance ancientLimitScalarBarrierSmooth : IsManifold I ∞ F.M := F.smooth
local instance ancientLimitScalarBarrierC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := ∞) (by decide : (1 : WithTop ℕ∞) ≤ ∞)
local instance ancientLimitScalarBarrierSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact
local instance ancientLimitScalarBarrierT2 : T2Space F.M := F.t2
local instance ancientLimitScalarBarrierTangentT2 : T2Space (TangentBundle I F.M) :=
  F.t2TangentBundle

variable {kappa : Real}

theorem ancientKappa_scalarLowerBarrier_lt (hdim : Module.finrank Real E = 3)
    (hF : IsAncientKappaSolution kappa F) {c : Real} (hc : 0 < c) {t : Real}
    (ht : t ∈ D.carrier) (htc : -c ≤ t) (x : F.M) :
    scalarLowerBarrier 3 (-3 / (2 * c)) t < F.S.scalar t x := by
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, Set.mem_Iic] using ht
  have hpos : 0 < F.S.scalar t x := ancientKappa_scalar_pos F hdim hF ht0 x
  refine lt_of_le_of_lt ?_ hpos
  have hden : 1 - (2 / 3 : Real) * (-3 / (2 * c)) * t = (t + c) / c := by
    field_simp
    ring
  rw [scalarLowerBarrier, hden]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by linarith))
    (div_nonneg (by linarith) hc.le)

theorem ancientKappa_scalarBase_lowerBarrier_lt (hdim : Module.finrank Real E = 3)
    (hF : IsAncientKappaSolution kappa F) {c : Real} (hc : 0 < c) (x : F.M) :
    -3 / (2 * c) < F.S.scalar 0 x := by
  have h0 : (0 : Real) ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact Set.mem_Iic.mpr le_rfl
  simpa only [scalarLowerBarrier_zero] using
    ancientKappa_scalarLowerBarrier_lt F hdim hF hc h0 (by linarith) x

theorem ancientKappa_scalar_strictLowerBound_of_compact (hdim : Module.finrank Real E = 3)
    (hF : IsAncientKappaSolution kappa F) [CompactSpace F.M] [Nonempty F.M] :
    ∃ eps : Real, 0 < eps ∧ ∀ x : F.M, eps ≤ F.S.scalar 0 x := by
  have h0 : (0 : Real) ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact Set.mem_Iic.mpr le_rfl
  have hcont : ContinuousOn (fun x : F.M => F.S.scalar 0 x) (Set.univ : Set F.M) :=
    (DifferentialGeometry.Geometry.Curvature.metricScalar_smooth (I := I) (M := F.M)
      (F.S.base.metric 0)).continuous.continuousOn
  obtain ⟨x0, -, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set F.M)).exists_isMinOn Set.univ_nonempty hcont
  exact ⟨F.S.scalar 0 x0, ancientKappa_scalar_pos F hdim hF le_rfl x0,
    fun x => hmin (Set.mem_univ x)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (ancientKappa_scalar_pos ancientKappa_scalarLowerBarrier_lt
    ancientKappa_scalarBase_lowerBarrier_lt)
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

theorem scalarLowerBarrier_strict_of_maximalPointSlabLimitSelection
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (o : TangentOrientationSection M) {kappa : Real}
    (h : MaximalPointSlabLimitSelection.{u} hT S hS o kappa)
    {theta : Real} (htheta : 0 < theta)
    (x : Nat → M) (t : Nat → Real) (htpos : ∀ i, 0 < t i)
    (htmem0 : ∀ i, t i ∈ Set.Ico (0 : Real) T)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i))
    (htlower : ∀ i, theta ≤ t i)
    (hscalar : Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop)
    (hmax : ∀ i s, s ∈ Set.Icc 0 (t i) → ∀ y : M,
      S.scalar s y ≤ S.scalar (t i) (x i))
    {c : Real} (hc : 0 < c) :
    ∃ (L : PointedFlowData.{u, 0, 0} (I := I3) ancientTimeInterval) (phi : Nat → Nat),
      StrictMono phi ∧ IsAncientKappaSolution (I := I3) kappa L ∧
      PointedFlowScalarAtBase (I := I3) L 1 ∧
      (∀ t' : Real, t' ∈ ancientTimeInterval.carrier → ∀ y : L.M,
        0 < L.S.scalar t' y) ∧
      (∀ t' : Real, t' ∈ ancientTimeInterval.carrier → -c ≤ t' → ∀ y : L.M,
        scalarLowerBarrier 3 (-3 / (2 * c)) t' < L.S.scalar t' y) ∧
      -3 / (2 * c) < L.S.scalar 0 L.basepoint := by
  have hdim : Module.finrank Real ThreeSpace = 3 := by simp [ThreeSpace]
  obtain ⟨L, phi, _, hphi, hanc, hconvT, _, _, _⟩ :=
    h theta htheta x t htpos htmem0 hpos htlower hscalar hmax
  obtain ⟨F0, hF0⟩ := hconvT 0 le_rfl
  have hbase : PointedFlowScalarAtBase (I := I3) L 1 :=
    pointedFlowScalarAtBase_of_metricConvergence_at_zero hT S hS x t htmem0 htpos hpos L phi F0 hF0
  refine ⟨L, phi, hphi, hanc, hbase, ?_, ?_, ?_⟩
  · intro t' ht' y
    exact ancientKappa_scalar_pos L hdim hanc
      (by simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using ht') y
  · exact fun t' ht' => ancientKappa_scalarLowerBarrier_lt L hdim hanc hc ht'
  · exact ancientKappa_scalarBase_lowerBarrier_lt L hdim hanc hc L.basepoint

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
