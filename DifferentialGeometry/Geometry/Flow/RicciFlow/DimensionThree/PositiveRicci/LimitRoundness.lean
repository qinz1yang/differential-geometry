import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Blowup
import Mathlib.Analysis.InnerProductSpace.PiL2
import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Topology.ThreeManifold

set_option autoImplicit false

noncomputable section

universe u

namespace DifferentialGeometry.PDE.RicciFlow
namespace HamiltonPositiveRicci

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem limit_base_scalar_one
    {g0 : SmoothRiemannianMetric I M}
    (P : HamiltonFiniteTimeFlow (I := I) (M := M) g0)
    (Q : HamiltonBlowup M)
    (hsel : hamiltonBlowupPointSelection (I := I) P Q)
    {L : HamiltonCGHLimit (I := I) M}
    (hconv : hamiltonLimitBaseScalarConvergence (I := I) P Q L) :
    limitBaseScalarOne (I := I) L := by
  classical
  let : TopologicalSpace L.N := L.topology
  let : ChartedSpace H L.N := L.charted
  let : IsManifold I ∞ L.N := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  let : SigmaCompactSpace L.N := L.sigmaCompact
  let : T2Space L.N := L.t2
  rcases hsel with ⟨_hscale, _htime, _htimeMem, _hprod, hbase, _hscalarMax⟩
  let f : Nat -> Real :=
    fun k : Nat =>
      hamiltonRescaledScalar (I := I) P Q (L.subseq k) 0 (Q.point (L.subseq k))
  have hconv' : Filter.Tendsto f Filter.atTop
      (nhds (L.S.scalar 0 L.basepoint)) := by
    simpa [hamiltonLimitBaseScalarConvergence, f] using hconv
  have hconst : Filter.Tendsto f Filter.atTop (nhds (1 : Real)) := by
    have hf : f = fun _ : Nat => (1 : Real) := by
      funext k
      exact hbase (L.subseq k)
    rw [hf]
    exact (tendsto_const_nhds : Filter.Tendsto
      (fun _ : Nat => (1 : Real)) Filter.atTop (nhds (1 : Real)))
  have heq : L.S.scalar 0 L.basepoint = 1 :=
    tendsto_nhds_unique hconv' hconst
  simpa [limitBaseScalarOne] using heq

omit [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [T2Space M] in
theorem tracefree_zero_of_decay
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    {t : Real}
    (hdecay : limitTracefreeRicciDecayAt (I := I) L t) :
    limitTracefreeRicciZeroAt (I := I) L t := by
  classical
  let : TopologicalSpace L.N := L.topology
  let : ChartedSpace H L.N := L.charted
  let : IsManifold I ∞ L.N := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  let : SigmaCompactSpace L.N := L.sigmaCompact
  let : T2Space L.N := L.t2
  intro x
  let q : Real :=
    DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq L.S.scalar
      (DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S) t x
  have hnonneg : 0 <= q := by
    have hdimT :
        forall (_t : Real) (y : L.N),
          Module.finrank Real (TangentSpace I y) = 3 := by
      intro _ y
      rw [show Module.finrank Real (TangentSpace I y) = Module.finrank Real E from rfl]
      exact hdim
    simpa [q] using
      (DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_nonneg (I := I) (M := L.N) L.S hdimT t x)
  have hle0 : q <= 0 := by
    have hforall : forall ε : Real, 0 < ε -> q <= 0 + ε := by
      intro ε hε
      simpa [q] using hdecay x ε hε
    exact le_of_forall_pos_le_add hforall
  simpa [q] using le_antisymm hle0 hnonneg

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
theorem limit_einstein_of_tracefree_ricci_zero
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    {t0 : Real} (htf : limitTracefreeRicciZeroAt (I := I) L t0) :
    limitEinsteinAt (I := I) L t0 := by
  classical
  let : TopologicalSpace L.N := L.topology
  let : ChartedSpace H L.N := L.charted
  let : IsManifold I ∞ L.N := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  let : SigmaCompactSpace L.N := L.sigmaCompact
  let : T2Space L.N := L.t2
  intro x v w
  let g := L.S.base.metric t0
  let Ric := L.S.ricciAt t0 x
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I) (M := L.N) Ric :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g Ric hdimT
    hsym with
    ⟨basis, l1, l2, l3, horth, hdiag⟩
  have hscalarTrace :=
    DifferentialGeometry.PDE.RicciFlow.scalarTrace_delta (I := I) (M := L.N) g Ric horth
  have hscalar :
      L.S.scalar t0 x = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
    calc
      L.S.scalar t0 x =
          DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (M := L.N)
            (L.S.family.metric t0) (L.S.ricciAt t0 x) :=
            DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar_eq_metricTrace (I := I) (M := L.N)
              L.S t0 x
      _ = DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) (M := L.N) g
        Ric := by
            rfl
      _ = DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3 l1 l2 l3 := by
            exact DifferentialGeometry.PDE.RicciFlow.scalar_eq_diag (I := I) hscalarTrace hdiag
  have hinv :
      Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
        DifferentialGeometry.Geometry.Curvature.delta3 :=
    DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (M := L.N) g basis horth
  have hnorm :
      DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S t0 x =
        DifferentialGeometry.PDE.RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
    calc
      DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I) L.S t0 x =
          Tensor0SBundle.normSq0S (I := I) (M := L.N) g x 2 Ric := by
            rfl
      _ = DifferentialGeometry.PDE.RicciFlow.ricciNormAt (I := I) (M := L.N) Ric basis := by
            exact (DifferentialGeometry.PDE.RicciFlow.ricciNorm_inner (I := I) (M := L.N)
              g Ric basis hinv).symm
  have htf_eigen :
      DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3 l1 l2 l3 = 0 := by
    have htf_x := htf x
    rw [DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSq,
      DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqOf,
      hscalar, hnorm,
      DifferentialGeometry.PDE.RicciFlow.ricciNormAt_diag (I := I) (M := L.N) hdiag] at htf_x
    simpa [DifferentialGeometry.PDE.RicciFlow.traceFreeRicciNormSqAt,
      DifferentialGeometry.PDE.RicciFlow.trace_free_ricci_norm_sq_eigenvalues] using htf_x
  have heq :=
    (DifferentialGeometry.Geometry.Curvature.tracefreeRicciEigenNormSq3_eq_zero_iff l1 l2 l3).1
      htf_eigen
  rcases heq with ⟨h12, h23⟩
  have hscalar_l1 : L.S.scalar t0 x / 3 = l1 := by
    rw [hscalar, h12, h23]
    unfold DifferentialGeometry.Geometry.Curvature.ricciEigenScalar3
    ring
  let T := DifferentialGeometry.Geometry.Curvature.ricciEndAt (I := I) (M := L.N) g Ric
  rcases DifferentialGeometry.PDE.RicciFlow.ricciEnd_diagVec (I := I) (M := L.N) g
      (Ric := Ric) horth hdiag with
    ⟨hT0, hT1, hT2⟩
  have hT_basis : forall i : Fin 3, T (basis i) = l1 • basis i := by
    intro i
    fin_cases i
    · simpa [T] using hT0
    · simpa [T, h12] using hT1
    · simpa [T, h12, h23] using hT2
  have hT_all : T v = l1 • v := by
    calc
      T v = T (∑ i : Fin 3, basis.repr v i • basis i) := by
        rw [basis.sum_repr]
      _ = ∑ i : Fin 3, T (basis.repr v i • basis i) := by
        exact map_sum T (fun i : Fin 3 => basis.repr v i • basis i) Finset.univ
      _ = ∑ i : Fin 3, basis.repr v i • T (basis i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp
      _ = ∑ i : Fin 3, basis.repr v i • (l1 • basis i) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hT_basis i]
      _ = l1 • (∑ i : Fin 3, basis.repr v i • basis i) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp [smul_smul, mul_comm]
      _ = l1 • v := by
        rw [basis.sum_repr]
  calc
    L.S.ricciAt t0 x (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
        g.inner x (T v) w := by
          exact (DifferentialGeometry.Geometry.Curvature.ricciEnd_inner (I := I) (M := L.N) g Ric v
            w).symm
    _ = g.inner x (l1 • v) w := by rw [hT_all]
    _ = l1 * g.inner x v w := by simp
    _ = (L.S.scalar t0 x / 3) * (L.S.base.metric t0).inner x v w := by
          rw [hscalar_l1]

omit [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] in
theorem limit_round_base
    {L : HamiltonCGHLimit (I := I) M}
    (hdim : Module.finrank Real E = 3)
    (hconn : hamiltonLimitConnected (I := I) L)
    (hbdry : hamiltonLimitBoundaryless (I := I))
    {t0 : Real}
    (hbase :
      letI : TopologicalSpace L.N := L.topology
      letI : ChartedSpace H L.N := L.charted
      letI : IsManifold I ∞ L.N := L.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
      letI : SigmaCompactSpace L.N := L.sigmaCompact
      letI : T2Space L.N := L.t2
      0 < L.S.scalar t0 L.basepoint)
    (heinstein : limitEinsteinAt (I := I) L t0) :
    limitRoundAt (I := I) L t0 := by
  classical
  let : NeZero (Module.finrank Real E) := ⟨by omega⟩
  let : TopologicalSpace L.N := L.topology
  let : ChartedSpace H L.N := L.charted
  let : IsManifold I ∞ L.N := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  let : SigmaCompactSpace L.N := L.sigmaCompact
  let : T2Space L.N := L.t2
  have : ConnectedSpace L.N := by
    simpa [hamiltonLimitConnected] using hconn
  have : I.Boundaryless := by
    simpa [hamiltonLimitBoundaryless] using hbdry
  let g : SmoothRiemannianMetric I L.N := L.S.base.metric t0
  have hEinStatic :
      ∀ y : L.N, ∀ v w : TangentSpace I y,
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) (M := L.N) g y
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v w) =
          (DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) (M := L.N) g y / 3) *
            g.inner y v w := by
    intro y v w
    have h := heinstein y v w
    simpa [g, limitEinsteinAt, DifferentialGeometry.PDE.RicciFlow.SolutionOn.ricciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.ricciAt,
        DifferentialGeometry.Geometry.Curvature.metricRicciAt,
      DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
        DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt] using h
  have hdScalar :
      ∀ x : L.N, ∀ X : TangentSpace I x,
        DifferentialGeometry.Geometry.Operator.differential1FormFun (I := I)
            (fun y : L.N =>
              DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) (M := L.N) g y)
            x (fun _ : Fin 1 => X) = 0 := by
    intro x X
    have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
      rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
      exact hdim
    have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I)
        (L.S.ricciAt t0 x) :=
      DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
    rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g
        (L.S.ricciAt t0 x) hdimT hsym with
      ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
    have hinv :
        Tensor0SBundle.MetricInverseInBasis (I := I) (M := L.N) g x basis
          DifferentialGeometry.Geometry.Curvature.delta3 :=
      DifferentialGeometry.Geometry.Curvature.orthonormal_invBasis3 (I := I) (M := L.N) g basis
        horth
    exact DifferentialGeometry.Geometry.Curvature.dScalar_zero_ein3_at (I := I) (M := L.N) g basis
      DifferentialGeometry.Geometry.Curvature.delta3 hinv hEinStatic X
  rcases DifferentialGeometry.Geometry.Curvature.metricScalar_const_of_dScalar_zero (I := I)
    (M := L.N) g
      hdScalar with
    ⟨R0, hR0_metric⟩
  have hR0_scalar : ∀ x : L.N, L.S.scalar t0 x = R0 := by
    intro x
    have hx := hR0_metric x
    simpa [g, DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar,
      DifferentialGeometry.Geometry.Curvature.metricScalarAt] using hx
  have hR0_pos : 0 < R0 := by
    rw [hR0_scalar L.basepoint] at hbase
    exact hbase
  have hRic :
      forall x : L.N, forall v : TangentSpace I x,
        (((Module.finrank Real E : Real) - 1) * (R0 / 6)) * g.inner x v v <=
          DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
            (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v) := by
    intro x v
    rw [hEinStatic x v v, hR0_metric x, hdim]
    have hcoef : (((3 : Nat) : Real) - 1) * (R0 / 6) = R0 / 3 := by
      ring
    rw [hcoef]
  refine ⟨R0 / 6, by nlinarith, hRic, R0 / 6, by nlinarith, ?_⟩
  intro x X Y
  have hdimT : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hsym : DifferentialGeometry.Geometry.Curvature.RicciSymAt (I := I)
      (L.S.ricciAt t0 x) :=
    DifferentialGeometry.PDE.RicciFlow.ricci_is_symmetric (I := I) (M := L.N) L.S t0 x
  rcases DifferentialGeometry.Geometry.Curvature.ricciEigen3 (I := I) (M := L.N) g
      (L.S.ricciAt t0 x) hdimT hsym with
    ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩
  have htrace :=
    DifferentialGeometry.PDE.RicciFlow.riemann_from_ricci_trace_data (I := I) (M := L.N) L.S
      (t := t0) (x := x) (basis := basis) horth
  have hEinCompNeg : ∀ i j : Fin 3,
      DifferentialGeometry.Geometry.Curvature.ricciCompAt (I := I) basis (-(L.S.ricciAt t0 x)) i j
        =
        ((-L.S.scalar t0 x) / 3) * DifferentialGeometry.Geometry.Curvature.delta3 i j := by
    intro i j
    have hij := heinstein x (basis i) (basis j)
    rw [DifferentialGeometry.Geometry.Curvature.ricciCompAt_apply]
    change -(L.S.ricciAt t0 x
        (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) (basis i) (basis j))) =
      ((-L.S.scalar t0 x) / 3) * DifferentialGeometry.Geometry.Curvature.delta3 i j
    rw [hij]
    rw [horth i j]
    ring
  have hRm :=
    DifferentialGeometry.Geometry.Curvature.rm04_einstein3_at (I := I) (M := L.N) htrace
      hEinCompNeg X Y
  have hscalar_x : L.S.scalar t0 x = R0 := hR0_scalar x
  calc
    DifferentialGeometry.Geometry.Curvature.metricRm04StdAt (I := I) (M := L.N) g x X Y Y X =
        L.S.base.rm04 t0 x (DifferentialGeometry.Geometry.Curvature.vec4 (I := I) X Y Y X) := by
          rfl
    _ = -((-L.S.scalar t0 x) / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := hRm
    _ = (R0 / 6) *
          (g.inner x X X * g.inner x Y Y -
            g.inner x X Y * g.inner x X Y) := by
          rw [hscalar_x]
          ring

omit [SigmaCompactSpace M] in
theorem limit_to_orig
    (hM : isClosedThreeManifold (I := I) (M := M))
    {L : HamiltonCGHLimit (I := I) M}
    {t : Real} (_ht : t ∈ L.D.carrier)
    (_hconn : hamiltonLimitConnected (I := I) L)
    (_hround : limitRoundAt (I := I) L t) :
    exists gInf : SmoothRiemannianMetric I M,
      constantPositiveSectionalCurvatureMetric (I := I) (M := M) gInf := by
  classical
  let : TopologicalSpace L.N := L.topology
  let : ChartedSpace H L.N := L.charted
  let : IsManifold I ∞ L.N := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.N := L.smooth_plus
  let : SigmaCompactSpace L.N := L.sigmaCompact
  let : T2Space L.N := L.t2
  let : T2Space (TangentBundle I L.N) := L.t2TangentBundle
  have : ConnectedSpace L.N := by
    simpa [hamiltonLimitConnected] using _hconn
  have : ConnectedSpace M := hM.2.1
  have : I.Boundaryless := hM.2.2.1
  let g : SmoothRiemannianMetric I L.N := L.S.base.metric t
  change exists K : Real, 0 < K /\
    (forall x : L.N, forall v : TangentSpace I x,
      (((Module.finrank Real E : Real) - 1) * K) * g.inner x v v <=
        DifferentialGeometry.Geometry.Curvature.metricRicciAt (I := I) g x
          (DifferentialGeometry.Geometry.Curvature.vec2 (I := I) v v)) /\
    constantPositiveSectionalCurvatureMetric (I := I) (M := L.N) g at _hround
  rcases _hround with ⟨K, hK, hRic, hsecg⟩
  have hRicBM :
      DifferentialGeometry.Geometry.Riemannian.BonnetMyers.RicciBoundedBelow
        (I := I) g (((Module.finrank Real E : Real) - 1) * K) := by
    intro x v
    rw [← DifferentialGeometry.metricRicciAt_apply_eq_ricciTensor]
    exact hRic x v
  have hcomplete :
      DifferentialGeometry.HCGCompactness.MetricComplete
        (I := I) (L.limit.atTime (I := I) t) := by
    with_unfolding_all
      exact L.limitComplete t _ht
  have hdim : 2 <= Module.finrank Real E := by
    have hdim3 : Module.finrank Real E = 3 := hM.2.2.2
    omega
  let : CompactSpace L.N :=
    DifferentialGeometry.HCGCompactness.PointedRiemannianManifold.compact_of_ricci
      (I := I) (P := L.limit.atTime (I := I) t) (by
        with_unfolding_all
          exact _hconn)
      hdim hK (by
        with_unfolding_all
          exact hRicBM) hcomplete
  let Phi := L.cgh.spatial.maps
  obtain ⟨k, hk⟩ :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.exists_source_univ
      (I := I) Phi (isCompact_univ : IsCompact (Set.univ : Set L.N))
  have hsource : Phi.source k = Set.univ := hk k le_rfl
  let j : Nat := L.cghSubseq k
  let : TopologicalSpace (L.sourceTerm j).M := (L.sourceTerm j).topology
  let : ChartedSpace H (L.sourceTerm j).M := (L.sourceTerm j).charted
  let : ConnectedSpace (L.sourceTerm j).M :=
    (L.sourceToOrig j).symm.surjective.connectedSpace (L.sourceToOrig j).symm.continuous
  have htarget : Phi.target k = Set.univ :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.target_univ
      (I := I) Phi k (isCompact_univ : IsCompact (Set.univ : Set L.N))
        inferInstance hsource
  let limitToSource : L.N ≃ₘ⟮I, I⟯ (L.sourceTerm j).M :=
    DifferentialGeometry.HCGCompactness.PointedCGHMaps.globalDiffeomorph
      (I := I) Phi k hsource htarget
  let limitToOrig : L.N ≃ₘ⟮I, I⟯ M :=
    limitToSource.trans (L.sourceToOrig j)
  rcases hsecg with ⟨c, hc, hsec⟩
  refine ⟨Diffeomorph.pullbackMetricCross g limitToOrig.symm, c, hc, fun x X Y => ?_⟩
  rw [DifferentialGeometry.Geometry.Curvature.metricRm04Std_pullbackCross
        g limitToOrig.symm x X Y Y X, hsec,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x X X,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x Y Y,
    ← Diffeomorph.pullbackMetricCross_inner g limitToOrig.symm x X Y]

end HamiltonPositiveRicci
end DifferentialGeometry.PDE.RicciFlow
