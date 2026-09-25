import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundBackwardPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRoundEvolution


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance roundFlowTopology : TopologicalSpace F.M := F.topology
local instance roundFlowCharted : ChartedSpace H F.M := F.charted
local instance roundFlowSmooth : IsManifold I ∞ F.M := F.smooth
local instance roundFlowC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance roundFlowT2 : T2Space F.M := F.t2
local instance roundFlowSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance roundFlowLimitTopology : TopologicalSpace L.M := L.topology
local instance roundFlowLimitCharted : ChartedSpace H L.M := L.charted
local instance roundFlowLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance roundFlowLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
local instance roundFlowLimitT2 : T2Space L.M := L.t2
local instance roundFlowLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact


theorem ancient_roundScaling_of_round_backward_convergence
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (hcompactF : CompactSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    let T := 3 / (2 * F.S.scalar 0 F.basepoint)
    ∃ hT : 0 < T,
      (∀ t ≤ 0, ∀ x : F.M, F.S.scalar t x = 3 / (2 * (T - t))) ∧
      (∀ (t : ℝ) (ht : t ≤ 0), F.S.family.metric t =
        scaleMetric ((T - t) / T) (div_pos (by linarith) hT) (F.S.family.metric 0)) ∧
      ∀ t ≤ 0, ∀ x : F.M, ∀ X Y : TangentSpace I x,
        metricRm04StandardAt (F.S.family.metric t) x X Y Y X =
          (1 / (4 * (T - t))) * ((F.S.family.metric t).inner x X X *
            (F.S.family.metric t).inner x Y Y -
            (F.S.family.metric t).inner x X Y * (F.S.family.metric t).inner x X Y) := by
  let _ : CompactSpace F.M := hcompactF
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨rho, c, hrhoPos, hrho, hc, hcUpper, hpinch⟩ :=
    exists_backward_ricci_pinching_of_round_limit F hdim hconn tau htau hescape q hphi Phi C
      hcanonical hcompact hR hscalar hEin
  have ha : Tendsto (fun i => -rho i) atTop atBot := tendsto_neg_atTop_atBot.comp hrho
  have hinitial := fun i x v => (hpinch i x).2 v
  have hconstant := ancient_scalar_constant_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial
  have hEinstein := ancient_ricci_einstein_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial
  have hpositive (b : ℝ) (hb : b ≤ 0) (x : F.M) : 0 < F.S.scalar b x := by
    obtain ⟨i, hi⟩ := (hrho.eventually (eventually_ge_atTop (-b))).exists
    have hab : -rho i ≤ b := by linarith
    exact (hpinch i x).1.trans_le (ancient_scalar_monotone_of_spatially_constant F
      hconstant x (neg_nonpos.mpr (hrhoPos i).le) hb hab)
  obtain ⟨hT, hprofile, hmetric⟩ := ancient_einstein3_roundScaling F.S F.isSolution hdim
    hpositive hconstant hEinstein F.basepoint
  refine ⟨hT, hprofile, hmetric, fun t ht x X Y => ?_⟩
  let g := F.S.family.metric t
  obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
    ricciEigen3 g (F.S.ricciAt t x) hdim (ricci_is_symmetric F.S t x)
  have htrace := riemann_from_ricci_trace F.S (t := t) (x := x) (basis := basis) horth
  have hneg (i j : Fin 3) : ricciCompAt basis (-(F.S.ricciAt t x)) i j =
      ((-F.S.scalar t x) / 3) * delta3 i j := by
    rw [ricciCompAt_apply]
    change -(F.S.ricciAt t x (vec2 (basis i) (basis j))) = _
    rw [hEinstein t ht x (basis i) (basis j)]
    change -((F.S.scalar t x / 3) * g.inner x (basis i) (basis j)) = _
    rw [horth i j]
    ring
  have hRm := rm04_einstein3_at htrace hneg X Y
  rw [hprofile t ht x] at hRm
  calc
    _ = -(-(3 / (2 * (3 / (2 * F.S.scalar 0 F.basepoint) - t))) / 6) *
        ((F.S.family.metric t).inner x X X * (F.S.family.metric t).inner x Y Y -
          (F.S.family.metric t).inner x X Y * (F.S.family.metric t).inner x X Y) := hRm
    _ = _ := by simp only [div_mul_eq_div_div]; ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
