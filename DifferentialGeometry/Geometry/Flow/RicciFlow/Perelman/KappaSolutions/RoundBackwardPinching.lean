import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundMetricPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.RoundPinchingTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.GlobalizedMetricConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRicciPinching


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

private theorem continuousOn_timeSlice {P : Type*} [TopologicalSpace P]
    {f : ℝ → P → ℝ}
    (h : ContinuousOn (fun q : ℝ × P => f q.1 q.2) (Iic 0 ×ˢ univ)) (x : P) :
    ContinuousOn (fun t => f t x) (Iic 0) := by
  have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  exact h.comp hmap.continuousOn (fun _ ht => ⟨ht, mem_univ x⟩)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance roundBackwardTopology : TopologicalSpace F.M := F.topology
local instance roundBackwardCharted : ChartedSpace H F.M := F.charted
local instance roundBackwardSmooth : IsManifold I ∞ F.M := F.smooth
local instance roundBackwardC1 : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)
local instance roundBackwardT2 : T2Space F.M := F.t2
local instance roundBackwardSigma : SigmaCompactSpace F.M := F.sigmaCompact

variable {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}

local instance roundBackwardLimitTopology : TopologicalSpace L.M := L.topology
local instance roundBackwardLimitCharted : ChartedSpace H L.M := L.charted
local instance roundBackwardLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance roundBackwardLimitC1 : IsManifold I 1 L.M := IsManifold.of_le (n := ∞) (by decide)
local instance roundBackwardLimitT2 : T2Space L.M := L.t2
local instance roundBackwardLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact


theorem exists_backward_ricci_pinching_of_round_limit
    (hdim : Module.finrank ℝ E = 3) (hconn : ConnectedSpace F.M)
    (tau : ℕ → ℝ) (htau : ∀ i, 0 < tau i) (hescape : Tendsto tau atTop atTop)
    (q : ℕ → F.M) {phi : ℕ → ℕ} (hphi : StrictMono phi)
    (Phi : PointedRiemannianConvergenceMaps (I := I) (backwardSliceSequence F tau htau q) L phi)
    (C : MetricConvergenceData (I := I) Phi)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Phi k)
    (hcompact : CompactSpace L.M) {R : ℝ} (hR : 0 < R)
    (hscalar : ∀ x : L.M, metricScalarAt L.metric x = R)
    (hEin : ∀ x : L.M, ∀ v : TangentSpace I x,
      ricciTensor L.metric x v v = (R / 3) * L.metric.inner x v v) :
    ∃ rho c : ℕ → ℝ, (∀ i, 0 < rho i) ∧ Tendsto rho atTop atTop ∧
      Tendsto c atTop (𝓝 (1 / 3)) ∧ (∀ i, c i < 1 / 3) ∧
      ∀ i, ∀ x : F.M, 0 < F.S.scalar (-rho i) x ∧ ∀ v : TangentSpace I x,
        c i * F.S.scalar (-rho i) x * (F.S.family.metric (-rho i)).inner x v v ≤
          F.S.ricciAt (-rho i) x (vec2 v v) := by
  classical
  let _ : CompactSpace L.M := hcompact
  have hconnected : ∀ k : ℕ,
      @ConnectedSpace ((backwardSliceSequence F tau htau q).obj (phi k)).M
        ((backwardSliceSequence F tau htau q).obj (phi k)).topology := fun _ => hconn
  obtain ⟨k0, e, _, hconv⟩ :=
    compactLimit_global_pullback_metric_convergence Phi C hcanonical hcompact hconnected
  let G : ℕ → SmoothRiemannianMetric I L.M := fun k => Diffeomorph.pullbackMetric
    ((backwardSliceSequence F tau htau q).obj (phi (k0 + k))).metric (e k)
  have hGconv : MetricCInfConvergenceOnCompacts G L.metric L.metric := hconv
  let c : ℕ → ℝ := fun i => 1 / 3 - (1 / 3) / ((i : ℝ) + 1)
  have hc0 (i : ℕ) : 0 ≤ c i := by
    have hdiv : (1 / 3 : ℝ) / ((i : ℝ) + 1) ≤ 1 / 3 := by
      apply (div_le_iff₀ (by positivity : 0 < (i : ℝ) + 1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    exact sub_nonneg.mpr hdiv
  have hcUpper (i : ℕ) : c i < 1 / 3 := by
    have hp : 0 < (1 / 3 : ℝ) / ((i : ℝ) + 1) := by positivity
    dsimp only [c]
    linarith
  have hplus : Tendsto (fun i : ℕ => (i : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun i => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc : Tendsto c atTop (𝓝 (1 / 3)) := by
    have hz := tendsto_inv_atTop_zero.comp hplus
    have h : Tendsto (fun i : ℕ => (1 / 3 : ℝ) - (1 / 3) * ((i : ℝ) + 1)⁻¹)
        atTop (𝓝 ((1 / 3 : ℝ) - (1 / 3) * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hz)
    simpa only [c, div_eq_mul_inv, mul_zero, sub_zero] using h
  choose kPinch hkPinch using fun i =>
    metric_ricci_pinching_eventually_of_round_convergence G L.metric hdim hR hscalar hEin hGconv
      (hc0 i) (hcUpper i)
  let j : ℕ → ℕ := fun i => max (kPinch i) i
  have hj : Tendsto j atTop atTop := tendsto_atTop_mono (fun i => le_max_right _ _) tendsto_id
  have hshift : Tendsto (fun k : ℕ => k0 + k) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat k0
  let rho : ℕ → ℝ := fun i => tau (phi (k0 + j i))
  have hrho (i : ℕ) : 0 < rho i := htau _
  have hrhoEscape : Tendsto rho atTop atTop :=
    hescape.comp (hphi.tendsto_atTop.comp (hshift.comp hj))
  refine ⟨rho, c, hrho, hrhoEscape, hc, hcUpper, ?_⟩
  intro i
  have hg := hkPinch i (j i) (le_max_left _ _)
  have hpinch := (ricci_trace_pinching_pullback_iff
    ((backwardSliceSequence F tau htau q).obj (phi (k0 + j i))).metric (e (j i)) (c i)).mp
      (fun x v => (hg x).2 v)
  have hsource := (ricci_trace_pinching_scaleMetric_iff (F.S.family.metric (-rho i))
    (rho i)⁻¹ (inv_pos.mpr (hrho i)) (c i)).mp hpinch
  have hpositive := scalar_positive_of_pullback_scaleMetric (F.S.family.metric (-rho i))
    (e (j i)) (rho i)⁻¹ (inv_pos.mpr (hrho i)) (fun x => (hg x).1)
  intro x
  refine ⟨hpositive x, fun v => ?_⟩
  have h := hsource x v
  change c i * metricScalarAt (F.S.family.metric (-rho i)) x *
    (F.S.family.metric (-rho i)).inner x v v ≤
      metricRicciAt (F.S.family.metric (-rho i)) x (vec2 v v)
  rw [metricRicciAt_apply_eq_ricciTensor]
  exact h


theorem ancient_constant_sectional_of_round_backward_convergence
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
    ∀ b : ℝ, b ≤ 0 → ∃ K : ℝ, ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric b) x X Y Y X =
        K * ((F.S.family.metric b).inner x X X * (F.S.family.metric b).inner x Y Y -
          (F.S.family.metric b).inner x X Y * (F.S.family.metric b).inner x X Y) := by
  let _ : CompactSpace F.M := hcompactF
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨rho, c, _, hrho, hc, hcUpper, hpinch⟩ :=
    exists_backward_ricci_pinching_of_round_limit F hdim hconn tau htau hescape q hphi Phi C
      hcanonical hcompact hR hscalar hEin
  have ha : Tendsto (fun i => -rho i) atTop atBot := tendsto_neg_atTop_atBot.comp hrho
  exact ancient_constant_sectional_of_backward_pinching F.S F.isSolution hdim ha hc hcUpper
    (fun i x v => (hpinch i x).2 v)


theorem ancient_scalar_monotone_of_spatially_constant
    (hconstant : ∀ t : ℝ, t ≤ 0 → ∃ R : ℝ, ∀ x : F.M, F.S.scalar t x = R)
    (x : F.M) : MonotoneOn (fun t => F.S.scalar t x) (Iic 0) := by
  have hcont : ContinuousOn (fun t => F.S.scalar t x) (Iic 0) :=
    continuousOn_timeSlice (P := F.M) (f := F.S.scalar) F.isSolution.scalarCont x
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic 0) hcont
    (f' := fun t => 2 * normSq0S (F.S.family.metric t) x 2 (F.S.ricci t x))
  · intro t ht
    have ht' : t < 0 := by simpa only [interior_Iic, mem_Iio] using ht
    have h := (smoothOfSolution F.S F.isSolution).scalarEvolution (flowG F.S)
      (fun _ => rfl) (fun _ => rfl) ⟨t, ht'⟩ x
    obtain ⟨R, hR⟩ := hconstant t ht'.le
    have hf : F.S.scalar t = fun _ => R := funext hR
    simp only [hf, laplacianAt, laplacian_const, zero_add] at h
    exact h.mono interior_subset
  · intro t _ht
    exact mul_nonneg (by norm_num) (normSq0S_nonneg _ _ _ _)


theorem ancient_positive_constant_sectional_of_round_backward_convergence
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
    ∀ b : ℝ, b ≤ 0 → ∃ K : ℝ, 0 < K ∧ ∀ x : F.M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt (F.S.family.metric b) x X Y Y X =
        K * ((F.S.family.metric b).inner x X X * (F.S.family.metric b).inner x Y Y -
          (F.S.family.metric b).inner x X Y * (F.S.family.metric b).inner x X Y) := by
  let _ : CompactSpace F.M := hcompactF
  let _ : ConnectedSpace F.M := hconn
  obtain ⟨rho, c, hrhoPos, hrho, hc, hcUpper, hpinch⟩ :=
    exists_backward_ricci_pinching_of_round_limit F hdim hconn tau htau hescape q hphi Phi C
      hcanonical hcompact hR hscalar hEin
  have ha : Tendsto (fun i => -rho i) atTop atBot := tendsto_neg_atTop_atBot.comp hrho
  have hinitial := fun i x v => (hpinch i x).2 v
  have hconstant := ancient_scalar_constant_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial
  have hpositive (b : ℝ) (hb : b ≤ 0) (x : F.M) : 0 < F.S.scalar b x := by
    obtain ⟨i, hi⟩ := (hrho.eventually (eventually_ge_atTop (-b))).exists
    have hab : -rho i ≤ b := by linarith
    have hm := ancient_scalar_monotone_of_spatially_constant F hconstant x
      (neg_nonpos.mpr (hrhoPos i).le) hb hab
    exact (hpinch i x).1.trans_le hm
  intro b hb
  obtain ⟨Rb, hRb⟩ := hconstant b hb
  have hRbPos : 0 < Rb := by
    rw [← hRb F.basepoint]
    exact hpositive b hb F.basepoint
  have hEinSlice := ancient_ricci_einstein_of_backward_pinching F.S F.isSolution hdim
    ha hc hcUpper hinitial b hb
  refine ⟨Rb / 6, div_pos hRbPos (by norm_num), fun x X Y => ?_⟩
  let g := F.S.family.metric b
  obtain ⟨basis, _l1, _l2, _l3, horth, _hdiag⟩ :=
    ricciEigen3 g (F.S.ricciAt b x) hdim (ricci_is_symmetric F.S b x)
  have htrace := riemann_from_ricci_trace F.S (t := b) (x := x) (basis := basis) horth
  have hneg (i j : Fin 3) : ricciCompAt basis (-(F.S.ricciAt b x)) i j =
      ((-F.S.scalar b x) / 3) * delta3 i j := by
    rw [ricciCompAt_apply]
    change -(F.S.ricciAt b x (vec2 (basis i) (basis j))) = _
    rw [hEinSlice x (basis i) (basis j)]
    change -((F.S.scalar b x / 3) * g.inner x (basis i) (basis j)) = _
    rw [horth i j]
    ring
  have hRm := rm04_einstein3_at htrace hneg X Y
  calc
    _ = -((-F.S.scalar b x) / 6) *
        (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y) := hRm
    _ = _ := by rw [hRb x]; ring

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
