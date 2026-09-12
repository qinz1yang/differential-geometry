import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedInverseDistanceControl
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private theorem tendsto_of_eventual_multiplicative_comparison
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ} {d : ℝ}
    (ha : Tendsto a l (𝓝 d))
    (hcomparison : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in l, b i ≤ (1 + epsilon) * a i ∧ a i ≤ (1 + epsilon) * b i) :
    Tendsto b l (𝓝 d) := by
  apply Metric.tendsto_nhds.mpr
  intro eta heta
  let K : ℝ := |d| + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hdK : d < K := by dsimp only [K]; linarith [le_abs_self d]
  let delta : ℝ := eta / (4 * K)
  have hdelta : 0 < delta := div_pos heta (mul_pos (by norm_num) hK)
  have hdelta_eq : delta * (4 * K) = eta :=
    div_mul_cancel₀ eta (ne_of_gt (mul_pos (by norm_num) hK))
  have hbound := ha.eventually (gt_mem_nhds hdK)
  have hclose := Metric.tendsto_nhds.mp ha (eta / 2) (by linarith)
  filter_upwards [hbound, hclose, hcomparison 1 (by norm_num), hcomparison delta hdelta]
    with i hiK hiclose hiunit hidelta
  have hbK : b i ≤ 2 * K := by nlinarith [hiunit.1]
  have hmulA := mul_le_mul_of_nonneg_left hiK.le hdelta.le
  have hmulB := mul_le_mul_of_nonneg_left hbK hdelta.le
  have hdiff : |b i - a i| ≤ eta / 2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [hidelta.2]
    · nlinarith [hidelta.1]
  rw [Real.dist_eq] at hiclose ⊢
  calc
    |b i - d| ≤ |b i - a i| + |a i - d| := abs_sub_le _ _ _
    _ < eta / 2 + eta / 2 := add_lt_add_of_le_of_lt hdiff hiclose
    _ = eta := by ring

private theorem ennreal_tendsto_of_eventual_multiplicative_comparison
    {ι : Type*} {l : Filter ι} {a b : ι → ℝ≥0∞} {d : ℝ}
    (ha : Tendsto (fun i => (a i).toReal) l (𝓝 d))
    (hafinite : ∀ᶠ i in l, a i ≠ ⊤)
    (hcomparison : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ i in l, b i ≤ ENNReal.ofReal (1 + epsilon) * a i ∧
        a i ≤ ENNReal.ofReal (1 + epsilon) * b i) :
    Tendsto (fun i => (b i).toReal) l (𝓝 d) ∧
      Tendsto b l (𝓝 (ENNReal.ofReal d)) := by
  have hbfinite : ∀ᶠ i in l, b i ≠ ⊤ := by
    filter_upwards [hafinite, hcomparison 1 (by norm_num)] with i hi hc
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hi) hc.1
  have hreal : Tendsto (fun i => (b i).toReal) l (𝓝 d) := by
    apply tendsto_of_eventual_multiplicative_comparison ha
    intro epsilon hepsilon
    filter_upwards [hafinite, hbfinite, hcomparison epsilon hepsilon]
      with i hia hib hic
    have hleft := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hia) hic.1
    have hright := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hib) hic.2
    simpa only [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 + epsilon)] using And.intro hleft hright
  refine ⟨hreal, ?_⟩
  exact (ENNReal.tendsto_ofReal hreal).congr'
    (hbfinite.mono fun i hi => ENNReal.ofReal_toReal hi)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
  {subseq : ℕ → ℕ} {Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq}

local instance pointedDistanceLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedDistanceLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedDistanceLimitSmooth : IsManifold I ∞ L.M := L.smooth

local instance pointedDistanceLimitTermTopology (k : ℕ) :
    TopologicalSpace (X.obj (subseq k)).M := (X.obj (subseq k)).topology
local instance pointedDistanceLimitTermCharted (k : ℕ) :
    ChartedSpace H (X.obj (subseq k)).M := (X.obj (subseq k)).charted
local instance pointedDistanceLimitTermSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj (subseq k)).M := (X.obj (subseq k)).smooth

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] in
private theorem approximant_pair_edist_le (k : ℕ) {rho : ℝ} (hrho : 0 ≤ rho)
    (y z : (X.obj (subseq k)).M)
    (hy : y ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint rho)
    (hz : z ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
      (X.obj (subseq k)).basepoint rho) :
    riemannianEDistOf (I := I) (X.obj (subseq k)).metric y z ≤ ENNReal.ofReal (2 * rho) := by
  let g := (X.obj (subseq k)).metric
  let p := (X.obj (subseq k)).basepoint
  let _ : RiemannianBundle (fun x : (X.obj (subseq k)).M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have htriangle : riemannianEDistOf (I := I) g y z ≤
      riemannianEDistOf (I := I) g y p + riemannianEDistOf (I := I) g p z :=
    Manifold.riemannianEDist_triangle
  have hcomm : riemannianEDistOf (I := I) g y p =
      riemannianEDistOf (I := I) g p y := Manifold.riemannianEDist_comm
  calc
    riemannianEDistOf (I := I) g y z ≤
        riemannianEDistOf (I := I) g y p + riemannianEDistOf (I := I) g p z := htriangle
    _ = riemannianEDistOf (I := I) g p y + riemannianEDistOf (I := I) g p z := by rw [hcomm]
    _ ≤ ENNReal.ofReal rho + ENNReal.ofReal rho := add_le_add hy hz
    _ = ENNReal.ofReal (2 * rho) := by rw [← ENNReal.ofReal_add hrho hrho, two_mul]

theorem eventually_pointed_inverse_pair_in_compact_ball
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (y z : ∀ k : ℕ, (X.obj (subseq k)).M)
    (hball : ∀ᶠ k in atTop,
      y k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho ∧
      z k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho) :
    IsCompact (riemannianClosedBallOf (I := I) L.metric L.basepoint (2 * rho)) ∧
    (∀ᶠ k in atTop,
      y k ∈ (Φ.partialDiffeomorph k).target ∧ z k ∈ (Φ.partialDiffeomorph k).target ∧
      (Φ.partialDiffeomorph k).symm (y k) ∈
        riemannianClosedBallOf (I := I) L.metric L.basepoint (2 * rho) ∧
      (Φ.partialDiffeomorph k).symm (z k) ∈
        riemannianClosedBallOf (I := I) L.metric L.basepoint (2 * rho)) := by
  obtain ⟨hcpt, k0, hk0⟩ := exists_pointed_inverse_distance_control
    C hreference hcomplete rho hrho 1 (by norm_num)
  refine ⟨by simpa only [one_add_one_eq_two] using hcpt, ?_⟩
  filter_upwards [eventually_ge_atTop k0, hball] with k hk hkb
  have hy := (hk0 k hk).1 (y k) hkb.1
  have hz := (hk0 k hk).1 (z k) hkb.2
  simpa only [one_add_one_eq_two] using And.intro hy.1 (And.intro hz.1 (And.intro hy.2 hz.2))

theorem tendsto_pointed_inverse_distance
    (C : MetricConvergenceData (I := I) Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L)
    (rho : ℝ) (hrho : 0 ≤ rho)
    (y z : ∀ k : ℕ, (X.obj (subseq k)).M)
    (hball : ∀ᶠ k in atTop,
      y k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho ∧
      z k ∈ riemannianClosedBallOf (I := I) (X.obj (subseq k)).metric
        (X.obj (subseq k)).basepoint rho)
    (d : ℝ)
    (hdist : Tendsto (fun k =>
      (riemannianEDistOf (I := I) (X.obj (subseq k)).metric (y k) (z k)).toReal)
      atTop (𝓝 d)) :
    Tendsto (fun k => (riemannianEDistOf (I := I) L.metric
      ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k))).toReal)
      atTop (𝓝 d) ∧
    Tendsto (fun k => riemannianEDistOf (I := I) L.metric
      ((Φ.partialDiffeomorph k).symm (y k)) ((Φ.partialDiffeomorph k).symm (z k)))
      atTop (𝓝 (ENNReal.ofReal d)) := by
  apply ennreal_tendsto_of_eventual_multiplicative_comparison hdist
  · filter_upwards [hball] with k hk
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (approximant_pair_edist_le k hrho (y k) (z k) hk.1 hk.2)
  · intro epsilon hepsilon
    obtain ⟨_, k0, hk0⟩ := exists_pointed_inverse_distance_control
      C hreference hcomplete rho hrho epsilon hepsilon
    filter_upwards [eventually_ge_atTop k0, hball] with k hk hkb
    exact (hk0 k hk).2 (y k) hkb.1 (z k) hkb.2

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
