import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonComposition

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

def WindowedModelWitness.parabolicComparison
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (c : ℝ) (hc : delta < c) (p : ℕ) (hp : p ≤ modelOrder delta) :
    MetricComparisonOn
      (rescaledMetric W.model.S 0 c (W.eps_pos.trans hc))
      (rescaledMetric S t (c * S.scalar t x) (mul_pos (W.eps_pos.trans hc) W.scalar_pos))
      W.embedding
      (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
      (Icc (-1 : ℝ) 0) p
      ((max 1 (Real.sqrt c)⁻¹) ^ p * delta) := by
  have hcpos : 0 < c := W.eps_pos.trans hc
  have htime {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 0) :
      parabolicTime 0 c s ∈ Ioc (-modelDepth delta) 0 := by
    have hinv : c⁻¹ < modelDepth delta := inv_strictAnti₀ W.eps_pos hc
    have hlo : -c⁻¹ ≤ s / c := by
      simpa only [neg_div, one_div] using div_le_div_of_nonneg_right hs.1 hcpos.le
    simp only [parabolicTime, zero_add]
    exact ⟨by linarith, div_nonpos_of_nonpos_of_nonneg hs.2 hcpos.le⟩
  have hmap : MapsTo (parabolicTime 0 c) (Icc (-1 : ℝ) 0)
      (Icc (-modelDepth delta) 0) := fun _ hs => ⟨(htime hs).1.le, (htime hs).2⟩
  let C := W.comparison.parabolicRescale 0 c hcpos p hp (Icc (-1 : ℝ) 0)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hmap (fun b s hs y hy v =>
      (W.comparison_jet_contDiffWithinAt hS hreg b (htime hs) y hy v).differentiableWithinAt
        (by simp))
  have hg : (fun s => scaleMetric c hcpos
      (rescaledMetric S t (S.scalar t x) W.scalar_pos (parabolicTime 0 c s))) =
      rescaledMetric S t (c * S.scalar t x) (mul_pos hcpos W.scalar_pos) := by
    funext s
    have ht : parabolicTime t (S.scalar t x) (parabolicTime 0 c s) =
        parabolicTime t (c * S.scalar t x) s := by
      simp only [parabolicTime, zero_add, div_div]
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    simp only [rescaledMetric, scaleMetric_inner, ht, mul_assoc]
  change MetricComparisonOn
    (fun s => scaleMetric c hcpos (W.model.S.base.metric (parabolicTime 0 c s)))
    (rescaledMetric S t (c * S.scalar t x) (mul_pos hcpos W.scalar_pos))
    W.embedding
    (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
    (Icc (-1 : ℝ) 0) p ((max 1 (Real.sqrt c)⁻¹) ^ p * delta)
  rw [← hg]
  exact C

theorem WindowedModelWitness.exists_source_curvature_normalized_comparison
    (hS : IsSolutionOn S) {delta kappa eps C1 C2 : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 4) (hbuffer : 2 * C1 ≤ modelRadius delta)
    (hsmall : 486 * C2 * (1 + 3 * C2) * delta ≤ 1)
    (p : ℕ) (hp : p ≤ modelOrder delta) {y : W.model.M} (hy : y ∈ K.domain.carrier) :
    ∃ hQ : 0 < S.scalar t (W.embedding y),
      Nonempty (MetricComparisonOn
        (rescaledMetric W.model.S 0 (S.scalar t (W.embedding y) / S.scalar t x)
          (div_pos hQ W.scalar_pos))
        (rescaledMetric S t (S.scalar t (W.embedding y)) hQ)
        W.embedding
        (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
        (Icc (-1 : ℝ) 0) p ((max 1 (Real.sqrt (2 * C2))) ^ p * delta)) := by
  have hC2 : 0 < C2 := zero_lt_one.trans_le K.one_le_comparison_constant
  have hbound := W.scalar_bounds_on_canonical_domain K hdelta hbuffer hsmall hy
  have hQ : 0 < S.scalar t (W.embedding y) :=
    (mul_pos (inv_pos.mpr (by positivity : 0 < 2 * C2)) W.scalar_pos).trans_le hbound.1
  let c := S.scalar t (W.embedding y) / S.scalar t x
  have hcpos : 0 < c := div_pos hQ W.scalar_pos
  have hclower : (2 * C2)⁻¹ ≤ c := (le_div_iff₀ W.scalar_pos).mpr hbound.1
  have hfactor : 2 * C2 * delta < 1 := by
    have hprod : 0 < C2 * delta := mul_pos hC2 W.eps_pos
    have hwide : C2 * delta ≤ C2 * (1 + 3 * C2) * delta := by
      nlinarith [mul_nonneg (mul_nonneg hC2.le hC2.le) W.eps_pos.le]
    nlinarith
  have hdc : delta < c := by
    have hinv : 2 * C2 * (2 * C2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
    have hlt : delta < (2 * C2)⁻¹ := by nlinarith [hfactor]
    exact hlt.trans_le hclower
  have hcinv : c⁻¹ ≤ 2 * C2 := by
    have hh := inv_anti₀ (inv_pos.mpr (by positivity : 0 < 2 * C2)) hclower
    simpa only [inv_inv] using hh
  have hsqrt : (Real.sqrt c)⁻¹ ≤ Real.sqrt (2 * C2) := by
    rw [← Real.sqrt_inv]
    exact Real.sqrt_le_sqrt hcinv
  have hloss : (max 1 (Real.sqrt c)⁻¹) ^ p * delta ≤
      (max 1 (Real.sqrt (2 * C2))) ^ p * delta :=
    mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_le_max_left _ hsqrt) p)
      W.eps_pos.le
  let C := (W.parabolicComparison hS hreg c hdc p hp).mono (subset_refl _) le_rfl hloss
  have hcQ : c * S.scalar t x = S.scalar t (W.embedding y) :=
    div_mul_cancel₀ _ W.scalar_pos.ne'
  refine ⟨hQ, ?_⟩
  have hg : rescaledMetric S t (c * S.scalar t x) (mul_pos hcpos W.scalar_pos) =
      rescaledMetric S t (S.scalar t (W.embedding y)) hQ := by
    congr 1
  change Nonempty (MetricComparisonOn (rescaledMetric W.model.S 0 c hcpos)
    (rescaledMetric S t (S.scalar t (W.embedding y)) hQ) W.embedding
    (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
    (Icc (-1 : ℝ) 0) p ((max 1 (Real.sqrt (2 * C2))) ^ p * delta))
  rw [← hg]
  exact ⟨C⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
