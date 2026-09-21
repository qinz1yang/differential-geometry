import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EndRayCompactness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EscapeReindexingReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarDistanceLimit

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

universe u v

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {W : Type v} [MetricSpace W]

theorem exists_endRay_subseq_of_source_scalar_convergence
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ epsStar → ∀ sigma : ℝ, 0 < sigma →
        ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
          ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
            ∀ ell : ℝ, 0 < ell →
              ∀ (y : ∀ i, ℝ → (X.term i).M) (points : ∀ i, (X.term i).M),
              ∀ beta : ℕ → ℝ → W,
              (∀ s ∈ Ico 0 ell, ∃ K : Set W, IsCompact K ∧
                ∀ᶠ i in atTop, beta i s ∈ K) →
              (∀ r ∈ Ioo 0 ell, ∃ L : ℝ≥0,
                ∀ᶠ i in atTop, LipschitzOnWith L (beta i) (Icc 0 r)) →
              (∀ s ∈ Ico 0 ell, ∀ t ∈ Ico 0 ell,
                Tendsto (fun i => dist (beta i s) (beta i t)) atTop (𝓝 |s - t|)) →
              ∀ f : W → ℝ, Continuous f →
              (∀ s ∈ Ico 0 ell, ∀ᶠ i in atTop,
                2 ≤ (X.term i).S.scalar 0 (y i s)) →
              Tendsto (fun i => (X.term i).S.scalar 0 (points i)) atTop atTop →
              (∀ s ∈ Ico 0 ell, Tendsto
                (fun i => (X.term i).S.scalar 0 (y i s) - f (beta i s)) atTop (𝓝 0)) →
              (∀ s ∈ Ico 0 ell, Tendsto
                (fun i => metricDistance ((X.term i).S.base.metric 0) (y i s) (points i))
                atTop (𝓝 (ell - s))) →
              ∃ (phi : ℕ → ℕ) (E : UniformSpace.Completion W) (a : EndRay E),
                StrictMono phi ∧ a.length = ell ∧
                (∀ r : ℝ, r < ell → TendstoUniformlyOn
                  (fun i (s : Ico 0 ell) => beta (phi i) s)
                  (fun s : Ico 0 ell => a.point (ell - s)) atTop {s | (s : ℝ) ≤ r}) ∧
                (∀ s ∈ Ioc 0 ell, 1 ≤ f (a.point s) * s ^ 2) ∧
                (∀ x : W, (x : UniformSpace.Completion W) ≠ E) := by
  obtain ⟨epsStar, hepsStar, hlower⟩ := exists_scalar_mul_sq_distance_limit_lower_bound hmod
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hsmall sigma hsigma Phi hPhi X ell hell y points beta
    hcompact hLip hpair f hf hhigh hcurv hscalar hdistance
  apply exists_endRay_subseq_of_eventually_lipschitzOnWith hell beta hcompact hLip hpair f hf
  intro phi hphi s hs w hw
  have hscalarSelected : Tendsto (fun i => (X.term (phi i)).S.scalar 0 (y (phi i) s))
      atTop (𝓝 (f w)) := by
    simpa only [Function.comp_def, sub_add_cancel, zero_add] using
      ((hscalar s hs).comp hphi.tendsto_atTop).add (hf.continuousAt.tendsto.comp hw)
  exact hlower eps heps hsmall sigma hsigma Phi hPhi (X.reindex phi hphi)
    (fun i => y (phi i) s) (fun i => points (phi i))
    (hphi.tendsto_atTop.eventually (hhigh s hs)) (hcurv.comp hphi.tendsto_atTop)
    (f w) (ell - s) hscalarSelected ((hdistance s hs).comp hphi.tendsto_atTop)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
