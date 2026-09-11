import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Jacobi
import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati.Local

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Filter Matrix Set
open scoped ContDiff Manifold Matrix Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open BonnetMyers
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Volume
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem curveMean_le_on
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q a b : ℝ)
    (hq : 0 ≤ q)
    (ha : 0 < a)
    (hcard : Fintype.card ι = Module.finrank ℝ E - 1)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) b,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = a ^ 2)
    (hVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0)
    (hDVperp : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0)
    (hVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hDVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t)
    (hLI : ∀ t ∈ Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hJ : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) b,
      -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2) *
          g.inner (γ t) (curveVelocity (I := I) γ t)
            (curveVelocity (I := I) γ t) ≤
        ricciTensor (I := I) g (γ t)
          (curveVelocity (I := I) γ t)
          (curveVelocity (I := I) γ t))
    (hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity (q * a) (Module.finrank ℝ E - 1) t) :
    ∀ t ∈ Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤
        hyperbolicMeanCurv (q * a) (Module.finrank ℝ E - 1) t := by
  let d : ℕ := Module.finrank ℝ E - 1
  have hqa : 0 ≤ q * a := mul_nonneg hq ha.le
  let m' : ℝ → ℝ := fun t =>
    -trace ((curveGram (I := I) g γ V t)⁻¹ *
        curveCurvGram (I := I) g γ V t) -
      trace ((curveShape (I := I) g γ V t) ^ 2)
  have hm : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt (curveMean (I := I) g γ V) (m' t) t := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_on (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      (hRic t ht)).1
  have hmle : ∀ t ∈ Ioo (0 : ℝ) b,
      m' t ≤ (d : ℝ) * (q * a) ^ 2 -
        curveMean (I := I) g γ V t ^ 2 / (d : ℝ) := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_on (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      (hRic t ht)).2
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / hyperbolicDensity (q * a) d t
  have hR : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - hyperbolicMeanCurv (q * a) d t)) t := by
    intro t ht
    simpa only [R, d] using
      hasDerivAt_denRatio (I := I) hn g γ V (q * a) t d hqa ht.1 (hγ t ht)
        (hVdiff t ht) (curveGram_det_pos (I := I) g γ V t (hLI t ht))
        (hW t ht)
  have hRpos : ∀ t ∈ Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (hyperbolicDensity_pos hqa ht.1)
  apply mean_le_hyperbolic_of_ratio hqa hd hm hmle hR hRpos
  simpa only [R, d] using hRatioLower

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
