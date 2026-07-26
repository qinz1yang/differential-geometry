import DifferentialGeometry.Geometry.Comparison.Volume.HyperbolicModel
import DifferentialGeometry.Geometry.Comparison.Volume.JacobiRiccati
import DifferentialGeometry.Geometry.Comparison.Volume.JacobianBounds
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame

/-!
# Bishop comparison for Jacobi families

This file combines the Jacobi density derivative, the trace Riccati inequality,
and the hyperbolic scalar comparison kernel.  It is the radial geometric core
of Bishop comparison, before polar integration and cut-locus transfer.
-/

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
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- The Jacobi density ratio has logarithmic derivative equal to the
difference between the Jacobi and model mean curvatures. -/
theorem hasDerivAt_denRatio
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q t : ℝ) (d : ℕ)
    (hq : 0 ≤ q) (ht : 0 < t)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hpos : 0 < (curveGram (I := I) g γ V t).det)
    (hW : ∀ i j, jacobiWronskian g γ (V i) (V j) t = 0) :
    HasDerivAt
      (fun r => curveDensity (I := I) g γ V r / hypDensity q d r)
      ((curveDensity (I := I) g γ V t / hypDensity q d t) *
        (curveMean (I := I) g γ V t - hypMeanCurv q d t)) t := by
  have hden : HasDerivAt (curveDensity (I := I) g γ V)
      (curveMean (I := I) g γ V t * curveDensity (I := I) g γ V t) t := by
    simpa only [curveMean] using
      hasDerivAt_symmDen (I := I) hn g γ V t hγ hVdiff hpos hW
  exact hasDerivAt_hypRatio
    (j' := fun r => curveMean (I := I) g γ V r *
      curveDensity (I := I) g γ V r)
    (m := curveMean (I := I) g γ V) hq ht hden rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
/-- A uniform linear lower bound for every unit Jacobi combination gives a
positive lower bound for its hyperbolic density ratio at the pole. -/
theorem denRatio_ge_of_dir
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q B : ℝ)
    (hq : 0 ≤ q) (hB : 0 < B)
    (hLI : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      LinearIndependent ℝ fun i => V i t)
    (hdir : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
        (B * t) ^ 2 ≤
          g.inner (γ t) (∑ i, v i • V i t) (∑ i, v i • V i t)) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hypDensity q (Fintype.card ι) t := by
  refine ⟨(B / 2) ^ Fintype.card ι,
    pow_pos (div_pos hB (by norm_num)) _, ?_⟩
  filter_upwards [hLI, hdir, hypSn_le_two q, self_mem_nhdsWithin]
    with t hLIt hdirT hsn ht
  change 0 < t at ht
  have hgram := curveGram_posDef (I := I) g γ V t hLIt
  have hray : ∀ v : EuclideanSpace ℝ ι, ‖v‖ = 1 →
      (B * t) ^ 2 ≤ RCLike.re
        (dotProduct (star ⇑v) (Matrix.mulVec (curveGram (I := I) g γ V t) ⇑v)) := by
    intro v hv
    have hquad := curveGram_dotVec (I := I) g γ V t (⇑v)
    change (B * t) ^ 2 ≤
      dotProduct (star ⇑v) (Matrix.mulVec (curveGram (I := I) g γ V t) ⇑v)
    rw [hquad]
    exact hdirT v hv
  have hdet := sqrt_pow_le_sqrt_det_of_rayleigh
    (A := curveGram (I := I) g γ V t) (a := (B * t) ^ 2)
    hgram.posSemidef (sq_nonneg _) hray
  have hsqrt :
      Real.sqrt (((B * t) ^ 2) ^ Fintype.card ι) =
        (B * t) ^ Fintype.card ι := by
    calc
      Real.sqrt (((B * t) ^ 2) ^ Fintype.card ι) =
          Real.sqrt (((B * t) ^ Fintype.card ι) ^ 2) := by
            congr 1
            rw [← pow_mul, ← pow_mul]
            congr 1
            omega
      _ = |(B * t) ^ Fintype.card ι| := Real.sqrt_sq_eq_abs _
      _ = (B * t) ^ Fintype.card ι :=
        abs_of_nonneg (pow_nonneg (mul_nonneg hB.le ht.le) _)
  have hcurve :
      (B * t) ^ Fintype.card ι ≤ curveDensity (I := I) g γ V t := by
    rw [← hsqrt]
    simpa only [curveDensity] using hdet
  have hmodel : hypDensity q (Fintype.card ι) t ≤
      (2 * t) ^ Fintype.card ι := by
    exact pow_le_pow_left₀ (hypSn_pos hq ht).le hsn _
  rw [le_div_iff₀ (hypDensity_pos hq ht)]
  calc
    (B / 2) ^ Fintype.card ι * hypDensity q (Fintype.card ι) t ≤
        (B / 2) ^ Fintype.card ι * (2 * t) ^ Fintype.card ι :=
      mul_le_mul_of_nonneg_left hmodel (pow_nonneg (div_nonneg hB.le (by norm_num)) _)
    _ = (B * t) ^ Fintype.card ι := by
      rw [← mul_pow]
      congr 1
      ring
    _ ≤ curveDensity (I := I) g γ V t := hcurve

/-- A Jacobi density whose mean curvature is bounded above by the model mean
curvature has antitone ratio to the model density. -/
theorem curveRatio_anti
    {n : WithTop ℕ∞} (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (V : ι → ∀ t, TangentSpace I (γ t)) (q b : ℝ) (d : ℕ)
    (hq : 0 ≤ q)
    (hγ : ∀ t ∈ Ioo (0 : ℝ) b,
      ContMDiffAt 𝓘(ℝ, ℝ) I n γ t)
    (hVdiff : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t)
    (hLI : ∀ t ∈ Ioo (0 : ℝ) b,
      LinearIndependent ℝ fun i => V i t)
    (hW : ∀ t ∈ Ioo (0 : ℝ) b, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0)
    (hmean : ∀ t ∈ Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤ hypMeanCurv q d t) :
    AntitoneOn
      (fun t => curveDensity (I := I) g γ V t / hypDensity q d t)
      (Ioo (0 : ℝ) b) := by
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / hypDensity q d t
  have hR : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - hypMeanCurv q d t)) t := by
    intro t ht
    simpa only [R] using
      hasDerivAt_denRatio (I := I) hn g γ V q t d hq ht.1 (hγ t ht)
        (hVdiff t ht) (curveGram_det_pos (I := I) g γ V t (hLI t ht))
        (hW t ht)
  have hRpos : ∀ t ∈ Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (hypDensity_pos hq ht.1)
  have hdiff : DifferentiableOn ℝ R (Ioo (0 : ℝ) b) := by
    intro t ht
    exact (hR t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) b,
      R t * (curveMean (I := I) g γ V t - hypMeanCurv q d t) ≤ 0 := by
    intro t ht
    exact mul_nonpos_of_nonneg_of_nonpos (hRpos t ht).le
      (sub_nonpos.mpr (hmean t ht))
  have hanti : AntitoneOn R (Ioo (0 : ℝ) b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ioo 0 b) hdiff.continuousOn ?_ ?_
    · simpa using hdiff
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) b := by simpa using ht
      rw [(hR t ht').deriv]
      exact hderiv t ht'
  simpa only [R] using hanti

/-- A positive constant-speed transverse Jacobi family under the Ricci lower
bound has mean curvature at most the speed-scaled hyperbolic model, provided
its density ratio stays positive at the pole. -/
theorem curveMean_le_hyp
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
    (hRic : RicciBoundedBelow (I := I) g
      (-(((Module.finrank ℝ E - 1 : ℕ) : ℝ) * q ^ 2)))
    (hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hypDensity (q * a) (Module.finrank ℝ E - 1) t) :
    ∀ t ∈ Ioo (0 : ℝ) b,
      curveMean (I := I) g γ V t ≤
        hypMeanCurv (q * a) (Module.finrank ℝ E - 1) t := by
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
    exact (mean_riccati_le (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      hRic).1
  have hmle : ∀ t ∈ Ioo (0 : ℝ) b,
      m' t ≤ (d : ℝ) * (q * a) ^ 2 -
        curveMean (I := I) g γ V t ^ 2 / (d : ℝ) := by
    intro t ht
    have hupos : 0 < g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) := by rw [hspeed t ht]; positivity
    obtain ⟨e, hON, hEperp⟩ := exists_perp_pos (I := I) g (γ t)
      (curveVelocity (I := I) γ t) hupos
    exact (mean_riccati_le (I := I) hn g γ V t q a
      (curveVelocity (I := I) γ t) rfl hcard hd ha (hspeed t ht)
      (hVperp t ht) (hDVperp t ht) (hγ t ht) (hVdiff t ht) (hDVdiff t ht)
      (hLI t ht) (hW t ht) (hJ t ht) e hON hEperp
      hRic).2
  let R : ℝ → ℝ := fun t =>
    curveDensity (I := I) g γ V t / hypDensity (q * a) d t
  have hR : ∀ t ∈ Ioo (0 : ℝ) b,
      HasDerivAt R
        (R t * (curveMean (I := I) g γ V t - hypMeanCurv (q * a) d t)) t := by
    intro t ht
    simpa only [R, d] using
      hasDerivAt_denRatio (I := I) hn g γ V (q * a) t d hqa ht.1 (hγ t ht)
        (hVdiff t ht) (curveGram_det_pos (I := I) g γ V t (hLI t ht))
        (hW t ht)
  have hRpos : ∀ t ∈ Ioo (0 : ℝ) b, 0 < R t := by
    intro t ht
    exact div_pos (curveDensity_pos (I := I) g γ V t (hLI t ht))
      (hypDensity_pos hqa ht.1)
  apply mean_le_hyp_of_ratio hqa hd hm hmle hR hRpos
  simpa only [R, d] using hRatioLower

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry

end
