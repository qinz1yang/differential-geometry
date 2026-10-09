import DifferentialGeometry.Geometry.Collapse.RadialFunctionBand
import DifferentialGeometry.Geometry.Collapse.RadialAnnularCutoff

/-!
# Consumer: from an LC28 smoothing output to the LC31 annular cutoff

Composes the unconditional tiers: an `F` with the LC28 output clauses for `Y = {p}` (sheet
`build-logs/resume/sheet-W3-F4.md`, Addendum 1) is an LC30 radial function
(`radialFunction_of_smoothing`, which uses LC29), and the standard profile
`cutoffProfile = smoothTransition (1 - ·)` turns it into the LC31 cutoff
`ζ = annularCutoff cutoffProfile ∘ F` (`annularCutoff_comp_radial`). Once the LC28 lane delivers
`F`, this is the radial-function and cutoff part of LC30–LC31 at one cone scale.
-/

set_option autoImplicit false

noncomputable section
open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- From LC28's output to the LC31 cutoff: `ζ = Φ ∘ F` (standard profile) is smooth, valued in
`[0, 1]`, one on `F⁻¹[3/10, 4/5]`, topologically supported in `{1/5 - e < d_p < 9/10 + e}`, with
`‖∇ζ‖ ≤ L_Φ (1 + ε)`, and `F` itself has the LC30 band properties. -/
theorem annularCutoff_of_smoothing (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (p : M) {ε e : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1) (he : e < 1 / 40) {F : M → ℝ} {O : Set M}
    (hO : IsOpen O) (hCO : {x : M | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ⊆ O)
    (hFO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O)
    (hclose : ∀ x, |F x - Metric.infDist x {p}| < e)
    (hout : ∀ x, x ∉ {x : M | 1 / 20 < dist x p ∧ dist x p < 20} → F x = Metric.infDist x {p})
    (hlip : ∀ x y,
      |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤ ε * dist x y) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
      (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
      tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
        {x : M | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
      ∀ q, Real.sqrt (g.inner q (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)
        (gradFun g (fun x => annularCutoff cutoffProfile (F x)) q)) ≤ L * (1 + ε) := by
  obtain ⟨-, -, hgrad, -, hsub, -⟩ :=
    radialFunction_of_smoothing g hEnorm p hε hε1 he hO hCO hFO hclose hout hlip
  obtain ⟨L, hL0, hL⟩ := exists_abs_deriv_annularCutoff_le cutoffProfile_contDiff
    fun _ ht => cutoffProfile_eq_zero ht
  have hdiff : LipschitzWith ⟨ε, hε⟩ (fun x => F x - Metric.infDist x {p}) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq]
      exact hlip x y
  have hFc : Continuous F := by
    have h := hdiff.continuous.add (Metric.continuous_infDist_pt ({p} : Set M))
    convert h using 1
    funext x
    simp only [Pi.add_apply, sub_add_cancel]
  simp only [Metric.infDist_singleton] at hclose
  have hband : F ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ F ⁻¹' Icc (1 / 5 : ℝ) 2 :=
    fun x hx => ⟨hx.1, hx.2.trans (by norm_num)⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := annularCutoff_comp_radial cutoffProfile_contDiff
    cutoffProfile_mem_Icc (fun _ ht => cutoffProfile_eq_one ht) (fun _ ht => cutoffProfile_eq_zero ht)
    g p hε hFc hO hFO (fun x hx => hCO (hsub (hband hx))) hclose
    (fun q hq => (hgrad q (hsub (hband hq))).2) hL
  exact ⟨L, hL0, hL, h1, h2, h3, h4, h5⟩

end DifferentialGeometry.Geometry.Collapse
