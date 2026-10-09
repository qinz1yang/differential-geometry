import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientRicciPinching
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceMetricEvolution


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology

private theorem ancient_eq_terminal_of_deriv_zero {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Iic 0))
    (hderiv : ∀ s < 0, HasDerivAt f 0 s) {t : ℝ} (ht : t ≤ 0) : f t = f 0 := by
  have hdiff : DifferentiableOn ℝ f (interior (Iic 0)) := by
    intro s hs
    exact (hderiv s (by simpa only [interior_Iic, mem_Iio] using hs)).differentiableAt.differentiableWithinAt
  have hzero (s : ℝ) (hs : s ∈ interior (Iic 0)) : deriv f s = 0 :=
    (hderiv s (by simpa only [interior_Iic, mem_Iio] using hs)).deriv
  have hm := monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont hdiff
    (fun s hs => by rw [hzero s hs])
  have ha := antitoneOn_of_deriv_nonpos (convex_Iic 0) hcont hdiff
    (fun s hs => by rw [hzero s hs])
  exact le_antisymm (hm ht (by simp) ht) (ha ht (by simp) ht)


theorem ancient_positive_quadratic_ode_profile {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Iic 0)) (hpos : ∀ t ≤ 0, 0 < f t)
    (hderiv : ∀ s < 0, HasDerivAt f ((2 / 3) * f s ^ 2) s) :
    let T := 3 / (2 * f 0)
    0 < T ∧ ∀ t ≤ 0, f t = 3 / (2 * (T - t)) := by
  have hf0 : 0 < f 0 := hpos 0 le_rfl
  have hT : 0 < 3 / (2 * f 0) := by positivity
  refine ⟨hT, ?_⟩
  intro t ht
  let q : ℝ → ℝ := fun s => (f s)⁻¹ + (2 / 3) * s
  have hqcont : ContinuousOn q (Iic 0) :=
    (hcont.inv₀ (fun s hs => (hpos s hs).ne')).add
      (continuous_const.mul continuous_id).continuousOn
  have hqderiv (s : ℝ) (hs : s < 0) : HasDerivAt q 0 s := by
    have h := ((hderiv s hs).inv (hpos s hs.le).ne').add
      ((hasDerivAt_id s).const_mul (2 / 3))
    have hc : -((2 / 3) * f s ^ 2) / f s ^ 2 + (2 / 3) * 1 = 0 := by
      field_simp [(hpos s hs.le).ne']
      ring
    exact h.congr_deriv hc
  have hq := ancient_eq_terminal_of_deriv_zero hqcont hqderiv ht
  have htpos := hpos t ht
  have hden : 0 < 3 / (2 * f 0) - t := by linarith
  dsimp only [q] at hq
  simp only [mul_zero, add_zero, inv_eq_one_div] at hq
  apply (eq_div_iff (mul_pos (by norm_num) hden).ne').mpr
  have hinv : 1 / f t = 1 / f 0 - (2 / 3) * t := by linarith
  have hm := congrArg (fun r : ℝ => r * f t) hinv
  field_simp [htpos.ne', hf0.ne'] at hm ⊢
  nlinarith

private theorem ancient_continuousOn_timeSlice {P : Type*} [TopologicalSpace P]
    {f : ℝ → P → ℝ}
    (h : ContinuousOn (fun q : ℝ × P => f q.1 q.2) (Iic 0 ×ˢ univ)) (x : P) :
    ContinuousOn (fun t => f t x) (Iic 0) := by
  have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
  exact h.comp hmap.continuousOn (fun _ ht => ⟨ht, mem_univ x⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

omit [I.Boundaryless] [T2Space M] in
private theorem einstein3_ricci_reaction
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 3) (x : M)
    (hEin : ∀ v w : TangentSpace I x, metricRicciAt g x (vec2 v w) =
      (metricScalarAt g x / 3) * g.inner x v w) :
    2 * normSq0S g x 2 (metricRicciAt g x) = (2 / 3) * metricScalarAt g x ^ 2 := by
  have hRic : metricRicciAt g x = (metricScalarAt g x / 3) • metricTensor0S g x := by
    ext v
    have hv : v = vec2 (v 0) (v 1) := by
      funext i
      fin_cases i <;> rfl
    rw [hv, Tensor0SSpace.smul_apply, metricTensor0S_apply]
    exact hEin _ _
  have hmetric : normSq0S g x 2 (metricTensor0S g x) = 3 := by
    change metricTracePair0SAt g (metricTensor0S g x) = 3
    simpa only [hdim, Nat.cast_ofNat] using metricTracePair0SAt_metric g x
  rw [hRic, normSq0S_smul, hmetric]
  ring


theorem ancient_einstein3_scalar_hasDerivAt
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {t : ℝ} (ht : t < 0)
    (hconstant : ∃ R : ℝ, ∀ x : M, S.scalar t x = R)
    (hEin : ∀ x : M, ∀ v w : TangentSpace I x,
      S.ricciAt t x (vec2 v w) = (S.scalar t x / 3) * (S.family.metric t).inner x v w)
    (x : M) :
    HasDerivAt (fun s => S.scalar s x) ((2 / 3) * S.scalar t x ^ 2) t := by
  have he := (smoothOfSolution S hS).scalarEvolution (flowG S)
    (fun _ => rfl) (fun _ => rfl) ⟨t, ht⟩ x
  obtain ⟨R, hR⟩ := hconstant
  have hf : S.scalar t = fun _ => R := funext hR
  have hricci : S.ricci t x = metricRicciAt (S.family.metric t) x := by
    simpa only [SolutionOn.ricci, SolutionOn.family, SolutionFamily.ricciAt] using
      SolutionFamily.ricci_apply S.base t x
  have hreaction : 2 * normSq0S (S.family.metric t) x 2 (S.ricci t x) =
      (2 / 3) * S.scalar t x ^ 2 := by
    rw [hricci]
    exact einstein3_ricci_reaction (S.family.metric t) hdim x (hEin x)
  rw [hreaction] at he
  simp only [hf, laplacianAt, laplacian_const, zero_add] at he
  simpa only [hR x] using he.hasDerivAt (ancientTimeInterval.regular_mem_nhds ht)


theorem ancient_einstein3_scalar_profile
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hpositive : ∀ t ≤ 0, ∀ x : M, 0 < S.scalar t x)
    (hconstant : ∀ t ≤ 0, ∃ R : ℝ, ∀ x : M, S.scalar t x = R)
    (hEin : ∀ t ≤ 0, ∀ x : M, ∀ v w : TangentSpace I x,
      S.ricciAt t x (vec2 v w) = (S.scalar t x / 3) * (S.family.metric t).inner x v w)
    (x₀ : M) :
    let T := 3 / (2 * S.scalar 0 x₀)
    0 < T ∧ ∀ t ≤ 0, ∀ x : M, S.scalar t x = 3 / (2 * (T - t)) := by
  have hcont : ContinuousOn (fun t => S.scalar t x₀) (Iic 0) :=
    ancient_continuousOn_timeSlice hS.scalarCont x₀
  obtain ⟨hT, hprofile⟩ := ancient_positive_quadratic_ode_profile hcont
    (fun t ht => hpositive t ht x₀)
    (fun t ht => ancient_einstein3_scalar_hasDerivAt S hS hdim ht
      (hconstant t ht.le) (hEin t ht.le) x₀)
  refine ⟨hT, fun t ht x => ?_⟩
  obtain ⟨R, hR⟩ := hconstant t ht
  exact ((hR x).trans (hR x₀).symm).trans (hprofile t ht)


theorem ancient_einstein3_roundScaling
    (S : SolutionOn (I := I) (M := M) ancientTimeInterval) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    (hpositive : ∀ t ≤ 0, ∀ x : M, 0 < S.scalar t x)
    (hconstant : ∀ t ≤ 0, ∃ R : ℝ, ∀ x : M, S.scalar t x = R)
    (hEin : ∀ t ≤ 0, ∀ x : M, ∀ v w : TangentSpace I x,
      S.ricciAt t x (vec2 v w) = (S.scalar t x / 3) * (S.family.metric t).inner x v w)
    (x₀ : M) :
    let T := 3 / (2 * S.scalar 0 x₀)
    ∃ hT : 0 < T,
      (∀ t ≤ 0, ∀ x : M, S.scalar t x = 3 / (2 * (T - t))) ∧
      ∀ (t : ℝ) (ht : t ≤ 0), S.family.metric t =
        scaleMetric ((T - t) / T) (div_pos (by linarith) hT) (S.family.metric 0) := by
  obtain ⟨hT, hscalar⟩ := ancient_einstein3_scalar_profile S hS hdim
    hpositive hconstant hEin x₀
  refine ⟨hT, hscalar, fun t ht => ?_⟩
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner]
  refine eq_linear_scale_of_ancient_reciprocal_ode hT (hS.smoothMetric.coeff_cont x v w) ?_ ht
  intro s hs
  have hd := metricDerivAt S hS ⟨s, hs⟩ x v w
  change HasDerivAt (fun r => (S.family.metric r).inner x v w)
    ((-2 : ℝ) * S.ricciAt s x (vec2 v w)) s at hd
  rw [hEin s hs.le x v w, hscalar s hs.le x] at hd
  exact hd.congr_deriv (by simp only [div_mul_eq_div_div]; ring)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
