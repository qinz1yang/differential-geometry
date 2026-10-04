import DifferentialGeometry.Analysis.Elliptic.Poisson
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.LaplacianDifference
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Green.Identities
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

/-!
# Variable-metric Poisson stability

Review 17 §6.2 (and §5.3 step 4): stability of mean-zero solutions of `Δ_g f = q` when the metric
varies, on a compact connected closed manifold.

* `exists_poincare_const`: the Poincaré inequality `∫ u² ≤ C ∫ |∇u|²` for mean-zero smooth `u`,
  from the spectral gap and the eigenbasis of the Laplacian (Parseval) and Green's identity.
* `exists_poincare_const_of_uniformlyEquivalent`: one Poincaré constant for all metrics that are
  `Λ`-equivalent to a fixed metric (volume densities and gradient norms are compared pointwise).
* `tendsto_meanZero_poisson_of_metric_tendsto`: if `g k → gInf` in the background `C¹` sense
  (`metricDerivNorm a (g k) gInf h → 0` uniformly for `a ≤ 1`), `q k → qInf` uniformly, and
  `f k`, `fInf` are the mean-zero solutions, then `f k → fInf` in `L²(g k)` and
  `∇(f k - fInf) → 0` in `L²(g k)` (estimates of order one in `L²`). The proof combines the uniform
  Poincaré inequality, the energy identity, the Laplacian difference estimate
  `lapDiff_sq_le` and the convergence of the volume densities (mean normalisation).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators lp
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.DivergenceTheorem

section Poincare

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
private theorem inner_smoothToLp_eq_integral_mul'
    (g : SmoothRiemannianMetric I M) (f h : SmoothScalar g) :
    ⟪smoothToLp (I := I) (M := M) g f, smoothToLp (I := I) (M := M) g h⟫_ℝ =
      ∫ x, f.toFun x * h.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) f.memLp_two,
    MemLp.coeFn_toLp (p := (2 : ℝ≥0∞))
      (μ := riemannianVolumeMeasure (I := I) (M := M) g) h.memLp_two] with x hx₁ hx₂
  rw [smoothToLp_apply, smoothToLp_apply, hx₁, hx₂, Real.inner_apply]

private theorem inner_eigenbasis_eq_zero_of_eigenvalue_zero [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (q : SmoothScalar g)
    (hq : (∫ x, q.toFun x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0)
    (i : Σ μ : NonzeroResolventEigenvalue (I := I) (M := M) g,
      Fin (Module.finrank ℝ (resolventEigenspace (I := I) (M := M) g μ.val)))
    (hi : laplacianEigenvalueOf i.1.val = 0) :
    ⟪resolventHilbertEigenbasisSigma (I := I) (M := M) g i,
      smoothToLp (I := I) (M := M) g q⟫_ℝ = 0 := by
  classical
  let b := resolventEigenbasisSigma (I := I) (M := M) g i
  have hbridge : b = resolventHilbertEigenbasisSigma (I := I) (M := M) g i := rfl
  have hμ1 : i.1.val = 1 := by
    have hne : i.1.val ≠ 0 := i.1.val_ne_zero
    unfold laplacianEigenvalueOf at hi
    rw [div_eq_zero_iff] at hi
    rcases hi with h | h
    · linarith
    · exact absurd h hne
  have hmem : b ∈ resolventEigenspace (I := I) (M := M) g i.1.val := by
    rw [hbridge]
    simpa only [resolventHilbertEigenbasisSigma_apply] using
      resolventEigenbasisVec_mem (I := I) (M := M) g i
  have hRu : resolventL2 (I := I) (M := M) g b = b := by
    have h := (mem_resolventEigenspace_iff (I := I) (M := M) g i.1.val b).mp hmem
    rw [hμ1, one_smul] at h
    exact h
  let v : laplacianDomain (I := I) (M := M) g :=
    ⟨resolvent (I := I) (M := M) g b,
      (laplacianDomain_mem_iff (I := I) (M := M) g).mpr ⟨b, rfl⟩⟩
  have hv : (v : H1Compl (I := I) (M := M) g) = resolvent (I := I) (M := M) g b := rfl
  have hpre : laplacianDomain.preimage (I := I) (M := M) g v = b := by
    apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq (I := I) (M := M) g v, hv]
  have hlap : laplacianOp (I := I) (M := M) g v = 0 := by
    rw [laplacianOp_apply, hpre, hv, ← resolventL2_apply, hRu, sub_self]
  obtain ⟨f, hfΔ, hfcls⟩ := exists_smooth_representative_of_laplacianOp_eq_smoothToLp
    (I := I) (M := M) g (0 : SmoothScalar g) v (by rw [hlap, map_zero])
  have hfΔzero : ∀ x : M, ΔG (I := I) g (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) x = 0 := by
    intro x
    have := hfΔ x
    simpa using this
  obtain ⟨c, hc⟩ := exists_eq_const_of_laplacian_eq_zero (I := I) (M := M) g
    (⟨f.toFun, f.smooth⟩ : C^∞⟮I, M; ℝ⟯) hfΔzero
  have hfconst : f = (⟨(fun _ : M => c), contMDiff_const⟩ : SmoothScalar g) := by
    apply SmoothScalar.ext
    funext x
    exact hc x
  have hcls : smoothToLp (I := I) (M := M) g f = b := by
    rw [← H1ComplToLp_smoothToH1Compl (I := I) (M := M) g f]
    rw [hfcls, hv, ← resolventL2_apply, hRu]
  have hb : resolventHilbertEigenbasisSigma (I := I) (M := M) g i =
      smoothToLp (I := I) (M := M) g
        (⟨(fun _ : M => c), contMDiff_const⟩ : SmoothScalar g) := by
    rw [← hbridge, ← hcls, hfconst]
  rw [hb, inner_smoothToLp_eq_integral_mul']
  have hint : (∫ x, (fun _ : M => c) x * q.toFun x
      ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = c * ∫ x, q.toFun x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    have hfun : (fun x : M => (fun _ : M => c) x * q.toFun x) =
        (fun x : M => c * q.toFun x) := rfl
    rw [hfun, integral_const_mul]
  rw [hint, hq, mul_zero]

theorem exists_poincare_const [ConnectedSpace M] (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : C^∞⟮I, M; ℝ⟯,
      (∫ x, u x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 →
        (∫ x, u x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * ∫ x, g.inner x ((gradG (I := I) g u :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  obtain ⟨c₀, hc₀, hgap⟩ := exists_pos_le_nonzeroLaplacianEigenvalueSet (I := I) (M := M) g
  refine ⟨c₀⁻¹, inv_pos.2 hc₀, fun u hu => ?_⟩
  set ū : SmoothScalar g := ⟨fun x => u x, u.contMDiff⟩ with hū
  set U := smoothToLp (I := I) (M := M) g ū with hU
  set uh : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g ū,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) ū⟩ with huh
  have hHU : H1ComplToLp (I := I) (M := M) g (uh : H1Compl g) = U :=
    H1ComplToLp_smoothToH1Compl (I := I) (M := M) g ū
  have hLU : laplacianOp (I := I) (M := M) g uh = smoothToLp (I := I) (M := M) g ū.laplacian :=
    laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian (I := I) (M := M) ū
  set b := resolventHilbertEigenbasisSigma (I := I) (M := M) g with hb
  have hcoef := fun i => laplacianOp_inner_eigenbasis (I := I) (M := M) g uh i
  have hP1 := b.hasSum_inner_mul_inner U U
  have hP2 := b.hasSum_inner_mul_inner U (laplacianOp (I := I) (M := M) g uh)
  have hterm : ∀ i, c₀ * (⟪U, b i⟫_ℝ * ⟪b i, U⟫_ℝ) ≤
      -(⟪U, b i⟫_ℝ * ⟪b i, laplacianOp (I := I) (M := M) g uh⟫_ℝ) := by
    intro i
    rw [hcoef i, hHU, real_inner_comm U (b i)]
    by_cases hi : laplacianEigenvalueOf i.1.val = 0
    · have h0 := inner_eigenbasis_eq_zero_of_eigenvalue_zero (I := I) (M := M) g ū hu i hi
      rw [← hU] at h0
      have h0' : ⟪U, b i⟫_ℝ = 0 := by rw [real_inner_comm]; exact h0
      simp [h0']
    · have hge := hgap _ (mem_nonzeroLaplacianEigenvalueSet_of_laplacianEigenvalueOf_ne_zero
        (I := I) (M := M) i.1 hi)
      have hsq := sq_nonneg ⟪b i, U⟫_ℝ
      nlinarith
  have hle := hasSum_le hterm (hP1.mul_left c₀) hP2.neg
  have hUU : ⟪U, U⟫_ℝ = ∫ x, u x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hU, inner_smoothToLp_eq_integral_mul']
    congr 1
    funext x
    simp [hū, sq]
  have hUL : ⟪U, laplacianOp (I := I) (M := M) g uh⟫_ℝ =
      -∫ x, g.inner x ((gradG (I := I) g u :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [hLU, hU, inner_smoothToLp_eq_integral_mul']
    have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g u.contMDiff u.contMDiff (HasCompactSupport.of_compactSpace _)
    rw [show (⟨_, u.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) = u from rfl] at hgreen
    rw [hgreen, neg_neg]
    congr 1
  rw [hUU, hUL, neg_neg] at hle
  rw [inv_mul_eq_div, le_div_iff₀ hc₀]
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem gradFun_sub_const (g : SmoothRiemannianMetric I M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x) (c : ℝ) :
    gradFun (I := I) g (fun y => f y - c) x = gradFun (I := I) g f x := by
  have h2 := (hf.hasMFDerivAt.sub (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, ℝ)) c x)).mfderiv
  have h3 : mfderiv I 𝓘(ℝ, ℝ) (fun y => f y - c) x = mfderiv I 𝓘(ℝ, ℝ) f x :=
    h2.trans (sub_zero _)
  simp only [gradFun_def, h3]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [CompactSpace M] in
private theorem inner_gradFun_le_of_le (g g₀ : SmoothRiemannianMetric I M) {Q : ℝ} (hQ : 0 ≤ Q)
    (f : M → ℝ) (x : M) (hcomp : ∀ v : TangentSpace I x, g.inner x v v ≤ Q * g₀.inner x v v) :
    g₀.inner x (gradFun (I := I) g₀ f x) (gradFun (I := I) g₀ f x) ≤
      Q * g.inner x (gradFun (I := I) g f x) (gradFun (I := I) g f x) := by
  set X := gradFun (I := I) g₀ f x
  set Y := gradFun (I := I) g f x
  have hXX : g₀.inner x X X = g.inner x Y X := by
    rw [inner_gradFun (I := I) g₀ f x X, inner_gradFun (I := I) g f x X]
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (v : TangentSpace I x), 0 ≤ q.inner x v v := by
    intro q v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hcs := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (I := I) g x Y X
  set A := g₀.inner x X X
  set B := g.inner x Y Y
  have hA := hnn g₀ X
  have hB := hnn g Y
  have hXg : g.inner x X X ≤ Q * A := hcomp X
  have h1 : A ≤ Real.sqrt B * Real.sqrt (Q * A) := by
    calc A = g.inner x Y X := hXX
      _ ≤ |g.inner x Y X| := le_abs_self _
      _ ≤ Real.sqrt B * Real.sqrt (g.inner x X X) := hcs
      _ ≤ Real.sqrt B * Real.sqrt (Q * A) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hXg) (Real.sqrt_nonneg _)
  have h2 : A ^ 2 ≤ B * (Q * A) := by
    have := mul_self_le_mul_self hA h1
    rwa [mul_mul_mul_comm, Real.mul_self_sqrt hB, Real.mul_self_sqrt (mul_nonneg hQ hA),
      ← sq] at this
  by_cases hA0 : A = 0
  · rw [hA0]; exact mul_nonneg hQ hB
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hA0)
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem integral_le_of_volumeDensity (g₀ g : SmoothRiemannianMetric I M) {Q : ℝ}
    (hQ : 0 < Q) (hcomp : ∀ x : M, ∀ v : TangentSpace I x, g.inner x v v ≤ Q * g₀.inner x v v)
    {F : M → ℝ} (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x) :
    (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      Real.sqrt (Q ^ Module.finrank ℝ E) *
        ∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g₀) := by
  have hfmc : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g₀) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g₀
  rw [integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (I := I) g₀ g F,
    ← integral_const_mul]
  refine integral_mono ?_ ?_ fun x => ?_
  · exact ((riemannianVolumeDensity_contMDiff (I := I) g₀ g).continuous.smul
      hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact (continuous_const.mul hF).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_right
      (riemannianVolumeDensity_le_of_inner_le (I := I) g₀ g hQ x (hcomp x)) (hF0 x)

theorem exists_poincare_const_of_uniformlyEquivalent [ConnectedSpace M]
    (g₀ : SmoothRiemannianMetric I M) (Λ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : SmoothRiemannianMetric I M,
      (∀ x : M, ∀ v : TangentSpace I x,
        Λ⁻¹ * g₀.inner x v v ≤ g.inner x v v ∧ g.inner x v v ≤ Λ * g₀.inner x v v) →
      ∀ u : C^∞⟮I, M; ℝ⟯,
        (∫ x, u x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 →
        (∫ x, u x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          C * ∫ x, g.inner x ((gradG (I := I) g u :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  obtain ⟨P, hP, hPo⟩ := exists_poincare_const (I := I) (M := M) g₀
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  have hΛ'0 : 0 < Λ' := lt_of_lt_of_le one_pos hΛ'1
  set D : ℝ := Real.sqrt (Λ' ^ Module.finrank ℝ E) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  refine ⟨D * P * Λ' * D + 1, by positivity, fun g hg u hu => ?_⟩
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x),
      0 ≤ q.inner x v v := by
    intro q x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hup : ∀ x : M, ∀ v : TangentSpace I x, g.inner x v v ≤ Λ' * g₀.inner x v v :=
    fun x v => (hg x v).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hnn g₀ x v))
  have hdown : ∀ x : M, ∀ v : TangentSpace I x, g₀.inner x v v ≤ Λ' * g.inner x v v := by
    intro x v
    by_cases hv : v = 0
    · subst hv; simp
    have hg0 := g₀.pos x v hv
    have hg1 := g.pos x v hv
    have hΛpos : 0 < Λ := by
      by_contra hneg
      push Not at hneg
      have := (hg x v).2
      nlinarith
    have h1 := (hg x v).1
    rw [inv_mul_le_iff₀ hΛpos] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hg1.le)
  have hfmc : ∀ q : SmoothRiemannianMetric I M,
      IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) q) :=
    fun q => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) q
  have hfin : ∀ q : SmoothRiemannianMetric I M,
      IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) q) :=
    fun q => riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) q
  have hint : ∀ (q : SmoothRiemannianMetric I M) {F : M → ℝ}, Continuous F →
      Integrable F (riemannianVolumeMeasure (I := I) (M := M) q) :=
    fun q F hF => hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  set μ₀ := riemannianVolumeMeasure (I := I) (M := M) g₀ with hμ₀
  set c : ℝ := (∫ x, u x ∂μ₀) / (μ₀.real Set.univ) with hc
  have huc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => u y - c) := u.contMDiff.sub contMDiff_const
  set u' : C^∞⟮I, M; ℝ⟯ := ⟨fun y => u y - c, huc⟩ with hu'
  have hu'mean : (∫ x, u' x ∂μ₀) = 0 := by
    change (∫ x, (u x - c) ∂μ₀) = 0
    rw [integral_sub (hint g₀ u.contMDiff.continuous) (integrable_const c), integral_const,
      smul_eq_mul]
    rcases isEmpty_or_nonempty M with hM | hM
    · have h0 : riemannianVolumeMeasure (I := I) (M := M) g₀ = 0 :=
        Measure.eq_zero_of_isEmpty _
      simp [h0]
    · have hvolpos : (riemannianVolumeMeasure (I := I) (M := M) g₀).IsOpenPosMeasure :=
        riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g₀
      have hpos : 0 < μ₀.real Set.univ := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos _ isOpen_univ univ_nonempty)
          (measure_ne_top _ _)
      have hcancel : μ₀.real Set.univ * c = ∫ x, u x ∂μ₀ := by
        rw [hc]; field_simp
      linarith
  have hstep1 : (∫ x, u x ^ 2 ∂μ) ≤ ∫ x, (u x - c) ^ 2 ∂μ := by
    have hexp : ∀ x, (u x - c) ^ 2 = u x ^ 2 - 2 * c * u x + c ^ 2 := fun x => by ring
    simp_rw [hexp]
    have hI1 : Integrable (fun x => u x ^ 2) μ := hint g (u.contMDiff.continuous.pow 2)
    have hI2 : Integrable (fun x => 2 * c * u x) μ :=
      (hint g u.contMDiff.continuous).const_mul (2 * c)
    rw [integral_add (f := fun x => u x ^ 2 - 2 * c * u x) (g := fun _ => c ^ 2)
      (hI1.sub hI2) (integrable_const _),
      integral_sub (f := fun x => u x ^ 2) (g := fun x => 2 * c * u x) hI1 hI2,
      integral_const_mul, hu, integral_const, smul_eq_mul]
    have : 0 ≤ μ.real Set.univ * c ^ 2 := mul_nonneg measureReal_nonneg (sq_nonneg c)
    linarith
  have hstep2 : (∫ x, (u x - c) ^ 2 ∂μ) ≤ D * ∫ x, (u x - c) ^ 2 ∂μ₀ :=
    integral_le_of_volumeDensity (I := I) g₀ g hΛ'0 hup
      ((u.contMDiff.continuous.sub continuous_const).pow 2) (fun x => sq_nonneg _)
  have hstep3 : (∫ x, (u x - c) ^ 2 ∂μ₀) ≤ P * ∫ x, g₀.inner x
      ((gradG (I := I) g₀ u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g₀ u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ₀ := by
    have h := hPo u' hu'mean
    have hgr : ∀ x, (gradG (I := I) g₀ u' : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
        (gradG (I := I) g₀ u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := fun x => by
      simp only [grad_g_apply]
      exact gradFun_sub_const (I := I) g₀ (u.contMDiff.mdifferentiableAt (by simp)) c
    simp_rw [hgr] at h
    exact h
  have hgcont : ∀ q : SmoothRiemannianMetric I M, Continuous fun x => q.inner x
      ((gradG (I := I) q u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) q u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := by
    intro q
    have h := (tangentSectionAction_contMDiff (I := I) (gradG (I := I) q u)
      u.contMDiff).continuous
    refine h.congr fun x => ?_
    exact tangentSectionAction_eq_inner_grad_g (I := I) q u (gradG (I := I) q u) x
  have hgnn : ∀ (q : SmoothRiemannianMetric I M) (x : M), 0 ≤ q.inner x
      ((gradG (I := I) q u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) q u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) :=
    fun q x => hnn q x _
  have hcont' : Continuous fun x => g.inner x
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) := hgcont g
  have hstep4 : (∫ x, g₀.inner x
      ((gradG (I := I) g₀ u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g₀ u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ₀) ≤
      Λ' * ∫ x, g.inner x
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ₀ := by
    rw [← integral_const_mul]
    refine integral_mono (hint g₀ (hgcont g₀)) (hint g₀ (continuous_const.mul hcont'))
      fun x => ?_
    simp only [grad_g_apply]
    exact inner_gradFun_le_of_le (I := I) g g₀ hΛ'0.le u x (hup x)
  have hstep5 : (∫ x, g.inner x
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ₀) ≤
      D * ∫ x, g.inner x
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ :=
    integral_le_of_volumeDensity (I := I) g g₀ hΛ'0 hdown hcont' (hgnn g)
  have hJ0 : 0 ≤ ∫ x, g.inner x
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ :=
    integral_nonneg (hgnn g)
  have hDP : 0 ≤ D * P := mul_nonneg hD0 hP.le
  calc (∫ x, u x ^ 2 ∂μ) ≤ D * (P * (Λ' * (D * ∫ x, g.inner x
        ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ))) := by
        refine hstep1.trans (hstep2.trans (mul_le_mul_of_nonneg_left
          (hstep3.trans (mul_le_mul_of_nonneg_left (hstep4.trans
            (mul_le_mul_of_nonneg_left hstep5 hΛ'0.le)) hP.le)) hD0))
    _ ≤ (D * P * Λ' * D + 1) * ∫ x, g.inner x
        ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ := by
        nlinarith

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] in
private theorem ΔG_sub_const' (g : SmoothRiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (c : ℝ) (x : M) :
    ΔG (I := I) g (⟨(fun y : M => f y - c), hf.sub contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) x =
      ΔG (I := I) g (⟨f, hf⟩ : C^∞⟮I, M; ℝ⟯) x := by
  have h := BochnerPolarised.Δ_g_sub (I := I) (M := M) g (f := f) (h := fun _ : M => c)
    hf contMDiff_const (hf.sub contMDiff_const) x
  have hc : ΔG (I := I) g (⟨(fun _ : M => c), contMDiff_const⟩ : C^∞⟮I, M; ℝ⟯) x = 0 := by
    convert Δ_g_const (I := I) g c x using 1
    rfl
  linarith [h, hc]

omit [NeZero (Module.finrank ℝ E)] in
private theorem poisson_energy_estimate [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (P : ℝ) (hP : 0 < P)
    (hPo : ∀ u : C^∞⟮I, M; ℝ⟯,
      (∫ x, u x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 →
        (∫ x, u x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
          P * ∫ x, g.inner x ((gradG (I := I) g u :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
    (F : C^∞⟮I, M; ℝ⟯) (σ : ℝ) (hσ : ∀ x, |ΔG (I := I) g F x| ≤ σ) :
    (∫ x, g.inner x ((gradG (I := I) g F : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) g F : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ≤
      P * σ ^ 2 * (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ ∧
    (∫ x, F x ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) g)) *
        (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ ≤
      P ^ 2 * σ ^ 2 * (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ ^ 2 +
        (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 := by
  classical
  set μ := riemannianVolumeMeasure (I := I) (M := M) g with hμ
  have hfmc : IsFiniteMeasureOnCompacts μ :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  have hfin : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hint : ∀ {G : M → ℝ}, Continuous G → Integrable G μ :=
    fun hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : μ = 0 := Measure.eq_zero_of_isEmpty _
    simp [h0]
  have hvolpos : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  set V := μ.real Set.univ with hV
  have hVpos : 0 < V := by
    rw [hV, measureReal_def]
    exact ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos _ isOpen_univ univ_nonempty)
      (measure_ne_top _ _)
  set c : ℝ := (∫ x, F x ∂μ) / V with hc
  have huc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => F y - c) := F.contMDiff.sub contMDiff_const
  set u : C^∞⟮I, M; ℝ⟯ := ⟨fun y => F y - c, huc⟩ with hu
  have hcancel : V * c = ∫ x, F x ∂μ := by rw [hc]; field_simp
  have humean : (∫ x, u x ∂μ) = 0 := by
    change (∫ x, (F x - c) ∂μ) = 0
    rw [integral_sub (hint F.contMDiff.continuous) (integrable_const c), integral_const,
      smul_eq_mul]
    linarith
  have hΔu : ∀ x, ΔG (I := I) g u x = ΔG (I := I) g F x := fun x =>
    ΔG_sub_const' (I := I) g F.contMDiff c x
  have hgru : ∀ x, (gradG (I := I) g u : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x =
      (gradG (I := I) g F : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x := fun x => by
    simp only [grad_g_apply]
    exact gradFun_sub_const (I := I) g (F.contMDiff.mdifferentiableAt (by simp)) c
  set En := ∫ x, g.inner x ((gradG (I := I) g F : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
    ((gradG (I := I) g F : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ with hEn
  have hgreen := green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
    (I := I) g u.contMDiff u.contMDiff (HasCompactSupport.of_compactSpace _)
  rw [show (⟨_, u.contMDiff⟩ : C^∞⟮I, M; ℝ⟯) = u from rfl] at hgreen
  simp_rw [hgru, hΔu] at hgreen
  have hEn_eq : En = -∫ x, u x * ΔG (I := I) g F x ∂μ := hgreen
  have hPu := hPo u humean
  simp_rw [hgru] at hPu
  have hucont : Continuous fun x => u x := u.contMDiff.continuous
  have hΔcont : Continuous fun x => ΔG (I := I) g F x := (Δ_g_contMDiff (I := I) g F).continuous
  have hpt : ∀ x, -(u x * ΔG (I := I) g F x) ≤ u x ^ 2 / (2 * P) + P / 2 * σ ^ 2 := by
    intro x
    have h1 : |ΔG (I := I) g F x| ≤ σ := hσ x
    have h2 : (ΔG (I := I) g F x) ^ 2 ≤ σ ^ 2 := by
      have := sq_abs (ΔG (I := I) g F x)
      nlinarith [abs_nonneg (ΔG (I := I) g F x)]
    have h3 : -(u x * ΔG (I := I) g F x) ≤ u x ^ 2 / (2 * P) + P / 2 * (ΔG (I := I) g F x) ^ 2 := by
      rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (u x + P * ΔG (I := I) g F x)]
    nlinarith
  have hEn_le : En ≤ (∫ x, u x ^ 2 ∂μ) / (2 * P) + P / 2 * σ ^ 2 * V := by
    rw [hEn_eq, ← integral_neg]
    have hI1 : Integrable (fun x => -(u x * ΔG (I := I) g F x)) μ :=
      hint (hucont.mul hΔcont).neg
    have hI2 : Integrable (fun x => u x ^ 2 / (2 * P)) μ :=
      hint ((hucont.pow 2).div_const _)
    have hI3 : Integrable (fun x => u x ^ 2 / (2 * P) + P / 2 * σ ^ 2) μ :=
      hint (((hucont.pow 2).div_const _).add continuous_const)
    have hmono : (∫ x, -(u x * ΔG (I := I) g F x) ∂μ) ≤
        ∫ x, (u x ^ 2 / (2 * P) + P / 2 * σ ^ 2) ∂μ :=
      integral_mono hI1 hI3 (fun x => hpt x)
    have hsplit : (∫ x, (u x ^ 2 / (2 * P) + P / 2 * σ ^ 2) ∂μ) =
        (∫ x, u x ^ 2 ∂μ) / (2 * P) + P / 2 * σ ^ 2 * V := by
      rw [integral_add (f := fun x => u x ^ 2 / (2 * P)) (g := fun _ => P / 2 * σ ^ 2) hI2
        (integrable_const _), integral_div, integral_const, smul_eq_mul]
      ring
    linarith
  have hEn_bd : En ≤ P * σ ^ 2 * V := by
    have h1 : (∫ x, u x ^ 2 ∂μ) / (2 * P) ≤ En / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  refine ⟨hEn_bd, ?_⟩
  have hu2 : (∫ x, u x ^ 2 ∂μ) ≤ P ^ 2 * σ ^ 2 * V := by
    calc (∫ x, u x ^ 2 ∂μ) ≤ P * En := hPu
      _ ≤ P * (P * σ ^ 2 * V) := mul_le_mul_of_nonneg_left hEn_bd hP.le
      _ = P ^ 2 * σ ^ 2 * V := by ring
  have hF2 : (∫ x, F x ^ 2 ∂μ) = (∫ x, u x ^ 2 ∂μ) + c ^ 2 * V := by
    have hexp : ∀ x, F x ^ 2 = u x ^ 2 + 2 * c * u x + c ^ 2 := fun x => by
      change F x ^ 2 = (F x - c) ^ 2 + 2 * c * (F x - c) + c ^ 2
      ring
    simp_rw [hexp]
    rw [integral_add (f := fun x => u x ^ 2 + 2 * c * u x) (g := fun _ => c ^ 2)
      ((hint (hucont.pow 2)).add ((hint hucont).const_mul (2 * c))) (integrable_const _),
      integral_add (f := fun x => u x ^ 2) (g := fun x => 2 * c * u x) (hint (hucont.pow 2))
        ((hint hucont).const_mul (2 * c)),
      integral_const_mul, humean, integral_const, smul_eq_mul]
    ring
  rw [hF2]
  have hcV : c ^ 2 * V * V = (∫ x, F x ∂μ) ^ 2 := by rw [← hcancel]; ring
  nlinarith [mul_le_mul_of_nonneg_right hu2 hVpos.le]

section Stability

variable [SigmaCompactSpace M] [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem eventually_derivNorm_self_lt (h gInf : SmoothRiemannianMetric I M)
    (g : ℕ → SmoothRiemannianMetric I M)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, a ≤ 1 → ∀ x : M,
      metricDerivNorm (I := I) a (g k) gInf h x < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, a ≤ 1 → ∀ x : M,
      metricDerivNorm (I := I) a (g k) gInf gInf x < ε := by
  obtain ⟨D, hD0, hD⟩ := exists_metric_deriv_norm_reference_bound (I := I) isCompact_univ h gInf 1
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := hg (ε / (2 * D + 1)) (by positivity)
  refine ⟨k₀, fun k hk a ha x => ?_⟩
  have h1 := hD (g k) gInf a ha x (Set.mem_univ x)
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h1
  have h2 := hk₀ k hk 0 (by norm_num) x
  have h3 := hk₀ k hk 1 le_rfl x
  have hpos : 0 < 2 * D + 1 := by positivity
  have h4 : D * (metricDerivNorm (I := I) 0 (g k) gInf h x +
      metricDerivNorm (I := I) 1 (g k) gInf h x) ≤ D * (2 * (ε / (2 * D + 1))) :=
    mul_le_mul_of_nonneg_left (by linarith) hD0
  have h5 : D * (2 * (ε / (2 * D + 1))) < ε := by
    rw [mul_div_assoc', mul_div_assoc', div_lt_iff₀ hpos]
    nlinarith
  linarith

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem eventually_abs_laplacian_sub_lt (h gInf : SmoothRiemannianMetric I M)
    (g : ℕ → SmoothRiemannianMetric I M)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, a ≤ 1 → ∀ x : M,
      metricDerivNorm (I := I) a (g k) gInf h x < ε)
    (f : C^∞⟮I, M; ℝ⟯) :
    ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : M,
      |ΔG (I := I) (g k) f x - ΔG (I := I) gInf f x| < ε := by
  classical
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨B1, hB1⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth (I := I) gInf
      (DifferentialGeometry.Geometry.Connection.leviHessSec (I := I) gInf f
        f.contMDiff)).continuous.continuousOn)
  obtain ⟨B2, hB2⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth (I := I) gInf
      (duSec (I := I) f f.contMDiff)).continuous.continuousOn)
  set K : ℝ := 8 * n ^ 2 * |B1| + 72 * n * |B2| + 1 with hK
  have hK0 : 0 < K := by positivity
  intro ε hε
  set η : ℝ := min (1 / (2 * (n + 1))) (ε / (2 * (Real.sqrt K + 1))) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  obtain ⟨k₀, hk₀⟩ := eventually_derivNorm_self_lt (I := I) h gInf g hg η hηpos
  refine ⟨k₀, fun k hk x => ?_⟩
  set ρ := metricDerivNormSupOn (I := I) Set.univ 1 (g k) gInf gInf with hρ
  have hρη : ρ ≤ η := metricDerivNormSupOn_le_of_forall (I := I) Set.univ 1 (g k) gInf gInf η
    hηpos.le (fun a ha y _ => (hk₀ k hk a ha y).le)
  have hρ0 : 0 ≤ ρ :=
    DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.metricDerivNormSupOn_nonneg
      (I := I) Set.univ 1 (g k) gInf gInf
  have hsmall : n * ρ ≤ 1 / 2 := by
    have h1 : η ≤ 1 / (2 * (n + 1)) := min_le_left _ _
    have h2 : n * ρ ≤ n * (1 / (2 * (n + 1))) := mul_le_mul_of_nonneg_left (hρη.trans h1) hn0
    have h3 : n * (1 / (2 * (n + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hlap := lapDiff_sq_le (I := I) gInf (g k) f.contMDiff x hsmall
  have hb1 := hB1 x (Set.mem_univ x)
  have hb2 := hB2 x (Set.mem_univ x)
  rw [Real.norm_eq_abs] at hb1 hb2
  have hsq : (ΔG (I := I) (g k) f x - ΔG (I := I) gInf f x) ^ 2 ≤ ρ ^ 2 * K := by
    have hh1 := ((le_abs_self _).trans hb1).trans (le_abs_self B1)
    have hh2 := ((le_abs_self _).trans hb2).trans (le_abs_self B2)
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
    calc (ΔG (I := I) (g k) f x - ΔG (I := I) gInf f x) ^ 2
        ≤ 8 * n ^ 2 * ρ ^ 2 * Tensor0SBundle.normSq0S (I := I) gInf x 2
            (DifferentialGeometry.Geometry.Connection.leviHessSec (I := I) gInf f
              f.contMDiff x) +
          72 * n * ρ ^ 2 * Tensor0SBundle.normSq0S (I := I) gInf x 1
            (duSec (I := I) f f.contMDiff x) := hlap
      _ ≤ 8 * n ^ 2 * ρ ^ 2 * |B1| + 72 * n * ρ ^ 2 * |B2| := by
          gcongr
      _ ≤ ρ ^ 2 * K := by rw [hK]; nlinarith
  have habs : |ΔG (I := I) (g k) f x - ΔG (I := I) gInf f x| ≤ ρ * Real.sqrt K := by
    rw [← Real.sqrt_sq (abs_nonneg _), sq_abs, ← Real.sqrt_sq hρ0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  have hsK : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  have h2 : η ≤ ε / (2 * (Real.sqrt K + 1)) := min_le_right _ _
  have h3 : ρ * Real.sqrt K ≤ ε / (2 * (Real.sqrt K + 1)) * Real.sqrt K :=
    mul_le_mul_of_nonneg_right (hρη.trans h2) hsK
  have h4 : ε / (2 * (Real.sqrt K + 1)) * Real.sqrt K < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [CompleteSpace E]
  [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem exists_delta_density_close (gInf : SmoothRiemannianMetric I M) (η : ℝ)
    (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ ∀ g' : SmoothRiemannianMetric I M,
      (∀ x : M, ∀ v : TangentSpace I x,
        |g'.inner x v v - gInf.inner x v v| ≤ δ * gInf.inner x v v) →
      ∀ x : M, |riemannianVolumeDensity gInf g' x - 1| ≤ η := by
  set φ : ℝ → ℝ := fun t => Real.sqrt ((1 + 2 * t) ^ Module.finrank ℝ E) with hφ
  have hφc : Continuous φ := by
    rw [hφ]; fun_prop
  have hφ0 : φ 0 = 1 := by simp [hφ]
  obtain ⟨δ₁, hδ₁, hδ₁φ⟩ := Metric.continuous_iff.1 hφc 0 η hη
  refine ⟨min (δ₁ / 2) (1 / 2), lt_min (by positivity) (by norm_num), min_le_right _ _,
    fun g' hg' x => ?_⟩
  set δ := min (δ₁ / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ12 : δ ≤ 1 / 2 := min_le_right _ _
  have hφδ : φ δ < 1 + η := by
    have hd : dist δ 0 < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]
      exact (min_le_left _ _).trans_lt (by linarith)
    have := hδ₁φ δ hd
    rw [hφ0, Real.dist_eq] at this
    linarith [le_abs_self (φ δ - 1)]
  have hnn : ∀ (q : SmoothRiemannianMetric I M) (v : TangentSpace I x), 0 ≤ q.inner x v v := by
    intro q v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (q.pos x v hv).le
  have hQ : 0 < 1 + 2 * δ := by linarith
  have hup : ∀ v : TangentSpace I x, g'.inner x v v ≤ (1 + 2 * δ) * gInf.inner x v v := by
    intro v
    have := (abs_le.1 (hg' x v)).2
    nlinarith [hnn gInf v]
  have hdown : ∀ v : TangentSpace I x, gInf.inner x v v ≤ (1 + 2 * δ) * g'.inner x v v := by
    intro v
    have := (abs_le.1 (hg' x v)).1
    have h0 := hnn gInf v
    nlinarith [mul_nonneg (mul_nonneg hδ0.le (by linarith : (0 : ℝ) ≤ 1 / 2 - δ)) h0]
  have hd1 := riemannianVolumeDensity_le_of_inner_le (I := I) gInf g' hQ x hup
  have hd2 := riemannianVolumeDensity_le_of_inner_le (I := I) g' gInf hQ x hdown
  have hmul := riemannianVolumeDensity_mul (I := I) gInf g' gInf x
  rw [riemannianVolumeDensity_self] at hmul
  have hp1 := riemannianVolumeDensity_pos (I := I) gInf g' x
  have hp2 := riemannianVolumeDensity_pos (I := I) g' gInf x
  change riemannianVolumeDensity gInf g' x ≤ φ δ at hd1
  change riemannianVolumeDensity g' gInf x ≤ φ δ at hd2
  rw [abs_le]
  constructor
  · have : 1 ≤ riemannianVolumeDensity gInf g' x * (1 + η) := by
      calc (1 : ℝ) = riemannianVolumeDensity gInf g' x * riemannianVolumeDensity g' gInf x :=
            hmul.symm
        _ ≤ riemannianVolumeDensity gInf g' x * (1 + η) :=
            mul_le_mul_of_nonneg_left (hd2.trans hφδ.le) hp1.le
    nlinarith
  · linarith

private theorem stability_arith_l2 {P V A ε σ η Vk X B : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hε : 0 < ε) (hσ2 : σ ^ 2 = ε / (4 * (P + 1) ^ 2 * (V + 1)))
    (hη2 : η ^ 2 ≤ ε * V / (8 * (A ^ 2 + 1))) (hlo : V / 2 ≤ Vk) (hhi : Vk ≤ 2 * V)
    (hX : X * Vk ≤ P ^ 2 * σ ^ 2 * Vk ^ 2 + B) (hB : B ≤ η ^ 2 * A ^ 2) : X < ε := by
  have hVk0 : 0 < Vk := by linarith
  have h3 : P ^ 2 * σ ^ 2 * Vk ^ 2 ≤ P ^ 2 * σ ^ 2 * (2 * V) * Vk := by
    rw [sq Vk, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhi (by positivity)) hVk0.le
  have h4 : P ^ 2 * σ ^ 2 * (2 * V) < ε / 2 := by
    rw [hσ2, show P ^ 2 * (ε / (4 * (P + 1) ^ 2 * (V + 1))) * (2 * V) =
      ε / 2 * ((P ^ 2 / (P + 1) ^ 2) * (V / (V + 1))) by field_simp; ring]
    have ha : P ^ 2 / (P + 1) ^ 2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
    have hb : V / (V + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have ha0 : 0 ≤ P ^ 2 / (P + 1) ^ 2 := by positivity
    have hb0 : 0 ≤ V / (V + 1) := by positivity
    have h5 : P ^ 2 / (P + 1) ^ 2 * (V / (V + 1)) < 1 := by nlinarith
    nlinarith
  have h7 : η ^ 2 * A ^ 2 ≤ ε * V / (8 * (A ^ 2 + 1)) * A ^ 2 :=
    mul_le_mul_of_nonneg_right hη2 (sq_nonneg A)
  have h8 : ε * V / (8 * (A ^ 2 + 1)) * A ^ 2 < ε / 2 * (V / 2) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hV]
  have h9 : ε / 2 * (V / 2) ≤ ε / 2 * Vk := mul_le_mul_of_nonneg_left hlo (by positivity)
  have h10 : X * Vk < ε * Vk := by nlinarith
  exact lt_of_mul_lt_mul_right h10 hVk0.le

private theorem stability_arith_energy {P V ε σ Vk Y : ℝ} (hP : 0 < P) (hV : 0 < V)
    (hε : 0 < ε) (hσ2 : σ ^ 2 = ε / (4 * (P + 1) ^ 2 * (V + 1))) (hhi : Vk ≤ 2 * V)
    (hY : Y ≤ P * σ ^ 2 * Vk) : Y < ε := by
  have h1 : P * σ ^ 2 * Vk ≤ P * σ ^ 2 * (2 * V) :=
    mul_le_mul_of_nonneg_left hhi (by positivity)
  have h2 : P * σ ^ 2 * (2 * V) = ε * ((P / (P + 1) ^ 2) * (V / (V + 1)) / 2) := by
    rw [hσ2]; field_simp; ring
  have ha : P / (P + 1) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]; nlinarith
  have hb : V / (V + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have ha0 : 0 ≤ P / (P + 1) ^ 2 := by positivity
  have hb0 : 0 ≤ V / (V + 1) := by positivity
  have h3 : (P / (P + 1) ^ 2) * (V / (V + 1)) / 2 < 1 := by nlinarith
  have h4 : ε * ((P / (P + 1) ^ 2) * (V / (V + 1)) / 2) < ε := by nlinarith
  linarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompleteSpace E]
  [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem volume_mean_bounds_of_density (gInf g' : SmoothRiemannianMetric I M)
    (fInf : C^∞⟮I, M; ℝ⟯)
    (hfInfmean : (∫ x, fInf x ∂(riemannianVolumeMeasure (I := I) (M := M) gInf)) = 0)
    (η : ℝ) (hη12 : η ≤ 1 / 2)
    (hρ : ∀ x : M, |riemannianVolumeDensity gInf g' x - 1| ≤ η) :
    (riemannianVolumeMeasure (I := I) (M := M) gInf).real Set.univ / 2 ≤
        (riemannianVolumeMeasure (I := I) (M := M) g').real Set.univ ∧
      (riemannianVolumeMeasure (I := I) (M := M) g').real Set.univ ≤
        2 * (riemannianVolumeMeasure (I := I) (M := M) gInf).real Set.univ ∧
      |∫ x, fInf x ∂(riemannianVolumeMeasure (I := I) (M := M) g')| ≤
        η * ∫ x, |fInf x| ∂(riemannianVolumeMeasure (I := I) (M := M) gInf) := by
  set μI := riemannianVolumeMeasure (I := I) (M := M) gInf with hμI
  set μk := riemannianVolumeMeasure (I := I) (M := M) g' with hμk
  have hfmc : IsFiniteMeasureOnCompacts μI :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) gInf
  have hfin : IsFiniteMeasure μI :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) gInf
  have hint : ∀ {G : M → ℝ}, Continuous G → Integrable G μI :=
    fun hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρcont : Continuous fun x => riemannianVolumeDensity gInf g' x :=
    (riemannianVolumeDensity_contMDiff (I := I) gInf g').continuous
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : ∀ r : SmoothRiemannianMetric I M,
        riemannianVolumeMeasure (I := I) (M := M) r = 0 := fun r => Measure.eq_zero_of_isEmpty _
    simp [hμI, hμk, h0]
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hρ (Classical.arbitrary M))
  set V := μI.real Set.univ with hV
  have hvolk : μk.real Set.univ = ∫ x, riemannianVolumeDensity gInf g' x ∂μI := by
    have h1 := integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (I := I) gInf
      g' (fun _ : M => (1 : ℝ))
    simp only [integral_const, smul_eq_mul, mul_one] at h1
    exact h1
  have hvolb : |μk.real Set.univ - V| ≤ η * V := by
    have h1 : μk.real Set.univ - V = ∫ x, (riemannianVolumeDensity gInf g' x - 1) ∂μI := by
      rw [integral_sub (hint hρcont) (integrable_const 1), integral_const, smul_eq_mul,
        mul_one, ← hvolk]
    rw [h1]
    refine (abs_integral_le_integral_abs).trans ?_
    calc (∫ x, |riemannianVolumeDensity gInf g' x - 1| ∂μI) ≤ ∫ _x, η ∂μI :=
          integral_mono (hint (hρcont.sub continuous_const).abs) (integrable_const η)
            (fun x => hρ x)
      _ = η * V := by rw [integral_const, smul_eq_mul, mul_comm]
  have hV0 : 0 ≤ V := measureReal_nonneg
  have hfInfk : |∫ x, fInf x ∂μk| ≤ η * ∫ x, |fInf x| ∂μI := by
    have h1 : (∫ x, fInf x ∂μk) =
        ∫ x, (riemannianVolumeDensity gInf g' x - 1) * fInf x ∂μI := by
      have hI1 : Integrable (fun x => riemannianVolumeDensity gInf g' x * fInf x) μI :=
        hint (hρcont.mul fInf.contMDiff.continuous)
      have hI2 : Integrable (fun x => fInf x) μI := hint fInf.contMDiff.continuous
      have heq : (fun x => (riemannianVolumeDensity gInf g' x - 1) * fInf x) =
          fun x => riemannianVolumeDensity gInf g' x * fInf x - fInf x := by
        funext x; ring
      rw [heq, integral_sub hI1 hI2, hfInfmean, sub_zero,
        integral_riemannianVolumeMeasure_eq_integral_volumeDensity_smul (I := I) gInf g']
      simp only [smul_eq_mul]
      rfl
    rw [h1]
    refine (abs_integral_le_integral_abs).trans ?_
    calc (∫ x, |(riemannianVolumeDensity gInf g' x - 1) * fInf x| ∂μI) ≤
        ∫ x, η * |fInf x| ∂μI := by
          refine integral_mono (hint ((hρcont.sub continuous_const).mul
            fInf.contMDiff.continuous).abs)
            (hint (continuous_const.mul fInf.contMDiff.continuous.abs)) fun x => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hρ x) (abs_nonneg _)
      _ = η * ∫ x, |fInf x| ∂μI := by rw [integral_const_mul]
  have hlo := (abs_le.1 hvolb).1
  have hhi := (abs_le.1 hvolb).2
  refine ⟨?_, ?_, hfInfk⟩
  · nlinarith
  · nlinarith


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [CompactSpace M] [SigmaCompactSpace M]
  [IsManifold I 1 M] [IsManifold I 2 M] [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem quad_close_of_derivNorm (gInf g' : SmoothRiemannianMetric I M) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (hm : ∀ x : M, metricDerivNorm (I := I) 0 g' gInf gInf x <
      δ / ((Module.finrank ℝ E : ℝ) + 1)) :
    ∀ x : M, ∀ v : TangentSpace I x,
      |g'.inner x v v - gInf.inner x v v| ≤ δ * gInf.inner x v v := by
  intro x v
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have h1 := metricQuadFormDiff_le_metricDerivNorm (I := I) g' gInf gInf x v
  have hfr : (Module.finrank ℝ (TangentSpace I x) : ℝ) = n := rfl
  rw [hfr] at h1
  have h0 : 0 ≤ gInf.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (gInf.pos x v hv).le
  have h3 : n * metricDerivNorm (I := I) 0 g' gInf gInf x ≤ δ := by
    have h4 : n * metricDerivNorm (I := I) 0 g' gInf gInf x ≤ n * (δ / (n + 1)) :=
      mul_le_mul_of_nonneg_left (hm x).le hn0
    have h5 : n * (δ / (n + 1)) ≤ δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right h3 h0)

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [CompactSpace M] [SigmaCompactSpace M]
  [CompleteSpace E] [IsManifold I 1 M] [IsManifold I 2 M]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem abs_laplacian_sub_le (g' gInf : SmoothRiemannianMetric I M)
    (fk fInf qk qInf : C^∞⟮I, M; ℝ⟯) (σ : ℝ)
    (hf : ∀ x : M, ΔG (I := I) g' fk x = qk x) (hfInf : ∀ x : M, ΔG (I := I) gInf fInf x = qInf x)
    (hlap : ∀ x : M, |ΔG (I := I) g' fInf x - ΔG (I := I) gInf fInf x| < σ / 2)
    (hq : ∀ x : M, |qk x - qInf x| < σ / 2) :
    ∀ x : M, |ΔG (I := I) g' (fk - fInf) x| ≤ σ := by
  intro x
  have hsub : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => fk y - fInf y) :=
    fk.contMDiff.sub fInf.contMDiff
  have hFk : (fk - fInf) = (⟨fun y : M => fk y - fInf y, hsub⟩ : C^∞⟮I, M; ℝ⟯) := rfl
  rw [hFk, BochnerPolarised.Δ_g_sub (I := I) (M := M) g' fk.contMDiff fInf.contMDiff hsub x]
  change |ΔG (I := I) g' fk x - ΔG (I := I) g' fInf x| ≤ σ
  rw [hf x]
  have h1 := hq x
  have h2 := hlap x
  rw [hfInf] at h2
  have : |qk x - ΔG (I := I) g' fInf x| ≤ |qk x - qInf x| + |ΔG (I := I) g' fInf x - qInf x| := by
    rw [abs_sub_comm (ΔG (I := I) g' fInf x)]
    exact abs_sub_le _ _ _
  linarith

theorem tendsto_meanZero_poisson_of_metric_tendsto [ConnectedSpace M]
    (h gInf : SmoothRiemannianMetric I M) (g : ℕ → SmoothRiemannianMetric I M)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, a ≤ 1 → ∀ x : M,
      metricDerivNorm (I := I) a (g k) gInf h x < ε)
    (q : ℕ → C^∞⟮I, M; ℝ⟯) (qInf : C^∞⟮I, M; ℝ⟯)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ x : M, |q k x - qInf x| < ε)
    (f : ℕ → C^∞⟮I, M; ℝ⟯) (fInf : C^∞⟮I, M; ℝ⟯)
    (hfmean : ∀ k : ℕ, (∫ x, f k x ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) = 0)
    (hf : ∀ k : ℕ, ∀ x : M, ΔG (I := I) (g k) (f k) x = q k x)
    (hfInfmean : (∫ x, fInf x ∂(riemannianVolumeMeasure (I := I) (M := M) gInf)) = 0)
    (hfInf : ∀ x : M, ΔG (I := I) gInf fInf x = qInf x) :
    Tendsto (fun k : ℕ => ∫ x, (f k x - fInf x) ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => ∫ x, (g k).inner x
        ((gradG (I := I) (g k) (f k - fInf) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) (g k) (f k - fInf) :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) atTop (𝓝 0) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · have h0 : ∀ r : SmoothRiemannianMetric I M,
        riemannianVolumeMeasure (I := I) (M := M) r = 0 := fun r => Measure.eq_zero_of_isEmpty _
    simp [h0]
  have hfmc : ∀ r : SmoothRiemannianMetric I M,
      IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) r) :=
    fun r => riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) r
  have hint : ∀ (r : SmoothRiemannianMetric I M) {G : M → ℝ}, Continuous G →
      Integrable G (riemannianVolumeMeasure (I := I) (M := M) r) :=
    fun r G hG => hG.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hV0 : 0 < (riemannianVolumeMeasure (I := I) (M := M) gInf).real Set.univ := by
    have := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) gInf
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.IsOpenPosMeasure.open_pos _ isOpen_univ univ_nonempty)
      (measure_ne_top _ _)
  set V := (riemannianVolumeMeasure (I := I) (M := M) gInf).real Set.univ with hV
  set A := ∫ x, |fInf x| ∂(riemannianVolumeMeasure (I := I) (M := M) gInf) with hA
  obtain ⟨P, hP, hPo⟩ := exists_poincare_const_of_uniformlyEquivalent (I := I) (M := M) gInf 2
  have hgnn : ∀ (r : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x),
      0 ≤ r.inner x v v := by
    intro r x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (r.pos x v hv).le
  have key : ∀ ε : ℝ, 0 < ε → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      (∫ x, (f k x - fInf x) ^ 2 ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) < ε ∧
      (∫ x, (g k).inner x
        ((gradG (I := I) (g k) (f k - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ((gradG (I := I) (g k) (f k - fInf) : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) < ε := by
    intro ε hε
    have hσarg : 0 < ε / (4 * (P + 1) ^ 2 * (V + 1)) := by positivity
    have hσ0 : 0 < Real.sqrt (ε / (4 * (P + 1) ^ 2 * (V + 1))) := Real.sqrt_pos.2 hσarg
    have hηarg : 0 < ε * V / (8 * (A ^ 2 + 1)) := by positivity
    set η : ℝ := min (1 / 2) (Real.sqrt (ε * V / (8 * (A ^ 2 + 1)))) with hη
    have hη0 : 0 < η := lt_min (by norm_num) (Real.sqrt_pos.2 hηarg)
    have hη2 : η ^ 2 ≤ ε * V / (8 * (A ^ 2 + 1)) := by
      calc η ^ 2 ≤ Real.sqrt (ε * V / (8 * (A ^ 2 + 1))) ^ 2 :=
            pow_le_pow_left₀ hη0.le (min_le_right _ _) 2
        _ = ε * V / (8 * (A ^ 2 + 1)) := Real.sq_sqrt hηarg.le
    obtain ⟨δ, hδ0, hδ12, hδρ⟩ := exists_delta_density_close (I := I) gInf η hη0
    obtain ⟨k₁, hk₁⟩ := eventually_derivNorm_self_lt (I := I) h gInf g hg
      (δ / ((Module.finrank ℝ E : ℝ) + 1)) (by positivity)
    obtain ⟨k₂, hk₂⟩ := eventually_abs_laplacian_sub_lt (I := I) h gInf g hg fInf
      (Real.sqrt (ε / (4 * (P + 1) ^ 2 * (V + 1))) / 2) (by positivity)
    obtain ⟨k₃, hk₃⟩ := hq (Real.sqrt (ε / (4 * (P + 1) ^ 2 * (V + 1))) / 2) (by positivity)
    refine ⟨max k₁ (max k₂ k₃), fun k hk => ?_⟩
    have hk1 : k₁ ≤ k := (le_max_left _ _).trans hk
    have hk2 : k₂ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
    have hk3 : k₃ ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
    have hclose := quad_close_of_derivNorm (I := I) gInf (g k) δ hδ0.le
      (fun x => hk₁ k hk1 0 (by norm_num) x)
    have hequiv : ∀ x : M, ∀ v : TangentSpace I x,
        (2 : ℝ)⁻¹ * gInf.inner x v v ≤ (g k).inner x v v ∧
          (g k).inner x v v ≤ 2 * gInf.inner x v v := by
      intro x v
      have h1 := abs_le.1 (hclose x v)
      have h0 := hgnn gInf x v
      constructor <;> nlinarith
    obtain ⟨hlo, hhi, hmeanI⟩ := volume_mean_bounds_of_density (I := I) gInf (g k) fInf
      hfInfmean η (min_le_left _ _) (hδρ (g k) hclose)
    have hΔF := abs_laplacian_sub_le (I := I) (g k) gInf (f k) fInf (q k) qInf _ (hf k) hfInf
      (hk₂ k hk2) (hk₃ k hk3)
    have hest := poisson_energy_estimate (I := I) (g k) P hP (hPo (g k) hequiv) (f k - fInf) _
      hΔF
    have hmeanF : (∫ x, (f k - fInf) x ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) =
        -∫ x, fInf x ∂(riemannianVolumeMeasure (I := I) (M := M) (g k)) := by
      change (∫ x, (f k x - fInf x) ∂(riemannianVolumeMeasure (I := I) (M := M) (g k))) = _
      rw [integral_sub (hint (g k) (f k).contMDiff.continuous)
        (hint (g k) fInf.contMDiff.continuous), hfmean k, zero_sub]
    have hσ2 := Real.sq_sqrt hσarg.le
    refine ⟨?_, stability_arith_energy hP hV0 hε hσ2 hhi hest.1⟩
    have h1 := hest.2
    rw [hmeanF, neg_sq] at h1
    refine stability_arith_l2 hP hV0 hε hσ2 hη2 hlo hhi h1 ?_
    rw [← mul_pow, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hmeanI 2
  constructor
  · refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨k₀, hk₀⟩ := key ε hε
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
    exact (hk₀ k hk).1
  · refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨k₀, hk₀⟩ := key ε hε
    refine ⟨k₀, fun k hk => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun x => hgnn (g k) x _)]
    exact (hk₀ k hk).2

end Stability

end Poincare

end Laplacian
end Analysis
end DifferentialGeometry
