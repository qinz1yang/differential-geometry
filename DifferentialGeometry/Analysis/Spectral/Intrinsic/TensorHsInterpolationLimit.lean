import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.FractionalPower
import DifferentialGeometry.Analysis.Spectral.Intrinsic.CompactSAResolventIntrinsic

/-!
# Spectral interpolation of `Hˢ`-convergence with uniform high-order mass

For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a spectral
Sobolev triple of orders `σ < σ' < σ''`, a sequence of tensor sections that

* converges in the *low* norm `Hˢ`, and
* carries a *uniform* high-order weighted mass bound (a uniform `H^{σ''}`
  norm bound),

automatically converges in every *intermediate* norm `H^{σ'}`. This is the
standard spectral interpolation / dominated-convergence brick: the weight ratio
`(1 + λᵢ)^{σ' - σ''} → 0` as the eigenvalue `λᵢ → ∞`, so the high-mode tail of
the `H^{σ'}` mass is controlled uniformly by the high-order mass bound, while on
the finitely many low modes (a finite set below any eigenvalue threshold,
`tensorEigenIdx_one_add_lambda_lt_finite`) the coordinates converge from the
`Hˢ` convergence. An `ε/2` split (uniform tail + finite low-mode part) then
forces `H^{σ'}` convergence.

## Main results

* `tensorHs_norm_tendsto_zero_of_low_tendsto_of_uniform` — the core single-
  sequence interpolation brick: for `d : ℕ → H^{σ''}` with a uniform `H^{σ''}`
  norm bound and `‖incl_{σ} (d n)‖ → 0`, also `‖incl_{σ'} (d n)‖ → 0`.
* `tensorHs_tendsto_of_tendsto_of_uniform_weightedMass` — the consumer-facing
  form: a sequence `u → ulim` in `Hˢ` with uniform high-order weighted mass `B`
  along the sequence and the same for the limit converges in the intermediate
  `H^{σ'}` norm of the difference.

## Sign convention

The eigenvalues `λᵢ ≥ 0` are the connection-Laplacian eigenvalues; the weight
is `tensorSobolevWeight i σ = (1 + λᵢ)^σ`. For `σ < σ' < σ''` the inclusions
`H^{σ''} → H^{σ'} → Hˢ` are coordinate-preserving contractions.
-/

noncomputable section

open Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Discreteness of the tensor connection-Laplacian spectrum below a
threshold.** For every threshold `Λ`, only finitely many eigen-indices `i`
satisfy `1 + λᵢ < Λ`. This is the standard discreteness of the spectrum of the
compact resolvent `tensorResolventL2 g r s`: the value map `i ↦ μ(i)` factors the
index set as a finite union over the (finitely many) resolvent eigenvalues
`μ` with `1/Λ < |μ|`, each with a finite-dimensional eigenspace fibre. -/
theorem tensorEigenIdx_one_add_lambda_lt_finite
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (Λ : ℝ) :
    {i : TensorEigenIdx (I := I) (M := M) g r s |
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ}.Finite := by
  classical
  by_cases hΛ : 0 < Λ
  · set B : Set (TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s) :=
      {μ | 1 + tensorLaplacianEigenvalueOf μ.val < Λ} with hB_def
    have hBfin : B.Finite := by
      apply Set.Finite.of_finite_image
        (f := fun μ : TensorNonzeroResolventEigenvalue (I := I) (M := M) g r s =>
          μ.val)
      · refine Set.Finite.subset
          (tensorResolvent_eigenvalues_finite_above (I := I) (M := M) g r s
            (DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s)
            (show (0 : ℝ) < 1 / Λ by positivity)) ?_
        rintro x ⟨μ, hμB, rfl⟩
        have hev : Module.End.HasEigenvalue
            ((tensorResolventL2 (I := I) (M := M) g r s).toLinearMap) μ.val :=
          μ.hasEigenvalue
        obtain ⟨u, hu_mem, hu_ne⟩ := μ.hasEigenvalue.exists_hasEigenvector
        have hu_in : u ∈ tensorResolventEigenspace (I := I) (M := M) g r s μ.val :=
          hu_mem
        have hμ_unit : μ.val ∈ Set.Ioc (0 : ℝ) 1 :=
          tensorResolvent_eigenvalue_mem_unit_interval
            (I := I) (M := M) g r s hu_in hu_ne
        have hμ_pos : 0 < μ.val := hμ_unit.1
        have hlt : 1 + tensorLaplacianEigenvalueOf μ.val < Λ := hμB
        have hinv : (μ.val)⁻¹ < Λ := by
          have heq : (μ.val)⁻¹ = 1 + tensorLaplacianEigenvalueOf μ.val := by
            rw [tensorLaplacianEigenvalueOf]
            field_simp; ring
          rw [heq]; exact hlt
        have hμ_gt : 1 / Λ < μ.val := by
          rw [div_lt_iff₀ hΛ]
          rw [inv_lt_iff_one_lt_mul₀ hμ_pos] at hinv
          linarith [hinv]
        exact ⟨hev, by rw [abs_of_pos hμ_pos]; exact le_of_lt hμ_gt⟩
      · intro μ₁ _ μ₂ _ h
        exact TensorNonzeroResolventEigenvalue.ext μ₁ μ₂ h
    have hset_eq :
        {i : TensorEigenIdx (I := I) (M := M) g r s |
          1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ}
          = ⋃ μ ∈ B, Sigma.mk μ '' Set.univ := by
      ext ⟨μ, k⟩
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_image, Set.mem_univ,
        true_and]
      constructor
      · intro h
        exact ⟨μ, by rw [hB_def]; exact h, k, rfl⟩
      · rintro ⟨μ', hμ'B, k', heq⟩
        obtain ⟨rfl, _⟩ := Sigma.mk.injEq .. ▸ heq
        rw [hB_def] at hμ'B; exact hμ'B
    rw [hset_eq]
    exact hBfin.biUnion (fun μ _ => Set.finite_univ.image _)
  · have hempty :
        {i : TensorEigenIdx (I := I) (M := M) g r s |
          1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro i hi
      have hlam := tensor_lambda_nonneg (I := I) (M := M) i
      have hΛle := not_lt.1 hΛ
      simp only [Set.mem_setOf_eq] at hi
      linarith
    rw [hempty]; exact Set.finite_empty

/-- The finite set of `(r,s)` tensor eigen-indices below the `n`-th spectral
threshold. -/
def eigenFinset (g : SmoothRiemannianMetric I M) (r s n : ℕ) :
    Finset (TensorEigenIdx (I := I) (M := M) g r s) :=
  (tensorEigenIdx_one_add_lambda_lt_finite
    (I := I) (M := M) g r s ((n : ℝ) + 1)).toFinset

/-- Membership in the generic tensor spectral truncation is the corresponding
strict eigenvalue bound. -/
lemma mem_eigenFinset (g : SmoothRiemannianMetric I M) (r s n : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    i ∈ eigenFinset (I := I) (M := M) g r s n ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < (n : ℝ) + 1 := by
  unfold eigenFinset
  rw [Set.Finite.mem_toFinset]
  rfl

/-- Generic tensor spectral truncations are monotone in the threshold. -/
lemma eigenFinset_mono (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Monotone (eigenFinset (I := I) (M := M) g r s) := by
  intro m n hmn i hi
  rw [mem_eigenFinset] at hi ⊢
  have hcast : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
    have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    linarith
  exact hi.trans_le hcast

/-- Every tensor eigen-index belongs to a sufficiently large generic spectral
truncation. -/
lemma eigenFinset_exhaust (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    ∃ n : ℕ, i ∈ eigenFinset (I := I) (M := M) g r s n := by
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (1 + TensorEigenIdx.lambda (I := I) (M := M) i)
  refine ⟨n, ?_⟩
  rw [mem_eigenFinset]
  linarith

/-- Generic tensor spectral truncations tend to the whole eigen-index type. -/
lemma eigenFinset_tendsto (g : SmoothRiemannianMetric I M) (r s : ℕ) :
    Tendsto (eigenFinset (I := I) (M := M) g r s) atTop atTop :=
  tendsto_atTop_finset_of_monotone
    (eigenFinset_mono (I := I) (M := M) g r s)
    (eigenFinset_exhaust (I := I) (M := M) g r s)

namespace tensorHs

variable {g : SmoothRiemannianMetric I M} {r s : ℕ}

omit [CompleteSpace E] in
/-- A single weighted-square coordinate term of `T ∈ Hˢ` is bounded by the
squared `Hˢ` norm: `(1 + λᵢ)^σ · (coeff i T)² ≤ ‖T‖²`. -/
lemma weight_mul_coeff_sq_le_normSq {σ : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ)
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    tensorSobolevWeight (I := I) (M := M) i σ * (T.coeff i) ^ 2 ≤ ‖T‖ ^ 2 := by
  rw [norm_sq_eq_tsum (I := I) (M := M) T]
  refine Summable.le_tsum T.weighted_summable i (fun j _ => ?_)
  have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) j σ :=
    tensorSobolevWeight_nonneg (I := I) (M := M) j σ
  positivity

omit [CompleteSpace E] in
/-- **Per-mode coordinate continuity from `Hˢ` convergence to zero.** If the
`Hˢ` norms of `d n` tend to `0`, then each fixed coordinate `(d n).coeff i`
tends to `0`. -/
lemma coeff_tendsto_zero_of_norm_tendsto_zero {σ : ℝ}
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ)
    (hd : Tendsto (fun n => ‖d n‖) atTop (𝓝 0))
    (i : TensorEigenIdx (I := I) (M := M) g r s) :
    Tendsto (fun n => (d n).coeff i) atTop (𝓝 0) := by
  have hbd : ∀ n, |(d n).coeff i| ≤
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖d n‖ := by
    intro n
    have hwpos : 0 < tensorSobolevWeight (I := I) (M := M) i σ :=
      tensorSobolevWeight_pos (I := I) (M := M) i σ
    have hsqrtpos : 0 < Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) :=
      Real.sqrt_pos.mpr hwpos
    have hterm : tensorSobolevWeight (I := I) (M := M) i σ * ((d n).coeff i) ^ 2 ≤
        ‖d n‖ ^ 2 := weight_mul_coeff_sq_le_normSq (I := I) (M := M) (d n) i
    have hsq : ((d n).coeff i) ^ 2 ≤
        ((Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖d n‖) ^ 2 := by
      have hsqrt_sq :
          Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) ^ 2 =
            tensorSobolevWeight (I := I) (M := M) i σ :=
        sq_sqrt_tensorSobolevWeight (I := I) (M := M) i σ
      rw [mul_pow, inv_pow, hsqrt_sq, inv_mul_eq_div, le_div_iff₀ hwpos, mul_comm]
      exact hterm
    have hrhs_nonneg :
        0 ≤ (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ * ‖d n‖ :=
      mul_nonneg (le_of_lt (inv_pos.mpr hsqrtpos)) (norm_nonneg (d n))
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hrhs_nonneg] at h
  have hupper :
      Tendsto (fun n => (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹ *
        ‖d n‖) atTop (𝓝 0) := by
    have := hd.const_mul
      (Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ))⁻¹
    simpa using this
  have habs : Tendsto (fun n => |(d n).coeff i|) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => abs_nonneg _) hbd hupper
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

end tensorHs

/-- Coordinatewise convergence to zero, together with a uniform higher-order
Sobolev bound, implies convergence to zero after a strict Sobolev downshift.

The high-mode tail of `‖incl_{σ'}(d n)‖²` is bounded, uniformly in `n`, by
`Λ^{σ'-σ''}·C²` via the weight ratio `(1+λᵢ)^{σ'-σ''} ≤ Λ^{σ'-σ''}` on
`{Λ ≤ 1+λᵢ}` (negative exponent), which is made small by choosing the threshold
`Λ` large; the finite low-mode part tends to zero coordinatewise. -/
theorem tendsto_of_coeff
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ' σ'' : ℝ}
    (hσ'σ'' : σ' < σ'')
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  classical
  set ι := TensorEigenIdx (I := I) (M := M) g r s

  have hnormsq : ∀ n,
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ ^ 2 =
        ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' *
          ((d n).coeff i) ^ 2 := by
    intro n
    have h := tensorHs.norm_sq_eq_tsum (I := I) (M := M)
      (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n))
    rwa [tensorHsInclusion_coeff] at h

  have hsumm' : ∀ n, Summable (fun i : ι =>
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) :=
    fun n => tensorHs.weighted_summable_of_le (I := I) (M := M) hσ'σ''.le (d n)

  have hmass'' : ∀ n,
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2
        = ‖d n‖ ^ 2 :=
    fun n => (tensorHs.norm_sq_eq_tsum (I := I) (M := M) (d n)).symm

  suffices hsq : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖ ^ 2) atTop (𝓝 0) by
    have hnn : ∀ n,
        0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (d n)‖ := fun n => norm_nonneg _
    have hsqrt :
        Tendsto (fun n => Real.sqrt
          (‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            hσ'σ''.le (d n)‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at hsqrt
    refine hsqrt.congr (fun n => ?_)
    rw [Real.sqrt_sq (hnn n)]

  rw [Metric.tendsto_atTop]
  intro ε hε
  have hexp : σ' - σ'' < 0 := by linarith

  obtain ⟨Λ, hΛgt1, hΛtail⟩ :
      ∃ Λ : ℝ, 1 < Λ ∧ Λ ^ (σ' - σ'') * C ^ 2 < ε / 2 := by
    set δ : ℝ := (ε / 2) / (C ^ 2 + 1) with hδ_def
    have hδ_pos : 0 < δ := by
      have : (0 : ℝ) < C ^ 2 + 1 := by positivity
      rw [hδ_def]; positivity
    have htend : Tendsto (fun x : ℝ => x ^ (σ' - σ'')) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := σ'' - σ') (by linarith)
      rwa [show -(σ'' - σ') = σ' - σ'' by ring] at h
    have hev : ∀ᶠ x : ℝ in atTop, x ^ (σ' - σ'') < δ :=
      htend.eventually_lt_const hδ_pos
    obtain ⟨Λ, hΛ1, hΛδ⟩ := ((eventually_gt_atTop 1).and hev).exists
    refine ⟨Λ, hΛ1, ?_⟩
    have hΛδ_nn : 0 ≤ Λ ^ (σ' - σ'') := Real.rpow_nonneg (by linarith) _
    have hCsq_nn : 0 ≤ C ^ 2 := sq_nonneg C
    have h1 : Λ ^ (σ' - σ'') * C ^ 2 ≤ δ * C ^ 2 :=
      mul_le_mul_of_nonneg_right hΛδ.le hCsq_nn
    have h2 : δ * C ^ 2 < ε / 2 := by
      rw [hδ_def]
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
      have hεpos : 0 < ε / 2 := by linarith
      nlinarith [hεpos, hCsq_nn]
    linarith

  set F : Finset ι :=
    (tensorEigenIdx_one_add_lambda_lt_finite (I := I) (M := M) g r s Λ).toFinset
    with hF_def
  have hmemF : ∀ i : ι, i ∈ F ↔
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ := by
    intro i; rw [hF_def, Set.Finite.mem_toFinset]; rfl

  have hcompl_bd : ∀ (n : ℕ) (i : ι), i ∉ F →
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
    intro n i hi
    have hΛle : Λ ≤ 1 + TensorEigenIdx.lambda (I := I) (M := M) i := by
      by_contra hcon
      exact hi ((hmemF i).2 (lt_of_not_ge hcon))

    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ' =
        tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
          tensorSobolevWeight (I := I) (M := M) i σ'' := by
      rw [← tensorHs.tensorSobolevWeight_add (I := I) (M := M)]
      congr 1; ring
    have hratio : tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') ≤
        Λ ^ (σ' - σ'') := by
      unfold tensorSobolevWeight
      exact Real.rpow_le_rpow_of_nonpos (by linarith) hΛle hexp.le
    have hw''_nn : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
      tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
    have hcoeff_nn : 0 ≤ ((d n).coeff i) ^ 2 := sq_nonneg _
    calc
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
          = tensorSobolevWeight (I := I) (M := M) i (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) := by
            rw [hsplit]; ring
      _ ≤ Λ ^ (σ' - σ'') *
              (tensorSobolevWeight (I := I) (M := M) i σ'' * ((d n).coeff i) ^ 2) :=
            mul_le_mul_of_nonneg_right hratio (by positivity)

  have htail : ∀ n,
      ∑' i : { i : ι // i ∉ F },
          tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 ≤
        Λ ^ (σ' - σ'') * C ^ 2 := by
    intro n
    have hsub_summ' : Summable (fun i : { i : ι // i ∉ F } =>
        tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2) :=
      (hsumm' n).subtype _
    have hsub_summ'' : Summable (fun i : { i : ι // i ∉ F } =>
        Λ ^ (σ' - σ'') *
          (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2)) :=
      ((d n).weighted_summable.subtype _).mul_left _
    calc
      ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2
          ≤ ∑' i : { i : ι // i ∉ F },
              Λ ^ (σ' - σ'') *
                (tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' *
                  ((d n).coeff i) ^ 2) :=
            hsub_summ'.tsum_le_tsum
              (fun i => hcompl_bd n i.1 i.2) hsub_summ''
      _ = Λ ^ (σ' - σ'') *
            ∑' i : { i : ι // i ∉ F },
              tensorSobolevWeight (I := I) (M := M) (i : ι) σ'' * ((d n).coeff i) ^ 2 :=
            (tsum_mul_left)
      _ ≤ Λ ^ (σ' - σ'') *
            ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ'' *
              ((d n).coeff i) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            refine ((d n).weighted_summable.subtype _).tsum_le_tsum_of_inj
              Subtype.val Subtype.val_injective (fun i _ => ?_) (fun i => le_refl _)
              (d n).weighted_summable
            have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
              tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
            positivity
      _ ≤ Λ ^ (σ' - σ'') * C ^ 2 := by
            rw [hmass'' n]
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by linarith) _)
            have hnn : (0 : ℝ) ≤ ‖d n‖ := norm_nonneg _
            nlinarith [hCbd n, hnn, hC]

  have hfin0 : Tendsto (fun n =>
      ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      atTop (𝓝 0) := by
    have h := tendsto_finset_sum (s := F)
      (f := fun i n => tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2)
      (a := fun _ : ι => (0 : ℝ))
      (fun i _ => by
        have hc : Tendsto (fun n => ((d n).coeff i) ^ 2) atTop (𝓝 (0 ^ 2)) :=
          (hcoeff0 i).pow 2
        rw [show (0 : ℝ) ^ 2 = 0 by ring] at hc
        have := hc.const_mul (tensorSobolevWeight (I := I) (M := M) i σ')
        simpa using this)
    simpa using h

  rw [Metric.tendsto_atTop] at hfin0
  obtain ⟨N, hN⟩ := hfin0 (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩

  have hsplit_sum :
      ∑' i : ι, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 =
        (∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2) +
          ∑' i : { i : ι // i ∉ F },
            tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 :=
    ((hsumm' n).sum_add_tsum_subtype_compl F).symm
  have hfin_lt : ∑ i ∈ F,
      tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2 < ε / 2 := by
    have hd := hN n hn
    rw [Real.dist_eq, sub_zero] at hd
    calc ∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2
        ≤ |∑ i ∈ F, tensorSobolevWeight (I := I) (M := M) i σ' * ((d n).coeff i) ^ 2| :=
          le_abs_self _
      _ < ε / 2 := hd
  have htail_lt : ∑' i : { i : ι // i ∉ F },
      tensorSobolevWeight (I := I) (M := M) (i : ι) σ' * ((d n).coeff i) ^ 2 < ε / 2 :=
    lt_of_le_of_lt (htail n) hΛtail
  have hbound : ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 < ε := by
    rw [hnormsq n, hsplit_sum]
    linarith

  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
      hσ'σ''.le (d n)‖ ^ 2 := sq_nonneg _
  rwa [abs_of_nonneg hnn]

/-- Coordinatewise continuity and a uniform higher-order Sobolev bound imply
continuity after a strict Sobolev downshift. -/
theorem cont_of_coeff
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ' σ'' : ℝ}
    (hσ'σ'' : σ' < σ'') (W : X → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ x, ‖W x‖ ≤ C)
    (hcoeff : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Continuous (fun x => (W x).coeff i)) :
    Continuous (fun x =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (W x)) := by
  rw [continuous_iff_seqContinuous]
  intro x x₀ hx
  let d : ℕ → tensorHs (I := I) (M := M) g r s σ'' :=
    fun n => W (x n) - W x₀
  have hd_bound (n : ℕ) : ‖d n‖ ≤ 2 * C := by
    calc
      ‖d n‖ = ‖W (x n) - W x₀‖ := rfl
      _ ≤ ‖W (x n)‖ + ‖W x₀‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add (hCbd _) (hCbd _)
      _ = 2 * C := by ring
  have hd_coeff (i : TensorEigenIdx (I := I) (M := M) g r s) :
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0) := by
    have hi := ((hcoeff i).tendsto x₀).comp hx
    have hi' : Tendsto (fun n => (W (x n)).coeff i - (W x₀).coeff i)
        atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hi
    simpa only [d, sub_eq_add_neg, tensorHs.add_coeff, tensorHs.neg_coeff,
      Pi.add_apply, Pi.neg_apply] using hi'
  have hnorm := tendsto_of_coeff (I := I) (M := M) hσ'σ'' d
    (mul_nonneg (by norm_num) hC) hd_bound hd_coeff
  have hzero : Tendsto (fun n =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hsub : Tendsto (fun n =>
      tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (W (x n)) -
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          hσ'σ''.le (W x₀)) atTop (𝓝 0) := by
    refine hzero.congr' (Eventually.of_forall fun n => ?_)
    simp only [d, map_sub]
  exact tendsto_sub_nhds_zero_iff.mp hsub

/-- If a uniformly high-order bounded sequence tends to zero in a lower
Sobolev norm, then it tends to zero at every strict intermediate order. -/
theorem tensorHs_norm_tendsto_zero_of_low_tendsto_of_uniform
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ σ' σ'' : ℝ}
    (hσσ' : σ ≤ σ') (hσ'σ'' : σ' < σ'')
    (d : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    {C : ℝ} (hC : 0 ≤ C) (hCbd : ∀ n, ‖d n‖ ≤ C)
    (hlow : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)‖) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (d n)‖) atTop (𝓝 0) := by
  have hcoeff0 : ∀ i : TensorEigenIdx (I := I) (M := M) g r s,
      Tendsto (fun n => (d n).coeff i) atTop (𝓝 0) := by
    intro i
    have h := tensorHs.coeff_tendsto_zero_of_norm_tendsto_zero (I := I) (M := M)
      (fun n => tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)) hlow i
    simpa only [tensorHsInclusion_coeff_apply] using h
  exact tendsto_of_coeff (I := I) (M := M) hσ'σ'' d hC hCbd hcoeff0

omit [CompleteSpace E] in
/-- A uniform weighted-mass bound bounds the `H^{σ''}` norm: if
`∑' i, (1 + λᵢ)^{σ''} · (T.coeff i)² ≤ B`, then `‖T‖_{σ''} ≤ √B`. -/
private lemma norm_le_sqrt_of_weightedMass_le
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ'' : ℝ}
    (T : tensorHs (I := I) (M := M) g r s σ'') {B : ℝ}
    (hB : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' * (T.coeff i) ^ 2 ≤ B) :
    ‖T‖ ≤ Real.sqrt B := by
  have hsq : ‖T‖ ^ 2 ≤ B := by
    rw [tensorHs.norm_sq_eq_tsum (I := I) (M := M) T]; exact hB
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg T)] at h

/-- **Spectral interpolation of `Hˢ`-convergence with uniform high-order mass.**
Let `σ ≤ σ' < σ''` be Sobolev orders. Suppose a sequence `u : ℕ → H^{σ''}` of
tensor sections converges to `ulim : H^{σ''}` in the *low* `Hˢ` topology (i.e.
the `Hˢ`-inclusions converge), and that both the sequence and its limit satisfy
a *uniform* high-order weighted-mass bound

  `∑' i, (1 + λᵢ)^{σ''} · (coeff i)² ≤ B`.

Then the differences `u n − ulim` converge to `0` in the *intermediate* `H^{σ'}`
norm. This is the gate-limit transfer brick: low-norm convergence plus a uniform
high-order spectral-mass bound upgrades to convergence in every intermediate
norm. -/
theorem tensorHs_tendsto_of_tendsto_of_uniform_weightedMass
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {σ σ' σ'' : ℝ}
    (hσσ' : σ ≤ σ') (hσ'σ'' : σ' < σ'')
    (u : ℕ → tensorHs (I := I) (M := M) g r s σ'')
    (ulim : tensorHs (I := I) (M := M) g r s σ'') {B : ℝ}
    (hconv : Tendsto (fun n =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) (u n)) atTop
        (𝓝 (tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) ulim)))
    (humass : ∀ n, ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' * ((u n).coeff i) ^ 2 ≤ B)
    (hlmass : ∑' i : TensorEigenIdx (I := I) (M := M) g r s,
      tensorSobolevWeight (I := I) (M := M) i σ'' * (ulim.coeff i) ^ 2 ≤ B) :
    Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        hσ'σ''.le (u n - ulim)‖) atTop (𝓝 0) := by

  set d : ℕ → tensorHs (I := I) (M := M) g r s σ'' := fun n => u n - ulim with hd_def

  have hBnn : 0 ≤ B :=
    le_trans (tsum_nonneg (fun i => by
      have hw : 0 ≤ tensorSobolevWeight (I := I) (M := M) i σ'' :=
        tensorSobolevWeight_nonneg (I := I) (M := M) i σ''
      positivity)) hlmass

  have hCbd : ∀ n, ‖d n‖ ≤ 2 * Real.sqrt B := by
    intro n
    have hu : ‖u n‖ ≤ Real.sqrt B :=
      norm_le_sqrt_of_weightedMass_le (I := I) (M := M) (u n) (humass n)
    have hl : ‖ulim‖ ≤ Real.sqrt B :=
      norm_le_sqrt_of_weightedMass_le (I := I) (M := M) ulim hlmass
    calc ‖d n‖ = ‖u n - ulim‖ := by rw [hd_def]
      _ ≤ ‖u n‖ + ‖ulim‖ := norm_sub_le _ _
      _ ≤ Real.sqrt B + Real.sqrt B := add_le_add hu hl
      _ = 2 * Real.sqrt B := by ring

  have hlow : Tendsto (fun n =>
      ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
        (hσσ'.trans hσ'σ''.le) (d n)‖) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n =>
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) (u n) -
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
          (hσσ'.trans hσ'σ''.le) ulim) atTop (𝓝 0) :=
      tendsto_sub_nhds_zero_iff.mpr hconv
    have heq : ∀ n,
        tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) (u n) -
          tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) ulim =
          tensorHsInclusion (I := I) (M := M) (g := g) (r := r) (s := s)
            (hσσ'.trans hσ'σ''.le) (d n) := by
      intro n; rw [hd_def, map_sub]
    rw [tendsto_zero_iff_norm_tendsto_zero] at hsub
    exact hsub.congr (fun n => by rw [heq n])
  exact tensorHs_norm_tendsto_zero_of_low_tendsto_of_uniform (I := I) (M := M)
    hσσ' hσ'σ'' d (by positivity) hCbd hlow

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry
