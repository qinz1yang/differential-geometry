import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Scalar.Comparison
import DifferentialGeometry.Geometry.Operator.LaplacianLinearity
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option autoImplicit false

noncomputable section

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Parabolic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def IsLinearSystemSolutionOn
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {n : ℕ}
    (C : ℝ → M → Fin n → Fin n → ℝ)
    (u : ℝ → M → Fin n → ℝ) (s T : ℝ) : Prop :=
  ∀ i : Fin n, ∀ t : ℝ, t ∈ Ioo s T → ∀ x : M,
    HasDerivAt (fun r : ℝ => u r x i)
      (laplacianAt (I := I) G t (fun y : M => u t y i) x +
        ∑ j : Fin n, C t x i j * u t x j) t

def euclideanNormSq {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i ^ 2

theorem euclideanNormSq_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ euclideanNormSq v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem euclideanNormSq_eq_zero_iff {n : ℕ} {v : Fin n → ℝ} :
    euclideanNormSq v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; simp [euclideanNormSq]⟩
  funext i
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
    ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mp h i (Finset.mem_univ i))

theorem hasDerivAt_component_sum_sq {n : ℕ} {f : Fin n → ℝ → ℝ} {f' : Fin n → ℝ}
    {t : ℝ} (h : ∀ i : Fin n, HasDerivAt (f i) (f' i) t) :
    HasDerivAt (fun s : ℝ => ∑ i : Fin n, f i s ^ 2)
      (∑ i : Fin n, 2 * f i t * f' i) t := by
  have hsum := HasDerivAt.sum (u := (Finset.univ : Finset (Fin n)))
    (A := fun i : Fin n => fun s : ℝ => f i s ^ 2)
    (A' := fun i : Fin n => 2 * f i t * f' i) (x := t) (fun i _ => by
      have h2 := (h i).pow 2
      have hfun : ((f i) ^ 2 : ℝ → ℝ) = fun s : ℝ => f i s ^ 2 := by
        funext s
        simp
      rw [hfun] at h2
      simpa [mul_assoc] using h2)
  have hfun : (∑ i : Fin n, fun s : ℝ => f i s ^ 2) =
      fun s : ℝ => ∑ i : Fin n, f i s ^ 2 := by
    funext s
    simp only [Finset.sum_apply]
  rw [hfun] at hsum
  exact hsum

theorem laplacianAt_univ_sum
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {n : ℕ}
    (f : Fin n → M → ℝ) (t : ℝ) (x : M)
    (hf : ∀ i : Fin n, ∀ y : M, MDifferentiableAt I 𝓘(ℝ, ℝ) (f i) y)
    (hgrad : ∀ i : Fin n,
      MDiffAt (T% fun y : M => gradientFun (I := I) (G.metric t) (f i) y) x) :
    laplacianAt (I := I) G t (fun y : M => ∑ i : Fin n, f i y) x =
      ∑ i : Fin n, laplacianAt (I := I) G t (f i) x := by
  simp only [laplacianAt_eq]
  exact laplacian_finset_sum_at (I := I) (G.connection t) (G.metric t)
    (Finset.univ : Finset (Fin n))
    (fun i _ => Filter.Eventually.of_forall (hf i)) (fun i _ => hgrad i)

theorem laplacianAt_sum_sq
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {n : ℕ}
    (u : M → Fin n → ℝ) (t : ℝ) (x : M)
    (hu : ∀ i : Fin n, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u y i)) :
    laplacianAt (I := I) G t (fun y : M => ∑ i : Fin n, u y i ^ 2) x =
      ∑ i : Fin n, laplacianAt (I := I) G t (fun y : M => u y i ^ 2) x := by
  refine laplacianAt_univ_sum (I := I) G (fun i : Fin n => fun y : M => u y i ^ 2) t x
    (fun i y => ((hu i).pow 2).contMDiffAt.mdifferentiableAt (by simp)) ?_
  intro i
  exact gradientFun_mdiffAt (I := I) (G.metric t) ((hu i).pow 2) x

theorem deriv_le_laplacianAt_of_linear_system
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {n : ℕ}
    (C : ℝ → M → Fin n → Fin n → ℝ) (u : ℝ → M → Fin n → ℝ)
    {t : ℝ} {x : M} {Λ : ℝ}
    (hu : ∀ i : Fin n, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u t y i))
    (hsys : ∀ i : Fin n, HasDerivAt (fun s : ℝ => u s x i)
      (laplacianAt (I := I) G t (fun y : M => u t y i) x +
        ∑ j : Fin n, C t x i j * u t x j) t)
    (hC : ∀ v : Fin n → ℝ,
      2 * (∑ i : Fin n, v i * (∑ j : Fin n, C t x i j * v j)) ≤ Λ * euclideanNormSq v) :
    deriv (fun s : ℝ => ∑ i : Fin n, u s x i ^ 2) t ≤
      laplacianAt (I := I) G t (fun y : M => ∑ i : Fin n, u t y i ^ 2) x +
        Λ * (∑ i : Fin n, u t x i ^ 2) := by
  have hderiv : deriv (fun s : ℝ => ∑ i : Fin n, u s x i ^ 2) t =
      ∑ i : Fin n, 2 * u t x i * (laplacianAt (I := I) G t (fun y : M => u t y i) x +
        ∑ j : Fin n, C t x i j * u t x j) :=
    (hasDerivAt_component_sum_sq hsys).deriv
  have hlap : laplacianAt (I := I) G t (fun y : M => ∑ i : Fin n, u t y i ^ 2) x =
      ∑ i : Fin n, (2 * u t x i * laplacianAt (I := I) G t (fun y : M => u t y i) x +
        2 * (G.metric t).inner x (gradientAt (I := I) G t (fun y : M => u t y i) x)
          (gradientAt (I := I) G t (fun y : M => u t y i) x)) := by
    rw [laplacianAt_sum_sq (I := I) G (u t) t x hu]
    exact Finset.sum_congr rfl (fun i _ =>
      laplacianAt_sq_of_scalarRegular (I := I) G t
        (fun y => ((hu i).contMDiffAt (x := y)).mdifferentiableAt (by simp))
        (fun y => gradientFun_mdiffAt (I := I) (G.metric t) (hu i) y))
  rw [hderiv, hlap]
  have hC' := hC (fun i : Fin n => u t x i)
  have hC'' : 2 * (∑ i : Fin n, u t x i * (∑ j : Fin n, C t x i j * u t x j)) ≤
      Λ * (∑ i : Fin n, u t x i ^ 2) := by
    simpa only [euclideanNormSq] using hC'
  have hinner : ∀ i : Fin n, 0 ≤ (G.metric t).inner x
      (gradientAt (I := I) G t (fun y : M => u t y i) x)
      (gradientAt (I := I) G t (fun y : M => u t y i) x) :=
    fun i => DifferentialGeometry.metric_inner_self_nonneg (I := I) (G.metric t) x _
  have hL : (∑ i : Fin n, 2 * u t x i *
        (laplacianAt (I := I) G t (fun y : M => u t y i) x +
          ∑ j : Fin n, C t x i j * u t x j)) =
      (∑ i : Fin n, 2 * u t x i * laplacianAt (I := I) G t (fun y : M => u t y i) x) +
        2 * (∑ i : Fin n, u t x i * (∑ j : Fin n, C t x i j * u t x j)) := by
    conv_rhs => rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hR : (∑ i : Fin n, (2 * u t x i * laplacianAt (I := I) G t (fun y : M => u t y i) x +
        2 * (G.metric t).inner x (gradientAt (I := I) G t (fun y : M => u t y i) x)
          (gradientAt (I := I) G t (fun y : M => u t y i) x))) =
      (∑ i : Fin n, 2 * u t x i * laplacianAt (I := I) G t (fun y : M => u t y i) x) +
        2 * (∑ i : Fin n, (G.metric t).inner x (gradientAt (I := I) G t (fun y : M => u t y i) x)
          (gradientAt (I := I) G t (fun y : M => u t y i) x)) := by
    conv_rhs => rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
  rw [hL, hR]
  have hsum : 0 ≤ ∑ i : Fin n, (G.metric t).inner x
      (gradientAt (I := I) G t (fun y : M => u t y i) x)
      (gradientAt (I := I) G t (fun y : M => u t y i) x) :=
    Finset.sum_nonneg (fun i _ => hinner i)
  linarith

theorem linear_system_eq_zero_of_initial_eq_zero
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {T : ℝ} (hT : 0 ≤ T) {n : ℕ}
    (C : ℝ → M → Fin n → Fin n → ℝ) (u : ℝ → M → Fin n → ℝ)
    (huSmooth : ∀ i : Fin n, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2 i) (Ioo 0 T ×ˢ (univ : Set M)))
    (huCont : ∀ i : Fin n, ContinuousOn (fun q : ℝ × M => u q.1 q.2 i)
      (Icc 0 T ×ˢ (univ : Set M)))
    (huSlice : ∀ i : Fin n, ∀ t ∈ Icc 0 T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u t y i))
    (hsys : IsLinearSystemSolutionOn (I := I) (M := M) G C u 0 T)
    (hC : ∃ Λ : ℝ, ∀ t ∈ Icc 0 T, ∀ x : M, ∀ v : Fin n → ℝ,
      2 * (∑ i : Fin n, v i * (∑ j : Fin n, C t x i j * v j)) ≤ Λ * euclideanNormSq v)
    (hinit : ∀ x : M, ∀ i : Fin n, u 0 x i = 0) :
    ∀ t ∈ Icc 0 T, ∀ x : M, ∀ i : Fin n, u t x i = 0 := by
  obtain ⟨Λ, hΛ⟩ := hC
  let w : ℝ → M → ℝ := fun t x => ∑ i : Fin n, u t x i ^ 2
  have hw : IsHeatPotSubsolutionOn (RealTimeInterval.closed 0 T hT) G (fun _ _ => Λ) w :=
    { jointSmooth := contMDiffOn_finsetSum (t := Finset.univ)
        (fun i _ => (huSmooth i).pow 2)
      jointCont := continuousOn_finsetSum Finset.univ (fun i _ => (huCont i).pow 2)
      sliceSmooth := fun t ht =>
        ContMDiff.sum (t := Finset.univ) (fun i _ => (huSlice i t ht).pow 2)
      timeDiff := fun t ht x =>
        (hasDerivAt_component_sum_sq (fun i => hsys i t ht x)).differentiableAt
      equation_le := fun t ht x =>
        deriv_le_laplacianAt_of_linear_system (I := I) G C u (fun i => huSlice i t
          (RealTimeInterval.regular_subset (RealTimeInterval.closed 0 T hT) ht))
          (fun i => hsys i t ht x) (fun v => hΛ t (RealTimeInterval.regular_subset
            (RealTimeInterval.closed 0 T hT) ht) x v) }
  have hzero : IsHeatPotSupersolutionOn (RealTimeInterval.closed 0 T hT) G
      (fun _ _ => Λ) (fun _ _ => (0 : ℝ)) :=
    { jointSmooth := contMDiffOn_const
      jointCont := continuousOn_const
      sliceSmooth := fun _ _ => contMDiff_const
      timeDiff := fun _ _ _ => differentiableAt_const 0
      equation_ge := fun t ht x => by
        rw [laplacianAt_eq, DifferentialGeometry.Geometry.Operator.laplacian_const]
        simp }
  have hle := heat_pot_comparison (I := I) G hT (fun _ _ => Λ) w (fun _ _ => (0 : ℝ))
    hw hzero Λ (fun t ht x => le_rfl) (fun x => by
      have h0 : w 0 x = 0 := by
        simp only [w]
        exact Finset.sum_eq_zero (fun i _ => by rw [hinit x i]; simp)
      rw [h0])
  intro t ht x i
  have hw0 : w t x = 0 := le_antisymm (hle t ht x)
    (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hsq : u t x i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u t x i))).mp hw0 i
      (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

private theorem quadraticForm_le_of_entry_bound {n : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (hM : ∀ i j, |M i j| ≤ Λ) :
    2 * (∑ i : Fin n, v i * (∑ j : Fin n, M i j * v j)) ≤
      (2 * (n : ℝ) * Λ) * ∑ i : Fin n, v i ^ 2 := by
  have h1 : ∑ i : Fin n, v i * (∑ j : Fin n, M i j * v j) ≤
      Λ * (∑ i : Fin n, |v i|) ^ 2 := by
    calc ∑ i : Fin n, v i * (∑ j : Fin n, M i j * v j)
        ≤ ∑ i : Fin n, ∑ j : Fin n, Λ * (|v i| * |v j|) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          calc v i * (M i j * v j) ≤ |v i * (M i j * v j)| := le_abs_self _
            _ = |v i| * |M i j| * |v j| := by rw [abs_mul, abs_mul, mul_assoc]
            _ ≤ |v i| * Λ * |v j| := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left (hM i j) (abs_nonneg _)) (abs_nonneg _)
            _ = Λ * (|v i| * |v j|) := by ring
      _ = Λ * (∑ i : Fin n, |v i|) ^ 2 := by
          have hinner : (∑ i : Fin n, ∑ j : Fin n, Λ * (|v i| * |v j|)) =
              Λ * ∑ i : Fin n, ∑ j : Fin n, |v i| * |v j| := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
          rw [hinner]
          congr 1
          rw [← Finset.sum_mul_sum, sq]
  have h2 : (∑ i : Fin n, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, v i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
      (fun i : Fin n => |v i|) (fun _ : Fin n => (1 : ℝ))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    simp only [mul_one, one_pow, sq_abs] at h
    calc (∑ i : Fin n, |v i|) ^ 2 ≤ (∑ i : Fin n, v i ^ 2) * (n : ℝ) := h
      _ = (n : ℝ) * ∑ i : Fin n, v i ^ 2 := by ring
  calc 2 * (∑ i : Fin n, v i * (∑ j : Fin n, M i j * v j))
      ≤ 2 * (Λ * (∑ i : Fin n, |v i|) ^ 2) := by linarith
    _ = (2 * Λ) * (∑ i : Fin n, |v i|) ^ 2 := by ring
    _ ≤ (2 * Λ) * ((n : ℝ) * ∑ i : Fin n, v i ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (2 * (n : ℝ) * Λ) * ∑ i : Fin n, v i ^ 2 := by ring

theorem exists_quadratic_bound_of_continuousOn
    [CompactSpace M]
    {a b : ℝ} {n : ℕ} (C : ℝ → M → Fin n → Fin n → ℝ)
    (hC : ContinuousOn (fun q : ℝ × M => C q.1 q.2)
      (Icc a b ×ˢ (univ : Set M))) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ t ∈ Icc a b, ∀ x : M, ∀ v : Fin n → ℝ,
      2 * (∑ i : Fin n, v i * (∑ j : Fin n, C t x i j * v j)) ≤ Λ * euclideanNormSq v := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hC
  refine ⟨2 * (n : ℝ) * max K 0, by positivity, fun t ht x v => ?_⟩
  refine le_trans (quadraticForm_le_of_entry_bound (le_max_right K 0) (C t x) v
    (fun i j => ?_)) (le_of_eq ?_)
  · calc |C t x i j| ≤ ‖C t x i‖ := norm_le_pi_norm (C t x i) j
      _ ≤ ‖C t x‖ := norm_le_pi_norm (C t x) i
      _ ≤ K := hK (t, x) ⟨ht, mem_univ x⟩
      _ ≤ max K 0 := le_max_left K 0
  · rw [euclideanNormSq]

theorem exists_isLinearSystemSolutionOn_with_quadratic_bound
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {T : ℝ} {n : ℕ} {v₀ : Fin n → ℝ}
    (hv₀ : v₀ ≠ 0) :
    ∃ (C : ℝ → M → Fin n → Fin n → ℝ) (u : ℝ → M → Fin n → ℝ),
      IsLinearSystemSolutionOn (I := I) (M := M) G C u 0 T ∧
        (∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ t ∈ Icc 0 T, ∀ x : M, ∀ v : Fin n → ℝ,
          2 * (∑ i : Fin n, v i * (∑ j : Fin n, C t x i j * v j)) ≤
            Λ * euclideanNormSq v) ∧
        u 0 = (fun _ : M => v₀) ∧ v₀ ≠ 0 := by
  refine ⟨fun _ _ _ _ => 0, fun _ _ => v₀, ?_,
    ⟨0, le_rfl, fun t ht x v => by simp [euclideanNormSq]⟩, rfl, hv₀⟩
  intro i t ht x
  have hlap : laplacianAt (I := I) G t (fun y : M => v₀ i) x = 0 := by
    rw [laplacianAt_eq, DifferentialGeometry.Geometry.Operator.laplacian_const]
  rw [hlap]
  simp [hasDerivAt_const]

theorem linear_system_eq_zero_of_initial_eq_zero_Icc
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {s T : ℝ} (hsT : s ≤ T) {n : ℕ}
    (C : ℝ → M → Fin n → Fin n → ℝ) (u : ℝ → M → Fin n → ℝ)
    (huSmooth : ∀ i : Fin n, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2 i) (Ioo s T ×ˢ (univ : Set M)))
    (huCont : ∀ i : Fin n, ContinuousOn (fun q : ℝ × M => u q.1 q.2 i)
      (Icc s T ×ˢ (univ : Set M)))
    (huSlice : ∀ i : Fin n, ∀ t ∈ Icc s T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u t y i))
    (hsys : IsLinearSystemSolutionOn (I := I) (M := M) G C u s T)
    (hC : ∃ Λ : ℝ, ∀ t ∈ Icc s T, ∀ x : M, ∀ v : Fin n → ℝ,
      2 * (∑ i : Fin n, v i * (∑ j : Fin n, C t x i j * v j)) ≤ Λ * euclideanNormSq v)
    (hinit : ∀ x : M, ∀ i : Fin n, u s x i = 0) :
    ∀ t ∈ Icc s T, ∀ x : M, ∀ i : Fin n, u t x i = 0 := by
  have hlen : 0 ≤ T - s := by linarith
  let G' : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := fun τ => G.metric (s + τ)
      connection := fun τ => G.connection (s + τ)
      metricCompatible := fun τ => G.metricCompatible (s + τ) }
  let shift : ℝ × M → ℝ × M := fun q => (s + q.1, q.2)
  let C' : ℝ → M → Fin n → Fin n → ℝ := fun τ x => C (s + τ) x
  let u' : ℝ → M → Fin n → ℝ := fun τ x => u (s + τ) x
  have hshift : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞ shift
      (Ioo 0 (T - s) ×ˢ (univ : Set M)) := by
    have hfst : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × M => s + q.1) (Ioo 0 (T - s) ×ˢ (univ : Set M)) :=
      (contMDiffOn_const).add (contMDiffOn_fst (I := 𝓘(ℝ, ℝ)) (J := I))
    exact hfst.prodMk (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I))
  have hmapS : MapsTo shift (Ioo 0 (T - s) ×ˢ (univ : Set M))
      (Ioo s T ×ˢ (univ : Set M)) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ q.2⟩
  have hmapC : MapsTo shift (Icc 0 (T - s) ×ˢ (univ : Set M))
      (Icc s T ×ˢ (univ : Set M)) := by
    intro q hq
    exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ q.2⟩
  have huSmooth' : ∀ i : Fin n, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u' q.1 q.2 i) (Ioo 0 (T - s) ×ˢ (univ : Set M)) := by
    intro i
    have hcomp := (huSmooth i).comp hshift hmapS
    convert hcomp using 1
    funext q
    rfl
  have huCont' : ∀ i : Fin n, ContinuousOn (fun q : ℝ × M => u' q.1 q.2 i)
      (Icc 0 (T - s) ×ˢ (univ : Set M)) := by
    intro i
    have hcont : ContinuousOn shift (Icc 0 (T - s) ×ˢ (univ : Set M)) :=
      ((continuousOn_const.add continuousOn_fst).prodMk continuousOn_snd)
    have hcomp := (huCont i).comp hcont hmapC
    convert hcomp using 1
    funext q
    rfl
  have huSlice' : ∀ i : Fin n, ∀ t ∈ Icc 0 (T - s),
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u' t y i) := by
    intro i t ht
    exact huSlice i (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hsys' : IsLinearSystemSolutionOn (I := I) (M := M) G' C' u' 0 (T - s) := by
    intro i τ hτ x
    have hbase : HasDerivAt (fun r : ℝ => u r x i)
        (laplacianAt (I := I) G (s + τ) (fun y : M => u (s + τ) y i) x +
          ∑ j : Fin n, C (s + τ) x i j * u (s + τ) x j) (s + τ) :=
      hsys i (s + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩ x
    refine HasDerivAt.comp_const_add (f := fun r : ℝ => u r x i)
      (f' := laplacianAt (I := I) G' τ (fun y : M => u' τ y i) x +
        ∑ j : Fin n, C' τ x i j * u' τ x j) s τ ?_
    exact hbase
  have hC' : ∃ Λ : ℝ, ∀ t ∈ Icc 0 (T - s), ∀ x : M, ∀ v : Fin n → ℝ,
      2 * (∑ i : Fin n, v i * (∑ j : Fin n, C' t x i j * v j)) ≤ Λ * euclideanNormSq v := by
    obtain ⟨Λ, hΛ⟩ := hC
    exact ⟨Λ, fun t ht x v =>
      hΛ (s + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x v⟩
  have hinit' : ∀ x : M, ∀ i : Fin n, u' 0 x i = 0 := by
    intro x i
    simpa only [u', add_zero] using hinit x i
  have hmain := linear_system_eq_zero_of_initial_eq_zero (I := I) G' hlen C' u'
    huSmooth' huCont' huSlice' hsys' hC' hinit'
  intro t ht x i
  have ht' : t - s ∈ Icc 0 (T - s) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h := hmain (t - s) ht' x i
  have hsub : s + (t - s) = t := by ring
  dsimp only [u'] at h
  rwa [hsub] at h

theorem linear_system_eq_zero_of_initial_eq_zero_of_continuousOn
    [I.Boundaryless] [CompactSpace M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ) {s T : ℝ} (hsT : s ≤ T) {n : ℕ}
    (C : ℝ → M → Fin n → Fin n → ℝ) (u : ℝ → M → Fin n → ℝ)
    (huSmooth : ∀ i : Fin n, ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × M => u q.1 q.2 i) (Ioo s T ×ˢ (univ : Set M)))
    (huCont : ∀ i : Fin n, ContinuousOn (fun q : ℝ × M => u q.1 q.2 i)
      (Icc s T ×ˢ (univ : Set M)))
    (huSlice : ∀ i : Fin n, ∀ t ∈ Icc s T,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => u t y i))
    (hsys : IsLinearSystemSolutionOn (I := I) (M := M) G C u s T)
    (hC : ContinuousOn (fun q : ℝ × M => C q.1 q.2)
      (Icc s T ×ˢ (univ : Set M)))
    (hinit : ∀ x : M, ∀ i : Fin n, u s x i = 0) :
    ∀ t ∈ Icc s T, ∀ x : M, ∀ i : Fin n, u t x i = 0 := by
  obtain ⟨Λ, -, hΛ⟩ := exists_quadratic_bound_of_continuousOn C hC
  exact linear_system_eq_zero_of_initial_eq_zero_Icc (I := I) G hsT C u
    huSmooth huCont huSlice hsys ⟨Λ, hΛ⟩ hinit

end DifferentialGeometry.Analysis.Parabolic
