import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Matrix

section Abstract

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

private theorem exists_coeff_inv_gram_eq
    (gb : LinearMap.BilinForm ℝ F) (u e : ι → F)
    (hspan : ∀ k, e k ∈ Submodule.span ℝ (Set.range u))
    (hON : ∀ k l, gb (e k) (e l) = if k = l then 1 else 0) :
    ∃ C : Matrix ι ι ℝ, (∀ k, ∑ i, C k i • u i = e k) ∧
      (Matrix.of fun i j => gb (u i) (u j))⁻¹ = C.transpose * C := by
  choose C hC using fun k => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan k)
  let C' : Matrix ι ι ℝ := Matrix.of C
  let G : Matrix ι ι ℝ := Matrix.of fun i j => gb (u i) (u j)
  have hCGC : C' * (G * C'.transpose) = 1 := by
    ext k l
    have h := hON k l
    rw [← hC k, ← hC l] at h
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul] at h
    rw [Matrix.one_apply, ← h]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, C', G,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨C', fun k => hC k, ?_⟩
  have h1 : G * C'.transpose * C' = 1 := mul_eq_one_comm.mp hCGC
  exact Matrix.inv_eq_right_inv (by rw [← Matrix.mul_assoc]; exact h1)

theorem trace_inv_gram_mul_eq_sum_orthonormal
    (gb φ : LinearMap.BilinForm ℝ F) (u e : ι → F)
    (hspan : ∀ k, e k ∈ Submodule.span ℝ (Set.range u))
    (hON : ∀ k l, gb (e k) (e l) = if k = l then 1 else 0) :
    trace ((Matrix.of fun i j => gb (u i) (u j))⁻¹ * Matrix.of fun i j => φ (u i) (u j)) =
      ∑ k, φ (e k) (e k) := by
  obtain ⟨C, hC, hinv⟩ := exists_coeff_inv_gram_eq gb u e hspan hON
  rw [hinv, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hC k]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {Fa : Type*} [AddCommGroup Fa] [Module ℝ Fa]

omit [DecidableEq ι] in
private theorem index_sum_smul_left
    (Q : V → V → ℝ) (A : Submodule ℝ V)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Q (x + y) z = Q x z + Q y z)
    (hsmul : ∀ c : ℝ, ∀ x ∈ A, ∀ z ∈ A, Q (c • x) z = c * Q x z)
    (J : ι → V) (hJ : ∀ i, J i ∈ A) (c : ι → ℝ) {z : V} (hz : z ∈ A) :
    Q (∑ i, c i • J i) z = ∑ i, c i * Q (J i) z := by
  classical
  have hzero : Q 0 z = 0 := by
    have h := hsmul 0 z hz z hz
    rwa [zero_smul, zero_mul] at h
  suffices h : ∀ s : Finset ι, Q (∑ i ∈ s, c i • J i) z = ∑ i ∈ s, c i * Q (J i) z from
    h _
  intro s
  refine Finset.induction_on s ?_ ?_
  · simpa only [Finset.sum_empty] using hzero
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hadd _ (A.smul_mem _ (hJ i)) _ (A.sum_mem fun j _ => A.smul_mem _ (hJ j)) z hz,
      hsmul _ _ (hJ i) z hz, ih]

private theorem index_add_self
    (Q : V → V → ℝ) (A : Submodule ℝ V)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Q (x + y) z = Q x z + Q y z)
    (hsymm : ∀ x ∈ A, ∀ y ∈ A, Q x y = Q y x) {x y : V} (hx : x ∈ A) (hy : y ∈ A) :
    Q (x + y) (x + y) = Q x x + 2 * Q x y + Q y y := by
  have hxy := A.add_mem hx hy
  rw [hadd x hx y hy _ hxy, hsymm x hx _ hxy, hsymm y hy _ hxy, hadd x hx y hy x hx,
    hadd x hx y hy y hy, hsymm y hy x hx]
  ring

theorem trace_inv_gram_mul_boundary_le_sum_index
    (Q : V → V → ℝ) (A : Submodule ℝ V) (eva : V →ₗ[ℝ] Fa) (evb : V →ₗ[ℝ] F)
    (gb : LinearMap.BilinForm ℝ F) (Na : ι → Fa →ₗ[ℝ] ℝ)
    (Nb : ι → F →ₗ[ℝ] ℝ)
    (J W : ι → V)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Q (x + y) z = Q x z + Q y z)
    (hsmul : ∀ c : ℝ, ∀ x ∈ A, ∀ z ∈ A, Q (c • x) z = c * Q x z)
    (hsymm : ∀ x ∈ A, ∀ y ∈ A, Q x y = Q y x)
    (hbdry : ∀ i, ∀ x ∈ A, Q (J i) x = (1 / 2) * (Nb i (evb x) - Na i (eva x)))
    (hnonneg : ∀ x ∈ A, eva x = 0 → evb x = 0 → 0 ≤ Q x x)
    (hJ : ∀ i, J i ∈ A) (hW : ∀ k, W k ∈ A)
    (hJa : ∀ i, eva (J i) = 0) (hWa : ∀ k, eva (W k) = 0)
    (hspan : ∀ k, evb (W k) ∈ Submodule.span ℝ (Set.range fun i => evb (J i)))
    (hON : ∀ k l, gb (evb (W k)) (evb (W l)) = if k = l then 1 else 0) :
    trace ((Matrix.of fun i j => gb (evb (J i)) (evb (J j)))⁻¹ *
        Matrix.of fun i j => Nb i (evb (J j))) ≤ 2 * ∑ k, Q (W k) (W k) := by
  obtain ⟨C, hC, hinv⟩ :=
    exists_coeff_inv_gram_eq gb (fun i => evb (J i)) (fun k => evb (W k)) hspan hON
  let Jt : ι → V := fun k => ∑ i, C k i • J i
  have hJt : ∀ k, Jt k ∈ A := fun k => A.sum_mem fun i _ => A.smul_mem _ (hJ i)
  have hJtb : ∀ k, evb (Jt k) = evb (W k) := by
    intro k
    simp only [Jt, map_sum, map_smul]
    exact hC k
  have hJta : ∀ k, eva (Jt k) = 0 := by
    intro k
    simp only [Jt, map_sum, map_smul, hJa, smul_zero, Finset.sum_const_zero]
  have hQJ : ∀ i, ∀ x ∈ A, eva x = 0 → Q (J i) x = (1 / 2) * Nb i (evb x) := by
    intro i x hx hxa
    rw [hbdry i x hx, hxa, map_zero, sub_zero]
  have hdiag : ∀ k, (C * Matrix.of (fun i j => Nb i (evb (J j))) * C.transpose) k k =
      2 * Q (Jt k) (Jt k) := by
    intro k
    rw [index_sum_smul_left Q A hadd hsmul J hJ (C k) (hJt k)]
    simp only [hQJ _ _ (hJt k) (hJta k), Jt, map_sum, map_smul, smul_eq_mul, Finset.mul_sum,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hmin : ∀ k, Q (Jt k) (Jt k) ≤ Q (W k) (W k) := by
    intro k
    have hX : W k - Jt k ∈ A := A.sub_mem (hW k) (hJt k)
    have hXa : eva (W k - Jt k) = 0 := by rw [map_sub, hWa, hJta, sub_zero]
    have hXb : evb (W k - Jt k) = 0 := by rw [map_sub, hJtb, sub_self]
    have hcross : Q (Jt k) (W k - Jt k) = 0 := by
      rw [index_sum_smul_left Q A hadd hsmul J hJ (C k) hX]
      simp only [hQJ _ _ hX hXa, hXb, map_zero, mul_zero, Finset.sum_const_zero]
    have hexp := index_add_self Q A hadd hsymm (hJt k) hX
    rw [add_sub_cancel, hcross] at hexp
    have hnn := hnonneg _ hX hXa hXb
    linarith
  rw [hinv, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.trace, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Matrix.diag_apply, hdiag k]
  linarith [hmin k]

theorem half_trace_inv_gram_mul_gramDeriv_le_sum_index
    (Q : V → V → ℝ) (A : Submodule ℝ V) (eva : V →ₗ[ℝ] Fa) (evb : V →ₗ[ℝ] F)
    (gb R : LinearMap.BilinForm ℝ F) (Na : ι → Fa →ₗ[ℝ] ℝ)
    (Nb : ι → F →ₗ[ℝ] ℝ)
    (J W : ι → V) {c : ℝ} (hc : 0 ≤ c)
    (hadd : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, Q (x + y) z = Q x z + Q y z)
    (hsmul : ∀ c : ℝ, ∀ x ∈ A, ∀ z ∈ A, Q (c • x) z = c * Q x z)
    (hsymm : ∀ x ∈ A, ∀ y ∈ A, Q x y = Q y x)
    (hbdry : ∀ i, ∀ x ∈ A, Q (J i) x = (1 / 2) * (Nb i (evb x) - Na i (eva x)))
    (hnonneg : ∀ x ∈ A, eva x = 0 → evb x = 0 → 0 ≤ Q x x)
    (hJ : ∀ i, J i ∈ A) (hW : ∀ k, W k ∈ A)
    (hJa : ∀ i, eva (J i) = 0) (hWa : ∀ k, eva (W k) = 0)
    (hspan : ∀ k, evb (W k) ∈ Submodule.span ℝ (Set.range fun i => evb (J i)))
    (hON : ∀ k l, gb (evb (W k)) (evb (W l)) = if k = l then 1 else 0) :
    (1 / 2) * trace ((Matrix.of fun i j => gb (evb (J i)) (evb (J j)))⁻¹ *
        (c • (Matrix.of (fun i j => Nb i (evb (J j))) +
            (Matrix.of fun i j => Nb i (evb (J j))).transpose) +
          (2 : ℝ) • Matrix.of fun i j => R (evb (J i)) (evb (J j)))) ≤
      2 * c * ∑ k, Q (W k) (W k) + ∑ k, R (evb (W k)) (evb (W k)) := by
  obtain ⟨C, -, hinv⟩ :=
    exists_coeff_inv_gram_eq gb (fun i => evb (J i)) (fun k => evb (W k)) hspan hON
  let N : Matrix ι ι ℝ := Matrix.of fun i j => Nb i (evb (J j))
  have hT : trace ((Matrix.of fun i j => gb (evb (J i)) (evb (J j)))⁻¹ * N.transpose) =
      trace ((Matrix.of fun i j => gb (evb (J i)) (evb (J j)))⁻¹ * N) := by
    rw [hinv, ← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.trace_mul_comm]
  have hmain := trace_inv_gram_mul_boundary_le_sum_index Q A eva evb gb Na Nb J W hadd hsmul
    hsymm hbdry hnonneg hJ hW hJa hWa hspan hON
  have hR := trace_inv_gram_mul_eq_sum_orthonormal gb R (fun i => evb (J i))
    (fun k => evb (W k)) hspan hON
  change (1 / 2) * trace ((Matrix.of fun i j => gb (evb (J i)) (evb (J j)))⁻¹ *
      (c • (N + N.transpose) + (2 : ℝ) • Matrix.of fun i j => R (evb (J i)) (evb (J j))))
    ≤ _
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add, hT, hR, smul_eq_mul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hmain hc]

end Abstract

section SingleFlow

open Set
open scoped Manifold ContDiff

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M] in
private theorem differentiableAt_chartRepAt_of_mem_span
    (alpha : ℝ → M) (G : Set (∀ r, TangentSpace I (alpha r))) (K : Set ℝ)
    (hG : ∀ X ∈ G, ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s)
    {X : ∀ r, TangentSpace I (alpha r)} (hX : X ∈ Submodule.span ℝ G) :
    ∀ s ∈ K, DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s := by
  induction hX using Submodule.span_induction with
  | mem x hx => exact hG x hx
  | zero =>
    intro s _
    have h0 : chartRepAt (I := I) alpha (0 : ∀ r, TangentSpace I (alpha r)) s = fun _ => 0 := by
      funext u
      simp [chartRepAt]
    rw [h0]
    exact differentiableAt_const _
  | add x y _ _ hx hy =>
    intro s hs
    rw [show x + y = fun r => x r + y r from rfl, chartRepAt_add]
    exact (hx s hs).add (hy s hs)
  | smul c x _ hx =>
    intro s hs
    rw [show c • x = fun r => c • x r from rfl, chartRepAt_smul]
    exact (hx s hs).const_smul c

omit [I.Boundaryless] in
private theorem intervalIntegrable_integrand_of_mem_span
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (alpha : ℝ → M)
    (G : Set (∀ r, TangentSpace I (alpha r))) (a b : ℝ)
    (hG : ∀ X ∈ G, ∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s)
    (hGint : ∀ X ∈ G, ∀ Y ∈ G, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X Y)
      MeasureTheory.volume a b)
    {X Y : ∀ r, TangentSpace I (alpha r)} (hX : X ∈ Submodule.span ℝ G)
    (hY : Y ∈ Submodule.span ℝ G) :
    IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X Y) MeasureTheory.volume a b := by
  have hd := fun {Z : ∀ r, TangentSpace I (alpha r)} (hZ : Z ∈ Submodule.span ℝ G) =>
    differentiableAt_chartRepAt_of_mem_span alpha G (uIcc a b) hG hZ
  have hstep : ∀ X ∈ G, ∀ Y ∈ Submodule.span ℝ G,
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X Y) MeasureTheory.volume a b := by
    intro X hXG Y hY
    induction hY using Submodule.span_induction with
    | mem y hy => exact hGint X hXG y hy
    | zero =>
      have h0 : lRegularizedIndexIntegrand S T alpha X 0 = fun _ => 0 := by
        funext s
        have h := lRegularizedIndexIntegrand_smul_right (I := I) S T 0 alpha X X s
        simp only [zero_smul, zero_mul] at h
        exact h
      rw [h0]
      exact intervalIntegrable_const
    | add y z hy hz iy iz =>
      refine (intervalIntegrable_congr (fun s hs => ?_)).mp (iy.add iz)
      exact (lRegularizedIndexIntegrand_add_right (I := I) S T alpha X y z s
        (hd hy s (uIoc_subset_uIcc hs)) (hd hz s (uIoc_subset_uIcc hs))).symm
    | smul c y _ iy =>
      have hc : lRegularizedIndexIntegrand S T alpha X (c • y) =
          fun s => c * lRegularizedIndexIntegrand S T alpha X y s := by
        funext s
        exact lRegularizedIndexIntegrand_smul_right (I := I) S T c alpha X y s
      rw [hc]
      exact iy.const_mul c
  induction hX using Submodule.span_induction with
  | mem x hx => exact hstep x hx Y hY
  | zero =>
    have h0 : lRegularizedIndexIntegrand S T alpha 0 Y = fun _ => 0 := by
      funext s
      have h := lRegularizedIndexIntegrand_smul (I := I) S T 0 alpha Y Y s
      simp only [zero_smul, zero_mul] at h
      exact h
    rw [h0]
    exact intervalIntegrable_const
  | add x z hx hz ix iz =>
    refine (intervalIntegrable_congr (fun s hs => ?_)).mp (ix.add iz)
    exact (lRegularizedIndexIntegrand_add (I := I) S T alpha x z Y s
      (hd hx s (uIoc_subset_uIcc hs)) (hd hz s (uIoc_subset_uIcc hs))).symm
  | smul c x _ ix =>
    have hc : lRegularizedIndexIntegrand S T alpha (c • x) Y =
        fun s => c * lRegularizedIndexIntegrand S T alpha x Y s := by
      funext s
      exact lRegularizedIndexIntegrand_smul (I := I) S T c alpha x Y s
    rw [hc]
    exact ix.const_mul c

theorem trace_inv_gram_mul_covDerivAlong_le_sum_lRegularizedIndex
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (alpha : ℝ → M) (J W : ι → ∀ r, TangentSpace I (alpha r)) (a b : ℝ)
    (ht : ∀ s ∈ uIcc a b, T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I alpha r)
    (hA : ∀ s ∈ uIcc a b, DifferentiableAt ℝ
      (chartRepAt (I := I) alpha (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : ∀ i, IsLRegularizedJacobi S T alpha (J i) (uIcc a b))
    (hWd : ∀ k, ∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := I) alpha (W k) s) s)
    (hJJ : ∀ i j, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (J i) (J j))
      MeasureTheory.volume a b)
    (hJW : ∀ i k, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (J i) (W k))
      MeasureTheory.volume a b)
    (hWW : ∀ k l, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (W k) (W l))
      MeasureTheory.volume a b)
    (hnonneg : ∀ X : ∀ r, TangentSpace I (alpha r),
      (∀ s ∈ uIcc a b, DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s) →
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X X) MeasureTheory.volume a b →
      X a = 0 → X b = 0 → 0 ≤ lRegularizedIndex S T alpha X X a b)
    (hJa : ∀ i, J i a = 0) (hWa : ∀ k, W k a = 0)
    (hspan : ∀ k, W k b ∈ Submodule.span ℝ (Set.range fun i => J i b))
    (hON : ∀ k l, (S.base.metric (T - b ^ 2)).inner (alpha b) (W k b) (W l b) =
      if k = l then 1 else 0) :
    trace ((Matrix.of fun i j => (S.base.metric (T - b ^ 2)).inner (alpha b) (J i b) (J j b))⁻¹ *
        Matrix.of fun i j => (S.base.metric (T - b ^ 2)).inner (alpha b)
          (covDerivAlong (I := I) (S.base.metric (T - b ^ 2)) alpha (J i) b) (J j b)) ≤
      2 * ∑ k, lRegularizedIndex S T alpha (W k) (W k) a b := by
  let G : Set (∀ r, TangentSpace I (alpha r)) := Set.range J ∪ Set.range W
  have hG : ∀ X ∈ G, ∀ s ∈ uIcc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s := by
    rintro X (⟨i, rfl⟩ | ⟨k, rfl⟩)
    · exact fun s hs => (hjac i s hs).2.1
    · exact hWd k
  have hGint : ∀ X ∈ G, ∀ Y ∈ G,
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X Y)
      MeasureTheory.volume a b := by
    rintro X (⟨i, rfl⟩ | ⟨k, rfl⟩) Y (⟨j, rfl⟩ | ⟨l, rfl⟩)
    · exact hJJ i j
    · exact hJW i l
    · refine (intervalIntegrable_congr (fun s _ => ?_)).mp (hJW j k)
      exact lRegularizedIndexIntegrand_symm (I := I) S T alpha (J j) (W k) s
    · exact hWW k l
  let A : Submodule ℝ (∀ r, TangentSpace I (alpha r)) := Submodule.span ℝ G
  have hd : ∀ X ∈ A, ∀ s ∈ uIcc a b,
      DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s :=
    fun X hX => differentiableAt_chartRepAt_of_mem_span alpha G (uIcc a b) hG hX
  have hint : ∀ X ∈ A, ∀ Y ∈ A,
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X Y)
      MeasureTheory.volume a b :=
    fun X hX Y hY => intervalIntegrable_integrand_of_mem_span S T alpha G a b hG hGint hX hY
  let eva : (∀ r, TangentSpace I (alpha r)) →ₗ[ℝ] TangentSpace I (alpha a) :=
    LinearMap.proj (R := ℝ) (φ := fun r => TangentSpace I (alpha r)) a
  let evb : (∀ r, TangentSpace I (alpha r)) →ₗ[ℝ] TangentSpace I (alpha b) :=
    LinearMap.proj (R := ℝ) (φ := fun r => TangentSpace I (alpha r)) b
  let gb : LinearMap.BilinForm ℝ (TangentSpace I (alpha b)) :=
    ContinuousLinearMap.toLinearMap₁₂ ((S.base.metric (T - b ^ 2)).inner (alpha b))
  let Na : ι → TangentSpace I (alpha a) →ₗ[ℝ] ℝ := fun i =>
    ((S.base.metric (T - a ^ 2)).inner (alpha a)
      (covDerivAlong (I := I) (S.base.metric (T - a ^ 2)) alpha (J i) a)).toLinearMap
  let Nb : ι → TangentSpace I (alpha b) →ₗ[ℝ] ℝ := fun i =>
    ((S.base.metric (T - b ^ 2)).inner (alpha b)
      (covDerivAlong (I := I) (S.base.metric (T - b ^ 2)) alpha (J i) b)).toLinearMap
  have hJA : ∀ i, J i ∈ A := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hWA : ∀ k, W k ∈ A := fun k => Submodule.subset_span (Or.inr ⟨k, rfl⟩)
  exact trace_inv_gram_mul_boundary_le_sum_index
    (fun X Y => lRegularizedIndex S T alpha X Y a b) A eva evb gb Na Nb J W
    (fun x hx y hy z _ => lRegularizedIndex_add (I := I) S T alpha x y z a b (hd x hx)
      (hd y hy) (hint x hx z ‹_›) (hint y hy z ‹_›))
    (fun c x _ z _ => lRegularizedIndex_smul (I := I) S T c alpha x z a b)
    (fun x _ y _ => lRegularizedIndex_symm (I := I) S T alpha x y a b)
    (fun i x hx => lRegularizedIndex_eq_half_boundary_of_isLRegularizedJacobi (I := I) S hS T
      alpha (J i) x a b ht halpha hA (hjac i) (hd x hx) (hint _ (hJA i) x hx))
    (fun x hx hxa hxb => hnonneg x (hd x hx) (hint x hx x hx) hxa hxb)
    hJA hWA hJa hWa hspan hON

theorem half_trace_inv_lGram_mul_lGramDeriv_le_sum_lRegularizedIndex
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (alpha : ℝ → M) (J W : ι → ∀ r, TangentSpace I (alpha r)) (a : ℝ) {tau : ℝ}
    (htau : 0 < tau)
    (ht : ∀ s ∈ uIcc a (Real.sqrt tau), T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ uIcc a (Real.sqrt tau), ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I alpha r)
    (hA : ∀ s ∈ uIcc a (Real.sqrt tau), DifferentiableAt ℝ
      (chartRepAt (I := I) alpha (fun r ↦ lVelocity (I := I) alpha r) s) s)
    (hjac : ∀ i, IsLRegularizedJacobi S T alpha (J i) (uIcc a (Real.sqrt tau)))
    (hWd : ∀ k, ∀ s ∈ uIcc a (Real.sqrt tau),
      DifferentiableAt ℝ (chartRepAt (I := I) alpha (W k) s) s)
    (hJJ : ∀ i j, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (J i) (J j))
      MeasureTheory.volume a (Real.sqrt tau))
    (hJW : ∀ i k, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (J i) (W k))
      MeasureTheory.volume a (Real.sqrt tau))
    (hWW : ∀ k l, IntervalIntegrable (lRegularizedIndexIntegrand S T alpha (W k) (W l))
      MeasureTheory.volume a (Real.sqrt tau))
    (hnonneg : ∀ X : ∀ r, TangentSpace I (alpha r),
      (∀ s ∈ uIcc a (Real.sqrt tau), DifferentiableAt ℝ (chartRepAt (I := I) alpha X s) s) →
      IntervalIntegrable (lRegularizedIndexIntegrand S T alpha X X) MeasureTheory.volume a
        (Real.sqrt tau) →
      X a = 0 → X (Real.sqrt tau) = 0 → 0 ≤ lRegularizedIndex S T alpha X X a (Real.sqrt tau))
    (hJa : ∀ i, J i a = 0) (hWa : ∀ k, W k a = 0)
    (hspan : ∀ k, W k (Real.sqrt tau) ∈
      Submodule.span ℝ (Set.range fun i => J i (Real.sqrt tau)))
    (hON : ∀ k l, (S.base.metric (T - tau)).inner (alpha (Real.sqrt tau))
      (W k (Real.sqrt tau)) (W l (Real.sqrt tau)) = if k = l then 1 else 0) :
    (1 / 2) * trace
        ((lGram S T (fun q => alpha (Real.sqrt q)) (fun i q => J i (Real.sqrt q)) tau)⁻¹ *
          lGramDeriv S T (fun q => alpha (Real.sqrt q)) (fun i q => J i (Real.sqrt q)) tau) ≤
      (1 / Real.sqrt tau) * ∑ k, lRegularizedIndex S T alpha (W k) (W k) a (Real.sqrt tau) +
        ∑ k, S.ricciAt (T - tau) (alpha (Real.sqrt tau))
          (vec2 (W k (Real.sqrt tau)) (W k (Real.sqrt tau))) := by
  set b := Real.sqrt tau with hbdef
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hbsq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hbmem : b ∈ uIcc a b := right_mem_uIcc
  let g := S.base.metric (T - tau)
  let x := alpha b
  let G : Matrix ι ι ℝ := Matrix.of fun i j => g.inner x (J i b) (J j b)
  let N : Matrix ι ι ℝ := Matrix.of fun i j =>
    g.inner x (covDerivAlong (I := I) g alpha (J i) b) (J j b)
  let Rm : Matrix ι ι ℝ := Matrix.of fun i j => ricciTensor (I := I) g x (J i b) (J j b)
  have hGeq : lGram S T (fun q => alpha (Real.sqrt q)) (fun i q => J i (Real.sqrt q)) tau = G :=
    rfl
  have hcov : ∀ i, covDerivAlong (I := I) g (fun q => alpha (Real.sqrt q))
      (fun q => J i (Real.sqrt q)) tau =
        (1 / (2 * b)) • covDerivAlong (I := I) g alpha (J i) b := by
    intro i
    rw [covDerivAlong_comp (I := I) g alpha (J i) Real.sqrt tau (halpha b hbmem).self_of_nhds
      (hjac i b hbmem).2.1 (Real.hasDerivAt_sqrt htau.ne').differentiableAt,
      (Real.hasDerivAt_sqrt htau.ne').deriv]
  have hGD : lGramDeriv S T (fun q => alpha (Real.sqrt q)) (fun i q => J i (Real.sqrt q)) tau =
      (1 / (2 * b)) • (N + N.transpose) + (2 : ℝ) • Rm := by
    ext i j
    simp only [lGramDeriv, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul, N, Rm]
    change g.inner x (covDerivAlong (I := I) g (fun q => alpha (Real.sqrt q))
        (fun q => J i (Real.sqrt q)) tau) (J j b) +
      g.inner x (J i b) (covDerivAlong (I := I) g (fun q => alpha (Real.sqrt q))
        (fun q => J j (Real.sqrt q)) tau) +
      2 * metricRicciAt (I := I) g x (vec2 (J i b) (J j b)) = _
    rw [hcov i, hcov j, metricRicciAt_apply_eq_ricciTensor, map_smul, map_smul,
      _root_.smul_apply, smul_eq_mul, smul_eq_mul,
      g.symm x (J i b) (covDerivAlong (I := I) g alpha (J j) b)]
    ring
  have hGs : G.transpose = G := by
    ext i j
    exact g.symm x (J j b) (J i b)
  have htrT : trace (G⁻¹ * N.transpose) = trace (G⁻¹ * N) := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hGs, Matrix.trace_mul_comm]
  have hmain := trace_inv_gram_mul_covDerivAlong_le_sum_lRegularizedIndex S hS T alpha J W a b
    ht halpha hA hjac hWd hJJ hJW hWW hnonneg hJa hWa hspan (by rw [hbsq]; exact hON)
  rw [hbsq] at hmain
  have hmain' : trace (G⁻¹ * N) ≤ 2 * ∑ k, lRegularizedIndex S T alpha (W k) (W k) a b :=
    hmain
  have hR : trace (G⁻¹ * Rm) = ∑ k, ricciTensor (I := I) g x (W k b) (W k b) :=
    trace_inv_gram_mul_eq_sum_orthonormal (ContinuousLinearMap.toLinearMap₁₂ (g.inner x))
      (ContinuousLinearMap.toLinearMap₁₂ (ricciTensor (I := I) g x)) (fun i => J i b)
      (fun k => W k b) hspan hON
  have hRic : ∑ k, S.ricciAt (T - tau) (alpha b) (vec2 (W k b) (W k b)) =
      ∑ k, ricciTensor (I := I) g x (W k b) (W k b) :=
    Finset.sum_congr rfl fun k _ => metricRicciAt_apply_eq_ricciTensor (I := I) g x _ _
  rw [hGeq, hGD, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_add,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_add, htrT, hR, hRic,
    smul_eq_mul, smul_eq_mul]
  have hkey : (1 / (2 * b)) * (2 * ∑ k, lRegularizedIndex S T alpha (W k) (W k) a b) =
      (1 / b) * ∑ k, lRegularizedIndex S T alpha (W k) (W k) a b := by
    field_simp
  have hc : 0 ≤ 1 / (2 * b) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmain' hc]

theorem half_trace_inv_lGram_mul_lGramDeriv_le_lK
    [NeZero (Module.finrank ℝ E)]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (x : M) (Z : TangentSpace I x) {tau : ℝ} (htau : 0 < tau)
    (hbdom : Real.sqrt tau ∈ lRegularizedDomain S T x Z)
    (J P : Fin (Module.finrank ℝ E) → ∀ s, TangentSpace I (lRegularizedCurve S T x Z s))
    (ht : ∀ s ∈ uIcc 0 (Real.sqrt tau), T - s ^ 2 ∈ D.regular)
    (halpha : ∀ s ∈ uIcc 0 (Real.sqrt tau), ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf ℝ ℝ) I (lRegularizedCurve S T x Z) r)
    (hA : ∀ s ∈ uIcc 0 (Real.sqrt tau), DifferentiableAt ℝ
      (chartRepAt (I := I) (lRegularizedCurve S T x Z)
        (fun r ↦ lVelocity (I := I) (lRegularizedCurve S T x Z) r) s) s)
    (hjac : ∀ i, IsLRegularizedJacobi S T (lRegularizedCurve S T x Z) (J i)
      (uIcc 0 (Real.sqrt tau)))
    (hJ0 : ∀ i, J i 0 = 0)
    (hP : ∀ i s, s ∈ Icc (0 : ℝ) (Real.sqrt tau) →
      DifferentiableAt ℝ (chartRepAt (I := I) (lRegularizedCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Icc (0 : ℝ) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) (lRegularizedCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegularizedCurve S T x Z s) (P i s))
    (hON : ∀ i j, (S.base.metric (T - tau)).inner (lRegularizedCurve S T x Z (Real.sqrt tau))
      (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable (fun s : ℝ ↦ (s / Real.sqrt tau) ^ 2 *
        lRegularizedIndexIntegrand S T (lRegularizedCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable (fun s : ℝ ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegularizedCurve S T x Z s) (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hJJ : ∀ i j, IntervalIntegrable
      (lRegularizedIndexIntegrand S T (lRegularizedCurve S T x Z) (J i) (J j))
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hJW : ∀ i k, IntervalIntegrable
      (lRegularizedIndexIntegrand S T (lRegularizedCurve S T x Z) (J i)
        (fun s ↦ (s / Real.sqrt tau) • P k s)) MeasureTheory.volume 0 (Real.sqrt tau))
    (hWW : ∀ k l, IntervalIntegrable
      (lRegularizedIndexIntegrand S T (lRegularizedCurve S T x Z)
        (fun s ↦ (s / Real.sqrt tau) • P k s) (fun s ↦ (s / Real.sqrt tau) • P l s))
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hnonneg : ∀ X : ∀ r, TangentSpace I (lRegularizedCurve S T x Z r),
      (∀ s ∈ uIcc 0 (Real.sqrt tau),
        DifferentiableAt ℝ (chartRepAt (I := I) (lRegularizedCurve S T x Z) X s) s) →
      IntervalIntegrable (lRegularizedIndexIntegrand S T (lRegularizedCurve S T x Z) X X)
        MeasureTheory.volume 0 (Real.sqrt tau) →
      X 0 = 0 → X (Real.sqrt tau) = 0 →
      0 ≤ lRegularizedIndex S T (lRegularizedCurve S T x Z) X X 0 (Real.sqrt tau))
    (hspan : ∀ k, P k (Real.sqrt tau) ∈
      Submodule.span ℝ (Set.range fun i => J i (Real.sqrt tau))) :
    (1 / 2) * trace
        ((lGram S T (fun q => lRegularizedCurve S T x Z (Real.sqrt q))
            (fun i q => J i (Real.sqrt q)) tau)⁻¹ *
          lGramDeriv S T (fun q => lRegularizedCurve S T x Z (Real.sqrt q))
            (fun i q => J i (Real.sqrt q)) tau) ≤
      (Module.finrank ℝ E : ℝ) / (2 * tau) -
        lK S T (lRegularizedCurve S T x Z) (Real.sqrt tau) /
          (2 * tau * Real.sqrt tau) := by
  set b := Real.sqrt tau with hbdef
  have hb : 0 < b := Real.sqrt_pos.2 htau
  have hbsq : b ^ 2 = tau := Real.sq_sqrt htau.le
  have hIcc : uIcc 0 b = Icc 0 b := uIcc_of_le hb.le
  let W : Fin (Module.finrank ℝ E) → ∀ s, TangentSpace I (lRegularizedCurve S T x Z s) :=
    fun k s => (s / b) • P k s
  have hWb : ∀ k, W k b = P k b := by
    intro k
    change (b / b) • P k b = P k b
    rw [div_self hb.ne', one_smul]
  have hWd : ∀ k, ∀ s ∈ uIcc 0 b,
      DifferentiableAt ℝ (chartRepAt (I := I) (lRegularizedCurve S T x Z) (W k) s) s := by
    intro k s hs
    rw [show W k = fun r => (r / b) • P k r from rfl, chartRepAt_smulFun]
    exact (differentiableAt_id.div_const b).smul (hP k s (hIcc ▸ hs))
  have h1 := half_trace_inv_lGram_mul_lGramDeriv_le_sum_lRegularizedIndex S hS T
    (lRegularizedCurve S T x Z) J W 0 htau ht halpha hA hjac hWd hJJ hJW hWW hnonneg hJ0
    (fun k => by change (0 / b) • P k 0 = 0; rw [zero_div, zero_smul])
    (fun k => by rw [hWb k]; exact hspan k)
    (fun k l => by rw [hWb k, hWb l]; exact hON k l)
  have hONb : ∀ i j, (S.base.metric (T - b ^ 2)).inner (lRegularizedCurve S T x Z b)
      (P i b) (P j b) = if i = j then 1 else 0 := by
    rw [hbsq]
    exact hON
  have htrace := lRegularizedIndex_trace_linear_cutoff_zero (I := I) S hS T
    (lRegularizedCurve S T x Z) P b hb (fun s hs => ht s (hIcc ▸ hs))
    (fun s hs => (halpha s (hIcc ▸ hs)).self_of_nhds) hP (fun i s hs => hDP i s hs) hONb
    hIint hRint
  have hint := lTraceInt_eq (I := I) S hS T x Z hb hbdom P hP hDP hONb hIint
  have hRic : ∑ k, S.ricciAt (T - tau) (lRegularizedCurve S T x Z b) (vec2 (W k b) (W k b)) =
      S.scalar (T - tau) (lRegularizedCurve S T x Z b) := by
    let g := S.base.metric (T - tau)
    let y := lRegularizedCurve S T x Z b
    calc ∑ k, S.ricciAt (T - tau) y (vec2 (W k b) (W k b)) =
          ∑ k, ricciTensor (I := I) g y (P k b) (P k b) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [hWb k]
            exact metricRicciAt_apply_eq_ricciTensor (I := I) g y (P k b) (P k b)
      _ = scalarCurv (I := I) g y :=
        (scalarCurv_eq_orthonormal_trace (I := I) g y (fun i ↦ P i b) hON).symm
      _ = S.scalar (T - tau) y := (metricScalar_eq_scal (I := I) g y).symm
  rw [hRic] at h1
  have hsum : ∑ k, lRegularizedIndex S T (lRegularizedCurve S T x Z) (W k) (W k) 0 b =
      (Module.finrank ℝ E : ℝ) / (2 * b) +
        (-b * S.scalar (T - b ^ 2) (lRegularizedCurve S T x Z b) -
          lK S T (lRegularizedCurve S T x Z) b / (2 * b ^ 2)) := by
    rw [← hint]
    exact htrace
  rw [hsum, hbsq] at h1
  refine h1.trans_eq ?_
  rw [← hbsq]
  simp only [Real.sqrt_sq hb.le]
  field_simp
  ring

end SingleFlow

end DifferentialGeometry.PDE.RicciFlow.Perelman
