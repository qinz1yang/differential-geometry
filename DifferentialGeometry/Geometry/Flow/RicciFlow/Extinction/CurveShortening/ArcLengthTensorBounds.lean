import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.IteratedDerivatives
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TensorDerivatives
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem iterated_ds_slice_congr (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {f h : ℝ → ℝ → ℝ} {t : ℝ} (heq : ∀ x, f x t = h x t) (m : ℕ) (x : ℝ) :
    (c.ds g)^[m] f x t = (c.ds g)^[m] h x t := by
  induction m generalizing x with
  | zero => exact heq x
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ds]
    rw [funext ih]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem iterated_ds_add (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (f h : ℝ → ℝ → ℝ) (t : ℝ) (ht : t ∈ J)
    (hf : ContDiff ℝ ∞ (fun x => f x t)) (hh : ContDiff ℝ ∞ (fun x => h x t))
    (m : ℕ) (x : ℝ) :
    (c.ds g)^[m] (fun y τ => f y τ + h y τ) x t =
      (c.ds g)^[m] f x t + (c.ds g)^[m] h x t := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    change (c.speed g x t)⁻¹ * deriv (fun y => (c.ds g)^[m] (fun z τ => f z τ + h z τ) y t) x = _
    rw [funext ih, deriv_fun_add
      ((c.iterated_ds_contDiff g hc hi f t ht hf m).differentiable (by simp) x)
      ((c.iterated_ds_contDiff g hc hi h t ht hh m).differentiable (by simp) x), mul_add]
    rfl

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
private theorem iterated_ds_sum (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ → ℝ) (t : ℝ) (ht : t ∈ J)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (fun x => f i x t)) (m : ℕ) (x : ℝ) :
    (c.ds g)^[m] (fun y τ => ∑ i ∈ S, f i y τ) x t =
      ∑ i ∈ S, (c.ds g)^[m] (f i) x t := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    change (c.speed g x t)⁻¹ * deriv (fun y => (c.ds g)^[m] (fun z τ => ∑ i ∈ S, f i z τ) y t) x = _
    rw [funext ih, deriv_fun_sum (fun i hiS =>
      (c.iterated_ds_contDiff g hc hi (f i) t ht (hf i hiS) m).differentiable (by simp) x), Finset.mul_sum]
    rfl

private def tensorTangentJet (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    {r : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (j : ℕ) (v : Fin (r + j) → ℕ) (x t : ℝ) : ℝ :=
  iterCov (g t) r (A t) j (c.lift x t)
    (fun i => c.iteratedDs g (v i) (c.unitTangent g) x t)

private theorem tensorTangentJet_contDiff (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {r : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (j : ℕ) (v : Fin (r + j) → ℕ) (t : ℝ) (ht : t ∈ J) :
    ContDiff ℝ ∞ (fun x => tensorTangentJet c g A j v x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact c.contDiffAt_tensor_eval (iterCov (g t) r (A t) j)
    (fun i => c.iteratedDs g (v i) (c.unitTangent g)) x t
    ((contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)) x)
    (fun i => c.iteratedDs_contMDiff g hc hi _ t ht
      (c.unitTangent_contMDiff g J hc hi t ht) (v i) x)

private theorem ds_tensorTangentJet (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {r : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (j : ℕ) (v : Fin (r + j) → ℕ) (x t : ℝ) (ht : t ∈ J) :
    c.ds g (tensorTangentJet c g A j v) x t =
      tensorTangentJet c g A (j + 1) (Fin.cons 0 v) x t +
      ∑ i, tensorTangentJet c g A j (Function.update v i (v i + 1)) x t := by
  classical
  let Z := fun d => c.iteratedDs g d (c.unitTangent g)
  have hZ (d : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Z d y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff g hc hi _ t ht (c.unitTangent_contMDiff g J hc hi t ht) d
  have hγ := contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hh := c.ds_tensor_eval g (fun τ => iterCov (g τ) r (A τ) j)
    (fun i => Z (v i)) x t ((hγ x).mdifferentiableAt (by simp))
    (fun i => chartRep_diff _ _ (hZ (v i)) x)
  have hsucc (d : ℕ) : c.Ds g (Z d) = Z (d + 1) := by
    simp only [Z, CurveMap.iteratedDs, Function.iterate_succ_apply']
  simp_rw [hsucc] at hh
  have hv (i : Fin (r + j)) : (fun l => Z (Function.update v i (v i + 1) l) x t) =
      Function.update (fun l => Z (v l) x t) i (Z (v i + 1) x t) := by
    funext l
    by_cases hl : l = i
    · subst l; simp
    · simp only [Function.update_of_ne hl]
  have hhead : (fun i => Z (Fin.cons (α := fun _ : Fin (r + j + 1) => ℕ) 0 v i) x t) =
      Fin.cons (c.unitTangent g x t) (fun i => Z (v i) x t) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simp_rw [← hv] at hh
  simp only [LeviCivita_eq_leviCivitaConnectionOfMetric] at hh
  change c.ds g (tensorTangentJet c g A j v) x t = _ at hh
  rw [hh]
  congr 1
  change _ = covStep (g t) (r + j) (iterCov (g t) r (A t) j) (c.lift x t)
    (fun i => Z (Fin.cons (α := fun _ : Fin (r + j + 1) => ℕ) 0 v i) x t)
  rw [covStep_apply, hhead]

private theorem exists_iterated_ds_tensorTangentJet_bound (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {r : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (hambient : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (normSq0S (g t) (c.lift x t) (r + j)
        (iterCov (g t) r (A t) j (c.lift x t))) ≤ C)
    (hjets : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g j (c.unitTangent g)) x t) ≤ C)
    (m j : ℕ) (v : Fin (r + j) → ℕ) :
    ∃ C : ℝ, ∀ x t, t ∈ J → |(c.ds g)^[m] (tensorTangentJet c g A j v) x t| ≤ C := by
  classical
  induction m generalizing j with
  | zero =>
    obtain ⟨C, hC⟩ := hambient j
    choose B hB using hjets
    let P := fun k => max 0 (B k)
    have hP (k : ℕ) : 0 ≤ P k := le_max_left _ _
    refine ⟨max 0 C * ∏ i, P (v i), fun x t ht => ?_⟩
    change |iterCov (g t) r (A t) j (c.lift x t)
      (fun i => c.iteratedDs g (v i) (c.unitTangent g) x t)| ≤ _
    refine (abs_apply_le_norm0S (g t) (c.lift x t) (r + j) _ _).trans ?_
    apply mul_le_mul ((hC x t ht).trans (le_max_right _ _))
    · exact Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _)
        (fun i _ => (hB (v i) x t ht).trans (le_max_right _ _))
    · exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
    · exact le_max_left _ _
  | succ m ih =>
    obtain ⟨C, hC⟩ := ih (j + 1) (Fin.cons 0 v)
    have hterm := fun i : Fin (r + j) => ih j (Function.update v i (v i + 1))
    choose B hB using hterm
    refine ⟨C + ∑ i, B i, fun x t ht => ?_⟩
    have heq := fun y => ds_tensorTangentJet c g hc hi A j v y t ht
    rw [Function.iterate_succ_apply]
    rw [iterated_ds_slice_congr c g
      (h := fun y τ => tensorTangentJet c g A (j + 1) (Fin.cons 0 v) y τ +
        ∑ i, tensorTangentJet c g A j (Function.update v i (v i + 1)) y τ) heq m x]
    rw [iterated_ds_add c g hc hi _ _ t ht
      (tensorTangentJet_contDiff c g hc hi A (j + 1) (Fin.cons 0 v) t ht)
      (ContDiff.sum (fun i _ => tensorTangentJet_contDiff c g hc hi A j
        (Function.update v i (v i + 1)) t ht)) m x]
    rw [iterated_ds_sum c g hc hi Finset.univ _ t ht
      (fun i _ => tensorTangentJet_contDiff c g hc hi A j
        (Function.update v i (v i + 1)) t ht) m x]
    exact (abs_add_le _ _).trans (add_le_add (hC x t ht)
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hB i x t ht))))

theorem exists_iterated_ds_tensor_unitTangent_bound (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    {r : ℕ} (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r)
    (hambient : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (normSq0S (g t) (c.lift x t) (r + j)
        (iterCov (g t) r (A t) j (c.lift x t))) ≤ C)
    (hjets : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq g (c.iteratedDs g j (c.unitTangent g)) x t) ≤ C)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x t, t ∈ J →
      |(c.ds g)^[m] (fun y τ => A τ (c.lift y τ)
        (fun _ => c.unitTangent g y τ)) x t| ≤ C := by
  obtain ⟨C, hC⟩ := exists_iterated_ds_tensorTangentJet_bound c g hc hi A hambient hjets m 0 (fun _ => 0)
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), fun x t ht => ?_⟩
  exact (hC x t ht).trans (le_max_right _ _)

theorem exists_iterated_ds_ricciTangent_bound (c : CurveMap M)
    (G : SolutionFamily (I := I) (M := M)) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (hambient : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (normSq0S (G.metric t) (c.lift x t) (2 + j)
        (iterCov (G.metric t) 2 (G.ricci t) j (c.lift x t))) ≤ C)
    (hjets : ∀ j, ∃ C : ℝ, ∀ x t, t ∈ J →
      Real.sqrt (c.normSq G.metric (c.iteratedDs G.metric j (c.unitTangent G.metric)) x t) ≤ C)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x t, t ∈ J → |(c.ds G.metric)^[m] (c.ricciTangent G) x t| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := c.exists_iterated_ds_tensor_unitTangent_bound G.metric hc hi G.ricci
    hambient hjets m
  refine ⟨C, hC, fun x t ht => ?_⟩
  have heq : (fun y τ => G.ricci τ (c.lift y τ) (fun _ => c.unitTangent G.metric y τ)) =
      c.ricciTangent G := by
    funext y τ
    unfold ricciTangent
    rw [SolutionFamily.ricci_apply]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [heq] at hbound
  exact hbound x t ht

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
