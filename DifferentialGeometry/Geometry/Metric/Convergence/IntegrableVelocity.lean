import DifferentialGeometry.Geometry.Metric.Convergence.Metric.Compactness
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.TimeRegularity
import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivativeBounds
import DifferentialGeometry.Geometry.Metric.Convergence.IntegrableVelocityTower

/-!
# Integrable metric velocity

A smooth family `k s` (`s ≥ s₀`) of Riemannian metrics on a fixed manifold with velocity
`V s = ∂ₛ k s` whose intrinsic derivative norms `|∇_{k s}^q V s|_{k s}` are bounded by rates
`a q s` with antiderivatives `α q` bounded above by `L q` (review 17, §5.3 step 3 and §5.4):

* `metric_exp_bounds_of_integrable_velocity`: `k s` and `k s'` are equivalent with factor
  `exp (α 0 s - α 0 s')`;
* `exists_metric_limit_of_integrable_velocity` (compact manifold, background `h`): a uniform lower
  bound, background bounds on every `∇_h^q (k s)`, the difference bounds
  `|∇_h^q (k s - k s')|_h ≤ C Σ_{j ≤ N} (α j s - α j s')`, and a smooth limit metric `kInf` with
  the tail rate `C Σ_{j ≤ N} (L j - α j s)`;
* `exists_metric_limit_of_exp_decay_velocity`: the same for exponential rates, with an exponential
  rate of convergence.

The background derivatives of the velocity are controlled by the tower of
`IntegrableVelocityTower.lean`, the time derivative commutes with the background covariant
derivative (`hasDerivAt_metricCovDeriv_of_velocity`), and the limit is extracted with
`exists_metric_subsequence_tendsto_on_compact`.
-/

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff Topology BigOperators RealInnerProductSpace
open Bundle Filter Set

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M] [SigmaCompactSpace M]
variable [IsManifold I 1 M] [IsManifold I 2 M]
variable [VectorBundle Real E (TangentSpace I : M -> Type _)]
variable [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]

theorem sub_le_sub_of_hasDerivAt_le {φ ψ φ' ψ' : ℝ → ℝ} {s' s : ℝ} (hss : s' ≤ s)
    (hφ : ∀ r ∈ Icc s' s, HasDerivAt φ (φ' r) r) (hψ : ∀ r ∈ Icc s' s, HasDerivAt ψ (ψ' r) r)
    (hle : ∀ r ∈ Icc s' s, φ' r ≤ ψ' r) : φ s - φ s' ≤ ψ s - ψ s' := by
  have hanti := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s' s)
    (f := fun r => φ r - ψ r) (f' := fun r => φ' r - ψ' r)
    (fun r hr => ((hφ r hr).sub (hψ r hr)).continuousAt.continuousWithinAt)
    (fun r hr => ((hφ r (interior_subset hr)).sub (hψ r (interior_subset hr))).hasDerivWithinAt)
    (fun r hr => sub_nonpos.2 (hle r (interior_subset hr)))
  have h := hanti ⟨le_rfl, hss⟩ ⟨hss, le_rfl⟩ hss
  simp only at h
  linarith

theorem norm_sub_le_mul_sub_of_norm_deriv_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f f' : ℝ → F} {β b : ℝ → ℝ} {s' s B : ℝ} (hss : s' ≤ s)
    (hf : ∀ r ∈ Icc s' s, HasDerivAt f (f' r) r) (hβ : ∀ r ∈ Icc s' s, HasDerivAt β (b r) r)
    (hbound : ∀ r ∈ Icc s' s, ‖f' r‖ ≤ B * b r) :
    ‖f s - f s'‖ ≤ B * (β s - β s') := by
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (f := fun r => f r - f s') (f' := f') (B := fun r => B * (β r - β s'))
    (B' := fun r => B * b r)
    (fun r hr => ((hf r hr).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun r hr => ((hf r (Ico_subset_Icc_self hr)).sub_const (f s')).hasDerivWithinAt)
    (by simp)
    (fun r hr => (continuousAt_const.mul
      ((hβ r hr).continuousAt.sub continuousAt_const)).continuousWithinAt)
    (fun r hr => (((hβ r (Ico_subset_Icc_self hr)).sub_const (β s')).const_mul B).hasDerivWithinAt)
    (fun r hr => hbound r (Ico_subset_Icc_self hr))
  exact h ⟨hss, le_rfl⟩

theorem norm_le_mul_exp_of_norm_deriv_le_affine {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {f f' : ℝ → F} {β b : ℝ → ℝ} {s' s K c : ℝ} (hss : s' ≤ s)
    (hK : 0 ≤ K) (hc : 0 < c)
    (hf : ∀ r ∈ Icc s' s, HasDerivAt f (f' r) r) (hβ : ∀ r ∈ Icc s' s, HasDerivAt β (b r) r)
    (hb : ∀ r ∈ Icc s' s, 0 ≤ b r)
    (hbound : ∀ r ∈ Icc s' s, ‖f' r‖ ≤ b r * (K * (‖f r‖ + c))) :
    ‖f s‖ ≤ (‖f s'‖ + c) * Real.exp (3 * K * (β s - β s')) := by
  set Ψ : ℝ → ℝ := fun r => ‖f r‖ ^ 2 + c ^ 2 with hΨ
  have hΨpos : ∀ r, 0 < Ψ r := fun r => by positivity
  have hΨd : ∀ r ∈ Icc s' s, HasDerivAt Ψ (2 * ⟪f r, f' r⟫) r := by
    intro r hr
    have h := (hf r hr).norm_sq
    simpa [hΨ] using h.add_const (c ^ 2)
  have hβmono : β s' ≤ β s := by
    have h := sub_le_sub_of_hasDerivAt_le (φ := fun _ => (0 : ℝ)) (φ' := fun _ => 0) hss
      (fun r _ => hasDerivAt_const r 0) hβ hb
    linarith
  have hlog : Real.log (Ψ s) - Real.log (Ψ s') ≤ 3 * K * β s - 3 * K * β s' := by
    refine sub_le_sub_of_hasDerivAt_le (φ' := fun r => 2 * ⟪f r, f' r⟫ / Ψ r)
      (ψ' := fun r => 3 * K * b r) hss
      (fun r hr => (hΨd r hr).log (hΨpos r).ne')
      (fun r hr => (hβ r hr).const_mul (3 * K)) ?_
    intro r hr
    rw [div_le_iff₀ (hΨpos r)]
    have hcs : 2 * ⟪f r, f' r⟫ ≤ 2 * (‖f r‖ * ‖f' r‖) := by
      have := real_inner_le_norm (f r) (f' r)
      linarith
    have hfb := hbound r hr
    have hn0 : 0 ≤ ‖f r‖ := norm_nonneg _
    have hb0 := hb r hr
    have hstep : 2 * (‖f r‖ * ‖f' r‖) ≤ 2 * (‖f r‖ * (b r * (K * (‖f r‖ + c)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfb hn0) (by norm_num)
    have hquad : 2 * (‖f r‖ * (‖f r‖ + c)) ≤ 3 * (‖f r‖ ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (‖f r‖ - c)]
    have hbK : 0 ≤ b r * K := mul_nonneg hb0 hK
    calc 2 * ⟪f r, f' r⟫ ≤ 2 * (‖f r‖ * (b r * (K * (‖f r‖ + c)))) := hcs.trans hstep
      _ = (b r * K) * (2 * (‖f r‖ * (‖f r‖ + c))) := by ring
      _ ≤ (b r * K) * (3 * (‖f r‖ ^ 2 + c ^ 2)) := mul_le_mul_of_nonneg_left hquad hbK
      _ = 3 * K * b r * Ψ r := by rw [hΨ]; ring
  have hΨle : Ψ s ≤ Ψ s' * Real.exp (3 * K * (β s - β s')) := by
    have h1 : Real.log (Ψ s) ≤ Real.log (Ψ s') + 3 * K * (β s - β s') := by linarith
    have h2 := Real.exp_le_exp.2 h1
    rwa [Real.exp_add, Real.exp_log (hΨpos s), Real.exp_log (hΨpos s')] at h2
  have hy : 0 ≤ 3 * K * (β s - β s') := by
    have := sub_nonneg.2 hβmono
    positivity
  have hfs : ‖f s‖ ≤ Real.sqrt (Ψ s) := by
    rw [hΨ]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg c])
  have hsqrtΨ' : Real.sqrt (Ψ s') ≤ ‖f s'‖ + c := by
    rw [hΨ, Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg (f s'), hc.le]
  have hsqrtexp : Real.sqrt (Real.exp (3 * K * (β s - β s'))) ≤
      Real.exp (3 * K * (β s - β s')) := by
    rw [Real.sqrt_le_left (Real.exp_pos _).le]
    have h1 : 1 ≤ Real.exp (3 * K * (β s - β s')) := Real.one_le_exp hy
    nlinarith
  calc ‖f s‖ ≤ Real.sqrt (Ψ s) := hfs
    _ ≤ Real.sqrt (Ψ s' * Real.exp (3 * K * (β s - β s'))) := Real.sqrt_le_sqrt hΨle
    _ = Real.sqrt (Ψ s') * Real.sqrt (Real.exp (3 * K * (β s - β s'))) :=
        Real.sqrt_mul (hΨpos s').le _
    _ ≤ (‖f s'‖ + c) * Real.exp (3 * K * (β s - β s')) :=
        mul_le_mul hsqrtΨ' hsqrtexp (Real.sqrt_nonneg _) (by positivity)

local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I (∞ : WithTop ℕ∞) M)

omit [SigmaCompactSpace M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem hasDerivAt_metricCovDeriv_of_velocity
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (p : ℕ) {t : ℝ} (ht : s₀ ≤ t) (x : M) (v : Fin (p + 2) → TangentSpace I x) :
    HasDerivAt (fun r => metricCovDeriv (I := I) (k r) h p x v)
      (tensor02CovDeriv (I := I) (V t) h p x v) t := by
  have hbase : ∀ t ∈ Ici s₀, ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivWithinAt (fun r : ℝ => (Tensor0SBundle.metricTensorField (I := I) (k r)) x v)
        ((V t) x v) univ t := by
    intro t ht x v
    simpa only [Tensor0SBundle.metricTensorField_apply, hasDerivWithinAt_univ] using
      hderiv t ht x v
  have hsm : ∀ t ∈ Ici s₀, ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (Tensor0SBundle.metricTensorField (I := I) (k q.1)) q.2
            (fun a : Fin 2 => W a q.2)) (t, x) := by
    intro t ht x W
    simpa only [Tensor0SBundle.metricTensorField_apply] using hjoint t ht x W
  have hswap := covDerivOfField_swapRegularity (I := I) h
    (fun r => Tensor0SBundle.metricTensorField (I := I) (k r)) V univ (Ici s₀)
    (subset_univ _) (fun _ => Filter.univ_mem) p hbase
    (fun q _ W t ht x => (covDerivOfField_eval_contMDiffAt (I := I) h
      (fun r => Tensor0SBundle.metricTensorField (I := I) (k r)) (t := t) (x := x)
      (hsm t ht x) q W).of_le (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞)))
    (fun q _ W _ _ x => covDerivOfField_eval_mdiffAt (I := I) h _ q W x)
    (fun q _ W _ _ x => covDerivOfField_eval_mdiffAt (I := I) h _ q W x)
  have hd := covDerivOfField_eval_hasDerivWithinAt (I := I) h
    (fun r => Tensor0SBundle.metricTensorField (I := I) (k r)) V univ (Ici s₀) p hbase hswap
    p le_rfl t ht x v
  rw [hasDerivWithinAt_univ] at hd
  simpa only [metricCovDeriv_eq_covDerivOfField, tensor02_cov_deriv_eq_cov_deriv_of_field]
    using hd

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M] [T2Space M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem abs_tensor02_apply_le_norm_mul
    (g : SmoothRiemannianMetric I M) {x : M}
    (A : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) 2 x)
    (v : TangentSpace I x) :
    |A ![v, v]| ≤ Real.sqrt (Tensor0SBundle.normSq0S (I := I) g x 2 A) * g.inner x v v := by
  classical
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have h := Tensor0SBundle.abs_apply_le_sqrt_normSq0S (I := I) g x 2 basis hON A ![v, v]
  have hvv : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (g.pos x v hv).le
  have hprod : ∏ a : Fin 2, Real.sqrt (g.inner x (![v, v] a) (![v, v] a)) = g.inner x v v := by
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Real.mul_self_sqrt hvv
  rwa [hprod] at h

omit [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
theorem metric_exp_bounds_of_integrable_velocity
    (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a α : ℝ → ℝ)
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hα : ∀ s, s₀ ≤ s → HasDerivAt α (a s) s)
    (hV : ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) 0 (V s) (k s) (k s) x ≤ a s) :
    ∀ s' s : ℝ, s₀ ≤ s' → s' ≤ s → ∀ x : M, ∀ v : TangentSpace I x,
      Real.exp (-(α s - α s')) * (k s').inner x v v ≤ (k s).inner x v v ∧
        (k s).inner x v v ≤ Real.exp (α s - α s') * (k s').inner x v v := by
  intro s' s hs' hss x v
  by_cases hv : v = 0
  · subst hv; simp
  have hpos : ∀ r, 0 < (k r).inner x v v := fun r => (k r).pos x v hv
  have hf : ∀ r ∈ Icc s' s, HasDerivAt (fun r => (k r).inner x v v) (V r x ![v, v]) r := by
    intro r hr
    simpa using hderiv r (hs'.trans hr.1) x ![v, v]
  have hbnd : ∀ r ∈ Icc s' s, |V r x ![v, v] / (k r).inner x v v| ≤ a r := by
    intro r hr
    rw [abs_div, abs_of_pos (hpos r), div_le_iff₀ (hpos r)]
    refine (abs_tensor02_apply_le_norm_mul (I := I) (k r) (V r x) v).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hpos r).le
    exact hV r (hs'.trans hr.1) x
  have hlogd : ∀ r ∈ Icc s' s, HasDerivAt (fun r => Real.log ((k r).inner x v v))
      (V r x ![v, v] / (k r).inner x v v) r :=
    fun r hr => (hf r hr).log (hpos r).ne'
  have hup := sub_le_sub_of_hasDerivAt_le hss hlogd (fun r hr => hα r (hs'.trans hr.1))
    (fun r hr => (le_abs_self _).trans (hbnd r hr))
  have hlow := sub_le_sub_of_hasDerivAt_le (φ := fun r => -Real.log ((k r).inner x v v)) hss
    (fun r hr => (hlogd r hr).neg) (fun r hr => hα r (hs'.trans hr.1))
    (fun r hr => (neg_le_abs _).trans (hbnd r hr))
  have habs : |Real.log ((k s).inner x v v) - Real.log ((k s').inner x v v)| ≤ α s - α s' := by
    rw [abs_le]; constructor <;> linarith
  exact exp_bounds_of_abs_log_sub_le (hpos s') (hpos s) habs

omit [SigmaCompactSpace M] [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem exists_curve_of_velocity
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (N : ℕ) (x : M) :
    ∃ X Y : ℝ → EuclideanSpace ℝ (Fin (N + 2) → Fin (Module.finrank ℝ (TangentSpace I x))),
      (∀ r, ‖X r‖ = metricCovDerivNorm (I := I) N (k r) h x) ∧
      (∀ r, ‖Y r‖ = tensor02CovDerivNormWith (I := I) N (V r) h h x) ∧
      (∀ r r', ‖X r - X r'‖ = metricDerivNorm (I := I) N (k r) (k r') h x) ∧
      (∀ r, s₀ ≤ r → HasDerivAt X (Y r) r) := by
  classical
  obtain ⟨basis, hON⟩ := Tensor0SBundle.exists_orthonormal_basis (I := I) h x
  have hinv := Tensor0SBundle.metricInverseInBasis_of_orthonormal (I := I) h basis hON
  set e := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (N + 2) → Fin (Module.finrank ℝ (TangentSpace I x)) => ℝ) with he
  have hnorm : ∀ A : Tensor0SBundle.Tensor0SSpace (𝕜 := ℝ) (E := E) (H := H) (I := I)
      (M := M) (N + 2) x,
      ‖e.symm (fun I0 => Tensor0SBundle.component0S (I := I) basis A I0)‖ =
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x (N + 2) A) := by
    intro A
    rw [EuclideanSpace.norm_eq,
      Tensor0SBundle.normSq0S_identity_eq_sum_sq (I := I) h x (N + 2) basis hinv A]
    congr 1
    refine Finset.sum_congr rfl fun I0 _ => ?_
    rw [he, PiLp.continuousLinearEquiv_symm_apply, Real.norm_eq_abs, sq_abs]
  refine ⟨fun r => e.symm (fun I0 => Tensor0SBundle.component0S (I := I) basis
      (metricCovDeriv (I := I) (k r) h N x) I0),
    fun r => e.symm (fun I0 => Tensor0SBundle.component0S (I := I) basis
      (tensor02CovDeriv (I := I) (V r) h N x) I0), fun r => ?_, fun r => ?_,
    fun r r' => ?_, fun r hr => ?_⟩
  · rw [hnorm]; rfl
  · rw [hnorm]; rfl
  · rw [← map_sub]
    have hsub : (fun I0 => Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (k r) h N x) I0) -
        (fun I0 => Tensor0SBundle.component0S (I := I) basis
          (metricCovDeriv (I := I) (k r') h N x) I0) =
        fun I0 => Tensor0SBundle.component0S (I := I) basis
          (metricDiffCovDerivAt (I := I) N (k r) (k r') h x) I0 := by
      funext I0
      simp only [Pi.sub_apply, Tensor0SBundle.component0S_apply, metricDiffCovDerivAt,
        sub_apply]
    rw [hsub, hnorm]
    rfl
  · have hg : HasDerivAt (fun ρ : ℝ => (fun I0 => Tensor0SBundle.component0S (I := I) basis
        (metricCovDeriv (I := I) (k ρ) h N x) I0))
        (fun I0 => Tensor0SBundle.component0S (I := I) basis
          (tensor02CovDeriv (I := I) (V r) h N x) I0) r := by
      rw [hasDerivAt_pi]
      intro I0
      simpa only [Tensor0SBundle.component0S_apply] using
        hasDerivAt_metricCovDeriv_of_velocity (I := I) h k V s₀ hjoint hderiv N hr x
          (fun q => basis (I0 q))
    exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt r hg

omit [SigmaCompactSpace M] [I.Boundaryless] [IsManifold I 2 M]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
private theorem exists_uniform_equiv_of_velocity [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a α : ℝ → ℝ) (L : ℝ)
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hα : ∀ s, s₀ ≤ s → HasDerivAt α (a s) s)
    (hαL : ∀ s, s₀ ≤ s → α s ≤ L)
    (hV : ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) 0 (V s) (k s) (k s) x ≤ a s) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ r, s₀ ≤ r → MetricUniformEquivalentOn (I := I) Set.univ h (k r) B := by
  obtain ⟨C₀, hC₀⟩ := metricUniformEquivalentOn_of_compact (I := I) h (k s₀)
  have hC₀1 : 1 ≤ C₀ := hC₀.1
  have hL0 : 0 ≤ L - α s₀ := sub_nonneg.2 (hαL s₀ le_rfl)
  have hE1 : 1 ≤ Real.exp (L - α s₀) := Real.one_le_exp hL0
  refine ⟨C₀ * Real.exp (L - α s₀), one_le_mul_of_one_le_of_one_le hC₀1 hE1, fun r hr => ?_⟩
  refine ⟨one_le_mul_of_one_le_of_one_le hC₀1 hE1, fun x _ v => ?_⟩
  have hexp := metric_exp_bounds_of_integrable_velocity (I := I) k V s₀ a α hderiv hα hV
    s₀ r le_rfl hr x v
  have hk0 := hC₀.2 x (Set.mem_univ x) v
  have hh0 : 0 ≤ h.inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact (h.pos x v hv).le
  have hks0 : 0 ≤ (k s₀).inner x v v := by
    by_cases hv : v = 0
    · subst hv; simp
    · exact ((k s₀).pos x v hv).le
  have hαr := hαL r hr
  have hlowexp : Real.exp (-(L - α s₀)) ≤ Real.exp (-(α r - α s₀)) :=
    Real.exp_le_exp.2 (by linarith)
  have hupexp : Real.exp (α r - α s₀) ≤ Real.exp (L - α s₀) := Real.exp_le_exp.2 (by linarith)
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀1
  constructor
  · calc (C₀ * Real.exp (L - α s₀))⁻¹ * h.inner x v v
        = Real.exp (-(L - α s₀)) * (C₀⁻¹ * h.inner x v v) := by
          rw [mul_inv, Real.exp_neg]; ring
      _ ≤ Real.exp (-(L - α s₀)) * (k s₀).inner x v v :=
          mul_le_mul_of_nonneg_left hk0.1 (Real.exp_pos _).le
      _ ≤ Real.exp (-(α r - α s₀)) * (k s₀).inner x v v :=
          mul_le_mul_of_nonneg_right hlowexp hks0
      _ ≤ (k r).inner x v v := hexp.1
  · calc (k r).inner x v v ≤ Real.exp (α r - α s₀) * (k s₀).inner x v v := hexp.2
      _ ≤ Real.exp (L - α s₀) * (k s₀).inner x v v :=
          mul_le_mul_of_nonneg_right hupexp hks0
      _ ≤ Real.exp (L - α s₀) * (C₀ * h.inner x v v) :=
          mul_le_mul_of_nonneg_left hk0.2 (Real.exp_pos _).le
      _ = C₀ * Real.exp (L - α s₀) * h.inner x v v := by ring

omit [SigmaCompactSpace M] [I.Boundaryless] in
private theorem velocity_bound_of_tower
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a : ℕ → ℝ → ℝ) (ha0 : ∀ j r, s₀ ≤ r → 0 ≤ a j r)
    (hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V s) (k s) (k s) x ≤ a q s)
    (Bmax : ℝ) (hBmax1 : 1 ≤ Bmax)
    (hequiv : ∀ r, s₀ ≤ r → MetricUniformEquivalentOn (I := I) Set.univ h (k r) Bmax)
    (q : ℕ) (Cg : ℕ → ℝ)
    (hCg : ∀ j : ℕ, 1 ≤ j → j < q → ∀ r, s₀ ≤ r → ∀ x : M,
      metricCovDerivNorm (I := I) j (k r) h x ≤ Cg j) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r, s₀ ≤ r → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V r) h h x ≤
        (∑ j ∈ Finset.range (q + 1), a j r) *
          (K * (metricCovDerivNorm (I := I) q (k r) h x + 1)) := by
  have hX0 : ∀ r x, 0 ≤ metricCovDerivNorm (I := I) q (k r) h x :=
    fun r x => Real.sqrt_nonneg _
  have hsum0 : ∀ r, s₀ ≤ r → 0 ≤ ∑ j ∈ Finset.range (q + 1), a j r :=
    fun r hr => Finset.sum_nonneg fun j _ => ha0 j r hr
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · refine ⟨Bmax, by linarith, fun r hr x => ?_⟩
    have hsymm := metricUniformEquivalentOn_symm (I := I) (hequiv r hr)
    have hcmp := (Tensor0SBundle.normSq0S_le_of_metric_equiv (I := I) (k r) h x 2 hBmax1
      (fun v => hsymm.2 x (Set.mem_univ x) v) (V r x)).2
    have hV0 := hV 0 r hr x
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) (k r) x 2 (V r x)) ≤ a 0 r at hV0
    change Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 (V r x)) ≤ _
    have hB0 : 0 < Bmax := lt_of_lt_of_le one_pos hBmax1
    have h1 : Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 (V r x)) ≤
        Bmax * Real.sqrt (Tensor0SBundle.normSq0S (I := I) (k r) x 2 (V r x)) := by
      rw [show (Bmax : ℝ) = Real.sqrt (Bmax ^ 2) from (Real.sqrt_sq hB0.le).symm,
        ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      simpa [zpow_natCast] using hcmp
    have ha := ha0 0 r hr
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    have hX := hX0 r x
    calc Real.sqrt (Tensor0SBundle.normSq0S (I := I) h x 2 (V r x))
        ≤ Bmax * a 0 r := h1.trans (mul_le_mul_of_nonneg_left hV0 hB0.le)
      _ ≤ a 0 r * (Bmax * (metricCovDerivNorm (I := I) 0 (k r) h x + 1)) := by
          nlinarith [mul_nonneg (mul_nonneg ha hB0.le) hX]
  · obtain ⟨hsl, hof⟩ := velCoeffs_nonneg (Module.finrank ℝ E) q Bmax Cg 1 hBmax1 zero_le_one
    refine ⟨(velTowerCoeffs (Module.finrank ℝ E) q Bmax Cg 1).slope +
      (velTowerCoeffs (Module.finrank ℝ E) q Bmax Cg 1).offset, add_nonneg hsl hof,
      fun r hr x => ?_⟩
    have htow := velocity_tower_scaled (I := I) h (k r) (V r) q hq Bmax hBmax1 Cg
      (hequiv r hr) (fun j h1 h2 y => hCg j h1 h2 r hr y)
      (∑ j ∈ Finset.range (q + 1), a j r) (hsum0 r hr)
      (fun j hj y => (hV j r hr y).trans
        (Finset.single_le_sum (f := fun j => a j r) (fun i _ => ha0 i r hr)
          (Finset.mem_range.2 (by omega)))) x
    refine htow.trans (mul_le_mul_of_nonneg_left ?_ (hsum0 r hr))
    have hX := hX0 r x
    nlinarith [mul_nonneg hsl hX, mul_nonneg hof hX]

omit [SigmaCompactSpace M] in
private theorem exists_covDerivNorm_bound_of_velocity [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a α : ℕ → ℝ → ℝ) (L : ℕ → ℝ)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hα : ∀ q : ℕ, ∀ s, s₀ ≤ s → HasDerivAt (α q) (a q s) s)
    (hαL : ∀ q : ℕ, ∀ s, s₀ ≤ s → α q s ≤ L q)
    (hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V s) (k s) (k s) x ≤ a q s)
    (ha0 : ∀ j r, s₀ ≤ r → 0 ≤ a j r) (Bmax : ℝ) (hBmax1 : 1 ≤ Bmax)
    (hequiv : ∀ r, s₀ ≤ r → MetricUniformEquivalentOn (I := I) Set.univ h (k r) Bmax) :
    ∀ N : ℕ, ∃ C : ℝ, ∀ r, s₀ ≤ r → ∀ x : M, metricCovDerivNorm (I := I) N (k r) h x ≤ C := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hex : ∀ j : ℕ, ∃ Cj : ℝ, j < N → ∀ r, s₀ ≤ r → ∀ x : M,
        metricCovDerivNorm (I := I) j (k r) h x ≤ Cj := by
      intro j
      by_cases hj : j < N
      · obtain ⟨C, hC⟩ := ih j hj
        exact ⟨C, fun _ => hC⟩
      · exact ⟨0, fun h' => absurd h' hj⟩
    choose Cg hCg using hex
    obtain ⟨K, hK0, hK⟩ := velocity_bound_of_tower (I := I) h k V s₀ a ha0 hV Bmax hBmax1
      hequiv N Cg (fun j _ hj r hr x => hCg j hj r hr x)
    obtain ⟨C0, hC0⟩ := metricCovDerivNorm_bddOn (I := I) isCompact_univ N (k s₀) h
    refine ⟨(C0 + 1) * Real.exp (3 * K * (∑ j ∈ Finset.range (N + 1), L j -
      ∑ j ∈ Finset.range (N + 1), α j s₀)), fun r hr x => ?_⟩
    obtain ⟨X, Y, hX, hY, -, hXY⟩ := exists_curve_of_velocity (I := I) h k V s₀ hjoint hderiv N x
    have hg := norm_le_mul_exp_of_norm_deriv_le_affine (f := X) (f' := Y)
      (β := fun ρ => ∑ j ∈ Finset.range (N + 1), α j ρ)
      (b := fun ρ => ∑ j ∈ Finset.range (N + 1), a j ρ) hr hK0 one_pos
      (fun ρ hρ => hXY ρ hρ.1)
      (fun ρ hρ => HasDerivAt.fun_sum fun j _ => hα j ρ hρ.1)
      (fun ρ hρ => Finset.sum_nonneg fun j _ => ha0 j ρ hρ.1)
      (fun ρ hρ => by rw [hY, hX]; exact hK ρ hρ.1 x)
    rw [hX, hX] at hg
    have hC0x := hC0 x (Set.mem_univ x)
    have hβ : ∑ j ∈ Finset.range (N + 1), α j r ≤ ∑ j ∈ Finset.range (N + 1), L j :=
      Finset.sum_le_sum fun j _ => hαL j r hr
    have hn0 : 0 ≤ metricCovDerivNorm (I := I) N (k s₀) h x := Real.sqrt_nonneg _
    refine hg.trans (mul_le_mul (by linarith) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (by linarith))
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

omit [SigmaCompactSpace M] in
private theorem exists_derivNorm_diff_bound_of_velocity [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a α : ℕ → ℝ → ℝ)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hα : ∀ q : ℕ, ∀ s, s₀ ≤ s → HasDerivAt (α q) (a q s) s)
    (hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V s) (k s) (k s) x ≤ a q s)
    (ha0 : ∀ j r, s₀ ≤ r → 0 ≤ a j r) (Bmax : ℝ) (hBmax1 : 1 ≤ Bmax)
    (hequiv : ∀ r, s₀ ≤ r → MetricUniformEquivalentOn (I := I) Set.univ h (k r) Bmax)
    (hbound : ∀ N : ℕ, ∃ C : ℝ, ∀ r, s₀ ≤ r → ∀ x : M,
      metricCovDerivNorm (I := I) N (k r) h x ≤ C) :
    ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s' s : ℝ, s₀ ≤ s' → s' ≤ s → ∀ q : ℕ, q ≤ N → ∀ x : M,
      metricDerivNorm (I := I) q (k s) (k s') h x ≤
        C * ∑ j ∈ Finset.range (N + 1), (α j s - α j s') := by
  choose Cb hCb using hbound
  choose K hK0 hK using fun q => velocity_bound_of_tower (I := I) h k V s₀ a ha0 hV Bmax
    hBmax1 hequiv q Cb (fun j _ _ r hr x => hCb j r hr x)
  intro N
  set D : ℕ → ℝ := fun q => K q * (max (Cb q) 0 + 1) with hD
  have hD0 : ∀ q, 0 ≤ D q := fun q => mul_nonneg (hK0 q) (by positivity)
  refine ⟨∑ q ∈ Finset.range (N + 1), D q, Finset.sum_nonneg fun q _ => hD0 q,
    fun s' s hs' hss q hq x => ?_⟩
  obtain ⟨X, Y, -, hY, hXX, hXY⟩ := exists_curve_of_velocity (I := I) h k V s₀ hjoint hderiv q x
  have hbN : ∀ ρ, s₀ ≤ ρ → ∑ j ∈ Finset.range (q + 1), a j ρ ≤
      ∑ j ∈ Finset.range (N + 1), a j ρ := fun ρ hρ =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun j _ _ => ha0 j ρ hρ)
  have hdiff := norm_sub_le_mul_sub_of_norm_deriv_le (f := X) (f' := Y)
    (β := fun ρ => ∑ j ∈ Finset.range (N + 1), α j ρ)
    (b := fun ρ => ∑ j ∈ Finset.range (N + 1), a j ρ) (B := D q) hss
    (fun ρ hρ => hXY ρ (hs'.trans hρ.1))
    (fun ρ hρ => HasDerivAt.fun_sum fun j _ => hα j ρ (hs'.trans hρ.1))
    (fun ρ hρ => by
      have hρ0 : s₀ ≤ ρ := hs'.trans hρ.1
      rw [hY]
      refine (hK q ρ hρ0 x).trans ?_
      have hX := hCb q ρ hρ0 x
      have hXn : 0 ≤ metricCovDerivNorm (I := I) q (k ρ) h x := Real.sqrt_nonneg _
      have hsum0 : 0 ≤ ∑ j ∈ Finset.range (q + 1), a j ρ :=
        Finset.sum_nonneg fun j _ => ha0 j ρ hρ0
      calc (∑ j ∈ Finset.range (q + 1), a j ρ) *
            (K q * (metricCovDerivNorm (I := I) q (k ρ) h x + 1))
          ≤ (∑ j ∈ Finset.range (q + 1), a j ρ) * D q := by
            refine mul_le_mul_of_nonneg_left ?_ hsum0
            exact mul_le_mul_of_nonneg_left (by linarith [le_max_left (Cb q) 0]) (hK0 q)
        _ ≤ (∑ j ∈ Finset.range (N + 1), a j ρ) * D q :=
            mul_le_mul_of_nonneg_right (hbN ρ hρ0) (hD0 q)
        _ = D q * ∑ j ∈ Finset.range (N + 1), a j ρ := mul_comm _ _)
  rw [hXX] at hdiff
  have hmono : 0 ≤ ∑ j ∈ Finset.range (N + 1), α j s - ∑ j ∈ Finset.range (N + 1), α j s' := by
    have h0 := sub_le_sub_of_hasDerivAt_le (φ := fun _ => (0 : ℝ)) (φ' := fun _ => 0)
      (ψ := fun ρ => ∑ j ∈ Finset.range (N + 1), α j ρ)
      (ψ' := fun ρ => ∑ j ∈ Finset.range (N + 1), a j ρ) hss
      (fun ρ _ => hasDerivAt_const ρ 0)
      (fun ρ hρ => HasDerivAt.fun_sum fun j _ => hα j ρ (hs'.trans hρ.1))
      (fun ρ hρ => Finset.sum_nonneg fun j _ => ha0 j ρ (hs'.trans hρ.1))
    simpa using h0
  rw [Finset.sum_sub_distrib]
  refine hdiff.trans (mul_le_mul_of_nonneg_right ?_ hmono)
  exact Finset.single_le_sum (f := D) (fun i _ => hD0 i) (Finset.mem_range.2 (by omega))

theorem exists_metric_limit_of_integrable_velocity [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (a α : ℕ → ℝ → ℝ) (L : ℕ → ℝ)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hα : ∀ q : ℕ, ∀ s, s₀ ≤ s → HasDerivAt (α q) (a q s) s)
    (hαL : ∀ q : ℕ, ∀ s, s₀ ≤ s → α q s ≤ L q)
    (hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V s) (k s) (k s) x ≤ a q s) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ s, s₀ ≤ s → ∀ x : M, ∀ v : TangentSpace I x,
        lam * h.inner x v v ≤ (k s).inner x v v) ∧
      (∀ x : M, ∀ v : TangentSpace I x, lam * h.inner x v v ≤ kInf.inner x v v) ∧
      (∀ q : ℕ, ∃ C : ℝ, ∀ x : M, metricCovDerivNorm (I := I) q kInf h x ≤ C ∧
        ∀ s, s₀ ≤ s → metricCovDerivNorm (I := I) q (k s) h x ≤ C) ∧
      (∀ N : ℕ, ∃ C : ℝ, ∀ s' s : ℝ, s₀ ≤ s' → s' ≤ s → ∀ q : ℕ, q ≤ N → ∀ x : M,
        metricDerivNorm (I := I) q (k s) (k s') h x ≤
          C * ∑ j ∈ Finset.range (N + 1), (α j s - α j s')) ∧
      (∀ N : ℕ, ∃ C : ℝ, ∀ s, s₀ ≤ s → ∀ q : ℕ, q ≤ N → ∀ x : M,
        metricDerivNorm (I := I) q (k s) kInf h x ≤
          C * ∑ j ∈ Finset.range (N + 1), (L j - α j s)) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨1, one_pos, h, fun _ _ x => isEmptyElim x, fun x => isEmptyElim x,
      fun _ => ⟨0, fun x => isEmptyElim x⟩, fun _ => ⟨0, fun _ _ _ _ _ _ x => isEmptyElim x⟩,
      fun _ => ⟨0, fun _ _ _ _ x => isEmptyElim x⟩⟩
  obtain ⟨x₀⟩ := hM
  have ha0 : ∀ j r, s₀ ≤ r → 0 ≤ a j r := fun j r hr =>
    (Real.sqrt_nonneg _).trans (hV j r hr x₀)
  obtain ⟨Bmax, hBmax1, hequiv⟩ := exists_uniform_equiv_of_velocity (I := I) h k V s₀ (a 0)
    (α 0) (L 0) hderiv (hα 0) (hαL 0) (hV 0)
  have hbound := exists_covDerivNorm_bound_of_velocity (I := I) h k V s₀ a α L hjoint hderiv hα
    hαL hV ha0 Bmax hBmax1 hequiv
  have hdiff := exists_derivNorm_diff_bound_of_velocity (I := I) h k V s₀ a α hjoint hderiv hα
    hV ha0 Bmax hBmax1 hequiv hbound
  have hB0 : 0 < Bmax := lt_of_lt_of_le one_pos hBmax1
  have hlow : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : TangentSpace I x,
      Bmax⁻¹ * h.inner x v v ≤ (k s).inner x v v :=
    fun s hs x v => ((hequiv s hs).2 x (Set.mem_univ x) v).1
  set gSeq : ℕ → SmoothRiemannianMetric I M := fun m => k (s₀ + m) with hgSeq
  have hs₀m : ∀ m : ℕ, s₀ ≤ s₀ + m := fun m => le_add_of_nonneg_right (Nat.cast_nonneg m)
  have hbdd : ∀ q : ℕ, ∀ K' : Set M, IsCompact K' → ∃ C : ℝ, ∀ m : ℕ, ∀ z, z ∈ K' →
      metricCovDerivNorm (I := I) q (gSeq m) h z ≤ C := by
    intro q K' _
    obtain ⟨C, hC⟩ := hbound q
    exact ⟨C, fun m z _ => hC (s₀ + m) (hs₀m m) z⟩
  have hlowSeq : ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ) (x : M) (v : TangentSpace I x),
      c * h.inner x v v ≤ (gSeq m).inner x v v :=
    ⟨Bmax⁻¹, inv_pos.2 hB0, fun m x v => hlow (s₀ + m) (hs₀m m) x v⟩
  choose φ hφ gp hgp_pt hgp_conv using fun p : ℕ =>
    exists_metric_subsequence_tendsto_on_compact (I := I) ⟨x₀⟩ Set.univ isCompact_univ p h gSeq
      hbdd hlowSeq
  have hαmono : ∀ j : ℕ, ∀ s' s, s₀ ≤ s' → s' ≤ s → α j s' ≤ α j s := by
    intro j s' s hs' hss
    have h0 := sub_le_sub_of_hasDerivAt_le (φ := fun _ => (0 : ℝ)) (φ' := fun _ => 0) hss
      (fun ρ _ => hasDerivAt_const ρ 0) (fun ρ hρ => hα j ρ (hs'.trans hρ.1))
      (fun ρ hρ => ha0 j ρ (hs'.trans hρ.1))
    linarith
  have hαcs : CauchySeq (fun m : ℕ => α 0 (s₀ + m)) := by
    refine (tendsto_atTop_ciSup (fun m m' hmm => hαmono 0 _ _ (hs₀m m)
      (by have := (Nat.cast_le (α := ℝ)).2 hmm; linarith)) ?_).cauchySeq
    exact ⟨L 0, by rintro _ ⟨m, rfl⟩; exact hαL 0 _ (hs₀m m)⟩
  obtain ⟨C0, hC00, hC0⟩ := hdiff 0
  have hd0 : ∀ m l : ℕ, ∀ x : M, metricDerivNorm (I := I) 0 (gSeq m) (gSeq l) h x ≤
      C0 * |α 0 (s₀ + m) - α 0 (s₀ + l)| := by
    intro m l x
    rcases le_total (s₀ + (m : ℝ)) (s₀ + l) with hml | hml
    · rw [metricDerivNorm_symm]
      have h1 := hC0 _ _ (hs₀m m) hml 0 le_rfl x
      simp only [zero_add, Finset.range_one, Finset.sum_singleton] at h1
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ hC00)
      rw [abs_sub_comm]; exact le_abs_self _
    · have h1 := hC0 _ _ (hs₀m l) hml 0 le_rfl x
      simp only [zero_add, Finset.range_one, Finset.sum_singleton] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC00)
  have hcauchy : ∀ x : M, ∀ v w : TangentSpace I x,
      CauchySeq (fun m => (gSeq m).inner x v w) := by
    intro x v w
    refine metricInner_cauchy (I := I) gSeq h x v w fun ε hε => ?_
    obtain ⟨m0, hm0⟩ := Metric.cauchySeq_iff.1 hαcs (ε / (C0 + 1)) (by positivity)
    refine ⟨m0, fun m hm l hl => lt_of_le_of_lt (hd0 m l x) ?_⟩
    have hdist := hm0 m hm l hl
    rw [Real.dist_eq] at hdist
    calc C0 * |α 0 (s₀ + m) - α 0 (s₀ + l)| ≤ C0 * (ε / (C0 + 1)) :=
          mul_le_mul_of_nonneg_left hdist.le hC00
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
          nlinarith
  have heq : ∀ p, gp p = gp 0 := fun p =>
    metricLimit_uniq (I := I) gSeq (gp p) (gp 0) hcauchy (φ p) (hφ p) (φ 0) (hφ 0) (hgp_pt p)
      (hgp_pt 0)
  have hrate : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ s, s₀ ≤ s → ∀ q : ℕ, q ≤ N → ∀ x : M,
      metricDerivNorm (I := I) q (k s) (gp 0) h x ≤
        C * ∑ j ∈ Finset.range (N + 1), (L j - α j s) := by
    intro N
    obtain ⟨C, hC0', hC⟩ := hdiff N
    refine ⟨C, hC0', fun s hs q hq x => le_of_forall_pos_lt_add fun ε hε => ?_⟩
    obtain ⟨m0, hm0⟩ := hgp_conv N ε hε
    set m := max m0 (Nat.ceil (s - s₀)) with hm
    have hφm : s ≤ s₀ + (φ N m : ℝ) := by
      have h1 : (Nat.ceil (s - s₀) : ℝ) ≤ φ N m := by
        exact_mod_cast (le_max_right _ _).trans ((hφ N).id_le m)
      linarith [Nat.le_ceil (s - s₀)]
    have htri := metricDerivNorm_triangle (I := I) q (k s) (gSeq (φ N m)) (gp 0) h x
    have h1 : metricDerivNorm (I := I) q (k s) (gSeq (φ N m)) h x ≤
        C * ∑ j ∈ Finset.range (N + 1), (L j - α j s) := by
      rw [metricDerivNorm_symm]
      refine (hC s _ hs hφm q hq x).trans (mul_le_mul_of_nonneg_left ?_ hC0')
      exact Finset.sum_le_sum fun j _ => by linarith [hαL j _ (hs₀m (φ N m))]
    have h2 := hm0 m (le_max_left _ _) q hq x (Set.mem_univ x)
    rw [heq N] at h2
    linarith
  refine ⟨Bmax⁻¹, inv_pos.2 hB0, gp 0, hlow, fun x v => ?_, fun q => ?_,
    fun N => ?_, fun N => ?_⟩
  · have hc : Continuous fun T : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ => T v v :=
      (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        (ContinuousLinearMap.apply ℝ (TangentSpace I x →L[ℝ] ℝ) v).continuous
    have ht := (hc.tendsto _).comp (hgp_pt 0 x)
    exact ge_of_tendsto ht (Filter.Eventually.of_forall fun m =>
      hlow _ (hs₀m (φ 0 m)) x v)
  · obtain ⟨Cq, hCq⟩ := hbound q
    obtain ⟨Cr, -, hCr⟩ := hrate q
    refine ⟨max Cq (Cq + Cr * ∑ j ∈ Finset.range (q + 1), (L j - α j s₀)), fun x =>
      ⟨?_, fun s hs => (hCq s hs x).trans (le_max_left _ _)⟩⟩
    refine le_trans ?_ (le_max_right _ _)
    have h1 := covNorm_le_add (I := I) q (gp 0) (k s₀) h x
    rw [metricDerivNorm_symm] at h1
    linarith [hCq s₀ le_rfl x, hCr s₀ le_rfl q le_rfl x]
  · obtain ⟨C, -, hC⟩ := hdiff N
    exact ⟨C, hC⟩
  · obtain ⟨C, -, hC⟩ := hrate N
    exact ⟨C, hC⟩

theorem exists_metric_limit_of_exp_decay_velocity [CompactSpace M]
    (h : SmoothRiemannianMetric I M) (k : ℝ → SmoothRiemannianMetric I M)
    (V : ℝ → Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (s₀ : ℝ) (C γ : ℕ → ℝ) (hγ : ∀ q : ℕ, 0 < γ q)
    (hjoint : ∀ s, s₀ ≤ s → ∀ x : M,
      ∀ W : Fin 2 → ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _),
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (∞ : WithTop ℕ∞)
          (fun q : ℝ × M => (k q.1).inner q.2 (W 0 q.2) (W 1 q.2)) (s, x))
    (hderiv : ∀ s, s₀ ≤ s → ∀ x : M, ∀ v : Fin 2 → TangentSpace I x,
      HasDerivAt (fun r => (k r).inner x (v 0) (v 1)) (V s x v) s)
    (hV : ∀ q : ℕ, ∀ s, s₀ ≤ s → ∀ x : M,
      tensor02CovDerivNormWith (I := I) q (V s) (k s) (k s) x ≤ C q * Real.exp (-(γ q * s))) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ kInf : SmoothRiemannianMetric I M,
      (∀ s, s₀ ≤ s → ∀ x : M, ∀ v : TangentSpace I x,
        lam * h.inner x v v ≤ (k s).inner x v v) ∧
      (∀ x : M, ∀ v : TangentSpace I x, lam * h.inner x v v ≤ kInf.inner x v v) ∧
      (∀ q : ℕ, ∃ B : ℝ, ∀ x : M, metricCovDerivNorm (I := I) q kInf h x ≤ B ∧
        ∀ s, s₀ ≤ s → metricCovDerivNorm (I := I) q (k s) h x ≤ B) ∧
      (∀ N : ℕ, ∃ B β : ℝ, 0 < β ∧ ∀ s, s₀ ≤ s → ∀ q : ℕ, q ≤ N → ∀ x : M,
        metricDerivNorm (I := I) q (k s) kInf h x ≤ B * Real.exp (-(β * s))) := by
  set c : ℕ → ℝ := fun q => max (C q) 0 with hc
  have hc0 : ∀ q, 0 ≤ c q := fun q => le_max_right _ _
  obtain ⟨lam, hlam, kInf, hlow, hlowInf, hbd, -, hrate⟩ :=
    exists_metric_limit_of_integrable_velocity (I := I) h k V s₀
      (fun q s => c q * Real.exp (-(γ q * s))) (fun q s => -(c q / γ q * Real.exp (-(γ q * s))))
      (fun _ => 0) hjoint hderiv
      (fun q s _ => by
        have h2 : HasDerivAt (fun s => -(γ q * s)) (-(γ q)) s := by
          simpa using ((hasDerivAt_id s).const_mul (γ q)).fun_neg
        have h3 := (h2.exp.const_mul (c q / γ q)).neg
        convert h3 using 1
        field_simp [(hγ q).ne'])
      (fun q s _ => by
        have : 0 ≤ c q / γ q * Real.exp (-(γ q * s)) :=
          mul_nonneg (div_nonneg (hc0 q) (hγ q).le) (Real.exp_pos _).le
        linarith)
      (fun q s hs x => (hV q s hs x).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le))
  refine ⟨lam, hlam, kInf, hlow, hlowInf, hbd, fun N => ?_⟩
  obtain ⟨Cr, hCr⟩ := hrate N
  have hne : (Finset.range (N + 1)).Nonempty := ⟨0, by simp⟩
  set β : ℝ := (Finset.range (N + 1)).inf' hne γ with hβ
  have hβpos : 0 < β := by
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' hne γ
    rw [hβ, hj]; exact hγ j
  have hβle : ∀ j ∈ Finset.range (N + 1), β ≤ γ j := fun j hj => Finset.inf'_le _ hj
  refine ⟨max Cr 0 * ∑ j ∈ Finset.range (N + 1),
      c j / γ j * Real.exp (-((γ j - β) * s₀)), β, hβpos, fun s hs q hq x => ?_⟩
  have h1 := hCr s hs q hq x
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range (N + 1),
      ((fun _ => (0 : ℝ)) j - -(c j / γ j * Real.exp (-(γ j * s)))) :=
    Finset.sum_nonneg fun j _ => by
      have := mul_nonneg (div_nonneg (hc0 j) (hγ j).le) (Real.exp_pos (-(γ j * s))).le
      simp only; linarith
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_max_left Cr 0) hsum0).trans ?_)
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  simp only [zero_sub, neg_neg]
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (hc0 j) (hγ j).le)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have hgb := sub_nonneg.2 (hβle j hj)
  nlinarith [mul_le_mul_of_nonneg_left hs hgb]

end CheegerGromovCompactness
end DifferentialGeometry
