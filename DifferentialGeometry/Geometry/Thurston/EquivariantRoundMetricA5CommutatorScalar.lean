import DifferentialGeometry.Geometry.Thurston.EquivariantRoundMetricA5Background
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import
  DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Evolution.SolutionHeatEquation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.HigherDerivativeReaction

/-!
# Derivative decay of the normalised scalar curvature along a surface flow

Chapter 7, surface lemma U1, route (a), step a5.3 D (lane U1C; design D18,
`docs/geometrization/handoffs/20261004-design-u1-a5-potential-gauge.md`, and review 18 §2).

* `covStep_metricRm04_apply_of_finrank_two`, `normSq0S_covStep_metricRm04_of_finrank_two`: in
  dimension two `Rm = (R / 2) (g ⊙ g)` and `∇g = 0` give `∇Rm = (dR / 2) ⊗ (g ⊙ g)`, hence
  `|∇Rm|² = |∇R|²` (the order-one case of the two-dimensional identity `|∇^q Rm| = |∇^q R|`).
* `surfaceFlow_scalar_derivative_decay`: if `|R · 2 (Tm - t) - 2| ≤ C (Tm - t)^δ` on `[0, Tm)`,
  then every normalised curvature derivative `(2 (Tm - t))^(q + 3) |∇^(q + 1) Rm|²` is
  `O((Tm - t)^(2 δ))` on every terminal interval. The family `u₀ = (R̂ - 2)²`,
  `u_q = (2 (Tm - t))^(q + 2) |∇^q Rm|²` (`q ≥ 1`) satisfies the linear tower of review 18 §2,
  `∂ₜ u_q ≤ Δ u_q + (-2 u_{q+1} + C_q Σ_{j ≤ q} u_j) / (2 (Tm - t))`: order zero from
  `∂ₜ R = Δ R + R²` and `|∇Rm|² = |∇R|²`, orders `q ≥ 1` from the curvature tower
  `towerHeatBoundOn_of_solution` with the a5.1 bounds
  (`surfaceFlow_normalized_curvatureDerivative_bound`) on the reaction factors.
  `flow_linear_tower_decay` then propagates the rate of `u₀`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Analysis.Parabolic
open Set
open scoped Manifold ContDiff

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M]

private def gG (g : SmoothRiemannianMetric I M) {x : M} (v : Fin 4 → TangentSpace I x) : ℝ :=
  g.inner x (v 0) (v 3) * g.inner x (v 1) (v 2) - g.inner x (v 0) (v 2) * g.inner x (v 1) (v 3)

omit [CompactSpace M] in
theorem metricRm04_apply_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (x : M) (v : Fin 4 → TangentSpace I x) :
    metricRm04 g x v = metricScalarAt g x / 2 * gG g v := by
  have hv : v = vec4 (v 0) (v 1) (v 2) (v 3) := by
    funext i; fin_cases i <;> rfl
  have h := metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two g hdim x (v 0) (v 1) (v 2) (v 3)
  rw [metricRm04StandardAt, tensor04StandardAt, ← hv] at h
  rw [metricRm04_apply, h]
  rfl

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
private theorem mvfderiv_inner_sections (g : SmoothRiemannianMetric I M)
    (Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _)) (x : M)
    (w : TangentSpace I x) :
    mvfderiv I (fun y => g.inner y (Y y) (Z y)) x w =
      g.inner x ((leviCivitaConnectionOfMetric g) (fun y => Y y) x w) (Z x) +
        g.inner x (Y x) ((leviCivitaConnectionOfMetric g) (fun y => Z y) x w) := by
  have hY : MDiffAt (T% (fun y => Y y)) x := (Y.contMDiff x).mdifferentiableAt (by simp)
  have hZ : MDiffAt (T% (fun y => Z y)) x := (Z.contMDiff x).mdifferentiableAt (by simp)
  have h := leviCivitaConnectionOfMetric_isMetricCompatible g hY hZ (mem_univ x) w
  exact h

omit [CompactSpace M] in
theorem covStep_metricRm04_apply_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) (x : M)
    (w : TangentSpace I x) (v : Fin 4 → TangentSpace I x) :
    covStep g 4 (metricRm04 g) x (Fin.cons w v) =
      mvfderiv I (metricScalarAt g) x w / 2 * gG g v := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E) (V := TangentSpace I)
    (n := (⊤ : ℕ∞)) x w
  choose V hV using fun a : Fin 4 => ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := TangentSpace I) (n := (⊤ : ℕ∞)) x (v a)
  have hv : v = fun q => V q x := funext fun q => (hV q).symm
  subst hv hX
  rw [covStep_eval_smooth_slots]
  set R := metricScalarAt g with hRdef
  set p : Fin 4 → Fin 4 → M → ℝ := fun i j y => g.inner y (V i y) (V j y) with hp
  set W : Fin 4 → TangentSpace I x := fun q =>
    (leviCivitaConnectionOfMetric g) (fun y => V q y) x (X x) with hW
  have hpd : ∀ i j, MDiffAt (p i j) x := fun i j =>
    metricInner_mdiffAt g (V i).contMDiff (V j).contMDiff x
  have hpv : ∀ i j, mvfderiv I (p i j) x (X x) =
      g.inner x (W i) (V j x) + g.inner x (V i x) (W j) := fun i j =>
    mvfderiv_inner_sections g (V i) (V j) x (X x)
  have hRd : MDiffAt R x := (hR x).mdifferentiableAt (by simp)
  have hfun : (fun y => metricRm04 g y (fun q => V q y)) =
      fun y => (R y * (2 : ℝ)⁻¹) * (p 0 3 y * p 1 2 y - p 0 2 y * p 1 3 y) := by
    funext y
    rw [metricRm04_apply_of_finrank_two hdim]
    simp only [gG, hp, div_eq_mul_inv, hRdef]
  have hsum : ∑ q : Fin 4, metricRm04 g x (Function.update (fun b => V b x) q (W q)) =
      R x / 2 * ∑ q : Fin 4, gG g (Function.update (fun b => V b x) q (W q)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => metricRm04_apply_of_finrank_two hdim g x _
  rw [hfun, hsum]
  have hc : MDiffAt (fun _ : M => (2 : ℝ)⁻¹) x := mdifferentiableAt_const
  have hR2 : MDiffAt (fun y => R y * (2 : ℝ)⁻¹) x := hRd.mul hc
  have hQ1 : MDiffAt (fun y => p 0 3 y * p 1 2 y) x := (hpd 0 3).mul (hpd 1 2)
  have hQ2 : MDiffAt (fun y => p 0 2 y * p 1 3 y) x := (hpd 0 2).mul (hpd 1 3)
  have e1 : mvfderiv I (fun y => R y * (2 : ℝ)⁻¹ * (p 0 3 y * p 1 2 y - p 0 2 y * p 1 3 y)) x =
      (R x * (2 : ℝ)⁻¹) • mvfderiv I (fun y => p 0 3 y * p 1 2 y - p 0 2 y * p 1 3 y) x +
        (p 0 3 x * p 1 2 x - p 0 2 x * p 1 3 x) • mvfderiv I (fun y => R y * (2 : ℝ)⁻¹) x :=
    mvfderiv_fun_mul hR2 (hQ1.sub hQ2)
  have e2 : mvfderiv I (fun y => R y * (2 : ℝ)⁻¹) x =
      R x • mvfderiv I (fun _ : M => (2 : ℝ)⁻¹) x + (2 : ℝ)⁻¹ • mvfderiv I R x :=
    mvfderiv_fun_mul hRd hc
  have e3 : mvfderiv I (fun y => p 0 3 y * p 1 2 y - p 0 2 y * p 1 3 y) x =
      mvfderiv I (fun y => p 0 3 y * p 1 2 y) x - mvfderiv I (fun y => p 0 2 y * p 1 3 y) x :=
    mvfderiv_fun_sub hQ1 hQ2
  have e4 : mvfderiv I (fun y => p 0 3 y * p 1 2 y) x =
      p 0 3 x • mvfderiv I (p 1 2) x + p 1 2 x • mvfderiv I (p 0 3) x :=
    mvfderiv_fun_mul (hpd 0 3) (hpd 1 2)
  have e5 : mvfderiv I (fun y => p 0 2 y * p 1 3 y) x =
      p 0 2 x • mvfderiv I (p 1 3) x + p 1 3 x • mvfderiv I (p 0 2) x :=
    mvfderiv_fun_mul (hpd 0 2) (hpd 1 3)
  rw [e1, e2, e3, e4, e5, mvfderiv_const]
  simp only [add_apply, sub_apply,
    smul_apply, zero_apply, smul_eq_mul, hpv,
    Fin.sum_univ_four, gG, Function.update_apply]
  simp only [hp]
  norm_num
  ring

private def slotsEquiv4 : (Fin 4 → Fin 2) ≃ (((Fin 2 × Fin 2) × Fin 2) × Fin 2) where
  toFun f := (((f 0, f 1), f 2), f 3)
  invFun p := ![p.1.1.1, p.1.1.2, p.1.2, p.2]
  left_inv f := by
    funext a
    fin_cases a <;> rfl
  right_inv p := by
    rcases p with ⟨⟨⟨i, j⟩, k⟩, l⟩
    rfl

private theorem sum_fin_cons {n : ℕ} {α : Type*} [Fintype α] (F : (Fin (n + 1) → α) → ℝ) :
    ∑ J, F J = ∑ a, ∑ J : Fin n → α, F (Fin.cons a J) := by
  rw [← (Fin.consEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type]
  rfl

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [FiniteDimensional ℝ E] in
private theorem sum_gG_sq (g : SmoothRiemannianMetric I M) {x : M}
    (e : Module.Basis (Fin 2) ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin 2, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∑ J : Fin 4 → Fin 2, gG g (fun a => e (J a)) ^ 2 = 4 := by
  rw [Fintype.sum_equiv slotsEquiv4 _
    (fun p => gG g (fun a => e (![p.1.1.1, p.1.1.2, p.1.2, p.2] a)) ^ 2)
    (fun J => by
      congr 2
      funext a
      fin_cases a <;> rfl)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, gG, horth]
  norm_num

omit [CompactSpace M] [I.Boundaryless] [T2Space M] [FiniteDimensional ℝ E] in
private theorem inner_self_eq_sum_sq (g : SmoothRiemannianMetric I M) {x : M}
    (e : Module.Basis (Fin 2) ℝ (TangentSpace I x))
    (horth : ∀ i j : Fin 2, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (u : TangentSpace I x) :
    g.inner x u u = ∑ a : Fin 2, g.inner x u (e a) ^ 2 := by
  have hr : ∀ a, g.inner x u (e a) = e.repr u a := by
    intro a
    rw [inner_eq_sum_repr_of_orthonormal g e horth u (e a)]
    fin_cases a <;> simp [Module.Basis.repr_self]
  rw [inner_eq_sum_repr_of_orthonormal g e horth u u, Fin.sum_univ_two, hr, hr]
  ring

omit [CompactSpace M] in
theorem normSq0S_covStep_metricRm04_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ (metricScalarAt g)) (x : M) :
    normSq0S g x (4 + 1) (covStep g 4 (metricRm04 g) x) =
      g.inner x (gradientFun g (metricScalarAt g) x) (gradientFun g (metricScalarAt g) x) := by
  obtain ⟨e, horth⟩ := exists_orthonormalBasis_of_finrank_two g x hdim
  rw [normSq0S_identity_eq_sum_sq g x (4 + 1) e (metricInverseInBasis_of_orthonormal g e horth),
    sum_fin_cons, inner_self_eq_sum_sq g e horth]
  have hcomp : ∀ (a : Fin 2) (J : Fin 4 → Fin 2),
      component0S e (covStep g 4 (metricRm04 g) x) (Fin.cons a J) =
        mvfderiv I (metricScalarAt g) x (e a) / 2 * gG g (fun b => e (J b)) := by
    intro a J
    rw [component0S_apply, ← covStep_metricRm04_apply_of_finrank_two hdim g hR x]
    congr 1
    funext b
    refine Fin.cases rfl (fun i => rfl) b
  simp_rw [hcomp, mul_pow, ← Finset.mul_sum, sum_gG_sq g e horth, inner_gradientFun]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

section Tower

variable {Tm : ℝ} {hTm : 0 < Tm}

omit [CompactSpace M] in
private theorem rm_tower [CompleteSpace E] (hdim : Module.finrank ℝ E = 2)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (k : ℕ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Ioo 0 Tm, ∀ x, ∃ d : ℝ,
      HasDerivAt (fun s => nablaKRm04NormSqIntrinsic S k s x) d t ∧
      d ≤ laplacianAt (flowG S) t (nablaKRm04NormSqIntrinsic S k t) x +
        (-2 * nablaKRm04NormSqIntrinsic S (k + 1) t x +
          towerReactionSum (nablaKRm04NormSqIntrinsic S) c k t x) := by
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  have h := (towerHeatBoundOn_of_solution S hS k).mono_const
    (le_max_left (rmTowerCost (Module.finrank ℝ E) k) 0)
  refine ⟨max (rmTowerCost (Module.finrank ℝ E) k) 0, le_max_right _ _, fun t ht x => ?_⟩
  obtain ⟨d, hd, hle⟩ := h ⟨t, ht⟩ x
  exact ⟨d, hd.hasDerivAt (Ico_mem_nhds ht.1 ht.2), hle⟩

private theorem tower_reaction_le {k : ℕ} (hk : 1 ≤ k) {τ c B : ℝ} (hτ : 0 < τ) (hc : 0 ≤ c)
    (W : ℕ → ℝ) (hW : ∀ i, 0 ≤ W i) (hWB : ∀ i ≤ k, τ ^ (i + 2) * W i ≤ B)
    (u : ℕ → ℝ) (hu0 : 0 ≤ u 0) (hu : ∀ i, 1 ≤ i → u i = τ ^ (i + 2) * W i) :
    τ ^ (k + 2) * ∑ j ∈ Finset.range (k + 1), c * Real.sqrt (W j) * Real.sqrt (W (k - j)) *
        Real.sqrt (W k) ≤
      2 * (k + 1) * c * Real.sqrt B * (∑ i ∈ Finset.range (k + 1), u i) / τ := by
  have hun : ∀ i, 0 ≤ u i := fun i => by
    rcases Nat.eq_zero_or_pos i with h | h
    · rw [h]; exact hu0
    · rw [hu i h]; exact mul_nonneg (pow_nonneg hτ.le _) (hW i)
  set U := ∑ i ∈ Finset.range (k + 1), u i with hU
  have hle : ∀ i ≤ k, 1 ≤ i → τ ^ (i + 2) * W i ≤ U := fun i hi h1 => by
    rw [← hu i h1]
    exact Finset.single_le_sum (fun j _ => hun j) (Finset.mem_range.mpr (by omega))
  have hsB : ∀ i ≤ k, Real.sqrt (τ ^ (i + 2) * W i) ≤ Real.sqrt B := fun i hi =>
    Real.sqrt_le_sqrt (hWB i hi)
  have hterm : ∀ j ∈ Finset.range (k + 1),
      τ ^ (k + 2) * (c * Real.sqrt (W j) * Real.sqrt (W (k - j)) * Real.sqrt (W k)) ≤
        2 * c * Real.sqrt B * U / τ := by
    intro j hj
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hkey := sqrt_mul_pow_triple hτ.le (i := j + 2) (j := k - j + 2) (k := k + 2) (e := k + 3)
      (by omega) (W j) (W (k - j)) (W k)
    have hprod : Real.sqrt (τ ^ (j + 2) * W j) * Real.sqrt (τ ^ (k - j + 2) * W (k - j)) *
        Real.sqrt (τ ^ (k + 2) * W k) ≤ 2 * Real.sqrt B * U := by
      have hk0 := Real.sqrt_nonneg (τ ^ (k + 2) * W k)
      have hj0 := Real.sqrt_nonneg (τ ^ (j + 2) * W j)
      have hl0 := Real.sqrt_nonneg (τ ^ (k - j + 2) * W (k - j))
      have hsqB := Real.sqrt_nonneg B
      have hUk := hle k le_rfl hk
      have hU0 : 0 ≤ U := Finset.sum_nonneg fun i _ => hun i
      have hsq : ∀ a : ℝ, 0 ≤ a → Real.sqrt a * Real.sqrt a = a := fun a ha =>
        Real.mul_self_sqrt ha
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0
        rw [Nat.sub_zero, mul_assoc, hsq _ (mul_nonneg (pow_nonneg hτ.le _) (hW k))]
        nlinarith [hsB 0 (Nat.zero_le k), mul_nonneg hsqB (mul_nonneg (pow_nonneg hτ.le (k + 2))
          (hW k))]
      · have hj := hle j hjk hpos
        have h1 : Real.sqrt (τ ^ (j + 2) * W j) * Real.sqrt (τ ^ (k + 2) * W k) ≤ U := by
          nlinarith [sq_nonneg (Real.sqrt (τ ^ (j + 2) * W j) - Real.sqrt (τ ^ (k + 2) * W k)),
            hsq _ (mul_nonneg (pow_nonneg hτ.le (j + 2)) (hW j)),
            hsq _ (mul_nonneg (pow_nonneg hτ.le (k + 2)) (hW k))]
        have h2 := hsB (k - j) (Nat.sub_le k j)
        calc Real.sqrt (τ ^ (j + 2) * W j) * Real.sqrt (τ ^ (k - j + 2) * W (k - j)) *
              Real.sqrt (τ ^ (k + 2) * W k)
            = Real.sqrt (τ ^ (k - j + 2) * W (k - j)) *
              (Real.sqrt (τ ^ (j + 2) * W j) * Real.sqrt (τ ^ (k + 2) * W k)) := by ring
          _ ≤ Real.sqrt B * U := mul_le_mul h2 h1 (mul_nonneg hj0 hk0) hsqB
          _ ≤ 2 * Real.sqrt B * U := by nlinarith [mul_nonneg hsqB hU0]
    rw [hkey] at hprod
    have hτ3 : τ ^ (k + 3) = τ ^ (k + 2) * τ := pow_succ τ (k + 2)
    rw [hτ3] at hprod
    rw [le_div_iff₀ hτ]
    have hS0 : 0 ≤ Real.sqrt (W j) * Real.sqrt (W (k - j)) * Real.sqrt (W k) :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    calc τ ^ (k + 2) * (c * Real.sqrt (W j) * Real.sqrt (W (k - j)) * Real.sqrt (W k)) * τ
        = c * (τ ^ (k + 2) * τ * (Real.sqrt (W j) * Real.sqrt (W (k - j)) *
            Real.sqrt (W k))) := by ring
      _ ≤ c * (2 * Real.sqrt B * U) := mul_le_mul_of_nonneg_left hprod hc
      _ = 2 * c * Real.sqrt B * U := by ring
  rw [Finset.mul_sum]
  calc ∑ j ∈ Finset.range (k + 1), τ ^ (k + 2) *
        (c * Real.sqrt (W j) * Real.sqrt (W (k - j)) * Real.sqrt (W k))
      ≤ ∑ _j ∈ Finset.range (k + 1), 2 * c * Real.sqrt B * U / τ := Finset.sum_le_sum hterm
    _ = 2 * (k + 1) * c * Real.sqrt B * U / τ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

omit [CompactSpace M] [I.Boundaryless] [T2Space M] in
private theorem laplacianAt_affine_sq {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t a b : ℝ) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M) :
    laplacianAt (flowG S) t (fun y => (f y * a - b) ^ 2) x =
      2 * (f x * a - b) * (a * laplacianAt (flowG S) t f x) +
        2 * a ^ 2 * (S.family.metric t).inner x (gradientFun (S.family.metric t) f x)
          (gradientFun (S.family.metric t) f x) := by
  set g := S.family.metric t with hg
  have hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => f y * a - b) := (hf.mul contMDiff_const).sub
    contMDiff_const
  have hφd : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y * a - b) y := fun y =>
    (hφ y).mdifferentiableAt (by simp)
  have hfd : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) f y := fun y => (hf y).mdifferentiableAt (by simp)
  rw [laplacianAt_sq_of_scalarRegular (flowG S) t hφd
    (fun y => gradientFun_mdiffAt ((flowG S).metric t) hφ y)]
  have hlap : laplacianAt (flowG S) t (fun y => f y * a - b) x =
      a * laplacianAt (flowG S) t f x := by
    unfold laplacianAt
    have hfa : ∀ y, MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y * a) y := fun y =>
      (hfd y).mul mdifferentiableAt_const
    rw [laplacian_sub_const _ _ b hfa x]
    have hsm : (fun y => f y * a) = a • f := by
      funext y; simp [smul_eq_mul, mul_comm]
    rw [hsm]
    exact laplacianAt_smul (flowG S) t a hfd (gradientFun_mdiffAt ((flowG S).metric t) hf x)
  have hgrad : gradientAt (flowG S) t (fun y => f y * a - b) x =
      a • gradientFun g f x := by
    apply SmoothRiemannianMetric.eq_of_inner_eq g
    intro ζ
    change g.inner x (gradientFun g (fun y => f y * a - b) x) ζ = _
    rw [inner_gradientFun, map_smul, smul_apply, inner_gradientFun,
      smul_eq_mul]
    have hm : (MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y * a) x) :=
      (hfd x).mul mdifferentiableAt_const
    have e1 : mvfderiv I (fun y => f y * a - b) x =
        mvfderiv I (fun y => f y * a) x - mvfderiv I (fun _ : M => b) x :=
      mvfderiv_fun_sub hm mdifferentiableAt_const
    have e2 : mvfderiv I (fun y => f y * a) x =
        f x • mvfderiv I (fun _ : M => a) x + a • mvfderiv I f x :=
      mvfderiv_fun_mul (hfd x) mdifferentiableAt_const
    rw [e1, e2, mvfderiv_const, mvfderiv_const]
    simp
  rw [hlap, hgrad]
  change 2 * (f x * a - b) * (a * laplacianAt (flowG S) t f x) +
      2 * g.inner x (a • gradientFun g f x) (a • gradientFun g f x) = _
  rw [map_smul, map_smul, smul_apply]
  simp only [smul_eq_mul]
  ring

private def dTower {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) :
    ℕ → ℝ → M → ℝ
  | 0 => fun t x => (S.scalar t x * (2 * (Tm - t)) - 2) ^ 2
  | (q + 1) => fun t x => (2 * (Tm - t)) ^ (q + 3) * nablaKRm04NormSqIntrinsic S (q + 1) t x

omit [CompactSpace M] in
private theorem nablaKRm04NormSqIntrinsic_one_of_finrank_two (hdim : Module.finrank ℝ E = 2)
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : ℝ) (x : M) :
    nablaKRm04NormSqIntrinsic S 1 t x =
      (S.family.metric t).inner x (gradientFun (S.family.metric t) (S.scalar t) x)
        (gradientFun (S.family.metric t) (S.scalar t) x) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := normSq0S_covStep_metricRm04_of_finrank_two hdim (S.family.metric t)
    (scalarSmoothOfSolution S t) x
  rw [nablaKRm04NormSqIntrinsic, nablaKRm_eq_iterCov]
  exact h

omit [CompactSpace M] in
private theorem dTower_joint {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (q : ℕ) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => dTower S q p.1 p.2)
      (Ioo 0 Tm ×ˢ univ) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  have hlin : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M => 2 * (Tm - p.1)) :=
    contMDiff_const.mul (contMDiff_const.sub contMDiff_fst)
  cases q with
  | zero =>
    have h := scalar_joint S hS
    exact ((h.mul hlin.contMDiffOn).sub contMDiffOn_const).pow 2
  | succ q =>
    exact (hlin.contMDiffOn.pow (q + 3)).mul (towerNorm_joint hS (q + 1))

omit [I.Boundaryless] [CompactSpace M] in
private theorem dTower_nonneg {Tm : ℝ} {hTm : 0 < Tm}
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (q : ℕ) {t : ℝ}
    (ht : t < Tm) (x : M) : 0 ≤ dTower S q t x := by
  cases q with
  | zero => exact sq_nonneg _
  | succ q =>
    exact mul_nonneg (pow_nonneg (by linarith) _) (nablaKRm04NormSqIntrinsic_nonneg S _ t x)

private theorem dTower_zero_tower [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2) {Tm : ℝ}
    {hTm : 0 < Tm} (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hscal : ∀ x, 0 < S.scalar 0 x) :
    ∃ C : ℝ, ∀ t ∈ Ioo 0 Tm, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => dTower S 0 s x) d t ∧
      d ≤ laplacianAt (flowG S) t (dTower S 0 t) x +
        (-2 * dTower S 1 t x + C * ∑ j ∈ Finset.range (0 + 1), dTower S j t x) /
          (2 * (Tm - t)) := by
  obtain ⟨K, hK⟩ := surfaceFlow_normalized_scalar_upper hdim S hS hscal
  have hTT := surfaceFlow_le_extinctionTime hTm S hS hdim hscal
  refine ⟨2 * max K 0, fun t ht x => ?_⟩
  set a := 2 * (Tm - t) with ha
  have ha0 : 0 < a := by rw [ha]; linarith [ht.2]
  set R := S.scalar t x with hRdef
  have hR0 : 0 < R := surfaceFlow_scalar_pos S hS hscal ⟨ht.1.le, ht.2⟩ x
  have hRa : R * a ≤ max K 0 := by
    have h1 := hK t ⟨ht.1.le, ht.2⟩ x
    have h2 : R * a ≤ R * (2 * (surfaceArea (S.family.metric 0) /
        totalScalarCurvature (S.family.metric 0) - t)) :=
      mul_le_mul_of_nonneg_left (by rw [ha]; linarith) hR0.le
    exact (h2.trans h1).trans (le_max_left _ _)
  set L := laplacianAt (flowG S) t (S.scalar t) x with hL
  set G := (S.family.metric t).inner x (gradientFun (S.family.metric t) (S.scalar t) x)
    (gradientFun (S.family.metric t) (S.scalar t) x) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact metric_inner_self_nonneg (S.family.metric t) x _
  have hR' := surfaceScalar_hasDerivAt S hS hdim ht x
  have hlap : laplacianAt (flowG S) t (S.scalar t) x =
      ΔG (S.family.metric t) ⟨S.scalar t, scalarSmoothOfSolution S t⟩ x :=
    laplacianAt_eq_delta (flowG S) t (scalarSmoothOfSolution S t) rfl x
  rw [← hlap, ← hL, ← hRdef] at hR'
  have hlin : HasDerivAt (fun s : ℝ => 2 * (Tm - s)) (-2) t := by
    have := ((hasDerivAt_const t Tm).sub (hasDerivAt_id t)).const_mul 2
    simpa using this
  have hd := ((hR'.mul hlin).sub_const 2).pow 2
  refine ⟨_, hd, ?_⟩
  have hu0 : dTower S 0 t = fun y => (S.scalar t y * a - 2) ^ 2 := rfl
  have hu1 : dTower S 1 t x = a ^ 3 * G := by
    change a ^ (0 + 3) * nablaKRm04NormSqIntrinsic S (0 + 1) t x = _
    rw [nablaKRm04NormSqIntrinsic_one_of_finrank_two hdim S t x]
  rw [hu0, laplacianAt_affine_sq S t a 2 (scalarSmoothOfSolution S t) x, hu1,
    Finset.sum_range_one]
  change _ ≤ _ + (-2 * (a ^ 3 * G) + 2 * max K 0 * (R * a - 2) ^ 2) / a
  have hsplit : (-2 * (a ^ 3 * G) + 2 * max K 0 * (R * a - 2) ^ 2) / a =
      -2 * a ^ 2 * G + 2 * max K 0 * (R * a - 2) ^ 2 / a := by
    field_simp
  rw [hsplit]
  have hkey : 2 * R * (R * a - 2) ^ 2 ≤ 2 * max K 0 * (R * a - 2) ^ 2 / a := by
    rw [le_div_iff₀ ha0]
    nlinarith [sq_nonneg (R * a - 2)]
  have e1 : ((fun s => S.scalar s x) * fun s => 2 * (Tm - s)) t = R * a := rfl
  rw [e1, ← hG]
  simp only [Nat.cast_ofNat, ← ha, pow_one, show (2 : ℕ) - 1 = 1 from rfl]
  nlinarith [hkey]

private theorem dTower_succ_tower [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2) {Tm : ℝ}
    {hTm : 0 < Tm} (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm))
    (hS : IsSolutionOn S) (hscal : ∀ x, 0 < S.scalar 0 x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 Tm)
    (q : ℕ) :
    ∃ C : ℝ, ∀ t ∈ Ioo t₀ Tm, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => dTower S (q + 1) s x) d t ∧
      d ≤ laplacianAt (flowG S) t (dTower S (q + 1) t) x +
        (-2 * dTower S (q + 1 + 1) t x +
          C * ∑ j ∈ Finset.range (q + 1 + 1), dTower S j t x) / (2 * (Tm - t)) := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)
  obtain ⟨c, hc, hev⟩ := rm_tower hdim S hS (q + 1)
  have hTT := surfaceFlow_le_extinctionTime hTm S hS hdim hscal
  choose Cb hCb using fun j => surfaceFlow_normalized_curvatureDerivative_bound hdim hTm S hS
    hscal ht₀.1 j
  set B := ∑ j ∈ Finset.range (q + 1 + 1), |Cb j| with hBdef
  refine ⟨2 * ((q + 1 : ℕ) + 1) * c * Real.sqrt B, fun t ht x => ?_⟩
  have htT : t ∈ Ioo 0 Tm := ⟨ht₀.1.trans ht.1, ht.2⟩
  obtain ⟨d, hd, hle⟩ := hev t htT x
  set a := 2 * (Tm - t) with ha
  have ha0 : 0 < a := by rw [ha]; linarith [ht.2]
  set w := nablaKRm04NormSqIntrinsic S with hw
  have hlin : HasDerivAt (fun s : ℝ => 2 * (Tm - s)) (-2) t := by
    have := ((hasDerivAt_const t Tm).sub (hasDerivAt_id t)).const_mul 2
    simpa using this
  have hD := (hlin.pow (q + 3)).mul hd
  refine ⟨_, hD, ?_⟩
  have hsm : dTower S (q + 1) t = a ^ (q + 3) • w (q + 1) t := by
    funext y; simp [dTower, smul_eq_mul, ha, hw]
  have hwsm : ContMDiff I 𝓘(ℝ, ℝ) ∞ (w (q + 1) t) := nablaKNorm_smooth S t (q + 1)
  have hlap : laplacianAt (flowG S) t (dTower S (q + 1) t) x =
      a ^ (q + 3) * laplacianAt (flowG S) t (w (q + 1) t) x := by
    rw [hsm]
    exact laplacianAt_smul (flowG S) t _ (fun y => (hwsm y).mdifferentiableAt (by simp))
      (gradientFun_mdiffAt ((flowG S).metric t) hwsm x)
  have hnext : dTower S (q + 1 + 1) t x = a ^ (q + 4) * w (q + 2) t x := rfl
  have hreact := tower_reaction_le (k := q + 1) (τ := a) (B := B) (by omega) ha0 hc
    (fun i => w i t x)
    (fun i => nablaKRm04NormSqIntrinsic_nonneg S i t x)
    (fun i hi => by
      have h1 := hCb i t ⟨ht.1.le, ht.2⟩ x
      have h2 : a ^ (i + 2) ≤ (2 * (surfaceArea (S.family.metric 0) /
          totalScalarCurvature (S.family.metric 0) - t)) ^ (i + 2) :=
        pow_le_pow_left₀ ha0.le (by rw [ha]; linarith) _
      have h3 : Cb i ≤ B := (le_abs_self _).trans (Finset.single_le_sum
        (fun j _ => abs_nonneg (Cb j)) (Finset.mem_range.mpr (by omega)))
      calc a ^ (i + 2) * w i t x ≤ (2 * (surfaceArea (S.family.metric 0) /
            totalScalarCurvature (S.family.metric 0) - t)) ^ (i + 2) * w i t x :=
            mul_le_mul_of_nonneg_right h2 (nablaKRm04NormSqIntrinsic_nonneg S i t x)
        _ ≤ Cb i := h1
        _ ≤ B := h3)
    (fun i => dTower S i t x) (dTower_nonneg S 0 ht.2 x)
    (fun i hi => by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rfl)
  rw [hlap, hnext]
  unfold towerReactionSum at hle
  set Rs := ∑ j ∈ Finset.range (q + 1 + 1), c * Real.sqrt (w j t x) *
    Real.sqrt (w (q + 1 - j) t x) * Real.sqrt (w (q + 1) t x) with hRs
  set Sd := ∑ j ∈ Finset.range (q + 1 + 1), dTower S j t x with hSd
  set Lw := laplacianAt (flowG S) t (w (q + 1) t) x with hLw
  set K := 2 * ((q + 1 : ℕ) + 1 : ℝ) * c * Real.sqrt B with hK
  have hreact' : a ^ (q + 3) * Rs ≤ K * Sd / a := by
    exact hreact
  have hw0 : 0 ≤ w (q + 1) t x := nablaKRm04NormSqIntrinsic_nonneg S _ t x
  have hpow : a ^ (q + 4) = a ^ (q + 3) * a := pow_succ a (q + 3)
  have hsplit : (-2 * (a ^ (q + 4) * w (q + 2) t x) + K * Sd) / a =
      -2 * (a ^ (q + 3) * w (q + 2) t x) + K * Sd / a := by
    rw [hpow]
    field_simp
  have e0 : ((fun s => 2 * (Tm - s)) ^ (q + 3)) t = a ^ (q + 3) := rfl
  rw [hsplit, e0]
  have hA : 0 ≤ a ^ (q + 3) := pow_nonneg ha0.le _
  have hmul : a ^ (q + 3) * d ≤ a ^ (q + 3) * Lw + -2 * (a ^ (q + 3) * w (q + 2) t x) +
      a ^ (q + 3) * Rs := by
    have := mul_le_mul_of_nonneg_left hle hA
    linarith
  have hfirst : (↑(q + 3) : ℝ) * a ^ (q + 3 - 1) * (-2) * w (q + 1) t x ≤ 0 := by
    have : 0 ≤ (↑(q + 3) : ℝ) * a ^ (q + 3 - 1) := by positivity
    nlinarith
  linarith [hreact', hmul, hfirst]

end Tower
theorem surfaceFlow_scalar_derivative_decay [ConnectedSpace M] (hdim : Module.finrank ℝ E = 2)
    {Tm : ℝ} (hTm : 0 < Tm)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 Tm hTm)) (hS : IsSolutionOn S)
    (hscal : ∀ x, 0 < S.scalar 0 x)
    (hrate : ∃ C δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico 0 Tm, ∀ x,
      |S.scalar t x * (2 * (Tm - t)) - 2| ≤ C * (Tm - t) ^ δ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 Tm) :
    ∀ q : ℕ, ∃ C β : ℝ, 0 < β ∧ ∀ t ∈ Ico t₀ Tm, ∀ x,
      (2 * (Tm - t)) ^ (q + 3) * nablaKRm04NormSqIntrinsic S (q + 1) t x ≤ C * (Tm - t) ^ β := by
  obtain ⟨Cr, δ, hδ, hr⟩ := hrate
  obtain ⟨C0, hC0⟩ := dTower_zero_tower hdim S hS hscal
  choose Cs hCs using dTower_succ_tower hdim S hS hscal ht₀
  let C : ℕ → ℝ := fun q => Nat.casesOn q C0 Cs
  have htower : ∀ q, ∀ t ∈ Ioo t₀ Tm, ∀ x, ∃ d : ℝ, HasDerivAt (fun s => dTower S q s x) d t ∧
      d ≤ laplacianAt (flowG S) t (dTower S q t) x +
        (-2 * dTower S (q + 1) t x + C q * ∑ j ∈ Finset.range (q + 1), dTower S j t x) /
          (2 * (Tm - t)) := by
    intro q
    cases q with
    | zero => exact fun t ht x => hC0 t ⟨ht₀.1.trans ht.1, ht.2⟩ x
    | succ q => exact hCs q
  have h0 : ∃ K : ℝ, ∀ t ∈ Ico t₀ Tm, ∀ x, dTower S 0 t x ≤ K * (Tm - t) ^ (2 * δ) := by
    refine ⟨Cr ^ 2, fun t ht x => ?_⟩
    have hτ : 0 < Tm - t := by linarith [ht.2]
    have h := hr t ⟨ht₀.1.le.trans ht.1, ht.2⟩ x
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    rw [sq_abs] at h2
    change (S.scalar t x * (2 * (Tm - t)) - 2) ^ 2 ≤ _
    calc (S.scalar t x * (2 * (Tm - t)) - 2) ^ 2 ≤ (Cr * (Tm - t) ^ δ) ^ 2 := h2
      _ = Cr ^ 2 * (Tm - t) ^ (2 * δ) := by
        rw [mul_pow, ← Real.rpow_natCast ((Tm - t) ^ δ) 2, ← Real.rpow_mul hτ.le,
          Nat.cast_ofNat, mul_comm δ 2]
  have hdec := flow_linear_tower_decay S (Tst := Tm) (c := 2 * δ) le_rfl (by positivity) ht₀
    (dTower S) (dTower_joint S hS) (fun q t ht x => dTower_nonneg S q ht.2 x) C htower h0
  intro q
  obtain ⟨K, hK⟩ := hdec (q + 1)
  exact ⟨K, 2 * δ, by positivity, fun t ht x => hK t ht x⟩


end GC.Geometry
