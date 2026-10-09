import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Comparison.Hessian.AlongGeodesic

/-!
# IMS04 / O2 kernel（O-W-CURV, suffix `_CV`）：曲线加速度的法向分解

horocycle 加速度 `|D^h β'|_h = ½|β'|²_h` 的三块抽象零件（与 cusp 无关）：

* `inner_self_eq_sq_of_normal_CV`（维数论证）：`T_q M` 中 `L(T_x N) ⊕ ℝ n` 满秩（`dim N + 1 = dim M`，
  `L` 正定、`n ⟂ L`、`|n| = 1`）时，`D ⟂ L(T_x N)` ⇒ `|D|² = ⟨D, n⟩²`；
* `inner_acceleration_comp_mfderiv_eq_zero_CV`（Gauss formula）：`ι` isometric、`γ` 为 geodesic ⇒
  `D^M (ι∘γ)' ⟂ dι(T N)`（`secondFundamentalFormAmbientAt` 的 diagonal 形式 + 法向性）；
* `inner_gradFun_acceleration_eq_neg_hessFun_CV`（level set 法向分量）：`ρ ∘ β` 常值 ⇒
  `⟨∇ρ, D β'⟩ = -Hess ρ(β', β')`（`(ρ∘β)' = ⟨∇ρ, β'⟩ ≡ 0` 求导 + metric compatibility +
  `covDerivAlong` of field = Levi-Civita + `hessFun_eq_cov_grad`）。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open Bundle
open scoped Manifold ContDiff
namespace GC.LongTime

section LinearAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EN : Type*} [AddCommGroup EN] [Module ℝ EN] [FiniteDimensional ℝ EN]

/-- **维数论证**：`L : EN → T_q M` 正定（`⟨La, La⟩ > 0`），`n ⟂ L(EN)`、`|n| = 1`、
`dim M = dim EN + 1`。则 `D ⟂ L(EN)` ⇒ `D = ⟨D, n⟩ n`，故 `|D|² = ⟨D, n⟩²`。 -/
theorem inner_self_eq_sq_of_normal_CV (g : SmoothRiemannianMetric I M) (q : M)
    (L : EN →ₗ[ℝ] TangentSpace I q) (hL : ∀ a, a ≠ 0 → 0 < g.inner q (L a) (L a))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ EN + 1) (n D : TangentSpace I q)
    (hn : g.inner q n n = 1) (hnL : ∀ a, g.inner q n (L a) = 0)
    (hDL : ∀ a, g.inner q D (L a) = 0) :
    g.inner q D D = g.inner q D n ^ 2 := by
  classical
  set c : ℝ := g.inner q D n with hc
  set P : TangentSpace I q := D - c • n with hP
  have hLn : ∀ a, g.inner q (L a) n = 0 := fun a => (g.symm q (L a) n).trans (hnL a)
  have hPn : g.inner q P n = 0 := by
    simp only [hP, map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul, hn]
    ring
  have hPL : ∀ a, g.inner q P (L a) = 0 := by
    intro a
    simp only [hP, map_sub, map_smul, sub_apply,
      smul_apply, smul_eq_mul, hDL a, hnL a]
    ring
  let Φ : EN × ℝ →ₗ[ℝ] TangentSpace I q :=
    L.coprod (LinearMap.toSpanSingleton ℝ (TangentSpace I q) n)
  have hΦ : ∀ (a : EN) (r : ℝ), Φ (a, r) = L a + r • n := fun _ _ => rfl
  have hpair : ∀ (a : EN) (r : ℝ), g.inner q (L a + r • n) n = r := by
    intro a r
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul, hLn a, hn]
    ring
  have hzero : ∀ a : EN, L a = 0 → a = 0 := by
    intro a ha
    by_contra hne
    have h := hL a hne
    simp [ha] at h
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, r⟩ h0
    rw [hΦ] at h0
    have hr : r = 0 := by
      have h1 := hpair a r
      rw [h0, map_zero, zero_apply] at h1
      exact h1.symm
    subst hr
    rw [zero_smul, add_zero] at h0
    rw [hzero a h0]
    rfl
  have hfin : Module.finrank ℝ (EN × ℝ) = Module.finrank ℝ (TangentSpace I q) := by
    rw [Module.finrank_prod, Module.finrank_self]
    exact hdim.symm
  obtain ⟨⟨a, r⟩, har⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj P
  rw [hΦ] at har
  have hr : r = 0 := by
    have h1 := hpair a r
    rw [har, hPn] at h1
    exact h1.symm
  subst hr
  rw [zero_smul, add_zero] at har
  have hP0 : P = 0 := by
    have h2 := hPL a
    rw [← har] at h2
    have ha0 : a = 0 := by
      by_contra hne
      exact (ne_of_gt (hL a hne)) h2
    rw [← har, ha0, map_zero]
  have hD : D = c • n := sub_eq_zero.mp hP0
  rw [hD]
  simp only [map_smul, smul_apply, smul_eq_mul, hn]
  ring

end LinearAlgebra

section Gauss

variable {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Gauss formula 的法向性**：`ι : N → M` isometric（逐点 `ι^* g_M = g_N`），`γ` 为 `g_N`-geodesic
⇒ `ι ∘ γ` 的 `g_M`-加速度与 `dι(T N)` 正交。 -/
theorem inner_acceleration_comp_mfderiv_eq_zero_CV
    (gN : SmoothRiemannianMetric IN N) (gM : SmoothRiemannianMetric I M) {ι : N → M}
    (hι : ContMDiff IN I ∞ ι)
    (hmetric : ∀ (x : N) (u v : TangentSpace IN x),
      gM.inner (ι x) (mfderiv IN I ι x u) (mfderiv IN I ι x v) = gN.inner x u v)
    {γ : ℝ → N} (hγ : ContMDiff 𝓘(ℝ, ℝ) IN ∞ γ) (hgeo : IsGeodesic gN γ) (t : ℝ)
    (w : TangentSpace IN (γ t)) :
    gM.inner (ι (γ t))
      (covDerivAlong gM (fun s => ι (γ s))
        (fun s => mfderiv 𝓘(ℝ, ℝ) I (fun s => ι (γ s)) s 1) t)
      (mfderiv IN I ι (γ t) w) = 0 := by
  have h1 := secondFundamentalFormAmbientAt_diagonal_along_curve gN gM hι γ hγ t
  have h0 : covariantAcceleration gN γ t = 0 := by
    rw [covariantAcceleration_def]
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 gN γ t
      ((hγ t).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))) (hgeo t)
  rw [secondFundamentalFormDiagonalAlongCurve_def, h0, map_zero, sub_zero,
    covariantAcceleration_def] at h1
  have key := secondFundamentalFormAmbientAt_inner_mfderiv_eq_zero_of_inner_map hι hmetric (γ t)
    ((mfderiv 𝓘(ℝ, ℝ) IN γ t : ℝ →L[ℝ] _) 1) ((mfderiv 𝓘(ℝ, ℝ) IN γ t : ℝ →L[ℝ] _) 1) w
  rw [h1] at key
  exact key

end Gauss

section Hessian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]

/-- **level set 的法向分量**：`ρ ∘ β` 常值 ⇒ `⟨∇ρ, D β'⟩ = -Hess ρ(β', β')`。 -/
theorem inner_gradFun_acceleration_eq_neg_hessFun_CV (g : SmoothRiemannianMetric I M)
    {ρ : M → ℝ} (hρ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ) {β : ℝ → M} (hβ : ContMDiff 𝓘(ℝ, ℝ) I ∞ β)
    (hconst : ∀ s, ρ (β s) = ρ (β 0)) (t : ℝ) :
    g.inner (β t) (gradFun g ρ (β t))
        (covDerivAlong g β (fun s => mfderiv 𝓘(ℝ, ℝ) I β s 1) t) =
      -hessFun g ρ (β t) (mfderiv 𝓘(ℝ, ℝ) I β t 1) (mfderiv 𝓘(ℝ, ℝ) I β t 1) := by
  have hzero : (fun s => g.inner (β s) (gradFun g ρ (β s)) (mfderiv 𝓘(ℝ, ℝ) I β s 1)) =
      fun _ => (0 : ℝ) := by
    funext s
    have hd := deriv_comp_eq_inner_grad_velocity g hρ hβ s
    have hc : ρ ∘ β = fun _ => ρ (β 0) := funext hconst
    rw [hc, deriv_const] at hd
    exact hd.symm
  have htot : ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun s => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) (β s)
        (gradFun g ρ (β s))) :=
    (gradFun_contMDiff_total_section g hρ).comp hβ
  have hGd : DifferentiableAt ℝ (chartRepAt (I := I) β (fun s => gradFun g ρ (β s)) t) t :=
    differentiableAt_chartRepAt_of_contMDiff_two
      (htot.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))) t
  have hVd : DifferentiableAt ℝ
      (chartRepAt (I := I) β (fun s => mfderiv 𝓘(ℝ, ℝ) I β s 1) t) t :=
    differentiableAt_chartRepAt_curveVelocity
      ((hβ t).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞))))
  have hder := Variation.inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g β
    (fun s => gradFun g ρ (β s)) (fun s => mfderiv 𝓘(ℝ, ℝ) I β s 1) t (hβ t) hGd hVd
  rw [hzero] at hder
  have h0 := hder.unique (hasDerivAt_const t (0 : ℝ))
  have hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun x => TotalSpace.mk' E (E := (TangentSpace I : M → Type _)) x (gradFun g ρ x))
      (β t) :=
    ((gradFun_contMDiff_total_section g hρ) (β t)).mdifferentiableAt (by simp)
  have hLC := covDerivAlong_restrict_eq_leviCivita g β (gradFun g ρ) t hβ hX
  have hH := hessFun_eq_cov_grad g hρ (β t) (mfderiv 𝓘(ℝ, ℝ) I β t 1)
    (mfderiv 𝓘(ℝ, ℝ) I β t 1)
  rw [hLC] at h0
  rw [hH]
  linear_combination h0

end Hessian

end GC.LongTime
