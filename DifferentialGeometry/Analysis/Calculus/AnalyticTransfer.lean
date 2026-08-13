import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Operator.LinearIsometry

noncomputable section


open Filter
open scoped Topology ContDiff ENNReal

namespace DifferentialGeometry
namespace AnalyticTransfer

variable {𝕜 X F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

lemma tendsto_slope_of_hasFDerivAt {f : X → F} {f' : X →L[𝕜] F} {x : X}
    (hf : HasFDerivAt f f' x) (v : X) :
    Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] (0 : 𝕜)) (𝓝 (f' v)) := by
  have hlim : Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + (t⁻¹)⁻¹ • v) - f x))
      (𝓝[≠] (0 : 𝕜)) (𝓝 (f' v)) := by
    exact hf.lim v (l := 𝓝[≠] (0 : 𝕜)) (c := fun t : 𝕜 => t⁻¹) (by
      convert (tendsto_norm_cobounded_atTop (E := 𝕜)).comp
        (tendsto_inv₀_nhdsNE_zero (α := 𝕜)) using 1)
  convert hlim using 1
  ext t
  rw [inv_inv]

lemma mem_submodule_of_hasFDerivAt {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {f' : X →L[𝕜] F} {x : X} (hf : HasFDerivAt f f' x)
    (hfS : ∀ y, f y ∈ S) (v : X) : f' v ∈ S := by
  have h₁ : Tendsto (fun t : 𝕜 => t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] (0 : 𝕜)) (𝓝 (f' v)) :=
    tendsto_slope_of_hasFDerivAt hf v
  have h₂ : ∀ᶠ t : 𝕜 in 𝓝[≠] (0 : 𝕜), t⁻¹ • (f (x + t • v) - f x) ∈ S := by
    filter_upwards with t
    exact S.smul_mem _ (S.sub_mem (hfS (x + t • v)) (hfS x))
  have h₃ : f' v ∈ closure (S : Set F) := mem_closure_of_tendsto h₁ h₂
  exact hS.closure_subset h₃

lemma hasFDerivAt_codRestrict {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {f' : X →L[𝕜] F} {x : X} (hf : HasFDerivAt f f' x)
    (hfS : ∀ y, f y ∈ S) :
    HasFDerivAt (fun y => ⟨f y, hfS y⟩ : X → S)
      (f'.codRestrict S (fun v => mem_submodule_of_hasFDerivAt hS hf hfS v)) x := by
  refine (hasFDerivAt_iff_tendsto (E := X) (F := S)
    (f := fun y : X => ⟨f y, hfS y⟩)
    (f' := f'.codRestrict S (fun v => mem_submodule_of_hasFDerivAt hS hf hfS v))
    (x := x)).2 ?_
  simpa [Submodule.coe_norm] using (hasFDerivAt_iff_tendsto.mp hf)

def multilinearValues (S : Submodule 𝕜 F) (k : ℕ) : Submodule 𝕜 (X [×k]→L[𝕜] F) where
  carrier := {T | ∀ v : Fin k → X, T v ∈ S}
  zero_mem' := by intro v; exact S.zero_mem
  add_mem' := by
    intro T U hT hU v
    exact S.add_mem (hT v) (hU v)
  smul_mem' := by
    intro c T hT v
    exact S.smul_mem c (hT v)

lemma isClosed_multilinearValues {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F)) (k : ℕ) :
    IsClosed {T : X [×k]→L[𝕜] F | ∀ v : Fin k → X, T v ∈ S} := by
  rw [show {T : X [×k]→L[𝕜] F | ∀ v : Fin k → X, T v ∈ S} =
      ⋂ v : Fin k → X, {T : X [×k]→L[𝕜] F | T v ∈ S} by
    ext T
    simp]
  exact isClosed_iInter (fun v : Fin k → X => hS.preimage
    (show Continuous fun T : X [×k]→L[𝕜] F => T v from continuous_eval_const v))

lemma fderiv_mem_multilinearValues {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {k : ℕ} {g : X → X [×k]→L[𝕜] F} {g' : X →L[𝕜] X [×k]→L[𝕜] F} {x : X} (hg : HasFDerivAt g g' x)
    (hgS : ∀ y v, g y v ∈ S) (v : X) (w : Fin k → X) : g' v w ∈ S := by
  have hw : g' v ∈ multilinearValues S k :=
    mem_submodule_of_hasFDerivAt (F := X [×k]→L[𝕜] F) (S := multilinearValues S k)
      (by simpa [multilinearValues] using isClosed_multilinearValues hS k)
      hg (fun y w' => hgS y w') v
  exact hw w

lemma hasFTaylorSeriesUpTo_coe_mem {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {p : X → FormalMultilinearSeries 𝕜 X F} {n : WithTop ℕ∞}
    (hp : HasFTaylorSeriesUpTo n f p) (hfS : ∀ x, f x ∈ S) :
    ∀ k : ℕ, k ≤ n → ∀ x : X, ∀ v : Fin k → X, p x k v ∈ S := by
  intro k
  induction k
  case zero =>
    intro hk x v
    have h : (p x 0) v = f x := by
      calc
        (p x 0) v = (p x 0).curry0 := by
          rw [ContinuousMultilinearMap.curry0_apply]
          congr
          ext i
          exact Fin.elim0 i
        _ = f x := hp.zero_eq x
    simpa [h] using hfS x
  case succ k ih =>
    intro hk x v
    have hmn : (k : WithTop ℕ∞) < n := by
      have hklt : (k : WithTop ℕ∞) < (k + 1 : WithTop ℕ∞) := by
        exact_mod_cast (Nat.lt_succ_self k)
      exact hklt.trans_le hk
    have hderiv : HasFDerivAt (fun y => p y k) (p x (k + 1)).curryLeft x :=
      hp.fderiv k hmn x
    have hmem : ∀ (y : X) (w : Fin k → X), p y k w ∈ S := by
      intro y w
      have hkle : (k : WithTop ℕ∞) ≤ (k + 1 : WithTop ℕ∞) := by
        exact_mod_cast (Nat.le_succ k)
      exact ih (le_trans hkle hk) y w
    have hfderiv : ∀ (v : X) (w : Fin k → X), fderiv 𝕜 (fun y => p y k) x v w ∈ S := by
      intro v w
      have hw : fderiv 𝕜 (fun y => p y k) x v ∈ multilinearValues S k :=
        by
          rw [hderiv.fderiv]
          exact mem_submodule_of_hasFDerivAt (F := X [×k]→L[𝕜] F) (S := multilinearValues S k)
            (by simpa [multilinearValues] using isClosed_multilinearValues hS k)
            hderiv (fun y w' => hmem y w') v
      exact hw w
    have hcons : Fin.cons (v 0) (Fin.tail v) = v := Fin.cons_self_tail v
    have hmain : p x (k + 1) v = (fderiv 𝕜 (fun y => p y k) x (v 0)) (Fin.tail v) := by
      rw [← hcons, hderiv.fderiv, ContinuousMultilinearMap.curryLeft_apply]
      simp [Fin.cons_zero]
    simpa [hmain] using hfderiv (v 0) (Fin.tail v)

lemma iteratedFDeriv_mem_submodule {S : Submodule 𝕜 F} (hS : IsClosed (S : Set F))
    {f : X → F} {x : X} {n : ℕ} (hf : ContDiff 𝕜 ω f) (hfS : ∀ y, f y ∈ S)
    (v : Fin n → X) : iteratedFDeriv 𝕜 n f x v ∈ S := by
  exact hasFTaylorSeriesUpTo_coe_mem hS hf.ftaylorSeries hfS n (by exact le_top) x v

lemma fpowerSeries_diag_eq_inv_factorial_smul_iteratedFDeriv [CharZero 𝕜]
    {f : X → F} {p : FormalMultilinearSeries 𝕜 X F} {x : X} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (hfa : AnalyticOn 𝕜 f Set.univ) (n : ℕ) (y : X) :
    p n (fun _ : Fin n => y) = ((Nat.factorial n : 𝕜)⁻¹) • iteratedFDeriv 𝕜 n f x
      (fun _ : Fin n => y) := by
  have h := HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum hp hfa (v := fun _ : Fin n => y)
  have hsum : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => y)) =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : 𝕜) • p n (fun _ : Fin n => y) := by
    rw [Finset.sum_const, Finset.card_univ]
    exact (Nat.cast_smul_eq_nsmul 𝕜 (Fintype.card (Equiv.Perm (Fin n)))
      (p n (fun _ : Fin n => y))).symm
  have hdiag : iteratedFDeriv 𝕜 n f x (fun _ : Fin n => y) =
      ((Fintype.card (Equiv.Perm (Fin n)) : ℕ) : 𝕜) • p n (fun _ : Fin n => y) := by
    rw [h, hsum]
  have hfact : (Fintype.card (Equiv.Perm (Fin n)) : ℕ) = Nat.factorial n := by
    simpa using (Fintype.card_perm (α := Fin n))
  rw [hfact] at hdiag
  calc
    p n (fun _ : Fin n => y) = ((Nat.factorial n : 𝕜)⁻¹) •
        ((Nat.factorial n : 𝕜) • p n (fun _ : Fin n => y)) := by
      rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))]
      simp
    _ = ((Nat.factorial n : 𝕜)⁻¹) • iteratedFDeriv 𝕜 n f x (fun _ : Fin n => y) := by
      rw [hdiag]

section real

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance mlNormSubmodule (S : Submodule ℝ F) (k : ℕ) :
    Norm (X [×k]→L[ℝ] S) := ⟨fun T =>
      ‖(S.subtypeₗᵢ : S →ₗᵢ[ℝ] F).toContinuousLinearMap.compContinuousMultilinearMap T‖⟩

lemma radius_le_radius_of_norm_le {G₁ G₂ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℝ G₂]
    {p : FormalMultilinearSeries ℝ X G₁} {q : FormalMultilinearSeries ℝ X G₂}
    (h : ∀ n, ‖q n‖ ≤ ‖p n‖) : p.radius ≤ q.radius := by
  rw [FormalMultilinearSeries.radius, FormalMultilinearSeries.radius]
  exact iSup_le fun r => iSup_le fun C => iSup_le fun hC =>
    le_iSup_of_le r <| le_iSup_of_le C <|
      le_iSup (f := fun _ : ∀ n, ‖q n‖ * (r : ℝ) ^ n ≤ C => (r : ℝ≥0∞))
        (fun n => (mul_le_mul_of_nonneg_right (h n) (pow_nonneg (by positivity) n)).trans (hC n))

lemma ftaylorSeries_norm_le {f : X → F} {p : FormalMultilinearSeries ℝ X F} {x : X} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (hfa : AnalyticOn ℝ f Set.univ) (n : ℕ) :
    ‖ftaylorSeries ℝ f x n‖ ≤ (Nat.factorial n : ℝ) * ‖p n‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (f := ftaylorSeries ℝ f x n) (M := (Nat.factorial n : ℝ) * ‖p n‖) (by positivity) ?_
  intro v
  calc
    ‖(ftaylorSeries ℝ f x n) v‖ = ‖iteratedFDeriv ℝ n f x v‖ := rfl
    _ = ‖∑ σ : Equiv.Perm (Fin n), p n (fun i => v (σ i))‖ := by
      rw [HasFPowerSeriesOnBall.iteratedFDeriv_eq_sum hp hfa]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i => v (σ i))‖ := norm_sum_le _ _
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i, ‖v i‖ := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        ‖p n (fun i => v (σ i))‖ ≤ ‖p n‖ * ∏ i, ‖v (σ i)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖p n‖ * ∏ i, ‖v i‖ := by
          simp [Equiv.prod_comp σ (fun i => ‖v i‖)]
    _ = (Nat.factorial n : ℝ) * (‖p n‖ * ∏ i, ‖v i‖) := by
      rw [Finset.sum_const, Finset.card_univ]
      norm_num [Fintype.card_perm (α := Fin n)]
    _ = (Nat.factorial n : ℝ) * ‖p n‖ * ∏ i, ‖v i‖ := by ring

lemma analyticOnNhd_codRestrict_real {S : Submodule ℝ F} (hS : IsClosed (S : Set F))
    {f : X → F} (hf : AnalyticOnNhd ℝ f Set.univ) (hfS : ∀ x, f x ∈ S) :
    AnalyticOnNhd ℝ (fun x => ⟨f x, hfS x⟩ : X → S) Set.univ := by
  intro x hx
  rcases hf x hx with ⟨p, r, hp⟩
  have hfa : AnalyticOn ℝ f Set.univ := hf.analyticOn
  have hft : HasFTaylorSeriesUpTo ω f (ftaylorSeries ℝ f) := hf.contDiff.ftaylorSeries
  have hmem : ∀ (n : ℕ) (v : Fin n → X), (ftaylorSeries ℝ f x n) v ∈ S := by
    intro n v
    exact hasFTaylorSeriesUpTo_coe_mem hS hft hfS n (by exact le_top) x v
  let q : FormalMultilinearSeries ℝ X S := fun n =>
    ((Nat.factorial n : ℝ)⁻¹ • (ftaylorSeries ℝ f x n).codRestrict S (hmem n))
  have hasSum : ∀ {y}, y ∈ Metric.eball (0 : X) r →
      HasSum (fun n : ℕ => q n (fun _ : Fin n => y)) (⟨f (x + y), hfS (x + y)⟩ : S) := by
    intro y hy
    have hqF : ∀ n : ℕ, ((q n (fun _ : Fin n => y) : S) : F) = p n (fun _ : Fin n => y) := by
      intro n
      have hrel : p n (fun _ : Fin n => y) =
          ((Nat.factorial n : ℝ)⁻¹) • iteratedFDeriv ℝ n f x (fun _ : Fin n => y) :=
        fpowerSeries_diag_eq_inv_factorial_smul_iteratedFDeriv (𝕜 := ℝ) hp hfa n y
      calc
        ((q n (fun _ : Fin n => y) : S) : F)
            = ((Nat.factorial n : ℝ)⁻¹) • (ftaylorSeries ℝ f x n) (fun _ : Fin n => y) := by
              rfl
        _ = ((Nat.factorial n : ℝ)⁻¹) • iteratedFDeriv ℝ n f x (fun _ : Fin n => y) := by
              rw [ftaylorSeries]
        _ = p n (fun _ : Fin n => y) := hrel.symm
    have hF : HasSum (fun n : ℕ => (q n (fun _ : Fin n => y) : F)) (f (x + y)) := by
      exact (tendsto_congr (fun s : Finset ℕ => by
        apply Finset.sum_congr rfl
        intro n hn
        exact hqF n)).mpr (hp.hasSum hy)
    change Tendsto (fun s : Finset ℕ => ∑ n ∈ s, q n (fun _ : Fin n => y))
      (SummationFilter.unconditional ℕ).filter (𝓝 (⟨f (x + y), hfS (x + y)⟩ : S))
    rw [tendsto_subtype_rng]
    simpa [HasSum] using hF
  have hqnorm : ∀ n, ‖q n‖ ≤ ‖p n‖ := by
    intro n
    have hincl : (S.subtypeₗᵢ : S →ₗᵢ[ℝ] F).toContinuousLinearMap.compContinuousMultilinearMap (q n)
        = (Nat.factorial n : ℝ)⁻¹ • (ftaylorSeries ℝ f x n) := by
      ext v
      rfl
    have hnorm : ‖(Nat.factorial n : ℝ)⁻¹‖ = (Nat.factorial n : ℝ)⁻¹ := by
      exact Real.norm_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ (Nat.factorial n : ℝ)))
    calc
      ‖q n‖ = ‖(S.subtypeₗᵢ : S →ₗᵢ[ℝ] F).toContinuousLinearMap.compContinuousMultilinearMap
        (q n)‖ := rfl
      _ = ‖(Nat.factorial n : ℝ)⁻¹ • (ftaylorSeries ℝ f x n)‖ := by rw [hincl]
      _ ≤ ‖(Nat.factorial n : ℝ)⁻¹‖ * ‖ftaylorSeries ℝ f x n‖ :=
        norm_smul_le (r := (Nat.factorial n : ℝ)⁻¹) (x := ftaylorSeries ℝ f x n)
      _ ≤ (Nat.factorial n : ℝ)⁻¹ * ((Nat.factorial n : ℝ) * ‖p n‖) := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left (ftaylorSeries_norm_le hp hfa n) (by positivity)
      _ = ‖p n‖ := by
        have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
        field_simp [hfac]
  have hrad : r ≤ q.radius := by
    exact (hp.r_le).trans (radius_le_radius_of_norm_le (p := p) (q := q) hqnorm)
  exact ⟨q, r, ⟨hrad, hp.r_pos, hasSum⟩⟩

def linearIsometryEquivRange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E →ₗᵢ[ℝ] F) : E ≃ₗᵢ[ℝ] e.toLinearMap.range where
  toFun := fun x => ⟨e x, LinearMap.mem_range_self (e : E →ₗ[ℝ] F) x⟩
  invFun := fun y => Classical.choose y.2
  left_inv := by
    intro x
    have hspec := Classical.choose_spec
      (show ∃ x' : E, (e : E →ₗ[ℝ] F) x' = e x from
        LinearMap.mem_range_self (e : E →ₗ[ℝ] F) x)
    exact e.injective hspec
  right_inv := by
    intro y
    ext
    exact Classical.choose_spec y.2
  map_add' := by
    intro x y
    ext
    simp [map_add]
  map_smul' := by
    intro c x
    ext
    simp [map_smul]
  norm_map' := by
    intro x
    simp [e.norm_map]

theorem contDiff_of_comp_linearIsometry_omega {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (e : E →ₗᵢ[ℝ] F) (he : IsClosed (Set.range e)) {g : X → E}
    (hg : ContDiff ℝ ω fun x => e (g x)) : ContDiff ℝ ω g := by
  rw [contDiff_omega_iff_analyticOnNhd] at hg ⊢
  intro x hx
  let S : Submodule ℝ F := e.toLinearMap.range
  have heS : IsClosed (S : Set F) := by
    simpa [S] using he
  have h₁ : AnalyticOnNhd ℝ (fun x : X => ⟨e (g x),
    LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x)⟩ : X → S)
      Set.univ := by
    exact analyticOnNhd_codRestrict_real heS hg (fun x =>
      LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x))
  let e₀ : E ≃ₗᵢ[ℝ] S := linearIsometryEquivRange e
  have h₂ : AnalyticAt ℝ (e₀.symm ∘ (fun x : X => ⟨e (g x),
    LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x)⟩ : X → S)) x := by
    have hlin : AnalyticOnNhd ℝ (e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap) Set.univ :=
      (e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap).analyticOnNhd Set.univ
    exact AnalyticAt.comp (hlin (⟨e (g x),
      LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x)⟩ : S) (by simp))
      (h₁ x hx)
  have hcongr : (fun x : X => e₀.symm (⟨e (g x),
    LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x)⟩ : S)) = g := by
    funext x
    exact (congrArg e₀.symm (by rfl : (⟨e (g x),
      LinearMap.mem_range_self (e : E →ₗ[ℝ] F) (g x)⟩ : S) = e₀ (g x))).trans
      (e₀.symm_apply_apply (g x))
  simpa [Function.comp_def, hcongr] using h₂

lemma isClosed_range_comp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ψ : E →ₗᵢ[ℝ] F) (hψ : IsClosed (Set.range ψ)) :
    IsClosed (Set.range (fun T : G →L[ℝ] E => ψ.toContinuousLinearMap.comp T)) := by
  let e₀ : E ≃ₗᵢ[ℝ] ψ.toLinearMap.range := linearIsometryEquivRange ψ
  have hmem : ∀ T' : G →L[ℝ] F,
    T' ∈ Set.range (fun T : G →L[ℝ] E => ψ.toContinuousLinearMap.comp T) ↔
      ∀ x, T' x ∈ Set.range ψ := by
    intro T'
    constructor
    · rintro ⟨T, rfl⟩ x
      exact ⟨T x, rfl⟩
    · intro hT'
      let T : G →L[ℝ] E :=
        (e₀.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
          (T'.codRestrict (ψ.toLinearMap.range) hT')
      refine ⟨T, ?_⟩
      ext x
      change ψ (e₀.symm ⟨T' x, hT' x⟩) = T' x
      exact congrArg Subtype.val (e₀.right_inv ⟨T' x, hT' x⟩)
  have hset : Set.range (fun T : G →L[ℝ] E => ψ.toContinuousLinearMap.comp T) =
      {T' | ∀ x, T' x ∈ Set.range ψ} := by
    ext T'
    exact hmem T'
  rw [hset]
  convert isClosed_iInter (fun x : G => hψ.preimage
    (show Continuous fun T' : G →L[ℝ] F => T' x from continuous_eval_const x)) using 1
  ext T'
  simp

end real


end AnalyticTransfer

end DifferentialGeometry

end
