import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1ModelProfile
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.ManifoldDerivative
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph

/-!
# Chapter-14 assembly, item L1, group G3a: fibrewise radial maps of `ℝ² × ℝ`

The pieces of the model cycle are fibrewise radial maps `(z, u) ↦ (m (z, u) • z, c + σ u)` of
`ℝ² × ℝ` with a radial ratio `m` (depending on `z` only through `‖z‖`). Such a map has an injective
differential at `(z, u)` as soon as `m (z, u) ≠ 0` and the radial profile `t ↦ t * m (t • z, u)`
has nonzero derivative at `t = 1` (`injective_fderiv_modelRadialMap`); the graph maps
`(z, t) ↦ (z, φ (z, t))` have an injective differential when `∂φ/∂t ≠ 0`
(`injective_fderiv_modelGraphMap`). An injective differential of a self-map of a finite-dimensional
space is invertible (`isInvertible_of_injective`), which with injectivity gives partial
diffeomorphisms (`exists_partialDiffeomorph_of_contDiffOn`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff Topology Manifold InnerProductSpace

namespace GC.GraphManifold.Assembly

/-- The plane of the radial maps. -/
abbrev ModelPlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The space of the radial maps. -/
abbrev ModelSpace : Type := ModelPlane × ℝ

/-- A fibrewise radial map. -/
def modelRadialMap (m : ModelSpace → ℝ) (c σ : ℝ) (y : ModelSpace) : ModelSpace :=
  (m y • y.1, c + σ * y.2)

/-- A graph map. -/
def modelGraphMap (φ : ModelSpace → ℝ) (y : ModelSpace) : ModelSpace := (y.1, φ y)

theorem hasFDerivAt_modelRadialMap {m : ModelSpace → ℝ} {m' : ModelSpace →L[ℝ] ℝ} {p : ModelSpace}
    (hm : HasFDerivAt m m' p) (c σ : ℝ) :
    HasFDerivAt (modelRadialMap m c σ) ((m p • ContinuousLinearMap.fst ℝ ModelPlane ℝ +
      m'.smulRight p.1).prod (σ • ContinuousLinearMap.snd ℝ ModelPlane ℝ)) p := by
  have h1 : HasFDerivAt (fun y : ModelSpace => m y • y.1)
      (m p • ContinuousLinearMap.fst ℝ ModelPlane ℝ + m'.smulRight p.1) p :=
    hm.smul (hasFDerivAt_fst (p := p))
  have h2 : HasFDerivAt (fun y : ModelSpace => c + σ * y.2)
      (σ • ContinuousLinearMap.snd ℝ ModelPlane ℝ) p := by
    have := ((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).const_mul σ).const_add c
    exact this.congr_fderiv (by ext v <;> simp)
  exact h1.prodMk h2

/-- The derivative of a radial ratio vanishes in the directions orthogonal to the point. -/
theorem fderiv_radial_orth {m : ModelSpace → ℝ} {m' : ModelSpace →L[ℝ] ℝ} {p : ModelSpace}
    (hm : HasFDerivAt m m' p)
    (hrad : ∀ y y' : ModelSpace, ‖y.1‖ = ‖y'.1‖ → y.2 = y'.2 → m y = m y')
    {η : ModelPlane} (hη : ⟪η, p.1⟫_ℝ = 0) : m' (η, 0) = 0 := by
  have hline : ∀ a : ℝ, HasDerivAt (fun t : ℝ => ((p.1 + (a * t) • η, p.2) : ModelSpace))
      ((a • η, 0) : ModelSpace) 0 := by
    intro a
    have h1 : HasDerivAt (fun t : ℝ => p.1 + (a * t) • η) (a • η) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul a).smul_const η
      simpa using this.const_add p.1
    exact h1.prodMk (hasDerivAt_const 0 p.2)
  have hp : (p.1 + (1 * (0 : ℝ)) • η, p.2) = p := by simp
  have hd1 : HasDerivAt (fun t : ℝ => m (p.1 + (1 * t) • η, p.2)) (m' ((1 : ℝ) • η, 0)) 0 := by
    have hm1 : HasFDerivAt m m' (p.1 + (1 * (0 : ℝ)) • η, p.2) := by rw [hp]; exact hm
    exact hm1.comp_hasDerivAt (0 : ℝ) (hline 1)
  have hd2 : HasDerivAt (fun t : ℝ => m (p.1 + (-1 * t) • η, p.2)) (m' ((-1 : ℝ) • η, 0)) 0 := by
    have hp' : (p.1 + (-1 * (0 : ℝ)) • η, p.2) = p := by simp
    have hm1 : HasFDerivAt m m' (p.1 + (-1 * (0 : ℝ)) • η, p.2) := by rw [hp']; exact hm
    exact hm1.comp_hasDerivAt (0 : ℝ) (hline (-1))
  have heq : (fun t : ℝ => m (p.1 + (1 * t) • η, p.2)) =
      fun t : ℝ => m (p.1 + (-1 * t) • η, p.2) := by
    funext t
    apply hrad
    · simp only
      rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        real_inner_comm η p.1, hη]
      simp
    · rfl
  rw [heq] at hd1
  have := hd1.unique hd2
  have h2 : m' ((-1 : ℝ) • η, 0) = -m' (η, 0) := by
    rw [show (((-1 : ℝ) • η, (0 : ℝ)) : ModelSpace) = (-1 : ℝ) • ((η, 0) : ModelSpace) by simp,
      map_smul]
    simp
  rw [h2, one_smul] at this
  linarith

/-- **Injective differential of a fibrewise radial map.** -/
theorem injective_fderiv_modelRadialMap {m : ModelSpace → ℝ} {m' : ModelSpace →L[ℝ] ℝ}
    {p : ModelSpace} (hm : HasFDerivAt m m' p)
    (hrad : ∀ y y' : ModelSpace, ‖y.1‖ = ‖y'.1‖ → y.2 = y'.2 → m y = m y')
    (hm0 : m p ≠ 0) {c σ : ℝ} (hσ : σ ≠ 0)
    (hd : p.1 ≠ 0 → ∃ d, d ≠ 0 ∧ HasDerivAt (fun t : ℝ => t * m (t • p.1, p.2)) d 1) :
    Injective (fderiv ℝ (modelRadialMap m c σ) p) := by
  rw [(hasFDerivAt_modelRadialMap hm c σ).fderiv]
  set F' := (m p • ContinuousLinearMap.fst ℝ ModelPlane ℝ + m'.smulRight p.1).prod
    (σ • ContinuousLinearMap.snd ℝ ModelPlane ℝ) with hF'
  have hF'apply : ∀ δ : ModelSpace, F' δ = (m p • δ.1 + m' δ • p.1, σ * δ.2) := fun δ => rfl
  rw [← ContinuousLinearMap.coe_coe, injective_iff_map_eq_zero]
  rintro ⟨v, w⟩ hvw
  rw [ContinuousLinearMap.coe_coe, hF'apply, Prod.mk_eq_zero] at hvw
  obtain ⟨h1, h2⟩ := hvw
  have hw : w = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hσ
    · exact h
  subst hw
  -- `m p • v + m' (v, 0) • p.1 = 0`
  by_cases hz : p.1 = 0
  · rw [hz, smul_zero, add_zero] at h1
    have hv : v = 0 := (smul_eq_zero.mp h1).resolve_left hm0
    rw [hv]
    rfl
  · obtain ⟨d, hd0, hder⟩ := hd hz
    -- `d = m p + m' (p.1, 0)`
    have hpath : HasDerivAt (fun t : ℝ => ((t • p.1, p.2) : ModelSpace)) ((p.1, 0) : ModelSpace) 1 :=
      ((hasDerivAt_id (1 : ℝ)).smul_const p.1).prodMk (hasDerivAt_const 1 p.2) |>.congr_deriv
        (by simp)
    have hp1 : ((1 : ℝ) • p.1, p.2) = p := by simp
    have hmline : HasDerivAt (fun t : ℝ => m (t • p.1, p.2)) (m' (p.1, 0)) 1 := by
      have hm1 : HasFDerivAt m m' ((1 : ℝ) • p.1, p.2) := by rw [hp1]; exact hm
      exact hm1.comp_hasDerivAt (1 : ℝ) hpath
    have hprod := (hasDerivAt_id (1 : ℝ)).mul hmline
    simp only [id, one_mul, hp1] at hprod
    have hdval : d = m p + m' (p.1, 0) := by
      have := hder.unique (hprod.congr_deriv rfl)
      simpa [one_smul] using this
    -- decompose `v`
    set μ : ℝ := ⟪v, p.1⟫_ℝ / ‖p.1‖ ^ 2 with hμ
    set η : ModelPlane := v - μ • p.1 with hη
    have hz2 : ‖p.1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
    have hηorth : ⟪η, p.1⟫_ℝ = 0 := by
      rw [hη, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, hμ]
      simp only [RCLike.conj_to_real]
      field_simp
      ring
    have hm'η := fderiv_radial_orth hm hrad hηorth
    have hv : v = μ • p.1 + η := by rw [hη]; abel
    have hm'v : m' (v, 0) = μ * m' (p.1, 0) := by
      have : ((v, (0 : ℝ)) : ModelSpace) = μ • ((p.1, 0) : ModelSpace) + ((η, 0) : ModelSpace) := by
        rw [hv]
        simp
      rw [this, map_add, map_smul, hm'η, add_zero, smul_eq_mul]
    rw [hm'v, hv] at h1
    have h1' : (μ * d) • p.1 + m p • η = 0 := by
      rw [hdval, ← h1]
      simp only
      module
    have hinη := congrArg (fun x => ⟪x, η⟫_ℝ) h1'
    simp only [inner_add_left, inner_smul_left, inner_zero_left, RCLike.conj_to_real,
      real_inner_comm η p.1, hηorth, mul_zero, zero_add, real_inner_self_eq_norm_sq] at hinη
    have hηzero : η = 0 := by
      rcases mul_eq_zero.mp hinη with h | h
      · exact absurd h hm0
      · exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
    rw [hηzero, smul_zero, add_zero] at h1'
    have hμ0 : μ * d = 0 := (smul_eq_zero.mp h1').resolve_right hz
    have hμ' : μ = 0 := (mul_eq_zero.mp hμ0).resolve_right hd0
    rw [hv, hμ', hηzero, zero_smul, add_zero]
    rfl

theorem hasFDerivAt_modelGraphMap {φ : ModelSpace → ℝ} {φ' : ModelSpace →L[ℝ] ℝ} {p : ModelSpace}
    (hφ : HasFDerivAt φ φ' p) :
    HasFDerivAt (modelGraphMap φ) ((ContinuousLinearMap.fst ℝ ModelPlane ℝ).prod φ') p :=
  (hasFDerivAt_fst (p := p)).prodMk hφ

/-- **Injective differential of a graph map.** -/
theorem injective_fderiv_modelGraphMap {φ : ModelSpace → ℝ} {φ' : ModelSpace →L[ℝ] ℝ}
    {p : ModelSpace} (hφ : HasFDerivAt φ φ' p) (hφ0 : φ' (0, 1) ≠ 0) :
    Injective (fderiv ℝ (modelGraphMap φ) p) := by
  rw [(hasFDerivAt_modelGraphMap hφ).fderiv]
  rw [← ContinuousLinearMap.coe_coe, injective_iff_map_eq_zero]
  rintro ⟨v, w⟩ hvw
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.coe_fst', Prod.mk_eq_zero] at hvw
  obtain ⟨hv, hw⟩ := hvw
  subst hv
  have : ((0 : ModelPlane), w) = w • ((0, 1) : ModelSpace) := by simp
  rw [this, map_smul, smul_eq_mul] at hw
  rcases mul_eq_zero.mp hw with h | h
  · rw [h]
    rfl
  · exact absurd h hφ0

/-- An injective endomorphism of a finite-dimensional space is invertible. -/
theorem isInvertible_of_injective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {A : E →L[ℝ] E} (hA : Injective A) : A.IsInvertible := by
  have hAs : Surjective A := LinearMap.surjective_of_injective (f := (A : E →ₗ[ℝ] E)) hA
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hA)
    (LinearMap.range_eq_top.mpr hAs), rfl⟩

/-- A smooth map of an open set of a finite-dimensional space into itself with injective
differential is a local diffeomorphism there. -/
theorem isLocalDiffeomorphOn_of_injective_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : E → E} {S : Set E} (hS : IsOpen S)
    (hf : ContDiffOn ℝ ∞ f S) (hd : ∀ x ∈ S, Injective (fderiv ℝ f x)) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f S := by
  apply hf.contMDiffOn.isLocalDiffeomorphOn_of_isInvertible_mfderiv hS (by simp)
  intro x hx
  rw [mfderiv_eq_fderiv]
  exact isInvertible_of_injective (hd x hx)

end GC.GraphManifold.Assembly
