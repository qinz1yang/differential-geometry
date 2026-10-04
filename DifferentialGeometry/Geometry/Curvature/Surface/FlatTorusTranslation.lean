import DifferentialGeometry.Geometry.Curvature.Surface.FlatTorusDistance
import DifferentialGeometry.Geometry.Curvature.Surface.FlatQuotientShift
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.TranslationExclusion
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# FT2: translations of a flat `C^m` torus and LFR23's torus exclusion

For a surface `M` diffeomorphic to `ℝ²/ℤ²` (`Φ : AddCircle 1 × AddCircle 1 ≃ₘ M`) carrying a
flat `C^n` (`n ≥ 2`) metric whose distance is the Riemannian distance:

* `exists_periodic_cover_of_diffeomorph_addCircle_prod`: the cover `cov : E → M`,
  `cov z = Φ (↑(T z).1, ↑(T z).2)` (`T : E ≃L ℝ × ℝ`), is an onto smooth local diffeomorphism
  whose fibres are the orbits of `ℤ v₁ + ℤ v₂`;
* `exists_isometryEquiv_shift_segment_of_flat_torus` (the producer, route (ii)): a metric
  segment of length `2s` is shifted by `s` by an isometry of `M` (descent of a translation of the
  developed plane, `FlatQuotientShift.lean` + `FlatTorusDistance.lean`);
* `false_of_flat_torus_of_endpoint_interval`: LFR23's torus case — no endpoint interval model
  with `δ < 5/3` along a unit-speed segment of length `5` (W4-F7c's `false_of_translation_of_lt`);
  `false_of_nonneg_torus_of_endpoint_interval` takes `K ≥ 0` instead of `K = 0` (SF-B2's periodic
  Gauss–Bonnet gives flatness).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Metric
open scoped Manifold ContDiff Topology

namespace Bundle.ContMDiffRiemannianMetric

section Cover

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem injective_mfderiv_addCircle_comp (L : E →L[ℝ] ℝ) (y : E) :
    ∀ u u', mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y u' → L u = L u' := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y) :=
    AddCircle.contMDiff_coe.mdifferentiable (by simp) (L y)
  have hl : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y :=
    (L.contDiff (n := 1)).contMDiff.mdifferentiable (by simp) y
  have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => (L z : AddCircle (1 : ℝ))) y =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun t : ℝ => (t : AddCircle (1 : ℝ))) (L y)).comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y) :=
    mfderiv_comp (f := fun z => L z) (g := fun t : ℝ => (t : AddCircle (1 : ℝ))) y hc hl
  have hL : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun z => L z) y = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  intro u u' h
  rw [hcomp, hL] at h
  exact (AddCircle.bijective_mfderiv_coe (L y)).1 h

private theorem exists_int_of_coe_eq {a b : ℝ} (h : (a : AddCircle (1 : ℝ)) = b) :
    ∃ m : ℤ, b = a + m := by
  have e : ((b - a : ℝ) : AddCircle (1 : ℝ)) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp e
  exact ⟨m, by rw [zsmul_eq_mul, mul_one] at hm; linarith⟩

variable [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The periodic cover of a torus.** For `Φ : AddCircle 1 × AddCircle 1 ≃ₘ M` there is an onto
smooth local diffeomorphism `cov : E → M` periodic along a basis `(v₁, v₂)` whose fibres are
exactly the orbits of `ℤ v₁ + ℤ v₂`. -/
theorem exists_periodic_cover_of_diffeomorph_addCircle_prod (hE : Module.finrank ℝ E = 2)
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M) :
    ∃ (cov : E → M) (v₁ v₂ : E), IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov ∧ Surjective cov ∧
      LinearIndependent ℝ ![v₁, v₂] ∧ (∀ y, cov (y + v₁) = cov y) ∧
      (∀ y, cov (y + v₂) = cov y) ∧
      ∀ y y', cov y = cov y' → ∃ n₁ n₂ : ℤ, y' = y + (n₁ • v₁ + n₂ • v₂) := by
  let T : E ≃L[ℝ] ℝ × ℝ := ContinuousLinearEquiv.ofFinrankEq (by simp [hE])
  let L₁ : E →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (T : E →L[ℝ] ℝ × ℝ)
  let L₂ : E →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (T : E →L[ℝ] ℝ × ℝ)
  let pair : E → AddCircle (1 : ℝ) × AddCircle (1 : ℝ) := fun z =>
    ((((T z).1 : ℝ) : AddCircle (1 : ℝ)), (((T z).2 : ℝ) : AddCircle (1 : ℝ)))
  have h₁ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (((T z).1 : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp L₁.contDiff.contMDiff
  have h₂ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (fun z => (((T z).2 : ℝ) : AddCircle (1 : ℝ))) :=
    AddCircle.contMDiff_coe.comp L₂.contDiff.contMDiff
  have hpair : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞ pair := h₁.prodMk h₂
  let cov : E → M := fun z => Φ (pair z)
  have hcovs : ContMDiff 𝓘(ℝ, E) I ∞ cov := Φ.contMDiff.comp hpair
  have hpair_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) := by
    intro y u u' h
    rw [mfderiv_prodMk (h₁.mdifferentiableAt (by decide)) (h₂.mdifferentiableAt (by decide))]
      at h
    have e1 := injective_mfderiv_addCircle_comp L₁ y u u' (congrArg Prod.fst h)
    have e2 := injective_mfderiv_addCircle_comp L₂ y u u' (congrArg Prod.snd h)
    exact T.injective (Prod.ext e1 e2)
  have hcov_inj : ∀ y, Injective (mfderiv 𝓘(ℝ, E) I cov y) := by
    intro y
    have hcomp : mfderiv 𝓘(ℝ, E) I cov y =
        (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I Φ (pair y)).comp
          (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) pair y) :=
      mfderiv_comp (f := pair) (g := Φ) y (Φ.contMDiff.mdifferentiable (by decide) (pair y))
        (hpair.mdifferentiable (by decide) y)
    rw [hcomp, ContinuousLinearMap.coe_comp]
    exact ((Φ.mfderivToContinuousLinearEquiv (by decide) (pair y)).injective).comp
      (hpair_inj y)
  have hcov : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ cov :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv cov hcovs
      hcov_inj rfl
  have hsurj : Surjective cov := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := Φ.toEquiv.surjective x
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective b
    refine ⟨T.symm (s, t), ?_⟩
    simp only [cov, pair, ContinuousLinearEquiv.apply_symm_apply]
    exact hab
  have hT₁ : T (T.symm (1, 0)) = (1, 0) := T.apply_symm_apply _
  have hT₂ : T (T.symm (0, 1)) = (0, 1) := T.apply_symm_apply _
  have hli : LinearIndependent ℝ ![T.symm (1, 0), T.symm (0, 1)] := by
    refine LinearIndependent.pair_iff.mpr fun s t hst => ?_
    have h := congrArg T hst
    rw [map_add, map_smul, map_smul, hT₁, hT₂, map_zero] at h
    simp only [Prod.smul_mk, smul_eq_mul, mul_one, mul_zero, Prod.mk_add_mk, add_zero,
      zero_add, Prod.mk_eq_zero] at h
    exact h
  have hper₁ : ∀ y, cov (y + T.symm (1, 0)) = cov y := by
    intro y
    simp only [cov, pair, map_add, hT₁, Prod.fst_add, Prod.snd_add, add_zero,
      AddCircle.coe_add_period]
  have hper₂ : ∀ y, cov (y + T.symm (0, 1)) = cov y := by
    intro y
    simp only [cov, pair, map_add, hT₂, Prod.fst_add, Prod.snd_add, add_zero,
      AddCircle.coe_add_period]
  refine ⟨cov, T.symm (1, 0), T.symm (0, 1), hcov, hsurj, hli, hper₁, hper₂,
    fun y y' h => ?_⟩
  have hp : pair y = pair y' := Φ.injective h
  obtain ⟨n₁, hn₁⟩ := exists_int_of_coe_eq (congrArg Prod.fst hp)
  obtain ⟨n₂, hn₂⟩ := exists_int_of_coe_eq (congrArg Prod.snd hp)
  refine ⟨n₁, n₂, T.injective ?_⟩
  rw [map_add, map_add, map_zsmul, map_zsmul, hT₁, hT₂]
  refine Prod.ext ?_ ?_
  · simp [hn₁]
  · simp [hn₂]

end Cover

section Producer

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {n : ℕ∞ω}

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

/-- **FT2: the τ-producer on a flat `C^m` torus** (route (ii) of LFR23's torus exclusion). -/
theorem exists_isometryEquiv_shift_segment_of_flat_torus (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hflat : ∀ x v w, k.sectionalCurvature x v w = 0)
    {γ : ℝ → M} {s : ℝ} (hs : 0 ≤ s)
    (hγ : ∀ t ∈ Icc 0 (2 * s), ∀ t' ∈ Icc 0 (2 * s), dist (γ t) (γ t') = |t - t'|) :
    ∃ τ : M ≃ᵢ M, τ (γ 0) = γ s ∧ τ (γ s) = γ (2 * s) := by
  obtain ⟨cov, v₁, v₂, hcov, hsurj, hli, hper₁, hper₂, hfib⟩ :=
    exists_periodic_cover_of_diffeomorph_addCircle_prod hE Φ
  obtain ⟨Ψ, Λ, hΨs, hinv, hfibΨ, hle, hreal⟩ :=
    exists_developing_cover_of_flat hE k hn hnorm hcov hsurj hli hper₁ hper₂ hfib hflat
  exact DifferentialGeometry.Analysis.exists_isometryEquiv_shift_segment_of_quotient hΨs hinv
    hfibΨ hle hreal hs hγ

/-- **LFR23, torus case (flat form).** A flat `C^m` torus carries no endpoint interval model with
`δ < 5/3` along a unit-speed segment of length `5` from `z₀`. -/
theorem false_of_flat_torus_of_endpoint_interval (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hflat : ∀ x v w, k.sectionalCurvature x v w = 0)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hq0 : q z₀ = 0) (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ)
    (hδ : δ < 5 / 3) {γ : ℝ → M} (hγ0 : γ 0 = z₀)
    (hγ : ∀ t ∈ Icc 0 5, ∀ t' ∈ Icc 0 5, dist (γ t) (γ t') = |t - t'|) : False := by
  obtain ⟨τ, hτ0, hτs⟩ := exists_isometryEquiv_shift_segment_of_flat_torus (s := 5 / 2) hE k hn
    hnorm Φ hflat (γ := γ) (by norm_num) (by rw [show (2 : ℝ) * (5 / 2) = 5 by norm_num]; exact hγ)
  rw [hγ0] at hτ0
  rw [show (2 : ℝ) * (5 / 2) = 5 by norm_num] at hτs
  exact DifferentialGeometry.Geometry.Collapse.false_of_translation_of_lt hq0 hqnn hdist hδ hγ0
    hγ τ hτ0 hτs

/-- **LFR23, torus case (`K ≥ 0` form).** As `false_of_flat_torus_of_endpoint_interval`, with
nonnegative sectional curvature (flatness from SF-B2's periodic Gauss–Bonnet). -/
theorem false_of_nonneg_torus_of_endpoint_interval (hE : Module.finrank ℝ E = 2)
    (k : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hn : (2 : ℕ∞ω) ≤ n)
    (hnorm : ∀ x (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (√(k.inner x w w)))
    (Φ : (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₘ⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), I⟯ M)
    (hK : ∀ x v w, 0 ≤ k.sectionalCurvature x v w)
    {z₀ : M} {q : M → ℝ} {δ : ℝ} (hq0 : q z₀ = 0) (hqnn : ∀ y ∈ closedBall z₀ 10, 0 ≤ q y)
    (hdist : ∀ y ∈ closedBall z₀ 10, ∀ y' ∈ closedBall z₀ 10, |dist (q y) (q y') - dist y y'| ≤ δ)
    (hδ : δ < 5 / 3) {γ : ℝ → M} (hγ0 : γ 0 = z₀)
    (hγ : ∀ t ∈ Icc 0 5, ∀ t' ∈ Icc 0 5, dist (γ t) (γ t') = |t - t'|) : False :=
  false_of_flat_torus_of_endpoint_interval hE k hn hnorm Φ
    (sectionalCurvature_eq_zero_of_diffeomorph_addCircle_prod hE k hn Φ hK) hq0 hqnn hdist hδ
    hγ0 hγ

end Producer

end Bundle.ContMDiffRiemannianMetric
