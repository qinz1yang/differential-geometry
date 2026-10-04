import DifferentialGeometry.Topology.Manifold.Embedding.CompactRetraction
import DifferentialGeometry.Analysis.Calculus.SmoothApproximation.FiniteSupported
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Basic
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import DifferentialGeometry.Analysis.Calculus.Cutoff.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth approximation with Lipschitz control along a `C¹` family of curves (W-SUB, A)

The "C¹ control" of the external review of the finite soul (§8) for the smooth replacement of a
compact `C^k` hypersurface (blueprint LFR47, design risk R7). Let `Ψ : S × ℝ → M` be `C¹` on
`S × (-c, c)` with `S` a compact `C¹` manifold (the fibres `τ ↦ Ψ (s, τ)` are the normal lines of
a tube), and let `g` be `C¹` on an open `U ⊇ Ψ (S × [-a, a])`, `a < c`.

* `differentiableAt_fibre`, `exists_bound_deriv_fibre`: the fibre curves of a `C¹` map
  `S × ℝ → F` into a normed space are differentiable, with derivative bounded uniformly on
  `S × [-a, a]` (chart-local bound and compactness).
* `exists_smooth_approx_fibre_lipschitz`: for every `η > 0` there is a globally smooth `f : M → ℝ`
  with `|f - g| < η` on `Ψ (S × [-a, a])` and `f - g` `η`-Lipschitz along every fibre on `[-a, a]`.

Route: a smooth embedding `e` into `ℝ^m` with a smooth retraction `r` near the compact set
(`exists_contMDiff_embedding_retraction_near_isCompact`); the `C¹` function `χ · (g ∘ r)` on `ℝ^m`
(cutoff `χ = 1` near `e (Ψ (S × [-a, a]))`) is mollified with uniform `C¹` convergence; `f = g_j ∘ e`.
Along a fibre, `f - g = (g_j - χ · (g ∘ r)) ∘ (e ∘ Ψ (s, ·))`, so the mean value theorem and the
uniform bound on `∂_t (e ∘ Ψ)` give the Lipschitz estimate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.CheegerGromovCompactness

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS}
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The fibre curves of a `C¹` map on `S × (-c, c)` are differentiable. -/
theorem differentiableAt_fibre {Ψ : S × ℝ → F} {c : ℝ}
    (hΨ : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) 1 Ψ (univ ×ˢ Ioo (-c) c)) (s : S) {t : ℝ}
    (ht : t ∈ Ioo (-c) c) : DifferentiableAt ℝ (fun τ => Ψ (s, τ)) t := by
  have h1 : ContMDiffAt (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) 1 Ψ (s, t) :=
    hΨ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ht⟩)
  have h2 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, F) 1 (fun τ => Ψ (s, τ)) t :=
    h1.comp t (contMDiffAt_const.prodMk contMDiffAt_id)
  exact (contMDiffAt_iff_contDiffAt.mp h2).differentiableAt (by simp)

/-- The chart representation `(u, τ) ↦ Ψ (φ⁻¹ u, τ)` of a `C^n` map on `S × ℝ` is `C^n`. -/
theorem contDiffAt_chartRep_prod [IS.Boundaryless] {n : ℕ∞} {Ψ : S × ℝ → F} {s₀ : S} {t₀ : ℝ}
    (hΨ : ContMDiffAt (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) n Ψ (s₀, t₀)) :
    ContDiffAt ℝ n (fun q : ES × ℝ => Ψ ((extChartAt IS s₀).symm q.1, q.2))
      (extChartAt IS s₀ s₀, t₀) := by
  have h2 := (contMDiffAt_iff.mp hΨ).2
  simp only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.prod_symm,
    PartialEquiv.refl_symm, ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h2
  exact h2

/-- **Uniform bound on the fibre derivative** of a `C¹` map `S × (-c, c) → F` over `S × [-a, a]`,
`S` compact. -/
theorem exists_bound_deriv_fibre [IS.Boundaryless] [CompactSpace S]
    {Ψ : S × ℝ → F} {a c : ℝ} (hac : a < c)
    (hΨ : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) 1 Ψ (univ ×ˢ Ioo (-c) c)) :
    ∃ B, ∀ s, ∀ t ∈ Icc (-a) a, ‖deriv (fun τ => Ψ (s, τ)) t‖ ≤ B := by
  let D : S × ℝ → F := fun p => deriv (fun τ => Ψ (p.1, τ)) p.2
  have hK : IsCompact (univ ×ˢ Icc (-a) a : Set (S × ℝ)) := isCompact_univ.prod isCompact_Icc
  have key : ∃ B, ∀ p ∈ (univ ×ˢ Icc (-a) a : Set (S × ℝ)), ‖D p‖ ≤ B := by
    refine hK.induction_on (p := fun A => ∃ B, ∀ p ∈ A, ‖D p‖ ≤ B) ⟨0, by simp⟩
      (fun A A' hAA' ⟨B, hB⟩ => ⟨B, fun p hp => hB p (hAA' hp)⟩)
      (fun A A' ⟨B, hB⟩ ⟨B', hB'⟩ => ⟨max B B', fun p hp => hp.elim
        (fun h => (hB p h).trans (le_max_left _ _)) (fun h => (hB' p h).trans (le_max_right _ _))⟩)
      ?_
    rintro ⟨s₀, t₀⟩ ⟨-, ht₀⟩
    have ht₀c : t₀ ∈ Ioo (-c) c := ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
    have hat : ContMDiffAt (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) 1 Ψ (s₀, t₀) :=
      hΨ.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ht₀c⟩)
    set φ := extChartAt IS s₀ with hφ
    let R : ES × ℝ → F := fun q => Ψ (φ.symm q.1, q.2)
    have hR : ContDiffAt ℝ 1 R (φ s₀, t₀) := contDiffAt_chartRep_prod hat
    set B₀ := ‖fderiv ℝ R (φ s₀, t₀)‖ + 1 with hB₀
    have hcont : ∀ᶠ q in 𝓝 (φ s₀, t₀), ‖fderiv ℝ R q‖ < B₀ :=
      (hR.continuousAt_fderiv (by simp)).norm.eventually (gt_mem_nhds (by linarith))
    have hdiff : ∀ᶠ q in 𝓝 (φ s₀, t₀), DifferentiableAt ℝ R q :=
      (hR.eventually (by simp)).mono fun q hq => hq.differentiableAt (by simp)
    have hχ : Tendsto (fun p : S × ℝ => (φ p.1, p.2)) (𝓝 (s₀, t₀)) (𝓝 (φ s₀, t₀)) :=
      (ContinuousAt.comp (g := φ) (f := Prod.fst) (x := ((s₀, t₀) : S × ℝ))
        (continuousAt_extChartAt (I := IS) s₀) continuousAt_fst).prodMk continuousAt_snd
    have hsrc : ∀ᶠ p : S × ℝ in 𝓝 (s₀, t₀), p.1 ∈ φ.source :=
      continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds (I := IS) s₀)
    refine ⟨{p | ‖fderiv ℝ R (φ p.1, p.2)‖ < B₀ ∧ DifferentiableAt ℝ R (φ p.1, p.2) ∧
        p.1 ∈ φ.source}, mem_nhdsWithin_of_mem_nhds ((hχ.eventually hcont).and
        ((hχ.eventually hdiff).and hsrc)), B₀ * ‖((0 : ES), (1 : ℝ))‖, ?_⟩
    rintro ⟨s, t⟩ ⟨h1, h2, h3⟩
    have hss : φ.symm (φ s) = s := φ.left_inv h3
    have hfib : (fun τ => Ψ (s, τ)) = fun τ => R (φ s, τ) := by
      funext τ
      simp only [R, hss]
    have hγ : HasDerivAt (fun τ : ℝ => (φ s, τ)) ((0 : ES), (1 : ℝ)) t :=
      (hasDerivAt_const t (φ s)).prodMk (hasDerivAt_id t)
    have hder : HasDerivAt (fun τ => Ψ (s, τ)) (fderiv ℝ R (φ s, t) ((0 : ES), (1 : ℝ))) t := by
      rw [hfib]
      exact h2.hasFDerivAt.comp_hasDerivAt t hγ
    change ‖deriv (fun τ => Ψ (s, τ)) t‖ ≤ B₀ * ‖((0 : ES), (1 : ℝ))‖
    rw [hder.deriv]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right h1.le (norm_nonneg _))
  obtain ⟨B, hB⟩ := key
  exact ⟨B, fun s t ht => hB (s, t) ⟨mem_univ _, ht⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

/-- **A: smooth approximation with `C⁰` control and Lipschitz control along the fibres.** -/
theorem exists_smooth_approx_fibre_lipschitz [IS.Boundaryless] [CompactSpace S] {g : M → ℝ} {U : Set M} (hU : IsOpen U) (hg : ContMDiffOn I 𝓘(ℝ, ℝ) 1 g U)
    {Ψ : S × ℝ → M} {a c : ℝ} (hac : a < c)
    (hΨ : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) I 1 Ψ (univ ×ˢ Ioo (-c) c))
    (hΨU : ∀ s, ∀ t ∈ Icc (-a) a, Ψ (s, t) ∈ U) {η : ℝ} (hη : 0 < η) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ s, ∀ t ∈ Icc (-a) a, |f (Ψ (s, t)) - g (Ψ (s, t))| < η) ∧
      ∀ s, ∀ t₁ ∈ Icc (-a) a, ∀ t₂ ∈ Icc (-a) a,
        |(f (Ψ (s, t₂)) - g (Ψ (s, t₂))) - (f (Ψ (s, t₁)) - g (Ψ (s, t₁)))| ≤ η * |t₂ - t₁| := by
  classical
  have hIcc : Icc (-a) a ⊆ Ioo (-c) c := Icc_subset_Ioo (by linarith) hac
  set K := Ψ '' (univ ×ˢ Icc (-a) a) with hKdef
  have hKc : IsCompact K := (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
    (hΨ.continuousOn.mono (prod_mono subset_rfl hIcc))
  have hmemK : ∀ s, ∀ t ∈ Icc (-a) a, Ψ (s, t) ∈ K := fun s t ht =>
    mem_image_of_mem _ ⟨mem_univ _, ht⟩
  have hKU : K ⊆ U := by
    rintro _ ⟨⟨s, t⟩, ⟨-, ht⟩, rfl⟩
    exact hΨU s t ht
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨fun _ => 0, contMDiff_const, fun s t ht => ?_, fun s t₁ ht₁ => ?_⟩
    · have := hmemK s t ht
      rw [hKe] at this
      exact absurd this (notMem_empty _)
    · have := hmemK s t₁ ht₁
      rw [hKe] at this
      exact absurd this (notMem_empty _)
  obtain ⟨N, m, e, r, V, hKN, he, -, -, -, hV, heV, hr, hre⟩ :=
    DifferentialGeometry.Geometry.exists_contMDiff_embedding_retraction_near_isCompact
      (I := I) hKc hKne
  -- `g ∘ r` is `C¹` on an open set around `e (K)`
  set V' := V ∩ r ⁻¹' U with hV'def
  have hV' : IsOpen V' := hr.continuousOn.isOpen_inter_preimage hV hU
  have heKV' : e '' K ⊆ V' := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨heV ⟨p, hKN hp, rfl⟩, ?_⟩
    change r (e p) ∈ U
    rw [hre p (hKN hp)]
    exact hKU hp
  have hgr : ContDiffOn ℝ 1 (fun z => g (r z)) V' := by
    have h1 : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℝ) 1 (g ∘ r) V' :=
      hg.comp ((hr.mono inter_subset_left).of_le (by exact_mod_cast le_top)) (fun z hz => hz.2)
    exact contMDiffOn_iff_contDiffOn.mp h1
  obtain ⟨χ, hχ, hχc, hχone, hχU, -⟩ :=
    DifferentialGeometry.Analysis.exists_bump_compact (hKc.image he.continuous) hV' heKV'
  obtain ⟨O1, hO1, hKO1, hO1one⟩ := mem_nhdsSet_iff_exists.mp hχone
  set G : EuclideanSpace ℝ (Fin m) → ℝ := fun z => χ z • g (r z) with hGdef
  have hG : ContDiff ℝ ((1 : ℕ) : ℕ∞ω) G := by
    apply contDiffOn_univ.mp
    exact DifferentialGeometry.Analysis.contDiffOn_cutoff_smul hV'
      (hχ.of_le (by exact_mod_cast le_top)) hχU
      (by rw [Nat.cast_one]; simpa only [univ_inter] using hgr)
  have hGc : HasCompactSupport G := hχc.smul_right
  have hGe : ∀ p ∈ K, G (e p) = g p := by
    intro p hp
    have h1 : χ (e p) = 1 := by simpa using hO1one (hKO1 ⟨p, hp, rfl⟩)
    simp only [hGdef, h1, one_smul, hre p (hKN hp)]
  obtain ⟨-, -, -, -, gs, hgs, -, hconv⟩ :=
    DifferentialGeometry.Analysis.exists_smooth_approx_supported_in_open_of_contDiff 1 hG hGc
      isOpen_univ (subset_univ _)
  have hgs1 : ∀ j, ContDiff ℝ (((1 : ℕ) : ℕ∞) : WithTop ℕ∞) (gs j) := fun j =>
    (hgs j).of_le (by exact_mod_cast le_top)
  have hGconv : MapCPConvergenceOn univ 1 gs G :=
    mapCPConvergenceOn_of_tendstoUniformly hgs1 hG fun j hj => (hconv j hj).tendstoUniformlyOn
  -- the uniform bound on the fibre derivative of `e ∘ Ψ`
  have hΨe : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1
      (fun p => e (Ψ p)) (univ ×ˢ Ioo (-c) c) :=
    (he.of_le (by exact_mod_cast le_top)).comp_contMDiffOn hΨ
  obtain ⟨B, hB⟩ := exists_bound_deriv_fibre hac hΨe
  set B' := max B 0 + 1 with hB'def
  have hB'pos : 0 < B' := by positivity
  set ε := min (η / 2) (η / B') with hεdef
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hεη : ε < η := (min_le_left _ _).trans_lt (by linarith)
  have hεB : ε * B' ≤ η := by
    calc ε * B' ≤ η / B' * B' := mul_le_mul_of_nonneg_right (min_le_right _ _) hB'pos.le
      _ = η := div_mul_cancel₀ η hB'pos.ne'
  obtain ⟨k0, hk0⟩ := hGconv ε hεpos
  set D : EuclideanSpace ℝ (Fin m) → ℝ := fun z => gs k0 z - G z with hDdef
  have hD0 : ∀ z, |D z| ≤ ε := by
    intro z
    have h := hk0 k0 le_rfl 0 (Nat.zero_le _) z (mem_univ _)
    unfold mapDerivNorm at h
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hD1 : ∀ z, ‖fderiv ℝ D z‖ ≤ ε := by
    intro z
    have h := hk0 k0 le_rfl 1 le_rfl z (mem_univ _)
    unfold mapDerivNorm at h
    rwa [norm_iteratedFDeriv_one] at h
  have hDd : Differentiable ℝ D :=
    ((hgs1 k0).sub hG).differentiable (by simp)
  have hfib : ∀ s, ∀ t ∈ Icc (-a) a, gs k0 (e (Ψ (s, t))) - g (Ψ (s, t)) = D (e (Ψ (s, t))) := by
    intro s t ht
    simp only [hDdef, hGe _ (hmemK s t ht)]
  refine ⟨fun p => gs k0 (e p), (hgs k0).contMDiff.comp he, fun s t ht => ?_, ?_⟩
  · rw [hfib s t ht]
    exact (hD0 _).trans_lt hεη
  intro s t₁ ht₁ t₂ ht₂
  rw [hfib s t₁ ht₁, hfib s t₂ ht₂]
  have hγd : ∀ τ ∈ Icc (-a) a, DifferentiableAt ℝ (fun τ => e (Ψ (s, τ))) τ := fun τ hτ =>
    differentiableAt_fibre hΨe s (hIcc hτ)
  have hφd : ∀ τ ∈ Icc (-a) a, DifferentiableAt ℝ (fun τ => D (e (Ψ (s, τ)))) τ := fun τ hτ =>
    (hDd _).comp τ (hγd τ hτ)
  have hφb : ∀ τ ∈ Icc (-a) a, ‖deriv (fun τ => D (e (Ψ (s, τ)))) τ‖ ≤ ε * B' := by
    intro τ hτ
    have hder0 := (hDd (e (Ψ (s, τ)))).hasFDerivAt.comp_hasDerivAt τ (hγd τ hτ).hasDerivAt
    have hder : HasDerivAt (fun τ => D (e (Ψ (s, τ))))
        (fderiv ℝ D (e (Ψ (s, τ))) (deriv (fun τ => e (Ψ (s, τ))) τ)) τ := hder0
    rw [hder.deriv]
    refine (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hD1 _) ?_ (norm_nonneg _)
      hεpos.le)
    exact (hB s τ hτ).trans ((le_max_left B 0).trans (by linarith))
  have hmvt := (convex_Icc (-a) a).norm_image_sub_le_of_norm_deriv_le hφd hφb ht₁ ht₂
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
  exact hmvt.trans (mul_le_mul_of_nonneg_right hεB (abs_nonneg _))

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
