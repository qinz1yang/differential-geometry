import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.TwoSided
import DifferentialGeometry.Topology.Manifold.SmoothApproximation.Hypersurface.LiftedStructure

/-!
# Smooth replacement of a compact one-sided `C^k` hypersurface (W-SUB, O2–O4)

Blueprint LFR47 (`master207A.tex:28975`, A:28994), design risk R7, external review of the finite
soul §8 (one-sided case), disposition D8, and the input shape frozen with lane D-CMS3: over the
unit-normal double cover `S̃` (a compact `C^n` manifold with the antipodal involution `σ`) the normal
exponential map `Φ̃ (v, h) = exp (h v)` is a `C^n` LOCAL diffeomorphism on `S̃ × (-ε, ε)`,
equivariant (`Φ̃ (σ v, -h) = Φ̃ (v, h)`) and injective modulo `τ (v, h) = (σ v, -h)`; the base `S`
is a `C^n` manifold with the double cover `π : S̃ → S` (`C^n` local diffeomorphism, fibres the
`σ`-orbits).

* `fibre_conditions_of_approx`: positive slope and end signs of a fibre function from `C⁰` and
  Lipschitz control (the real-variable step of the two-sided assembly).
* `exists_smooth_hypersurface_one_sided`: a compact smooth embedded slice `Ŝ ⊆ Φ̃ (S̃ × (-δ, δ))`,
  `Ŝ = {Φ̃ (v, h v)}` for a `C^n` ANTISYMMETRIC function `h` (`h ∘ σ = -h`, `|h| < δ`), and a `C^n`
  diffeomorphism `β : Ŝ ≃ S`, the normal projection (`β (Φ̃ (v, t)) = π v`).

Route (review §8): lift the smooth structure of `M` to `W = S̃ × (-ε, ε)` along `Φ̃` (O1,
`LiftedStructure.lean`); approximate the height by a smooth `f` on the lifted manifold (A) and
antisymmetrize, `f̂ = (f - f ∘ τ)/2` (`τ` is smooth there as a deck transformation); the fibre-root
kernel K2 on the lifted manifold gives a `τ`-invariant compact slice `Ẑ`, the graph of `h`; its
image `Ŝ = Φ̃ (Ẑ)` is an embedded slice of `M` (slice charts of `Ẑ` composed with the local inverse
branches of `Φ̃`; `Φ̃⁻¹ (Ŝ) ∩ W = Ẑ` by injectivity modulo `τ`), and the projection descends
equivariantly to `β`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Manifold TopologicalSpace
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology.Manifold.SmoothHypersurface

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Topology

/-- **Fibre conditions from approximation.** If `φ` is within `η` of the identity on `[-a, a]` and
`φ - id` is `η`-Lipschitz there (`η ≤ b < a`, `η < 1`), then `φ (-b) < 0 < φ b` and `φ' > 0` on
`(-a, a)`. -/
theorem fibre_conditions_of_approx {φ : ℝ → ℝ} {a b η : ℝ} (hb : 0 < b) (hba : b < a)
    (hηb : η ≤ b) (hη1 : η < 1) (hd : ∀ t ∈ Ioo (-a) a, DifferentiableAt ℝ φ t)
    (h0 : ∀ t ∈ Icc (-a) a, |φ t - t| < η)
    (h1 : ∀ t₁ ∈ Icc (-a) a, ∀ t₂ ∈ Icc (-a) a,
      |(φ t₂ - t₂) - (φ t₁ - t₁)| ≤ η * |t₂ - t₁|) :
    φ (-b) < 0 ∧ 0 < φ b ∧ ∀ t ∈ Ioo (-a) a, 0 < deriv φ t := by
  have hb' : b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
  have hnb' : -b ∈ Icc (-a) a := ⟨by linarith, by linarith⟩
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · have := (abs_lt.mp (h0 (-b) hnb')).2
    linarith
  · have := (abs_lt.mp (h0 b hb')).1
    linarith
  · have hslope : ∀ u ∈ Ioo (-a) a, ∀ v ∈ Ioo (-a) a, u ≤ v → (1 - η) * (v - u) ≤ φ v - φ u := by
      intro u hu v hv huv
      have h := h1 u (Ioo_subset_Icc_self hu) v (Ioo_subset_Icc_self hv)
      rw [abs_of_nonneg (sub_nonneg.mpr huv)] at h
      have h' := (abs_le.mp h).1
      nlinarith
    have := le_deriv_of_slope_le isOpen_Ioo hslope ht (hd t ht)
    linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [CompleteSpace ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {Sc : Type*} [TopologicalSpace Sc] [ChartedSpace HS Sc] [CompactSpace Sc]

/-- **Antisymmetric fibre-root hypersurface (O2–O3).** On a smooth manifold `N` with a `C^n` tube
`Ψ` over `Sc` and a smooth involution `τ` covering `(v, t) ↦ (σ v, -t)`, there is a compact smooth
embedded slice which is the graph of a `C^n` ANTISYMMETRIC function `h`, `|h| < δ`. -/
theorem exists_antisymmetric_fibreRoot_hypersurface {N : Type*} [TopologicalSpace N]
    [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N] {d : ℕ} (hdim : Module.finrank ℝ E = d + 1)
    {n : ℕ} (hn : 1 ≤ n) (Ψ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) I (Sc × ℝ) N n)
    {σ : Sc → Sc} (hσσ : ∀ v, σ (σ v) = v) {τ : N → N} (hτ : ContMDiff I I ∞ τ)
    {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) (hsrc : univ ×ˢ Ioo (-ε) ε ⊆ Ψ.source)
    (hτΨ : ∀ v, ∀ t ∈ Ioo (-ε) ε, τ (Ψ (v, t)) = Ψ (σ v, -t)) :
    ∃ Z : Set N, IsEmbeddedSlice I d Z ∧ IsCompact Z ∧
      ∃ h : Sc → ℝ, ContMDiff IS 𝓘(ℝ, ℝ) n h ∧ (∀ v, h (σ v) = -h v) ∧ (∀ v, |h v| < δ) ∧
        ∀ w, w ∈ Z ↔ ∃ v, Ψ (v, h v) = w := by
  have hn1 : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  set a := δ / 2 with ha
  set b := δ / 4 with hb
  set η := min (δ / 4) (1 / 2) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by norm_num)
  have hηb : η ≤ b := min_le_left _ _
  have hη1 : η < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hIoo : Ioo (-a) a ⊆ Ioo (-ε) ε := Ioo_subset_Ioo (by linarith) (by linarith)
  have hIcc : Icc (-a) a ⊆ Ioo (-ε) ε := Icc_subset_Ioo (by linarith) (by linarith)
  have hmem : ∀ v, ∀ t ∈ Ioo (-ε) ε, (v, t) ∈ Ψ.source := fun v t ht => hsrc ⟨mem_univ _, ht⟩
  -- the height and its approximation
  let g : N → ℝ := fun x => (Ψ.symm x).2
  have hg : ContMDiffOn I 𝓘(ℝ, ℝ) 1 g Ψ.target :=
    contMDiff_snd.comp_contMDiffOn (Ψ.contMDiffOn_invFun.of_le hn1)
  have hgΨ : ∀ v, ∀ t ∈ Ioo (-ε) ε, g (Ψ (v, t)) = t := by
    intro v t ht
    have hl : Ψ.symm.toPartialEquiv (Ψ.toPartialEquiv (v, t)) = (v, t) := Ψ.left_inv (hmem v t ht)
    change (Ψ.symm.toPartialEquiv (Ψ.toPartialEquiv (v, t))).2 = t
    rw [hl]
  have hΨ1 : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) I 1 Ψ (univ ×ˢ Ioo (-ε) ε) :=
    (Ψ.contMDiffOn_toFun.of_le hn1).mono hsrc
  obtain ⟨f, hf, hf0, hf1⟩ := exists_smooth_approx_fibre_lipschitz Ψ.open_target hg
    (a := a) (by linarith) hΨ1 (fun v t ht => Ψ.map_source (hmem v t (hIcc ht))) hηpos
  -- antisymmetrization
  let f' : N → ℝ := fun w => (f w - f (τ w)) / 2
  have hf' : ContMDiff I 𝓘(ℝ, ℝ) ∞ f' := (hf.sub (hf.comp hτ)).div_const _
  have hf'Ψ : ∀ v, ∀ t ∈ Ioo (-ε) ε,
      f' (Ψ (v, t)) - t = ((f (Ψ (v, t)) - g (Ψ (v, t))) -
        (f (Ψ (σ v, -t)) - g (Ψ (σ v, -t)))) / 2 := by
    intro v t ht
    have hnt : -t ∈ Ioo (-ε) ε := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [f', hτΨ v t ht, hgΨ v t ht, hgΨ (σ v) (-t) hnt]
    ring
  have hneg_mem : ∀ t ∈ Icc (-a) a, -t ∈ Icc (-a) a := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hf'Ψ1 : ContMDiffOn (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 1 (fun p => f' (Ψ p))
      (univ ×ˢ Ioo (-ε) ε) :=
    (hf'.of_le (by exact_mod_cast le_top)).comp_contMDiffOn hΨ1
  have hcond : ∀ v, f' (Ψ (v, -b)) < 0 ∧ 0 < f' (Ψ (v, b)) ∧
      ∀ t ∈ Ioo (-a) a, 0 < deriv (fun τ => f' (Ψ (v, τ))) t := by
    intro v
    refine fibre_conditions_of_approx (by positivity) (by linarith) hηb hη1
      (fun t ht => differentiableAt_fibre hf'Ψ1 v (hIoo ht)) (fun t ht => ?_)
      (fun t₁ ht₁ t₂ ht₂ => ?_)
    · rw [hf'Ψ v t (hIcc ht)]
      have h1 := hf0 v t ht
      have h2 := hf0 (σ v) (-t) (hneg_mem t ht)
      rw [abs_lt] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [hf'Ψ v t₂ (hIcc ht₂), hf'Ψ v t₁ (hIcc ht₁)]
      have h1 := hf1 v t₁ ht₁ t₂ ht₂
      have h2 := hf1 (σ v) (-t₁) (hneg_mem t₁ ht₁) (-t₂) (hneg_mem t₂ ht₂)
      have habs : |-t₂ - -t₁| = |t₂ - t₁| := by rw [← abs_neg]; ring_nf
      rw [habs] at h2
      rw [abs_le] at h1 h2 ⊢
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  obtain ⟨hZ, hc, -, hrest⟩ := exists_fibreRoot_hypersurface hdim hn Ψ (a := a) (b := b)
    (by positivity) (by linarith) (fun p hp => hsrc ⟨mem_univ _, hIoo hp.2⟩) hf'.contMDiffOn
    (fun v => (hcond v).1) (fun v => (hcond v).2.1) (fun v => (hcond v).2.2)
  let _ := embeddedSliceChartedSpace hZ
  obtain ⟨β, -, h, hh, hhb, hβs⟩ := hrest
  have hgraph : ∀ w, w ∈ fibreZeroSet Ψ a f' ↔ ∃ v, Ψ (v, h v) = w := by
    intro w
    constructor
    · intro hw
      refine ⟨β ⟨w, hw⟩, ?_⟩
      rw [← hβs, β.symm_apply_apply]
    · rintro ⟨v, rfl⟩
      rw [← hβs]
      exact (β.symm v).2
  have hha : ∀ v, h v ∈ Ioo (-a) a := fun v =>
    Ioo_subset_Ioo (by linarith) (by linarith) (hhb v)
  have hanti : ∀ v, h (σ v) = -h v := by
    intro v
    have hv := (hgraph _).mpr ⟨v, rfl⟩
    have hnh : -h v ∈ Ioo (-a) a := ⟨by linarith [(hha v).2], by linarith [(hha v).1]⟩
    have hw : Ψ (σ v, -h v) ∈ fibreZeroSet Ψ a f' := by
      refine ⟨mem_image_of_mem _ ⟨mem_univ _, hnh⟩, ?_⟩
      have h0 := hv.2
      have hτ1 := hτΨ v (h v) (hIoo (hha v))
      have hτ2 := hτΨ (σ v) (-h v) (hIoo hnh)
      rw [hσσ, neg_neg] at hτ2
      simp only [f'] at h0 ⊢
      rw [hτ2]
      rw [hτ1] at h0
      linarith
    obtain ⟨v', hv'⟩ := (hgraph _).mp hw
    have hinj := Ψ.injOn (hmem v' _ (hIoo (hha v'))) (hmem (σ v) _ (hIoo hnh)) hv'
    simp only [Prod.mk.injEq] at hinj
    rw [← hinj.1]
    exact hinj.2
  exact ⟨fibreZeroSet Ψ a f', hZ, hc, h, hh, hanti, fun v => abs_lt.mpr
    ⟨by linarith [(hhb v).1], by linarith [(hhb v).2]⟩, hgraph⟩

variable {ES' : Type*} [NormedAddCommGroup ES'] [NormedSpace ℝ ES']
  {HS' : Type*} [TopologicalSpace HS'] {IS' : ModelWithCorners ℝ ES' HS'}
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS' S]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **O: smooth replacement of a compact one-sided `C^k` hypersurface.** Over the unit-normal
double cover `Sc` with antipodal involution `σ`, let `Φ : Sc × ℝ → M` be a `C^n` local
diffeomorphism on `Sc × (-ε, ε)`, equivariant and injective modulo `(v, t) ↦ (σ v, -t)`, and let
`π : Sc → S` be the `C^n` double cover of the base. Then for every `0 < δ ≤ ε` there are a compact
smooth embedded slice `Ŝ ⊆ Φ (Sc × (-δ, δ))`, a `C^n` antisymmetric `h` with `Ŝ = {Φ (v, h v)}`, and
the `C^n` diffeomorphism `β : Ŝ ≃ S` given by the normal projection. -/
theorem exists_smooth_hypersurface_one_sided [T2Space Sc] {d : ℕ}
    (hdim : Module.finrank ℝ E = d + 1) {n : ℕ} (hn : 1 ≤ n) {Φ : Sc × ℝ → M} {σ : Sc → Sc}
    {π : Sc → S} {ε δ : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε)
    (hloc : IsLocalDiffeomorphOn (IS.prod 𝓘(ℝ, ℝ)) I n Φ (univ ×ˢ Ioo (-ε) ε))
    (hσ : Continuous σ) (hσσ : ∀ v, σ (σ v) = v) (hequiv : ∀ v t, Φ (σ v, -t) = Φ (v, t))
    (hinj : ∀ p ∈ univ ×ˢ Ioo (-ε) ε, ∀ q ∈ univ ×ˢ Ioo (-ε) ε, Φ p = Φ q →
      q = p ∨ q = (σ p.1, -p.2))
    (hπ : IsLocalDiffeomorph IS IS' n π) (hπs : Surjective π)
    (hπσ : ∀ v w, π v = π w ↔ w = v ∨ w = σ v) :
    ∃ Ŝ : Set M, ∃ hŜ : IsEmbeddedSlice I d Ŝ, IsCompact Ŝ ∧ Ŝ ⊆ Φ '' (univ ×ˢ Ioo (-δ) δ) ∧
      let _ := embeddedSliceChartedSpace hŜ
      ∃ β : Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS' Ŝ S n,
        ∃ h : Sc → ℝ, ContMDiff IS 𝓘(ℝ, ℝ) n h ∧ (∀ v, h (σ v) = -h v) ∧ (∀ v, |h v| < δ) ∧
          (∀ v, (β.symm (π v) : M) = Φ (v, h v)) ∧
          ∀ (x : Ŝ) (v : Sc) (t : ℝ), t ∈ Ioo (-ε) ε → Φ (v, t) = x → β x = π v := by
  classical
  have hε : 0 < ε := hδ.trans_le hδε
  have hnle : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  rcases isEmpty_or_nonempty Sc with hSc | ⟨⟨v₀⟩⟩
  · -- the empty cover
    have hS : IsEmpty S := ⟨fun s => isEmptyElim (Classical.choose (hπs s))⟩
    have hŜ : IsEmbeddedSlice I d (∅ : Set M) := fun x hx => absurd hx (notMem_empty x)
    refine ⟨∅, hŜ, isCompact_empty, empty_subset _, ?_⟩
    intro _
    refine ⟨{ toEquiv := Equiv.equivOfIsEmpty _ _
              contMDiff_toFun := fun x => isEmptyElim x
              contMDiff_invFun := fun s => isEmptyElim s }, fun v => isEmptyElim v,
      fun v => isEmptyElim v, fun v => isEmptyElim v, fun v => isEmptyElim v,
      fun v => isEmptyElim v, fun x => isEmptyElim x⟩
  -- the lifted manifold `W = Sc × (-ε, ε)`
  let W : Opens (Sc × ℝ) := ⟨univ ×ˢ Ioo (-ε) ε, isOpen_univ.prod isOpen_Ioo⟩
  have hF : IsLocalDiffeomorphOn (IS.prod 𝓘(ℝ, ℝ)) I n Φ W := hloc
  let _ : ChartedSpace H W := liftedChartedSpace hF
  have : IsManifold I ∞ W := lifted_isManifold hF
  have hWmem : ∀ v, ∀ t ∈ Ioo (-ε) ε, ((v, t) : Sc × ℝ) ∈ W := fun v t ht => ⟨mem_univ _, ht⟩
  let p₀ : W := ⟨(v₀, 0), hWmem v₀ 0 ⟨by linarith, hε⟩⟩
  let Ψ := liftedTube hF p₀
  have hΨval : ∀ v, ∀ t ∈ Ioo (-ε) ε, ((Ψ (v, t) : W) : Sc × ℝ) = (v, t) := fun v t ht =>
    liftedTube_apply hF p₀ (hWmem v t ht)
  have hnegmem : ∀ t ∈ Ioo (-ε) ε, -t ∈ Ioo (-ε) ε := fun t ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- the deck transformation
  let τ : W → W := fun w => ⟨(σ w.1.1, -w.1.2), hWmem _ _ (hnegmem _ w.2.2)⟩
  have hτc : Continuous τ :=
    ((hσ.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val).neg).subtype_mk _
  have hτ : ContMDiff I I ∞ τ := contMDiff_lifted_deck hF hτc (fun w => hequiv _ _)
  have hτΨ : ∀ v, ∀ t ∈ Ioo (-ε) ε, τ (Ψ (v, t)) = Ψ (σ v, -t) := by
    intro v t ht
    apply Subtype.ext
    change ((σ ((Ψ (v, t) : W) : Sc × ℝ).1, -((Ψ (v, t) : W) : Sc × ℝ).2) : Sc × ℝ) =
      ((Ψ (σ v, -t) : W) : Sc × ℝ)
    rw [hΨval v t ht, hΨval (σ v) (-t) (hnegmem t ht)]
  obtain ⟨Z, hZ, -, h, hh, hanti, hhδ, hgraph⟩ :=
    exists_antisymmetric_fibreRoot_hypersurface hdim hn Ψ hσσ hτ hδ hδε (fun p hp => hp) hτΨ
  have hhε : ∀ v, h v ∈ Ioo (-ε) ε := fun v =>
    ⟨by linarith [(abs_lt.mp (hhδ v)).1], by linarith [(abs_lt.mp (hhδ v)).2]⟩
  have hΨh : ∀ v, ((Ψ (v, h v) : W) : Sc × ℝ) = (v, h v) := fun v => hΨval v (h v) (hhε v)
  -- the hypersurface in `M`
  set Ŝ : Set M := range (fun v => Φ (v, h v)) with hŜdef
  have hkey : ∀ w : W, Φ w.1 ∈ Ŝ ↔ w ∈ Z := by
    intro w
    constructor
    · rintro ⟨v, hv⟩
      rcases hinj (v, h v) (hWmem v _ (hhε v)) w.1 w.2 hv with hw | hw
      · exact (hgraph w).mpr ⟨v, Subtype.ext ((hΨh v).trans hw.symm)⟩
      · refine (hgraph w).mpr ⟨σ v, Subtype.ext ?_⟩
        rw [hΨh (σ v), hw, hanti]
    · intro hw
      obtain ⟨v, rfl⟩ := (hgraph w).mp hw
      exact ⟨v, by rw [hΨh v]⟩
  have hOR : ∀ u w, π u = π w → Φ (u, h u) = Φ (w, h w) := by
    intro u w huw
    rcases (hπσ u w).mp huw with rfl | rfl
    · rfl
    · rw [hanti, hequiv]
  have hNP : ∀ (x : M) (u v : Sc) (t : ℝ), t ∈ Ioo (-ε) ε → Φ (v, t) = x →
      Φ (u, h u) = x → π u = π v := by
    intro x u v t ht hv hu
    rcases hinj (v, t) (hWmem v t ht) (u, h u) (hWmem u _ (hhε u)) (hv.trans hu.symm) with
      huv | huv
    · rw [show u = v from congrArg Prod.fst huv]
    · rw [show u = σ v from congrArg Prod.fst huv]
      exact ((hπσ v (σ v)).mpr (Or.inr rfl)).symm
  have hΦc : Continuous fun v => Φ (v, h v) :=
    continuous_iff_continuousAt.mpr fun v =>
      (contMDiffAt_of_isLocalDiffeomorphOn hF (hWmem v _ (hhε v))).continuousAt.comp
        (f := fun v => (v, h v)) (continuous_id.prodMk hh.continuous).continuousAt
  have hŜ : IsEmbeddedSlice I d Ŝ := by
    rintro x ⟨v, rfl⟩
    let z : W := Ψ (v, h v)
    have hzZ : z ∈ Z := (hgraph z).mpr ⟨v, rfl⟩
    obtain ⟨c, A, hfd, hzc, hdA, himage⟩ := hZ z hzZ
    let Θ : PartialDiffeomorph I I W M ∞ := liftedChartDiffeomorph hF z
    have hzΘ : z ∈ Θ.source := mem_liftedChart_source hF z
    have hΘz : Θ z = Φ (v, h v) := by
      rw [liftedChartDiffeomorph_apply, liftedChart_apply hF z hzΘ]
      exact congrArg Φ (hΨh v)
    refine ⟨Θ.symm.trans c, A, hfd, ⟨?_, ?_⟩, hdA, ?_⟩
    · change Φ (v, h v) ∈ Θ.target
      rw [← hΘz]
      exact Θ.map_source hzΘ
    · change Θ.symm.toPartialEquiv (Φ (v, h v)) ∈ c.source
      rw [← hΘz, show Θ.symm.toPartialEquiv (Θ.toPartialEquiv z) = z from Θ.left_inv hzΘ]
      exact hzc
    · intro y hy
      have hy1 : y ∈ Θ.target := hy.1
      have hy2 : Θ.symm.toPartialEquiv y ∈ c.source := hy.2
      change c.toPartialEquiv (Θ.symm.toPartialEquiv y) ∈ (A : Set E) ↔ y ∈ Ŝ
      rw [himage.apply_mem_iff hy2, ← hkey]
      have hy' : Φ (Θ.symm.toPartialEquiv y : W).1 = y := by
        have h1 := liftedChart_apply hF z (Θ.map_target hy1)
        have h2 : Θ.toPartialEquiv (Θ.symm.toPartialEquiv y) = y := Θ.right_inv hy1
        exact h1.symm.trans h2
      rw [hy']
  refine ⟨Ŝ, hŜ, isCompact_range hΦc, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨(v, h v), ⟨mem_univ _, abs_lt.mp (hhδ v)⟩, rfl⟩
  intro _
  -- the normal projection and its inverse
  have hxŜ : ∀ x : Ŝ, ∃ v, Φ (v, h v) = x.1 := fun x => x.2
  let vx : Ŝ → Sc := fun x => Classical.choose (hxŜ x)
  have hvx : ∀ x : Ŝ, Φ (vx x, h (vx x)) = x.1 := fun x => Classical.choose_spec (hxŜ x)
  let vs : S → Sc := fun s => Classical.choose (hπs s)
  have hvs : ∀ s, π (vs s) = s := fun s => Classical.choose_spec (hπs s)
  have hmemŜ : ∀ v, Φ (v, h v) ∈ Ŝ := fun v => ⟨v, rfl⟩
  have hNPb : ∀ (x : Ŝ) (v : Sc) (t : ℝ), t ∈ Ioo (-ε) ε → Φ (v, t) = x → π (vx x) = π v :=
    fun x v t ht hx => hNP x.1 (vx x) v t ht hx (hvx x)
  have hleft : ∀ x : Ŝ, (⟨Φ (vs (π (vx x)), h (vs (π (vx x)))), hmemŜ _⟩ : Ŝ) = x := fun x =>
    Subtype.ext ((hOR _ _ (hvs _)).trans (hvx x))
  have hright : ∀ s, π (vx ⟨Φ (vs s, h (vs s)), hmemŜ _⟩) = s := fun s =>
    (hNPb _ (vs s) (h (vs s)) (hhε _) rfl).trans (hvs s)
  have hval : ContMDiff 𝓘(ℝ, Fin d → ℝ) I ∞ (Subtype.val : Ŝ → M) :=
    embeddedSlice_inclusion_contMDiff hŜ
  have hbf : ContMDiff 𝓘(ℝ, Fin d → ℝ) IS' n (fun x : Ŝ => π (vx x)) := by
    intro x₀
    let z : W := Ψ (vx x₀, h (vx x₀))
    let Θ : PartialDiffeomorph I I W M ∞ := liftedChartDiffeomorph hF z
    have hzΘ : z ∈ Θ.source := mem_liftedChart_source hF z
    have hx₀Θ : x₀.1 ∈ Θ.target := by
      have hΘz : Θ z = x₀.1 := by
        rw [liftedChartDiffeomorph_apply, liftedChart_apply hF z hzΘ, ← hvx x₀]
        exact congrArg Φ (hΨh _)
      rw [← hΘz]
      exact Θ.map_source hzΘ
    have hloc_eq : (fun x : Ŝ => π (vx x)) =ᶠ[𝓝 x₀] fun x => π ((Θ.symm x.1 : W).1.1) := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
        (Θ.open_target.mem_nhds hx₀Θ)] with x hx
      have hw : Φ (Θ.symm x.1 : W).1 = x.1 := by
        have h1 := liftedChart_apply hF z (Θ.map_target hx)
        have h2 : Θ.toPartialEquiv (Θ.symm.toPartialEquiv x.1) = x.1 := Θ.right_inv hx
        exact h1.symm.trans h2
      exact hNPb x _ _ (Θ.symm x.1 : W).2.2 hw
    have h1 : ContMDiffAt I I ∞ Θ.symm x₀.1 :=
      Θ.contMDiffOn_invFun.contMDiffAt (Θ.open_target.mem_nhds hx₀Θ)
    have h2 : ContMDiff I (IS.prod 𝓘(ℝ, ℝ)) n (Subtype.val : W → Sc × ℝ) :=
      contMDiff_lifted_val hF
    have hcomp := hπ.contMDiff.contMDiffAt.comp x₀ (contMDiff_fst.contMDiffAt.comp x₀
      (h2.contMDiffAt.comp x₀ ((h1.of_le hnle).comp x₀ (hval.of_le hnle).contMDiffAt)))
    exact hcomp.congr_of_eventuallyEq hloc_eq
  have hgi : ContMDiff IS' I n (fun s => Φ (vs s, h (vs s))) := by
    intro s₀
    obtain ⟨P, hPs, hPeq⟩ := hπ (vs s₀)
    have hs₀P : s₀ ∈ P.target := by
      rw [← hvs s₀, hPeq hPs]
      exact P.map_source hPs
    have hloc_eq : (fun s => Φ (vs s, h (vs s))) =ᶠ[𝓝 s₀]
        fun s => Φ (P.symm s, h (P.symm s)) := by
      filter_upwards [P.open_target.mem_nhds hs₀P] with s hs
      apply hOR
      rw [hvs s]
      exact (P.right_inv hs).symm.trans (hPeq (P.map_target hs)).symm
    have hc1 : ContMDiffAt IS' IS n P.symm s₀ :=
      P.contMDiffOn_invFun.contMDiffAt (P.open_target.mem_nhds hs₀P)
    have hc2 : ContMDiffAt IS (IS.prod 𝓘(ℝ, ℝ)) n (fun u => (u, h u)) (P.symm s₀) :=
      contMDiffAt_id.prodMk hh.contMDiffAt
    have hc3 : ContMDiffAt (IS.prod 𝓘(ℝ, ℝ)) I n Φ (P.symm s₀, h (P.symm s₀)) :=
      contMDiffAt_of_isLocalDiffeomorphOn hF (hWmem _ _ (hhε _))
    exact (hc3.comp s₀ (hc2.comp s₀ hc1)).congr_of_eventuallyEq hloc_eq
  let β : Diffeomorph 𝓘(ℝ, Fin d → ℝ) IS' Ŝ S n :=
    { toFun := fun x => π (vx x)
      invFun := fun s => ⟨Φ (vs s, h (vs s)), hmemŜ _⟩
      left_inv := hleft
      right_inv := hright
      contMDiff_toFun := hbf
      contMDiff_invFun := embeddedSlice_contMDiff_corestrict hŜ (n := (n : ℕ∞)) _ hgi
        (fun s => hmemŜ _) }
  exact ⟨β, h, hh, hanti, hhδ, fun v => hOR _ _ (hvs _), hNPb⟩

end DifferentialGeometry.Topology.Manifold.SmoothHypersurface
