import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.RegularSublevelIsotopy
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Stability of transverse preimages under a family of maps (blueprint LFR03, LC82)

Let `F : [0, 1] × M → E'` be a jointly `C^r` family of maps `f_t = F (t, ·)` into a
normed space and let `X = {φ = 0, β ≥ 0} ⊆ E'` with side boundary
`∂X = {φ = 0, β = 0}` (`φ : E' → G`, `β : E' → ℝ` smooth). If every `f_t` is transverse to `X` and
to `∂X` in the sense of the defining pair (`D (φ ∘ f_t)` surjective along `f_t⁻¹ X` and
`D ((φ, β) ∘ f_t)` surjective along `f_t⁻¹ ∂X`), and all preimages `f_t⁻¹ X` lie in one compact
set, then a compactly supported `C^{r-1}` isotopy of `M` carries `f_0⁻¹ X` onto `f_1⁻¹ X` and
`f_0⁻¹ ∂X` onto `f_1⁻¹ ∂X` (`lfr03_exists_isotopy_fibre`, statement S5 of
`build-logs/resume/sheet-W5-FLOW.md`), with support in any prescribed open neighbourhood of the
preimages. In the smooth case the isotopy is `C^∞` (`lc82_exists_smooth_isotopy_fibre`, S6).

The family is first reparametrised by `Real.smoothTransition`, which maps `ℝ` into `[0, 1]`, is
`0` on `(-∞, 0]` and `1` on `[1, ∞)`; this extends it to all times without a Seeley extension, and
transversality and the compact enclosure then hold at every time. Then the kernel
`exists_isotopy_regularSublevel_ENat` applies to `Ψ = φ ∘ F̂`, `B = β ∘ F̂`.

Deviations from the blueprint wording (both are strengthenings; the verbatim forms are kept as
`example`s at the end): LFR03 assumes `3 ≤ r`, here `2 ≤ r` suffices; LFR03 asks for the preimages
in `int Q`, here in `Q`. The representation of `X` by a global defining pair covers all
blueprint consumers (LFR20, LFR28, LC84, LC85; see the sheet).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M] [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- **Fibre stability at any order `n : ℕ∞`** (common core of S5 and S6). A family `F` that is
`C^m` on `[0, 1] × M` (`n + 1 ≤ m`, `1 ≤ n`), transverse to `X = {φ = 0, β ≥ 0}` and to
`∂X = {φ = 0, β = 0}` at all times `t ∈ [0, 1]`, with all preimages in a compact `Q` and in an open
`N`, is followed by a jointly `C^n` isotopy of `C^n` diffeomorphisms `Φ t`, `Φ 0 = id`, the
identity off a compact `K ⊆ N`, with `Φ t (f_0⁻¹ X) = f_{σ t}⁻¹ X`, `σ = Real.smoothTransition`,
and the same for `∂X`; in particular `Φ 1 (f_0⁻¹ X) = f_1⁻¹ X`. -/
theorem exists_isotopy_fibre_ENat {n : ℕ∞} (hn : 1 ≤ n) {m : WithTop ℕ∞}
    (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    {F : ℝ × M → E'} (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') m F (Icc 0 1 ×ˢ univ))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    {X Xb : Set E'} (hX : X = {y | φ y = 0 ∧ 0 ≤ β y}) (hXb : Xb = {y | φ y = 0 ∧ β y = 0})
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ Xb →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q) (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ Q)
    {N : Set M} (hN : IsOpen N) (hNsub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ N) :
    ∃ (K : Set M) (Φ : ℝ → M ≃ₘ^n⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I n (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M n ∧
      (∀ t x, x ∉ K → Φ t x = x) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ X} = {x | F (Real.smoothTransition t, x) ∈ X}) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ Xb} = {x | F (Real.smoothTransition t, x) ∈ Xb}) ∧
      Φ 1 '' {x | F (0, x) ∈ X} = {x | F (1, x) ∈ X} ∧
      Φ 1 '' {x | F (0, x) ∈ Xb} = {x | F (1, x) ∈ Xb} := by
  set σ : ℝ → ℝ := Real.smoothTransition with hσ
  have hσmem : ∀ t, σ t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  -- the working order `k = n + 1 ≤ ∞`
  set k : WithTop ℕ∞ := ((n + 1 : ℕ∞) : WithTop ℕ∞) with hkdef
  have hkn : k = (n : WithTop ℕ∞) + 1 := by
    rw [hkdef]
    norm_cast
  have hnk : (n : WithTop ℕ∞) + 1 ≤ k := hkn.ge
  have hktop : k ≤ ∞ := WithTop.coe_le_coe.2 le_top
  have hFk : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') k F (Icc 0 1 ×ˢ univ) :=
    hF.of_le (hkn.le.trans hmn)
  -- the reparametrised family, defined for all times
  have hg : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) k
      (fun q : ℝ × M => ((σ q.1, q.2) : ℝ × M)) :=
    ((Real.smoothTransition.contDiff (n := ⊤)).contMDiff.of_le hktop |>.comp
      contMDiff_fst).prodMk contMDiff_snd
  have hF' : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') k (fun q : ℝ × M => F (σ q.1, q.2)) :=
    hFk.comp_contMDiff hg (fun q => ⟨hσmem q.1, mem_univ _⟩)
  set Ψ : ℝ × M → G := fun q => φ (F (σ q.1, q.2)) with hΨdef
  set B : ℝ × M → ℝ := fun q => β (F (σ q.1, q.2)) with hBdef
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) k Ψ :=
    (hφ.contMDiff.of_le hktop).comp hF'
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) k B :=
    (hβ.contMDiff.of_le hktop).comp hF'
  -- fibres in terms of the defining pair
  have hfib : ∀ t : ℝ, {x | F (σ t, x) ∈ X} = {x | Ψ (t, x) = 0 ∧ 0 ≤ B (t, x)} := by
    intro t
    subst hX
    rfl
  have hfibb : ∀ t : ℝ, {x | F (σ t, x) ∈ Xb} = {x | Ψ (t, x) = 0 ∧ B (t, x) = 0} := by
    intro t
    subst hXb
    rfl
  have htrans' : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => Ψ (q.1, y)) q.2) := by
    intro q h1 h2
    exact htrans (σ q.1) (hσmem q.1) q.2 (by rw [hX]; exact ⟨h1, h2⟩)
  have htransb' : ∀ q : ℝ × M, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2) := by
    intro q h1 h2
    exact htransb (σ q.1) (hσmem q.1) q.2 (by rw [hXb]; exact ⟨h1, h2⟩)
  -- one compact set containing all the preimages
  have hXc : IsClosed X := by
    rw [hX]
    exact (isClosed_eq hφ.continuous continuous_const).inter
      (isClosed_le continuous_const hβ.continuous)
  set T : Set (ℝ × M) := (Icc (0 : ℝ) 1 ×ˢ univ) ∩ F ⁻¹' X with hTdef
  have hTc : IsClosed T :=
    hF.continuousOn.preimage_isClosed_of_isClosed (isClosed_Icc.prod isClosed_univ) hXc
  have hTsub : T ⊆ Icc (0 : ℝ) 1 ×ˢ Q := by
    rintro ⟨t, x⟩ ⟨⟨ht, -⟩, hx⟩
    exact ⟨ht, hencl t ht x hx⟩
  have hT : IsCompact T := (isCompact_Icc.prod hQ).of_isClosed_subset hTc hTsub
  have hS : IsCompact (Prod.snd '' T) := hT.image continuous_snd
  have hWS : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q → q.2 ∈ Prod.snd '' T := by
    intro q h1 h2
    refine ⟨(σ q.1, q.2), ⟨⟨hσmem q.1, mem_univ _⟩, ?_⟩, rfl⟩
    change F (σ q.1, q.2) ∈ X
    rw [hX]
    exact ⟨h1, h2⟩
  have hSN : Prod.snd '' T ⊆ N := by
    rintro _ ⟨⟨t, x⟩, ⟨⟨ht, -⟩, hx⟩, rfl⟩
    exact hNsub t ht x hx
  obtain ⟨K, Φ₀, hK, hKN, hΦ₀, hself, hoff, himg, himgb⟩ :=
    exists_isotopy_regularSublevel_ENat hn hnk hΨ hB htrans' htransb' hS hWS hN hSN
  have h0 : ∀ x : M, F (σ 0, x) = F (0, x) := fun x => by
    rw [hσ, Real.smoothTransition.zero]
  have h1 : ∀ x : M, F (σ 1, x) = F (1, x) := fun x => by
    rw [hσ, Real.smoothTransition.one]
  have himg' : ∀ t, Φ₀ 0 t '' {x | F (0, x) ∈ X} = {x | F (σ t, x) ∈ X} := by
    intro t
    have e : {x | F (0, x) ∈ X} = {x | F (σ 0, x) ∈ X} := by simp only [h0]
    rw [e, hfib, hfib]
    exact himg 0 t
  have himgb' : ∀ t, Φ₀ 0 t '' {x | F (0, x) ∈ Xb} = {x | F (σ t, x) ∈ Xb} := by
    intro t
    have e : {x | F (0, x) ∈ Xb} = {x | F (σ 0, x) ∈ Xb} := by simp only [h0]
    rw [e, hfibb, hfibb]
    exact himgb 0 t
  refine ⟨K, fun t => Φ₀ 0 t, hK, hKN,
    hΦ₀.comp ((contMDiff_const.prodMk contMDiff_fst).prodMk contMDiff_snd), hself 0,
    fun t x hx => hoff 0 t x hx, himg', himgb', ?_, ?_⟩
  · rw [himg' 1]
    simp only [h1]
  · rw [himgb' 1]
    simp only [h1]

/-- **LFR03 (statement S5 of W5-FLOW): transverse preimages under a `C^r` family are isotopic.**
Let `2 ≤ r` and let `F` be jointly `C^r` on `[0, 1] × M` with values in a normed space
`E'`; let `X = {φ = 0, β ≥ 0}` with side boundary `Xb = {φ = 0, β = 0}` for smooth `φ, β`.
If every `f_t = F (t, ·)` is transverse to `X` and to `Xb` (through the defining pair), all
preimages `f_t⁻¹ X` lie in a compact `Q` and in an open `N`, then there are a compact `K ⊆ N` and a
jointly `C^{r-1}` isotopy `Φ` of `C^{r-1}` diffeomorphisms with `Φ 0 = id`, `Φ t = id` off `K`,
`Φ t (f_0⁻¹ X) = f_{σ t}⁻¹ X` (`σ = Real.smoothTransition`), the same for `Xb`, and in particular
`Φ 1 (f_0⁻¹ X) = f_1⁻¹ X`, `Φ 1 (f_0⁻¹ Xb) = f_1⁻¹ Xb`. -/
theorem lfr03_exists_isotopy_fibre {r : ℕ} (hr : 2 ≤ r)
    {F : ℝ × M → E'} (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    {X Xb : Set E'} (hX : X = {y | φ y = 0 ∧ 0 ≤ β y}) (hXb : Xb = {y | φ y = 0 ∧ β y = 0})
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ Xb →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q) (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ Q)
    {N : Set M} (hN : IsOpen N) (hNsub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ N) :
    ∃ (K : Set M) (Φ : ℝ → M ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ((r - 1 : ℕ) : WithTop ℕ∞) (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M ((r - 1 : ℕ) : WithTop ℕ∞) ∧
      (∀ t x, x ∉ K → Φ t x = x) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ X} = {x | F (Real.smoothTransition t, x) ∈ X}) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ Xb} = {x | F (Real.smoothTransition t, x) ∈ Xb}) ∧
      Φ 1 '' {x | F (0, x) ∈ X} = {x | F (1, x) ∈ X} ∧
      Φ 1 '' {x | F (0, x) ∈ Xb} = {x | F (1, x) ∈ Xb} := by
  have hcast : (((r - 1 : ℕ) : ℕ∞) : WithTop ℕ∞) + 1 = (r : WithTop ℕ∞) := by
    have h : r - 1 + 1 = r := Nat.sub_add_cancel (by omega)
    exact_mod_cast congrArg (fun k : ℕ => (k : WithTop ℕ∞)) h
  exact exists_isotopy_fibre_ENat (n := ((r - 1 : ℕ) : ℕ∞)) (by exact_mod_cast (by omega : 1 ≤ r - 1))
    hcast.le hF hφ hβ hX hXb htrans htransb hQ hencl hN hNsub

/-- **LC82 (statement S6 of W5-FLOW): transverse preimages under a smooth family are smoothly
isotopic.** For a family `F` that is `C^∞` on `[0, 1] × M`, transverse to `X = {φ = 0, β ≥ 0}` and
to `Xb = {φ = 0, β = 0}` at all times, with all preimages in a compact `Q`, there is a compactly
supported jointly `C^∞` isotopy of `C^∞` diffeomorphisms carrying `f_0⁻¹ X` onto `f_1⁻¹ X` and
`f_0⁻¹ Xb` onto `f_1⁻¹ Xb` (and `f_0⁻¹ X` onto `f_{σ t}⁻¹ X` at time `t`). -/
theorem lc82_exists_smooth_isotopy_fibre
    {F : ℝ × M → E'} (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') ∞ F (Icc 0 1 ×ˢ univ))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    {X Xb : Set E'} (hX : X = {y | φ y = 0 ∧ 0 ≤ β y}) (hXb : Xb = {y | φ y = 0 ∧ β y = 0})
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ Xb →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q) (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ Q) :
    ∃ Φ : ℝ → M ≃ₘ^∞⟮I, I⟯ M,
      ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun q : ℝ × M => Φ q.1 q.2) ∧
      Φ 0 = Diffeomorph.refl I M ∞ ∧
      (∃ K : Set M, IsCompact K ∧ ∀ t x, x ∉ K → Φ t x = x) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ X} = {x | F (Real.smoothTransition t, x) ∈ X}) ∧
      (∀ t, Φ t '' {x | F (0, x) ∈ Xb} = {x | F (Real.smoothTransition t, x) ∈ Xb}) ∧
      Φ 1 '' {x | F (0, x) ∈ X} = {x | F (1, x) ∈ X} ∧
      Φ 1 '' {x | F (0, x) ∈ Xb} = {x | F (1, x) ∈ Xb} := by
  obtain ⟨K, Φ, hK, -, hΦ, h0, hoff, himg, himgb, h1, h1b⟩ :=
    exists_isotopy_fibre_ENat (n := ⊤) le_top (by simp) hF hφ hβ hX hXb htrans htransb hQ hencl
      isOpen_univ (fun _ _ _ _ => mem_univ _)
  exact ⟨Φ, hΦ, h0, ⟨K, hK, hoff⟩, himg, himgb, h1, h1b⟩

/-- The verbatim form of LFR03 (A:24964–25014): `3 ≤ r` and the preimages in the interior of the
compact set `Q`. It follows from `lfr03_exists_isotopy_fibre`. -/
example {r : ℕ} (hr : 3 ≤ r)
    {F : ℝ × M → E'} (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E') r F (Icc 0 1 ×ˢ univ))
    {φ : E' → G} (hφ : ContDiff ℝ ∞ φ) {β : E' → ℝ} (hβ : ContDiff ℝ ∞ β)
    {X Xb : Set E'} (hX : X = {y | φ y = 0 ∧ 0 ≤ β y}) (hXb : Xb = {y | φ y = 0 ∧ β y = 0})
    (htrans : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => φ (F (t, y))) x))
    (htransb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ Xb →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (φ (F (t, y)), β (F (t, y)))) x))
    {Q : Set M} (hQ : IsCompact Q)
    (hencl : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ interior Q)
    {N : Set M} (hN : IsOpen N) (hNsub : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x, F (t, x) ∈ X → x ∈ N) :
    ∃ (K : Set M) (Φ : ℝ → M ≃ₘ^((r - 1 : ℕ) : WithTop ℕ∞)⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧ Φ 0 = Diffeomorph.refl I M ((r - 1 : ℕ) : WithTop ℕ∞) ∧
      (∀ t x, x ∉ K → Φ t x = x) ∧
      Φ 1 '' {x | F (0, x) ∈ X} = {x | F (1, x) ∈ X} ∧
      Φ 1 '' {x | F (0, x) ∈ Xb} = {x | F (1, x) ∈ Xb} := by
  obtain ⟨K, Φ, hK, hKN, -, h0, hoff, -, -, h1, h1b⟩ :=
    lfr03_exists_isotopy_fibre (by omega) hF hφ hβ hX hXb htrans htransb hQ
      (fun t ht x hx => interior_subset (hencl t ht x hx)) hN hNsub
  exact ⟨K, Φ, hK, hKN, h0, hoff, h1, h1b⟩

end DifferentialGeometry.Analysis.ODE
