import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.StepBLocalizedAA
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MapConvergenceComp

set_option autoImplicit false

/-!
# Local maps converge to the identity (MSM135 Ch4 Step B, `lbl399` — `C⁰` core)

`lbl399`: the composed local maps `F_{kℓ,β}^α = J̄_ℓ^{αβ} ∘ J_k^{βα} : E^β → vec E^β`
converge to the identity as `k, ℓ → ∞` (independently).  Since `J_k^{βα} → J_∞^{βα}` and
`J̄_ℓ^{αβ} → J̄_∞^{αβ}` with the limit cocycle `J̄_∞^{αβ} ∘ J_∞^{βα} = id`, this is the
two-parameter composition convergence `A_ℓ ∘ B_k → A_∞ ∘ B_∞ = id`.

## What is delivered: the `C⁰` (uniform-on-compacts) core

`comp_tendsto_id_on` proves the **order-`0`** content: from `B_k → B_∞` and
`A_ℓ → A_∞` uniformly on compacts (the `MapCInfConvOnCompacts` outputs of B-trans /
`isometry_seq_diffeo_on`) and the limit identity `A_∞ ∘ B_∞ = id`, the family
`A_ℓ ∘ B_k → id` **uniformly on each compact `K ⊆ U`** as `k, ℓ → ∞`.  The moving
evaluation point `B_k x` is corralled into a fixed compact `cthickening δ₀ (B_∞ '' K) ⊆
V` (Heine–Cantor uniform continuity of `A_∞` there + uniform convergence of `A_ℓ`).
The inverse identity is consumed **conditionally on `B_∞ x ∈ V`** (hypothesis `hKV`),
matching `isometry_seq_diffeo_on`'s honest membership conditions.

## Reported frontier: the full `C^∞` `lbl399`

Upgrading `comp_tendsto_id_on` from `C⁰` to `C^∞` (so that `F_{kℓ} → id` in
`MapCInfConvOnCompacts`, as the book states) requires a **Faà-di-Bruno composition
convergence** lemma: `∇ʳ(A_ℓ ∘ B_k)` is a universal polynomial in `(∇^{≤r}A_ℓ)∘B_k` and
`∇^{≤r}B_k`, and one must push the two-parameter uniform-on-compacts convergence through
that polynomial (with the moving evaluation point `B_k x`).  Mathlib has the static
Faà-di-Bruno formula but **no convergence version**.  This is the smallest missing
lemma; per the plan's "do not invent a broad convergence framework" it is reported, not
built here.  The same lemma is the frontier for `lbl404` (almost-identity pullback).
-/

namespace DifferentialGeometry
namespace HCGCompactness

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
/-- **Local maps converge to the identity** (`lbl399`, `C⁰` core).  Given
`B_k → B_∞` in `C^∞` on compacts of the open `U ⊆ E`, `A_ℓ → A_∞` in `C^∞` on compacts
of the open `V ⊆ F`, and the limit identity `A_∞ (B_∞ x) = x` (for `x ∈ U` with
`B_∞ x ∈ V`), the composed family `A_ℓ ∘ B_k` converges to the identity **uniformly on
each compact `K ⊆ U`** with `B_∞ '' K ⊆ V`, as `k, ℓ → ∞` independently:
for every `ε > 0` there is `N` with `dist (A_ℓ (B_k x)) x < ε` for all `k, ℓ ≥ N`,
`x ∈ K`. -/
theorem comp_tendsto_id_on
    {U : Set E} {V : Set F} (hV : IsOpen V)
    (B : ℕ → E → F) (Binf : E → F) (A : ℕ → F → E) (Ainf : F → E)
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBcont : ContinuousOn Binf U) (hAcont : ContinuousOn Ainf V)
    (hid : ∀ x ∈ U, Binf x ∈ V → Ainf (Binf x) = x)
    {K : Set E} (hKcpt : IsCompact K) (hKU : K ⊆ U) (hKV : ∀ x ∈ K, Binf x ∈ V) :
    ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ x ∈ K, dist (A l (B k x)) x < ε := by
  intro ε hε
  have hBKcpt : IsCompact (Binf '' K) := hKcpt.image_of_continuousOn (hBcont.mono hKU)
  have hBKV : Binf '' K ⊆ V := by rintro _ ⟨x, hx, rfl⟩; exact hKV x hx
  obtain ⟨δ₀, hδ₀pos, hδ₀V⟩ := hBKcpt.exists_cthickening_subset_open hV hBKV
  set K' : Set F := Metric.cthickening δ₀ (Binf '' K) with hK'def
  have hK'cpt : IsCompact K' := hBKcpt.cthickening
  have hK'V : K' ⊆ V := hδ₀V
  have huc : UniformContinuousOn Ainf K' :=
    hK'cpt.uniformContinuousOn_of_continuous (hAcont.mono hK'V)
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδpos, hδ⟩ := huc (ε / 2) (by positivity)
  have hA0 : TendstoUniformlyOn A Ainf atTop K' :=
    tendstoUniformlyOn_of_cPConv (hA K' hK'cpt hK'V 0)
  rw [Metric.tendstoUniformlyOn_iff] at hA0
  obtain ⟨NA, hNA⟩ := eventually_atTop.mp (hA0 (ε / 2) (by positivity))
  have hB0 : TendstoUniformlyOn B Binf atTop K :=
    tendstoUniformlyOn_of_cPConv (hB K hKcpt hKU 0)
  rw [Metric.tendstoUniformlyOn_iff] at hB0
  obtain ⟨NB, hNB⟩ := eventually_atTop.mp (hB0 (min δ δ₀) (by positivity))
  refine ⟨max NA NB, fun k hk l hl x hx => ?_⟩
  have hxU : x ∈ U := hKU hx
  have hBxV : Binf x ∈ V := hKV x hx
  have hBkx : dist (Binf x) (B k x) < min δ δ₀ := hNB k (le_trans (le_max_right _ _) hk) x hx
  have hBkxK' : B k x ∈ K' :=
    Metric.mem_cthickening_of_dist_le (B k x) (Binf x) δ₀ (Binf '' K) ⟨x, hx, rfl⟩
      (by rw [dist_comm]; exact le_of_lt (lt_of_lt_of_le hBkx (min_le_right _ _)))
  have hBinfxK' : Binf x ∈ K' := Metric.self_subset_cthickening _ ⟨x, hx, rfl⟩
  calc dist (A l (B k x)) x
      = dist (A l (B k x)) (Ainf (Binf x)) := by rw [hid x hxU hBxV]
    _ ≤ dist (A l (B k x)) (Ainf (B k x)) + dist (Ainf (B k x)) (Ainf (Binf x)) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add
        · rw [dist_comm]
          exact hNA l (le_trans (le_max_left _ _) hl) (B k x) hBkxK'
        · refine hδ (B k x) hBkxK' (Binf x) hBinfxK' ?_
          rw [dist_comm]; exact lt_of_lt_of_le hBkx (min_le_left _ _)
    _ = ε := by ring

omit [FiniteDimensional ℝ E] in
/-- **Local maps converge to the identity in `C^∞`** (`lbl399`, two-parameter
form).  This upgrades `comp_tendsto_id_on` from order `0` to every finite order:
for every compact `K ⊆ U`, order `p`, and `ε > 0`, all derivatives up to order
`p` of `A_l ∘ B_k - id` are uniformly `≤ ε` on `K` once both indices are large.

The proof uses the reusable same-index composition theorem in
`MapConvergenceComp.lean`: if such a two-parameter threshold failed, choosing bad
indices `k_N,l_N ≥ N` would give reindexed sequences still tending to infinity,
contradicting same-index `C^∞` convergence of `A_{l_N} ∘ B_{k_N}` to
`A∞ ∘ B∞ = id`. -/
theorem comp_cInf_id_on
    {U : Set E} {V : Set F} (hU : IsOpen U) (hV : IsOpen V)
    (B : ℕ → E → F) (Binf : E → F) (A : ℕ → F → E) (Ainf : F → E)
    (hB : MapCInfConvOnCompacts U B Binf) (hA : MapCInfConvOnCompacts V A Ainf)
    (hBc : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (B k) U)
    (hBinfc : ContDiffOn ℝ (⊤ : ℕ∞) Binf U)
    (hAc : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (A k) V)
    (hAinfc : ContDiffOn ℝ (⊤ : ℕ∞) Ainf V)
    (hmap : Set.MapsTo Binf U V) (hmapk : ∀ k, Set.MapsTo (B k) U V)
    (hid : ∀ x ∈ U, Ainf (Binf x) = x)
    {K : Set E} (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    ∀ p : ℕ, ∀ ε > 0, ∃ N : ℕ, ∀ k ≥ N, ∀ l ≥ N, ∀ r ≤ p, ∀ x ∈ K,
      mapDerivNorm r (fun y => A l (B k y)) (fun y : E => y) x ≤ ε := by
  classical
  intro p ε hε
  by_contra hbad
  push Not at hbad
  choose k hk hbad using hbad
  choose l hl hbad using hbad
  choose r hr hbad using hbad
  choose x hx hbad using hbad
  have hk_tendsto : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hl_tendsto : Tendsto l atTop atTop := tendsto_atTop_mono hl tendsto_id
  have hB' : MapCInfConvOnCompacts U (fun n => B (k n)) Binf :=
    hB.comp_tendsto_atTop hk_tendsto
  have hA' : MapCInfConvOnCompacts V (fun n => A (l n)) Ainf :=
    hA.comp_tendsto_atTop hl_tendsto
  have hcomp :
      MapCInfConvOnCompacts U
        (fun n y => A (l n) (B (k n) y)) (fun y => Ainf (Binf y)) :=
    MapCInfConvOnCompacts.comp hU hV hB' hA'
      (fun n => hBc (k n)) hBinfc (fun n => hAc (l n)) hAinfc hmap
      (fun n => hmapk (k n))
  have hcomp_id :
      MapCInfConvOnCompacts U
        (fun n y => A (l n) (B (k n) y)) (fun y : E => y) :=
    hcomp.congr hU (fun _ _ _ => rfl) (fun y hy => (hid y hy).symm)
  obtain ⟨N, hN⟩ := hcomp_id K hKcpt hKU p ε hε
  have hgood := hN N le_rfl (r N) (hr N) (x N) (hx N)
  exact not_lt_of_ge hgood (hbad N)

end HCGCompactness
end DifferentialGeometry
