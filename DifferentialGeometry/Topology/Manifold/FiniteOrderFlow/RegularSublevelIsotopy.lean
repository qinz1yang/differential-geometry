import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.TimeLift
import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.SublevelInvariance

/-!
# Compactly supported isotopies of a moving regular sublevel of a regular level

Kernel C of `build-logs/resume/sheet-W5-FLOW.md` (statement S4): for a time-dependent defining
pair `Ψ : ℝ × M → G`, `B : ℝ × M → ℝ` of class `C^{r+1}` whose slices are transverse along
`W_t = {Ψ (t, ·) = 0, B (t, ·) ≥ 0}` and (as a pair) along `∂W_t = {Ψ (t, ·) = 0, B (t, ·) = 0}`,
with all `W_t` inside one compact `S ⊆ N`, there is a jointly `C^r` two-parameter family of
`C^r` diffeomorphisms `Φ s t`, the identity off a compact `K ⊆ N`, carrying `W_s` onto `W_t` and
`∂W_s` onto `∂W_t`. This is the time-lifting field of `TimeLift.lean` fed into F-1's
compact-support flow, with the invariance of `SublevelInvariance.lean`.

The `C^∞` version (`exists_isotopy_regularSublevel_smooth`) uses the flow packaged at order
`∞` (`finiteOrderFlowDiffeomorphENat`), since F-1's `finiteOrderFlowDiffeomorph` is stated for
natural orders.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]

/-- **The flow of a compactly supported jointly `C^n` field as `C^n` diffeomorphisms**, for any
`n : ℕ∞` with `1 ≤ n` (including `n = ∞`). F-1's `finiteOrderFlowDiffeomorph` is the same map
for natural orders. -/
def finiteOrderFlowDiffeomorphENat {n : ℕ∞} (hn : 1 ≤ n) (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0) (s t : ℝ) :
    M ≃ₘ^n⟮I, I⟯ M where
  toFun := finiteOrderFlow V s t
  invFun := finiteOrderFlow V t s
  left_inv x := by
    have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
      (show (1 : WithTop ℕ∞) ≤ n by exact_mod_cast hn)
    rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]
  right_inv x := by
    have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
      (show (1 : WithTop ℕ∞) ≤ n by exact_mod_cast hn)
    rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]
  contMDiff_toFun :=
    (contMDiff_finiteOrderFlow hn V hV hK hsupp).comp
      ((contMDiff_const (c := ((s, t) : ℝ × ℝ))).prodMk contMDiff_id)
  contMDiff_invFun :=
    (contMDiff_finiteOrderFlow hn V hV hK hsupp).comp
      ((contMDiff_const (c := ((t, s) : ℝ × ℝ))).prodMk contMDiff_id)

section API

variable {n : ℕ∞} (hn : 1 ≤ n) (V : ℝ → (x : M) → TangentSpace I x)
  (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
    (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
  {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)

@[simp] theorem finiteOrderFlowDiffeomorphENat_apply (s t : ℝ) (x : M) :
    finiteOrderFlowDiffeomorphENat hn V hV hK hsupp s t x = finiteOrderFlow V s t x :=
  rfl

theorem finiteOrderFlowDiffeomorphENat_self (s : ℝ) :
    finiteOrderFlowDiffeomorphENat hn V hV hK hsupp s s = Diffeomorph.refl I M n := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ n by exact_mod_cast hn)
  ext x
  exact finiteOrderFlow_self V hW hK hsupp s x

theorem finiteOrderFlowDiffeomorphENat_eq_self_of_not_mem (s t : ℝ) {x : M} (hx : x ∉ K) :
    finiteOrderFlowDiffeomorphENat hn V hV hK hsupp s t x = x := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ n by exact_mod_cast hn)
  exact finiteOrderFlow_eq_self_of_forall_eq_zero V hW (fun t => hsupp t x hx) s t

theorem contMDiff_finiteOrderFlowDiffeomorphENat :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun q : (ℝ × ℝ) × M => finiteOrderFlowDiffeomorphENat hn V hV hK hsupp q.1.1 q.1.2 q.2) :=
  contMDiff_finiteOrderFlow hn V hV hK hsupp

end API

variable [SigmaCompactSpace M]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- **Kernel C at any order `n : ℕ∞`, `1 ≤ n`.** A `C^m` time-dependent defining pair (`n + 1 ≤ m`)
transverse along the moving sublevel and its side boundary, with all sublevels in one compact
`S ⊆ N`, is followed by a jointly `C^n` family of `C^n` diffeomorphisms, the identity off a
compact `K ⊆ N`. -/
theorem exists_isotopy_regularSublevel_ENat {n : ℕ∞} (hn : 1 ≤ n) {m : WithTop ℕ∞}
    (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    {Ψ : ℝ × M → G} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) m Ψ)
    {B : ℝ × M → ℝ} (hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) m B)
    (htrans : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => Ψ (q.1, y)) q.2))
    (htransb : ∀ q : ℝ × M, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ (K : Set M) (Φ : ℝ → ℝ → M ≃ₘ^n⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl I M n) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      (∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ 0 ≤ B (s, x)} = {x | Ψ (t, x) = 0 ∧ 0 ≤ B (t, x)}) ∧
      ∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ B (s, x) = 0} = {x | Ψ (t, x) = 0 ∧ B (t, x) = 0} := by
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hmn
    exact absurd hmn (by simp)
  obtain ⟨V, K, O, O', hV, hK, hKN, hsupp, hO, hWO, hO', hbO', hΨt, hBt⟩ :=
    exists_timeLift_field_Cn hmn hΨ hB htrans htransb hS hWS hN hSN
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have himg := image_finiteOrderFlow_sublevel hn' V hV hK hsupp hΨ.continuous hB.continuous hO hO'
    hWO hbO' (fun q _ => hΨ.mdifferentiable hm0 q) (fun q _ => hB.mdifferentiable hm0 q) hΨt hBt
  exact ⟨K, finiteOrderFlowDiffeomorphENat hn V hV hK hsupp, hK, hKN,
    contMDiff_finiteOrderFlowDiffeomorphENat hn V hV hK hsupp,
    finiteOrderFlowDiffeomorphENat_self hn V hV hK hsupp,
    fun s t _ hx => finiteOrderFlowDiffeomorphENat_eq_self_of_not_mem hn V hV hK hsupp s t hx,
    fun s t => (himg s t).1, fun s t => (himg s t).2⟩

/-- **Kernel C (statement S4 of W5-FLOW): all-time `C^r` isotopy of a moving regular sublevel.**
Let `1 ≤ r` and let `Ψ : ℝ × M → G`, `B : ℝ × M → ℝ` be `C^{r+1}`, with `Ψ (t, ·)` a submersion
along `{Ψ (t, ·) = 0, B (t, ·) ≥ 0}` and `(Ψ, B) (t, ·)` a submersion along
`{Ψ (t, ·) = 0, B (t, ·) = 0}`, all these sets lying in a compact `S` inside an open `N`. Then
there are a compact `K ⊆ N` and `C^r` diffeomorphisms `Φ s t`, jointly `C^r` in `(s, t, x)`,
with `Φ s s = id`, `Φ s t = id` off `K`, carrying the sublevel at time `s` onto the sublevel at
time `t`, and its side boundary onto the side boundary. -/
theorem exists_isotopy_regularSublevel_Cn {r : ℕ} (hr : 1 ≤ r)
    {Ψ : ℝ × M → G} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) (r + 1) Ψ)
    {B : ℝ × M → ℝ} (hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) (r + 1) B)
    (htrans : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => Ψ (q.1, y)) q.2))
    (htransb : ∀ q : ℝ × M, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ (K : Set M) (Φ : ℝ → ℝ → M ≃ₘ^r⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I r
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl I M r) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      (∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ 0 ≤ B (s, x)} = {x | Ψ (t, x) = 0 ∧ 0 ≤ B (t, x)}) ∧
      ∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ B (s, x) = 0} = {x | Ψ (t, x) = 0 ∧ B (t, x) = 0} :=
  exists_isotopy_regularSublevel_ENat (n := (r : ℕ∞)) (by exact_mod_cast hr) le_rfl hΨ hB
    htrans htransb hS hWS hN hSN

/-- **Kernel C at order `∞`.** A `C^∞` time-dependent defining pair transverse along the moving
sublevel and its side boundary, with all sublevels in one compact `S ⊆ N`, is followed by a jointly
`C^∞` family of `C^∞` diffeomorphisms, the identity off a compact `K ⊆ N`. -/
theorem exists_isotopy_regularSublevel_smooth
    {Ψ : ℝ × M → G} (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, G) ∞ Ψ)
    {B : ℝ × M → ℝ} (hB : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ B)
    (htrans : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv I 𝓘(ℝ, G) (fun y => Ψ (q.1, y)) q.2))
    (htransb : ∀ q : ℝ × M, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv I 𝓘(ℝ, G × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2))
    {S : Set M} (hS : IsCompact S) (hWS : ∀ q : ℝ × M, Ψ q = 0 → 0 ≤ B q → q.2 ∈ S)
    {N : Set M} (hN : IsOpen N) (hSN : S ⊆ N) :
    ∃ (K : Set M) (Φ : ℝ → ℝ → M ≃ₘ^∞⟮I, I⟯ M),
      IsCompact K ∧ K ⊆ N ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl I M ∞) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      (∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ 0 ≤ B (s, x)} = {x | Ψ (t, x) = 0 ∧ 0 ≤ B (t, x)}) ∧
      ∀ s t, Φ s t '' {x | Ψ (s, x) = 0 ∧ B (s, x) = 0} = {x | Ψ (t, x) = 0 ∧ B (t, x) = 0} :=
  exists_isotopy_regularSublevel_ENat (n := ⊤) le_top (by simp) hΨ hB htrans htransb hS hWS hN
    hSN

end DifferentialGeometry.Analysis.ODE
