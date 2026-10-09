import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.CompactSupportFlow
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# The `C^r` diffeomorphisms of a compactly supported time-dependent flow

The two-parameter flow `finiteOrderFlow V` of a jointly `C^r` time-dependent field with compact
spatial support, packaged as a family of `C^r` diffeomorphisms `Φ s t` with inverse `Φ t s`,
`Φ s s = id` and `Φ s t ≫ Φ t u = Φ s u`. This is statement (T) of lane W4-F7a
(`build-logs/resume/sheet-W4-F7a.md`, Addendum 1), the flow input of blueprint LFR03.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [BoundarylessManifold I M]
  [IsManifold I ∞ M]

/-- **The time-`s`-to-time-`t` map of a compactly supported `C^r` field, as a `C^r`
diffeomorphism.** Its inverse is the time-`t`-to-time-`s` map. -/
def finiteOrderFlowDiffeomorph {r : ℕ} (hr : 1 ≤ r) (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent r
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0) (s t : ℝ) :
    M ≃ₘ^r⟮I, I⟯ M where
  toFun := finiteOrderFlow V s t
  invFun := finiteOrderFlow V t s
  left_inv x := by
    have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
      (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
    rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]
  right_inv x := by
    have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
      (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
    rw [finiteOrderFlow_trans V hW hK hsupp, finiteOrderFlow_self V hW hK hsupp]
  contMDiff_toFun :=
    (contMDiff_finiteOrderFlow (n := r) (by exact_mod_cast hr) V hV hK hsupp).comp
      ((contMDiff_const (c := ((s, t) : ℝ × ℝ))).prodMk contMDiff_id)
  contMDiff_invFun :=
    (contMDiff_finiteOrderFlow (n := r) (by exact_mod_cast hr) V hV hK hsupp).comp
      ((contMDiff_const (c := ((t, s) : ℝ × ℝ))).prodMk contMDiff_id)

section API

variable {r : ℕ} (hr : 1 ≤ r) (V : ℝ → (x : M) → TangentSpace I x)
  (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent r
    (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
  {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0)

@[simp] theorem finiteOrderFlowDiffeomorph_apply (s t : ℝ) (x : M) :
    finiteOrderFlowDiffeomorph hr V hV hK hsupp s t x = finiteOrderFlow V s t x :=
  rfl

@[simp] theorem finiteOrderFlowDiffeomorph_symm (s t : ℝ) :
    (finiteOrderFlowDiffeomorph hr V hV hK hsupp s t).symm =
      finiteOrderFlowDiffeomorph hr V hV hK hsupp t s :=
  rfl

@[simp] theorem finiteOrderFlowDiffeomorph_self (s : ℝ) :
    finiteOrderFlowDiffeomorph hr V hV hK hsupp s s = Diffeomorph.refl I M r := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
  ext x
  exact finiteOrderFlow_self V hW hK hsupp s x

theorem finiteOrderFlowDiffeomorph_trans (s t u : ℝ) :
    (finiteOrderFlowDiffeomorph hr V hV hK hsupp s t).trans
        (finiteOrderFlowDiffeomorph hr V hV hK hsupp t u) =
      finiteOrderFlowDiffeomorph hr V hV hK hsupp s u := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
  ext x
  exact finiteOrderFlow_trans V hW hK hsupp s t u x

theorem finiteOrderFlowDiffeomorph_eq_self_of_not_mem (s t : ℝ) {x : M} (hx : x ∉ K) :
    finiteOrderFlowDiffeomorph hr V hV hK hsupp s t x = x := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
  exact finiteOrderFlow_eq_self_of_forall_eq_zero V hW (fun t => hsupp t x hx) s t

theorem contMDiff_finiteOrderFlowDiffeomorph :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I r
      (fun q : (ℝ × ℝ) × M => finiteOrderFlowDiffeomorph hr V hV hK hsupp q.1.1 q.1.2 q.2) :=
  contMDiff_finiteOrderFlow (n := r) (by exact_mod_cast hr) V hV hK hsupp

end API

/-- **Statement (T) of W4-F7a (the flow input of LFR03).** A time-dependent field on a smooth
boundaryless manifold, jointly `C^r` (`1 ≤ r`) as a map `ℝ × M → TM` and vanishing off one compact
set `K` at all times, has a flow from every time to every other time by `C^r` diffeomorphisms,
jointly `C^r` in `(s, t, x)`, with `Φ s s = id`, inverse `Φ t s`, the cocycle law, the equation
`∂ₜ Φ s t x = V t (Φ s t x)`, and `Φ s t = id` off `K`. -/
theorem exists_compactSupport_diffeomorph_flow_Ck {r : ℕ} (hr : 1 ≤ r)
    (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent r
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0) :
    ∃ Φ : ℝ → ℝ → M ≃ₘ^r⟮I, I⟯ M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I r
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s, Φ s s = Diffeomorph.refl I M r) ∧
      (∀ s t, (Φ s t).symm = Φ t s) ∧
      (∀ s t u, (Φ s t).trans (Φ t u) = Φ s u) ∧
      (∀ s t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (Φ s · x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (Φ s t x)))) ∧
      ∀ s t x, x ∉ K → Φ s t x = x := by
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le
    (show (1 : WithTop ℕ∞) ≤ r by exact_mod_cast hr)
  exact ⟨finiteOrderFlowDiffeomorph hr V hV hK hsupp,
    contMDiff_finiteOrderFlowDiffeomorph hr V hV hK hsupp,
    finiteOrderFlowDiffeomorph_self hr V hV hK hsupp,
    finiteOrderFlowDiffeomorph_symm hr V hV hK hsupp,
    finiteOrderFlowDiffeomorph_trans hr V hV hK hsupp,
    fun s t x => hasMFDerivAt_finiteOrderFlow V hW hK hsupp s t x,
    fun s t _ hx => finiteOrderFlowDiffeomorph_eq_self_of_not_mem hr V hV hK hsupp s t hx⟩

end DifferentialGeometry.Analysis.ODE
