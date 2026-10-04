import DifferentialGeometry.Analysis.ODE.TimeDependentFlow.FiniteOrder.Suspension
import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Complete `C^r` flows of compactly supported time-dependent vector fields

Let `V : ℝ → (x : M) → TangentSpace I x` be jointly `C^r` (`1 ≤ r`, finite or not) as a map
`ℝ × M → TM`, on a separated boundaryless manifold modelled on a finite-dimensional space, with
spatial support in one compact set `K` for all times. Then its two-parameter flow
`finiteOrderFlow V s t`, defined through TauCeti's maximal flow of the suspension `(1, V)` on
`ℝ × M`, exists for all `s, t`, is jointly `C^r` in `(s, t, x)`, satisfies the cocycle law, solves
`∂ₜ Φ s t x = V t (Φ s t x)`, is the identity off `K`, and is the unique solution of the
time-dependent equation through each point.

This is the flow statement of blueprint LFR03 (A:25005–25010: "its nonautonomous flow exists from
every time to every other time and is jointly `C^{r−1}`; solve backwards for its inverse; outside
the support the flow is the identity"), at the order of the field.

## Main results
* `finiteOrderFlow`: the flow, defined without hypotheses.
* `maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ`: completeness of the suspension.
* `contMDiff_finiteOrderFlow`: joint `C^n` regularity, `1 ≤ n ≤ ∞`.
* `exists_compactSupport_flow_Ck`: the packaged statement of design D-FOUND §D2 "F".
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle TauCeti
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The two-parameter flow of a time-dependent field.** `finiteOrderFlow V s t x` is the
position at time `t` of the solution of `γ' = V t γ` with `γ s = x`, read off from the maximal
integral curve of the suspension `(1, V)` through `(s, x)` at time `t - s`. It is defined for every
field (junk-valued where the maximal curve is not defined); its properties need the hypotheses of
the lemmas below. -/
def finiteOrderFlow (V : ℝ → (x : M) → TangentSpace I x) (s t : ℝ) (x : M) : M :=
  (maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) (t - s)).2

theorem finiteOrderFlow_def (V : ℝ → (x : M) → TangentSpace I x) (s t : ℝ) (x : M) :
    finiteOrderFlow V s t x =
      (maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) (t - s)).2 :=
  rfl

/-- A constant curve at a zero of every `V t` solves the time-dependent equation. -/
theorem hasMFDerivAt_const_of_forall_eq_zero (V : ℝ → (x : M) → TangentSpace I x) {x : M}
    (hx : ∀ t, V t x = 0) (t : ℝ) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun _ : ℝ => x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t x)) := by
  refine (hasMFDerivAt_const x t).congr_mfderiv ?_
  rw [hx t]
  exact (ContinuousLinearMap.smulRight_zero (1 : ℝ →L[ℝ] ℝ)).symm

section Flow

variable [T2Space M] [IsManifold I 1 M] [BoundarylessManifold I M]

/-- **Off the support the flow is the identity**, and the maximal curve of the suspension through
`(s, x)` is `τ ↦ (s + τ, x)`, defined for all time. -/
theorem maximalIntegralCurve_autonomizedFlowVF_of_forall_eq_zero
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {x : M} (hx : ∀ t, V t x = 0)
    (s : ℝ) :
    maximalIntegralCurveInterval (autonomizedFlowVF V) ((s, x) : ℝ × M) = univ ∧
      ∀ τ, maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) τ =
        ((s + τ, x) : ℝ × M) :=
  maximalIntegralCurve_autonomizedFlowVF_eq_of_hasMFDerivAt V hW
    (γ := fun _ : ℝ => x) (hasMFDerivAt_const_of_forall_eq_zero V hx) s

/-- **The spatial part of a maximal curve never leaves the support.** If `V t` vanishes off `K`
for every `t` and the curve starts in `K`, it stays in `K` on its whole interval of existence:
otherwise restarting it at a time where it is outside `K` gives the constant spatial curve there,
which at time `0` contradicts the initial point. -/
theorem maximalIntegralCurve_autonomizedFlowVF_snd_mem
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))) {K : Set M}
    (hsupp : ∀ t x, x ∉ K → V t x = 0) {p : ℝ × M} (hp : p.2 ∈ K) {τ : ℝ}
    (hτ : τ ∈ maximalIntegralCurveInterval (autonomizedFlowVF V) p) :
    (maximalIntegralCurve (autonomizedFlowVF V) p τ).2 ∈ K := by
  set γ := maximalIntegralCurve (autonomizedFlowVF V) p
  by_contra hy
  have h0 : (0 : ℝ) ∈ maximalIntegralCurveInterval (autonomizedFlowVF V) p := by
    obtain ⟨c, a, b, hc, hc0, h0ab, -⟩ := hτ
    exact hc.subset_maximalIntegralCurveInterval h0ab hc0 h0ab
  have hγτ : γ τ = ((p.1 + τ, (γ τ).2) : ℝ × M) :=
    Prod.ext (maximalIntegralCurve_autonomizedFlowVF_fst V hW p hτ) rfl
  have hadd := maximalIntegralCurve_add hW (s := -τ) hτ (by simpa using h0)
  rw [add_neg_cancel, maximalIntegralCurve_zero h0,
    show maximalIntegralCurve (autonomizedFlowVF V) p τ = ((p.1 + τ, (γ τ).2) : ℝ × M) from hγτ,
    (maximalIntegralCurve_autonomizedFlowVF_of_forall_eq_zero V hW
      (fun t => hsupp t _ hy) (p.1 + τ)).2 (-τ)] at hadd
  exact hy (congrArg Prod.snd hadd ▸ hp)

/-- **Completeness.** The suspension of a field with compact spatial support (uniform in time)
has maximal integral curves defined for all time. Escape lemma: near a finite endpoint the curve
would lie in the compact set `[s + b - 1, s + b + 1] × K`. -/
theorem maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ [CompleteSpace E]
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) (p : ℝ × M) :
    maximalIntegralCurveInterval (autonomizedFlowVF V) p = univ := by
  obtain ⟨s, x⟩ := p
  by_cases hx : x ∉ K
  · exact (maximalIntegralCurve_autonomizedFlowVF_of_forall_eq_zero V hW
      (fun t => hsupp t x hx) s).1
  rw [not_not] at hx
  set J := maximalIntegralCurveInterval (autonomizedFlowVF V) ((s, x) : ℝ × M)
  set γ := maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M)
  have h0 : (0 : ℝ) ∈ J := zero_mem_maximalIntegralCurveInterval hW.contMDiffAt
  have hin : ∀ τ ∈ J, γ τ ∈ Icc (s + τ) (s + τ) ×ˢ K := fun τ hτ =>
    ⟨by rw [maximalIntegralCurve_autonomizedFlowVF_fst V hW _ hτ]; exact ⟨le_rfl, le_rfl⟩,
      maximalIntegralCurve_autonomizedFlowVF_snd_mem V hW hsupp hx hτ⟩
  have hbox : ∀ c : ℝ, ∀ τ ∈ J, τ ∈ Ioo (c - 1) (c + 1) →
      γ τ ∈ Icc (s + c - 1) (s + c + 1) ×ˢ K := by
    intro c τ hτ hτc
    obtain ⟨h1, h2⟩ := hin τ hτ
    exact ⟨⟨by linarith [h1.1, hτc.1], by linarith [h1.2, hτc.2]⟩, h2⟩
  have hcomp : ∀ c : ℝ, IsCompact (Icc (s + c - 1) (s + c + 1) ×ˢ K) := fun c =>
    isCompact_Icc.prod hK
  have hup : ¬ BddAbove J := by
    intro hbdd
    have hlub := isLUB_csSup ⟨0, h0⟩ hbdd
    obtain ⟨a, ha, hb0, hsub⟩ :=
      exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB h0 hlub
    have hev : ∀ᶠ τ in 𝓝[<] sSup J, τ ∈ Ioo (max a (sSup J - 1)) (sSup J) :=
      Ioo_mem_nhdsLT (max_lt (ha.trans hb0) (by linarith))
    obtain ⟨τ, hτ1, hτ2⟩ := (hev.and (eventually_notMem_nhdsLT_maximalIntegralCurve hW h0 hlub
      (hcomp (sSup J)))).exists
    exact hτ2 (hbox (sSup J) τ (hsub ⟨(le_max_left _ _).trans_lt hτ1.1, hτ1.2⟩)
      ⟨(le_max_right _ _).trans_lt hτ1.1, by linarith [hτ1.2]⟩)
  have hlow : ¬ BddBelow J := by
    intro hbdd
    have hglb := isGLB_csInf ⟨0, h0⟩ hbdd
    obtain ⟨b, hb, ha0, hsub⟩ :=
      exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB h0 hglb
    have hev : ∀ᶠ τ in 𝓝[>] sInf J, τ ∈ Ioo (sInf J) (min b (sInf J + 1)) :=
      Ioo_mem_nhdsGT (lt_min (ha0.trans hb) (by linarith))
    obtain ⟨τ, hτ1, hτ2⟩ := (hev.and (eventually_notMem_nhdsGT_maximalIntegralCurve hW h0 hglb
      (hcomp (sInf J)))).exists
    exact hτ2 (hbox (sInf J) τ (hsub ⟨hτ1.1, hτ1.2.trans_le (min_le_left _ _)⟩)
      ⟨by linarith [hτ1.1], hτ1.2.trans_le (min_le_right _ _)⟩)
  exact maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow h0 hup hlow

/-- **The maximal curve of the suspension in terms of the flow.** -/
theorem maximalIntegralCurve_autonomizedFlowVF_eq_finiteOrderFlow [CompleteSpace E]
    (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) (s τ : ℝ) (x : M) :
    maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) τ =
      ((s + τ, finiteOrderFlow V s (s + τ) x) : ℝ × M) := by
  have huniv := maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ V hW hK hsupp (s, x)
  refine Prod.ext ?_ ?_
  · exact maximalIntegralCurve_autonomizedFlowVF_fst V hW _ (huniv ▸ mem_univ τ)
  · rw [finiteOrderFlow_def, add_sub_cancel_left]

/-- **Initial condition.** `Φ s s = id`. -/
theorem finiteOrderFlow_self [CompleteSpace E] (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) (s : ℝ) (x : M) :
    finiteOrderFlow V s s x = x := by
  have huniv := maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ V hW hK hsupp (s, x)
  rw [finiteOrderFlow_def, sub_self, maximalIntegralCurve_zero (huniv ▸ mem_univ 0)]

/-- **The cocycle law** `Φ t u ∘ Φ s t = Φ s u`. -/
theorem finiteOrderFlow_trans [CompleteSpace E] (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) (s t u : ℝ) (x : M) :
    finiteOrderFlow V t u (finiteOrderFlow V s t x) = finiteOrderFlow V s u x := by
  have huniv := maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ V hW hK hsupp
  have hadd := maximalIntegralCurve_add hW (x := ((s, x) : ℝ × M)) (t := t - s) (s := u - t)
    (huniv _ ▸ mem_univ _) (huniv _ ▸ mem_univ _)
  rw [maximalIntegralCurve_autonomizedFlowVF_eq_finiteOrderFlow V hW hK hsupp s (t - s) x,
    add_sub_cancel] at hadd
  rw [finiteOrderFlow_def V s u, show u - s = t - s + (u - t) by ring, hadd, finiteOrderFlow_def]

/-- **The flow solves the time-dependent equation** `∂ₜ Φ s t x = V t (Φ s t x)`. -/
theorem hasMFDerivAt_finiteOrderFlow [CompleteSpace E] (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {K : Set M} (hK : IsCompact K)
    (hsupp : ∀ t x, x ∉ K → V t x = 0) (s t : ℝ) (x : M) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun t => finiteOrderFlow V s t x) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (finiteOrderFlow V s t x))) := by
  have huniv := maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ V hW hK hsupp (s, x)
  have hγ : IsMIntegralCurve (maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M))
      (autonomizedFlowVF V) := by
    rw [isMIntegralCurve_iff_isMIntegralCurveOn, ← huniv]
    exact isMIntegralCurveOn_maximalIntegralCurve hW
  have h := autonomizedFlow_snd_hasMFDerivAt V _ t (hγ.comp_add (-s) t)
  have hfun : (fun σ => ((maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) ∘
      (· + -s)) σ).2) = fun σ => finiteOrderFlow V s σ x := by
    funext σ
    rw [finiteOrderFlow_def, comp_apply, sub_eq_add_neg]
  have hpt : (maximalIntegralCurve (autonomizedFlowVF V) ((s, x) : ℝ × M) ∘ (· + -s)) t =
      ((t, finiteOrderFlow V s t x) : ℝ × M) := by
    rw [comp_apply, maximalIntegralCurve_autonomizedFlowVF_eq_finiteOrderFlow V hW hK hsupp]
    congr 1 <;> ring_nf
  rw [hfun, hpt] at h
  exact h

/-- **The flow is the identity at common zeros of the field**, in particular off the support. -/
theorem finiteOrderFlow_eq_self_of_forall_eq_zero (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M))))
    {x : M} (hx : ∀ t, V t x = 0) (s t : ℝ) :
    finiteOrderFlow V s t x = x := by
  rw [finiteOrderFlow_def,
    (maximalIntegralCurve_autonomizedFlowVF_of_forall_eq_zero V hW hx s).2 (t - s)]

/-- **Uniqueness.** Every global solution of the time-dependent equation is a flow line:
`γ t = Φ s t (γ s)`. -/
theorem eq_finiteOrderFlow_of_hasMFDerivAt (V : ℝ → (x : M) → TangentSpace I x)
    (hW : ContMDiff (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I).tangent 1
      (fun p : ℝ × M =>
        (⟨p, autonomizedFlowVF V p⟩ : TangentBundle (𝓘(ℝ, ℝ).prod I) (ℝ × M)))) {γ : ℝ → M}
    (hγ : ∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t)))) (s t : ℝ) :
    γ t = finiteOrderFlow V s t (γ s) := by
  rw [finiteOrderFlow_def,
    (maximalIntegralCurve_autonomizedFlowVF_eq_of_hasMFDerivAt V hW hγ s).2 (t - s),
    add_sub_cancel]

/-- **Joint `C^n` regularity of the flow**, `1 ≤ n ≤ ∞`: `(s, t, x) ↦ Φ s t x` is `C^n` when the
field is jointly `C^n` as a map `ℝ × M → TM`. The suspension's maximal flow is `C^n` on its
natural domain (TauCeti), which is everything by completeness. -/
theorem contMDiff_finiteOrderFlow [FiniteDimensional ℝ E] {n : ℕ∞} (hn : 1 ≤ n)
    [IsManifold I n M] (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent n
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0) :
    ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I n
      (fun q : (ℝ × ℝ) × M => finiteOrderFlow V q.1.1 q.1.2 q.2) := by
  have hn' : (1 : WithTop ℕ∞) ≤ n := by exact_mod_cast hn
  have hWn := contMDiff_autonomizedFlowVF_section V hV
  have hW := hWn.of_le hn'
  have hdom : maximalIntegralCurveFlowDomain (autonomizedFlowVF V) = univ :=
    eq_univ_of_forall fun p => by
      rw [mem_maximalIntegralCurveFlowDomain,
        maximalIntegralCurveInterval_autonomizedFlowVF_eq_univ V hW hK hsupp]
      exact mem_univ _
  have hψ := contMDiffOn_maximalIntegralCurve (I := 𝓘(ℝ, ℝ).prod I) hn hWn
  rw [hdom, contMDiffOn_univ] at hψ
  have hg : ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) ((𝓘(ℝ, ℝ).prod I).prod 𝓘(ℝ, ℝ)) n
      (fun q : (ℝ × ℝ) × M => ((((q.1.1, q.2) : ℝ × M)), q.1.2 - q.1.1)) :=
    ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).prodMk
      ((contMDiff_snd.comp contMDiff_fst).sub (contMDiff_fst.comp contMDiff_fst))
  exact contMDiff_snd.comp (hψ.comp hg)

end Flow

section Packaged

variable [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] [IsManifold I ∞ M]

/-- **Design D-FOUND §D2 "F" (foundation of LFR03).** A time-dependent vector field on a smooth
boundaryless manifold, jointly `C^r` (`1 ≤ r`) as a map `ℝ × M → TM` and vanishing off one compact
set `K` at all times, has a global two-parameter flow `Φ` that is jointly `C^r`, satisfies
`Φ s s = id`, the cocycle law, the equation `∂ₜ Φ s t x = V t (Φ s t x)`, is the identity off `K`,
and through which every global solution of the equation runs. -/
theorem exists_compactSupport_flow_Ck {r : ℕ} (hr : 1 ≤ r) (V : ℝ → (x : M) → TangentSpace I x)
    (hV : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent r
      (fun q : ℝ × M => (⟨q.2, V q.1 q.2⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hsupp : ∀ t x, x ∉ K → V t x = 0) :
    ∃ Φ : ℝ → ℝ → M → M,
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I r
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s x, Φ s s x = x) ∧
      (∀ s t u x, Φ t u (Φ s t x) = Φ s u x) ∧
      (∀ s t x, HasMFDerivAt 𝓘(ℝ, ℝ) I (Φ s · x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (Φ s t x)))) ∧
      (∀ s t x, x ∉ K → Φ s t x = x) ∧
      ∀ (s : ℝ) (γ : ℝ → M), (∀ t, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (V t (γ t)))) → ∀ t, γ t = Φ s t (γ s) := by
  have hr' : (1 : WithTop ℕ∞) ≤ r := by exact_mod_cast hr
  have hW := (contMDiff_autonomizedFlowVF_section V hV).of_le hr'
  exact ⟨finiteOrderFlow V,
    contMDiff_finiteOrderFlow (n := r) (by exact_mod_cast hr) V hV hK hsupp,
    finiteOrderFlow_self V hW hK hsupp, finiteOrderFlow_trans V hW hK hsupp,
    hasMFDerivAt_finiteOrderFlow V hW hK hsupp,
    fun s t x hx => finiteOrderFlow_eq_self_of_forall_eq_zero V hW (fun t => hsupp t x hx) s t,
    fun s γ hγ t => eq_finiteOrderFlow_of_hasMFDerivAt V hW hγ s t⟩

end Packaged

end DifferentialGeometry.Analysis.ODE
