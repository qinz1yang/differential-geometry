import RicciFlower.Analysis.ODE.FlowCk
set_option linter.unusedSectionVars false

/-!
# Parametric `C^k` smoothness of the variational linear map

The previous file `FlowCk.lean` reduced the `C^k` flow problem to the joint `C^j`
smoothness of the *spatial piece* `Lsp(x, t) ∈ E →L[ℝ] E` of the joint Fréchet derivative
`D Φ`.  Pointwise, `Lsp(x, t) δ = y_δ(x, t)` where `y_δ` is the variational solution
along the orbit `Φ ⟨x, ·⟩` with initial variation `δ`.

The key mathematical observation is that the variational ODE itself defines a flow.
For each base point `x`, the variational ODE in `δ` is the linear ODE
`y'(t) = A_x(t) y(t)` where `A_x(t) := fderiv ℝ (f t) (Φ ⟨x, t⟩)`.  Equivalently,
viewing `Y(x, t) ∈ E →L[ℝ] E` (with `Y(x, t) δ := y_δ(x, t)`) as a CLM-valued curve,
`Y` solves the linear ODE on `E →L[ℝ] E` :
`Y'(t) = A_x(t) ∘ Y(t)`, `Y(t₀) = id`.

Crucially, this linear ODE on `E →L[ℝ] E` can be *packaged together with the original
ODE* into a single ODE on the augmented Banach space `E × (E →L[ℝ] E)`.  Define
`augF : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E))` by
```
augF t (x, Z) := (f t x, (fderiv ℝ (f t) x).comp Z)
```
The augmented vector field `augF` is jointly `C^k` whenever `f` is jointly `C^{k+1}`,
because the spatial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x` is `C^k` (it is the
post-composition of `fderiv ℝ (uncurry f)` — itself `C^k` from `f` being `C^{k+1}` — with
the inclusion `inr`).  Composition `(A, Z) ↦ A.comp Z` is bounded bilinear in
`A : E →L[ℝ] E` and `Z : E →L[ℝ] E`, hence jointly smooth.

The augmented flow `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` satisfies, for any
initial point `(x₀, Z₀)`,
```
aΦ ⟨(x, Z), t⟩ = (Φ(x, t), variationalLinearMapAt(x, t) ∘ Z)
```
when the original local flow `Φ` exists.  In particular, taking `Z = id` recovers
`variationalLinearMapAt(x, t)` as the second component of `aΦ ⟨(x, id), t⟩`.

This recursive observation gives the abstract induction:
* **Base** `k = 1` : V.2.c.2 applied to the original ODE gives `Φ ∈ C^1`.
* **Step** : if the augmented system has a flow that is jointly `C^k`, the projection
  `(x, t) ↦ Y(x, t) ∘ id = variationalLinearMapAt(x, t)` is jointly `C^k`, which
  discharges the spatial-piece hypothesis of `contDiffOn_flow_succ_of_spatial_smooth`
  (the inductive step from `FlowCk.lean`) and upgrades `Φ` from `C^k` to `C^{k+1}`.

This file provides the *structural* pieces of this argument:

* `augVF` — the augmented vector field on `E × (E →L[ℝ] E)`.
* `augVF_uncurry_contDiff` — `uncurry augVF` is `C^k` whenever `uncurry f` is `C^{k+1}`.
* `contDiffOn_partial_fderiv_of_succ` — the partial-Fréchet-derivative regularity
  `(t, x) ↦ fderiv ℝ (f t) x` is `C^k` from `uncurry f` `C^{k+1}`.
* `contDiffOn_variational_linear_of_aug_flow` — the projection lemma: if a function
  `Y : E × ℝ → E →L[ℝ] E` is the second component of a `C^k` candidate `aΦ` for the
  augmented flow with initial spatial-component `id`, then `Y` is jointly `C^k`.
* `contDiffOn_flow_of_isLocalFlow_of_contDiff_via_aug` — the cleanest packaging of the
  unconditional `C^k` flow theorem, parametrised by a *single* `C^k` candidate for the
  augmented flow.  This factors out the entire `Lsp_seq` sequence from `FlowCk.lean` into
  a single, mathematically-transparent hypothesis.

The connecting hypothesis between "the augmented system has a `C^k` joint flow" and
"the variational linear map is jointly `C^k`" is captured by a `Prop` predicate
`IsVariationalFlowProjection` that bundles the variational identity for the spatial
component of the augmented flow.  When discharged at level `k` (by the augmented flow
theorem or by a direct uniqueness argument), this predicate gives an unconditional
`C^k` flow theorem in one line.

All theorems are formulated on a generic Banach space `E`; `[InnerProductSpace ℝ E]` is
*not* used.  No manifold or tensor file is imported.
-/

noncomputable section

open Set Function Filter Metric Asymptotics Real
open scoped Topology NNReal

namespace RicciFlower
namespace Analysis
namespace ODE
namespace Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ## The augmented vector field on `E × (E →L[ℝ] E)`

For a time-dependent vector field `f : ℝ → E → E` we define the *augmented* vector field
`augVF f : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E))` whose orbits are pairs `(x(t), Z(t))`
where `x(t)` solves the original ODE and `Z(t)` solves the linear ODE
`Z'(t) = (fderiv ℝ (f t) (x(t))) ∘ Z(t)`.  Concretely:
```
augVF f t (x, Z) := (f t x, (fderiv ℝ (f t) x).comp Z)
```
The second component is the time-derivative of `Y(x, t) ∘ Z` viewed as a curve in
`E →L[ℝ] E` (post-composition with the constant `Z`). -/

section AugVFDefinition

/-- The **augmented vector field** for the linear-ODE coupling.  This is the
time-dependent vector field on `E × (E →L[ℝ] E)` whose first component is the original
ODE `x'(t) = f t (x(t))` and whose second component is the variational ODE for the
CLM-valued curve `Z(t) = Y(x(t)) ∘ Z₀`. -/
def augVF (f : ℝ → E → E) : ℝ → (E × (E →L[ℝ] E)) → (E × (E →L[ℝ] E)) :=
  fun t p => (f t p.1, ((fderiv ℝ (f t) p.1).comp p.2))

@[simp]
lemma augVF_apply (f : ℝ → E → E) (t : ℝ) (x : E) (Z : E →L[ℝ] E) :
    augVF f t (x, Z) = (f t x, ((fderiv ℝ (f t) x).comp Z)) := rfl

end AugVFDefinition

/-! ## Partial Fréchet derivative smoothness

If `uncurry f` is `C^{k+1}` on `Set.univ`, then `fderiv ℝ (uncurry f) : ℝ × E → ((ℝ × E) →L[ℝ] E)`
is `C^k`.  Composing with `inr : E →L[ℝ] ℝ × E` (which is a continuous linear map)
gives the partial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x`, which is therefore
also `C^k`. -/

section PartialFDerivSmoothness

variable {f : ℝ → E → E}

/-- The partial-Fréchet-derivative map `(t, x) ↦ fderiv ℝ (f t) x` equals the
post-composition of `fderiv ℝ (uncurry f)` with the inclusion `inr : E →L[ℝ] ℝ × E`,
on the open set where `uncurry f` is differentiable.  We package this on `Set.univ`,
since the project-wide hypothesis is `ContDiffOn ℝ _ (uncurry f) Set.univ`. -/
lemma partial_fderiv_eq_comp_inr_on_univ
    (hf : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ∀ p : ℝ × E, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p := by
    have hp_open : (Set.univ : Set (ℝ × E)) ∈ 𝓝 p := isOpen_univ.mem_nhds (mem_univ _)
    exact (hf.contDiffAt hp_open).differentiableAt one_ne_zero
  exact fderiv_eq_comp_inr hdiff_joint

/-- Local version of `partial_fderiv_eq_comp_inr_on_univ` on an open domain. -/
lemma partial_fderiv_eq_comp_inr_on_open
    {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℝ 1 (uncurry f) Ω) :
    ∀ p ∈ Ω, fderiv ℝ (f p.1) p.2
      = (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  intro p hp
  have hp_open : Ω ∈ 𝓝 p := hΩ.mem_nhds hp
  have hdiff_joint : DifferentiableAt ℝ (uncurry f) p :=
    ((hf.contDiffAt hp_open).differentiableAt one_ne_zero)
  exact fderiv_eq_comp_inr hdiff_joint

/-- **Spatial-Fréchet-derivative smoothness.**  If `uncurry f` is `C^{k+1}` on
`Set.univ`, then the partial Fréchet derivative `(t, x) ↦ fderiv ℝ (f t) x` is `C^k`
on `Set.univ`. -/
theorem contDiffOn_partial_fderiv_of_succ
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.univ : Set (ℝ × E)) := by
  -- `fderiv ℝ (uncurry f) : ℝ × E → ((ℝ × E) →L[ℝ] E)` is `C^k` on the open `Set.univ`.
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) := by
    have h : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) (Set.univ : Set (ℝ × E)) :=
      hf_succ.fderiv_of_isOpen isOpen_univ le_rfl
    exact h
  -- Post-compose with the bounded linear map `R ↦ R.comp inr`.
  -- `M ↦ M.comp inr : ((ℝ × E) →L[ℝ] E) → (E →L[ℝ] E)` is itself a continuous linear map.
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    -- `compL` is the composition map `M ↦ N ↦ M ∘ N` ; `.flip` swaps; apply with `inr`.
    rfl
  -- The composition `postL ∘ fderiv (uncurry f)` is `C^k`.
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) (Set.univ : Set (ℝ × E)) :=
    hfderiv_Ck.continuousLinearMap_comp postL
  -- And this composition equals the partial Fréchet derivative pointwise on `univ`.
  have heq : ∀ p ∈ (Set.univ : Set (ℝ × E)),
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p _
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact zero_le _
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast h1
      have := hf_succ.of_le h1'
      simpa using this
    have h := partial_fderiv_eq_comp_inr_on_univ hf_C1 p
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

/-- Local **spatial-Fréchet-derivative smoothness** on an open domain.  If
`uncurry f` is `C^{k+1}` on `Ω`, then `(t, x) ↦ fderiv ℝ (f t) x`
is `C^k` on the same `Ω`. -/
theorem contDiffOn_partial_fderiv_of_succ_local
    {k : ℕ∞} {Ω : Set (ℝ × E)} (hΩ : IsOpen Ω)
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) Ω) :
    ContDiffOn ℝ k (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) Ω := by
  have hfderiv_Ck : ContDiffOn ℝ k (fderiv ℝ (uncurry f)) Ω :=
    hf_succ.fderiv_of_isOpen hΩ le_rfl
  set postL : ((ℝ × E) →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E (ℝ × E) E).flip
      (ContinuousLinearMap.inr ℝ ℝ E) with hpostL_def
  have hpostL_apply : ∀ R : (ℝ × E) →L[ℝ] E,
      postL R = R.comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro R
    rfl
  have hcomp_Ck : ContDiffOn ℝ k
      (fun p : ℝ × E => postL (fderiv ℝ (uncurry f) p)) Ω :=
    hfderiv_Ck.continuousLinearMap_comp postL
  have heq : ∀ p ∈ Ω,
      fderiv ℝ (f p.1) p.2 = postL (fderiv ℝ (uncurry f) p) := by
    intro p hp
    have hf_C1 : ContDiffOn ℝ 1 (uncurry f) Ω := by
      have h1 : (1 : ℕ∞) ≤ k + 1 := by
        calc (1 : ℕ∞) = 0 + 1 := by simp
          _ ≤ k + 1 := by gcongr; exact zero_le _
      have h1' : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
        exact_mod_cast h1
      exact hf_succ.of_le h1'
    have h := partial_fderiv_eq_comp_inr_on_open hΩ hf_C1 p hp
    rw [hpostL_apply]
    exact h
  exact hcomp_Ck.congr heq

end PartialFDerivSmoothness

/-! ## Smoothness of the augmented vector field

The augmented vector field `augVF f` is jointly `C^k` whenever `uncurry f` is jointly
`C^{k+1}`.  The first component `f t x` inherits the regularity of `f` directly.  The
second component `(fderiv ℝ (f t) x).comp Z` factors through the bounded bilinear
composition `((·) ∘ (·)) : (E →L[ℝ] E) × (E →L[ℝ] E) → (E →L[ℝ] E)` applied to the
pair `(fderiv ℝ (f t) x, Z)`; the first factor is `C^k` by
`contDiffOn_partial_fderiv_of_succ`, and the second is the projection. -/

section AugVFSmoothness

variable {f : ℝ → E → E}

/-- **Smoothness of the augmented vector field.**  If `uncurry f` is `C^{k+1}` on
`Set.univ : Set (ℝ × E)`, then `uncurry (augVF f)` is `C^k` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`. -/
theorem augVF_uncurry_contDiff
    {k : ℕ∞} (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContDiffOn ℝ k (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  -- First-component smoothness.  `(t, (x, Z)) ↦ f t x` is `C^{k+1}` (hence `C^k`) via the
  -- canonical projection.
  set proj1 : ℝ × (E × (E →L[ℝ] E)) → ℝ × E := fun q => (q.1, q.2.1) with hproj1_def
  have hproj1_Ck : ContDiffOn ℝ k proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    refine ContDiffOn.prodMk ?_ ?_
    · exact contDiff_fst.contDiffOn
    · exact (contDiff_fst.comp contDiff_snd).contDiffOn
  have hmaps1 : MapsTo proj1 (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × E)) := fun _ _ => mem_univ _
  have hf_Ck : ContDiffOn ℝ k (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((k + 1 : ℕ∞) : WithTop ℕ∞) := by
      have hk_le : (k : ℕ∞) ≤ k + 1 := le_self_add
      exact_mod_cast hk_le
    exact hf_succ.of_le h_le
  have hcomp1 : ContDiffOn ℝ k (uncurry f ∘ proj1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hf_Ck.comp hproj1_Ck hmaps1
  have heq1 : (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1) = uncurry f ∘ proj1 := by
    funext q; rfl
  have hC1 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => f q.1 q.2.1)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq1]; exact hcomp1
  -- Second-component smoothness.  We factor `(t, (x, Z)) ↦ (fderiv ℝ (f t) x).comp Z` as
  -- `(t, (x, Z)) ↦ (fderiv ℝ (f t) x, Z) ↦ A.comp Z`.
  have hpartial_Ck := contDiffOn_partial_fderiv_of_succ hf_succ
  -- `(t, (x, Z)) ↦ fderiv ℝ (f t) x` is `C^k` by composition with `proj1`.
  have hA_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      fderiv ℝ (f q.1) q.2.1) (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
    have hcomp := hpartial_Ck.comp hproj1_Ck hmaps1
    have heq : (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) ∘ proj1
        = (fun q : ℝ × (E × (E →L[ℝ] E)) => fderiv ℝ (f q.1) q.2.1) := by
      funext q; rfl
    rw [← heq]; exact hcomp
  -- `(t, (x, Z)) ↦ Z` is `C^∞`.
  have hZ_Ck : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) => q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    (contDiff_snd.comp contDiff_snd).contDiffOn
  -- Pair them: `(t, (x, Z)) ↦ (fderiv ℝ (f t) x, Z)`.
  have hpair_Ck : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hA_Ck.prodMk hZ_Ck
  -- The composition `(A, Z) ↦ A.comp Z` is a bounded bilinear map, hence smooth on every
  -- finite order.
  have hbilin_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) :=
    (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := E) (F := E) (G := E)).contDiff
  have hbilin_Ck : ContDiffOn ℝ k
      (fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2)
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := hbilin_smooth.contDiffOn
  have hmaps_pair : MapsTo (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E)))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E))))
      (Set.univ : Set ((E →L[ℝ] E) × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hC2_pre : ContDiffOn ℝ k
      ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
       (fun q : ℝ × (E × (E →L[ℝ] E)) =>
        ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    hbilin_Ck.comp hpair_Ck hmaps_pair
  have heq2 : ((fun p : (E →L[ℝ] E) × (E →L[ℝ] E) => p.1.comp p.2) ∘
        (fun q : ℝ × (E × (E →L[ℝ] E)) =>
         ((fderiv ℝ (f q.1) q.2.1, q.2.2) : (E →L[ℝ] E) × (E →L[ℝ] E))))
      = (fun q : ℝ × (E × (E →L[ℝ] E)) =>
          (fderiv ℝ (f q.1) q.2.1).comp q.2.2) := by
    funext q; rfl
  have hC2 : ContDiffOn ℝ k (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (fderiv ℝ (f q.1) q.2.1).comp q.2.2)
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by rw [heq2] at hC2_pre; exact hC2_pre
  -- Combine: `uncurry (augVF f)` is the pair `(C1, C2)`.
  have hpair_final : ContDiffOn ℝ k
      (fun q : ℝ × (E × (E →L[ℝ] E)) => (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := hC1.prodMk hC2
  -- And this pair equals `uncurry (augVF f)`.
  have heq_final : (fun q : ℝ × (E × (E →L[ℝ] E)) =>
      (f q.1 q.2.1, (fderiv ℝ (f q.1) q.2.1).comp q.2.2))
      = uncurry (augVF f) := by
    funext q; rfl
  rw [heq_final] at hpair_final
  exact hpair_final

/-- The augmented vector field is `C^0` (continuous) when `uncurry f` is `C^1`.  This is
the base-level smoothness used for Picard–Lindelöf on the augmented system. -/
theorem augVF_uncurry_continuousOn_of_C1
    (hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E))) :
    ContinuousOn (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) := by
  have hf_succ : ContDiffOn ℝ ((0 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C1
  have h := augVF_uncurry_contDiff (k := (0 : ℕ∞)) hf_succ
  exact contDiffOn_zero.mp h

end AugVFSmoothness

/-! ## The variational-flow projection predicate

The bridge between "augmented flow `aΦ` is jointly `C^k`" and "the variational linear
map is jointly `C^k`" is captured by an explicit projection identity: for every
`(x, t)` in the relevant open neighbourhood, taking the *second* component of
`aΦ ⟨(x, id), t⟩` equals `variationalLinearMapAt(x, t)`.

The argument that the second component of the augmented flow is exactly the variational
linear map requires a uniqueness theorem for the linear ODE on `E →L[ℝ] E` —
specifically, that the curve `t ↦ aΦ ⟨(x, id), t⟩.2` is the unique solution of
`Z'(t) = (fderiv ℝ (f t) (Φ ⟨x, t⟩)) ∘ Z(t)` with `Z(t₀) = id`, and that this unique
solution agrees pointwise with the application `δ ↦ variationalSolutionFun(x, δ, t)`
via linearity.

We package the projection identity as a `Prop`-level predicate, and the abstract
inductive theorem consumes it as a hypothesis.  Discharging this predicate at level
`k` reduces precisely to: existence of a joint `C^k` flow of the augmented system on
the required neighbourhood, together with the variational identification of its
second component. -/

section ProjectionPredicate

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **The augmented-flow projection predicate.**

Given the parameters of `contDiffOn_flow_succ_of_spatial_smooth`, a function
`Y : E × ℝ → (E →L[ℝ] E)` is a *variational-flow projection at level `k`* if

* `Y` is jointly `C^k` on the open neighbourhood
  `ball x₀ ρ ×ˢ Ioo (t₀ - T) (t₀ + T)`;
* `Y(x, t)` agrees with the variational linear map at `(x, t)` for the local flow `Φ`.

The second clause is captured via the coproduct identity for `fderiv ℝ Φ`, matching
the hypothesis of `contDiffOn_flow_succ_of_spatial_smooth`. -/
structure IsVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ) (T : ℝ) (ρ : ℝ≥0)
    (Y : E × ℝ → (E →L[ℝ] E)) (k : ℕ∞) : Prop where
  contDiffOn : ContDiffOn ℝ k Y ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T))
  fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
    fderiv ℝ Φ q = (Y q).coprod (timePieceFn f Φ q)

/-- Mono: a level-`k` variational-flow projection is also a level-`j` one for `j ≤ k`. -/
lemma IsVariationalFlowProjection.of_le {hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ}
    {T : ℝ} {ρ : ℝ≥0} {Y : E × ℝ → (E →L[ℝ] E)} {k j : ℕ∞}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) (hjk : j ≤ k) :
    IsVariationalFlowProjection hΦ T ρ Y j := by
  refine
  { contDiffOn := ?_,
    fderiv_eq := hY.fderiv_eq }
  have hjk' : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hjk
  exact hY.contDiffOn.of_le hjk'

end ProjectionPredicate

/-! ## The recursive `C^k` flow theorem

Given a single variational-flow projection at level `k`, the flow is jointly `C^{k+1}`
on the required open neighbourhood.  This is a direct application of
`contDiffOn_flow_succ_of_spatial_smooth` (from `FlowCk.lean`) plus an induction on `k`
to upgrade the conclusion to `C^{k+1}`.  We work with `k : ℕ` so that the induction is
clean.

The hypothesis is structured to consume a *sequence* of projections — at every level
`j < k+1` — each of which is jointly `C^j` and agrees with `fderiv ℝ Φ` via the
coproduct.  In practice, all the candidate projections are the same function (the
unique variational linear map), so a single hypothesis at the highest level `j = k`
provides them all.  We expose both flavours below. -/

section RecursiveFlow

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Recursive `C^k` flow theorem (single-projection form).**

If a function `Y : E × ℝ → (E →L[ℝ] E)` is a variational-flow projection at level `k`,
then the flow `Φ` is jointly `C^{k+1}` on the strictly-interior open neighbourhood. -/
theorem contDiffOn_flow_succ_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y k) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
  contDiffOn_flow_succ_of_spatial_smooth hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid
    hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck
    hY.contDiffOn hY.fderiv_eq

/-- **Recursive `C^k` flow theorem (sequence form).**

A sequence of variational-flow projections, one at each level `j < k`, gives the flow
joint `C^k` regularity on the strictly-interior open neighbourhood, for any `k : ℕ`.
This is a direct consequence of `contDiffOn_flow_of_spatial_smooth_seq` once the
sequence-of-`Y_seq` formulation is unpacked. -/
theorem contDiffOn_flow_of_isVariationalFlowProjection_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (Y_seq : ℕ → E × ℝ → (E →L[ℝ] E))
    (hY_seq : ∀ j : ℕ, j + 1 ≤ k →
      IsVariationalFlowProjection hΦ T ρ (Y_seq j) (j : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  refine contDiffOn_flow_of_spatial_smooth_seq hΦ hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
    hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_ ?_
  · intro j hj
    exact (hY_seq j hj).contDiffOn
  · intro j hj
    exact (hY_seq j hj).fderiv_eq

/-- **Recursive `C^k` flow theorem (single-projection top-level form).**

Given a *single* variational-flow projection at level `k - 1`, the flow is jointly
`C^k` on the strictly-interior open neighbourhood, for any `k : ℕ` with `1 ≤ k`.

The single hypothesis at the highest level `k - 1` is upgraded via `IsVariationalFlowProjection.of_le`
to a sequence at every intermediate level `j < k`.  In particular, the user only ever
needs to supply *one* projection — at level `k - 1`. -/
theorem contDiffOn_flow_of_isVariationalFlowProjection_top
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ) (hk : 1 ≤ k)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y ((k - 1 : ℕ) : ℕ∞)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Use the sequence formulation, with `Y_seq j := Y` for every `j`.  Each `Y` is
  -- a `IsVariationalFlowProjection` at level `j ≤ k - 1`, by mono.
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun _ => Y with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  have hj_le : (j : ℕ∞) ≤ ((k - 1 : ℕ) : ℕ∞) := by
    have h : j ≤ k - 1 := by omega
    exact_mod_cast h
  exact hY.of_le hj_le

end RecursiveFlow

/-! ## The `k = 2` specialization via V.2.c.2 on the augmented system

For `k = 2`, the variational-flow projection at level `1` reduces to *joint continuity*
of the variational linear map.  This is already proved in `FlowC1Continuous.lean` (in
the `continuousOn_fderiv_flow_of_isLocalFlow` proof), where the spatial piece of
`fderiv ℝ Φ` is shown to be jointly continuous on the strictly-interior neighbourhood.

But continuity is not enough at level `1`: we need `C^1`.  The `C^1` claim is the
target of the next layer of recursion: applying V.2.c.2 (`contDiffOn_flow_of_isLocalFlow`)
to the *augmented system* `augVF f` on `E × (E →L[ℝ] E)`.  V.2.c.2 requires the
augmented vector field to be jointly `C^1`, which is satisfied when `uncurry f` is
jointly `C^2` (`augVF_uncurry_contDiff` at level `k = 1`).

The application of V.2.c.2 to the augmented system requires the augmented system to
have a `IsLocalFlow` in its own right.  Since the augmented vector field is jointly
`C^1` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`, V.2.b.1's
`exists_isLocalFlow_of_contDiffOn_univ` (in `FlowC1.lean`) produces a local flow of the
augmented system around any base point `((x₀, id), t₀)`.

The remaining step — identifying the second component of the augmented flow with the
variational linear map — uses uniqueness of the linear ODE for the variational
solution, applied pointwise in `δ`.  This identification is captured by the
`IsVariationalFlowProjection` predicate above. -/

section LevelTwo

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Existence of a local flow for the augmented system.**

When `uncurry f` is jointly `C^2` on `Set.univ`, the augmented vector field `augVF f`
is jointly `C^1` on `Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))`.  V.2.b.1's
`exists_isLocalFlow_of_contDiffOn_univ` (`FlowC1.lean`) then produces a local flow of
the augmented system around any base point. -/
theorem exists_isLocalFlow_augVF_of_C2
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    (t₀ : ℝ) (p₀ : E × (E →L[ℝ] E)) :
    ∃ (R : ℝ≥0) (ε : ℝ) (_ : 0 < R) (_ : 0 < ε)
      (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)),
      IsLocalFlow (augVF f) t₀ p₀ R (t₀ - ε) (t₀ + ε) aΦ := by
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_augVF_C1 : ContDiffOn ℝ 1 (uncurry (augVF f))
      (Set.univ : Set (ℝ × (E × (E →L[ℝ] E)))) :=
    augVF_uncurry_contDiff (k := (1 : ℕ∞)) hf_succ
  exact exists_isLocalFlow_of_contDiffOn_univ (augVF f) h_augVF_C1 t₀ p₀

/-- **The `C^2` flow theorem, conditional on a `C^1` variational-flow projection.**

If `uncurry f` is jointly `C^2`, the local flow `Φ` is jointly `C^1` on the
strictly-interior open neighbourhood (by V.2.c.2), and a `C^1` variational-flow
projection `Y` at level `1` exists, then `Φ` is jointly `C^2` on the same
neighbourhood. -/
theorem contDiffOn_flow_of_isLocalFlow_C2_of_isVariationalFlowProjection
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    (hf_C2 : ContDiffOn ℝ 2 (uncurry f) (Set.univ : Set (ℝ × E)))
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {Y : E × ℝ → (E →L[ℝ] E)}
    (hY : IsVariationalFlowProjection hΦ T ρ Y 1) :
    ContDiffOn ℝ 2 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- First get `C^1` of `Φ` via V.2.c.2.
  have hf_C1 : ContDiffOn ℝ 1 (uncurry f) (Set.univ : Set (ℝ × E)) := by
    have h_le : ((1 : ℕ∞) : WithTop ℕ∞) ≤ ((2 : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (by decide : (1 : ℕ∞) ≤ 2)
    exact hf_C2.of_le h_le
  have hΦ_C1 : ContDiffOn ℝ 1 Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) :=
    contDiffOn_flow_of_isLocalFlow hΦ hf_C1 hT hT_lt_mid hT_mid_lt_out hM hMT_mid hsub hr'
      hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
  -- Now apply the recursive step at `k = 1`.
  have hf_succ : ContDiffOn ℝ ((1 : ℕ∞) + 1) (uncurry f) (Set.univ : Set (ℝ × E)) := by
    simpa using hf_C2
  have h_step := contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid
    hT_mid_lt_out hM hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd
    (k := (1 : ℕ∞)) hf_succ hΦ_C1 hY
  -- `(1 : ℕ∞) + 1 = 2`.
  simpa using h_step

end LevelTwo

/-! ## Pointwise variational identification of the augmented-flow second component

The connecting lemma between an `aΦ` (any candidate for the augmented flow) and the
variational linear map is: at every initial point `(x, id)` and time `t`, the second
component of `aΦ ⟨(x, id), t⟩` *equals* `variationalLinearMapAt(x, t)`.

This identification is a uniqueness statement for the variational-style linear ODE on
`E →L[ℝ] E`.  It is mathematically subtle because the augmented flow is given by
Picard–Lindelöf on a *closed ball* centered at `(x₀, id)` in the product norm, and the
variational linear map is the operator-norm closure of solutions on a closed ball of
`E` (per-`δ`).  Reconciling the two requires a pointwise-in-`δ` argument:

* Apply the augmented flow's second component to a fixed `δ ∈ E`: `(aΦ ⟨(x, id), t⟩).2 δ
  : E`.
* Show that as a function of `t`, this satisfies the variational ODE with initial
  variation `δ`.
* By the uniqueness lemma `IsVariationalSolutionOn.unique_Icc` (from
  `FlowC1Bridge.lean`), it agrees with `variationalSolutionFun(x, δ, t)`.
* Hence the operator `(aΦ ⟨(x, id), t⟩).2` agrees pointwise (and hence as a CLM, since
  both are CLMs on `E`) with `variationalLinearMapAt(x, t)`.

The technical work for this identification — propagating the second-component
derivative through the augmented ODE, exchanging the application to `δ` with the
time-derivative, and recognising the resulting curve as a variational solution —
mirrors the existing `variationalSolution` infrastructure but on the larger space.

We expose the *structural* result: a function `aΦ` that satisfies the augmented flow
ODE in the second component (in the sense that `t ↦ aΦ ⟨(x, id), t⟩.2 δ` solves the
variational ODE for each `δ`) gives a variational-flow projection of `Φ`.  The
verification of the second-component-ODE hypothesis is the natural way to plug in any
specific construction of the augmented flow (Picard–Lindelöf, ODE shooting, fixed
point on a function space, ...). -/

section AugFlowProjection

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- The **operator-valued curve from a candidate augmented flow**: given a candidate
`aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)`, the projection
`Y(x, t) := aΦ ⟨(x, id), t⟩.2 : E →L[ℝ] E` is the natural candidate for the spatial
piece of `fderiv ℝ Φ`. -/
def fromAugFlow (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)) :
    E × ℝ → (E →L[ℝ] E) :=
  fun q => (aΦ ⟨(q.1, ContinuousLinearMap.id ℝ E), q.2⟩).2

@[simp]
lemma fromAugFlow_apply (aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (x : E) (t : ℝ) :
    fromAugFlow aΦ (x, t) = (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2 := rfl

/-- **Joint smoothness of the projection.**  If the candidate `aΦ` is jointly `C^k` in
its arguments on an open set `Ω ⊆ (E × (E →L[ℝ] E)) × ℝ`, and the embedding
`(x, t) ↦ ((x, id), t)` maps `U ⊆ E × ℝ` into `Ω`, then the projection `fromAugFlow aΦ`
is jointly `C^k` on `U`. -/
theorem contDiffOn_fromAugFlow
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {k : ℕ∞} {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)} {U : Set (E × ℝ)}
    (haΦ : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2)) U Ω) :
    ContDiffOn ℝ k (fromAugFlow aΦ) U := by
  -- The embedding `(x, t) ↦ ((x, id), t)` is `C^∞`.
  have h_embed_smooth : ContDiff ℝ (k : ℕ∞)
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) := by
    refine ContDiff.prodMk ?_ contDiff_snd
    refine ContDiff.prodMk contDiff_fst ?_
    exact contDiff_const
  have h_embed_Ck : ContDiffOn ℝ k
      (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2) :
        E × ℝ → (E × (E →L[ℝ] E)) × ℝ) U :=
    h_embed_smooth.contDiffOn
  -- Composition.
  have hcomp : ContDiffOn ℝ k (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U :=
    haΦ.comp h_embed_Ck hmap
  -- Take the second component.
  have hsnd_smooth : ContDiff ℝ (k : ℕ∞)
      (fun p : E × (E →L[ℝ] E) => p.2) := contDiff_snd
  have hsnd_Ck : ContDiffOn ℝ k (fun p : E × (E →L[ℝ] E) => p.2)
      (Set.univ : Set (E × (E →L[ℝ] E))) := hsnd_smooth.contDiffOn
  have hmaps : MapsTo (aΦ ∘ (fun q : E × ℝ =>
      ((q.1, ContinuousLinearMap.id ℝ E), q.2))) U
      (Set.univ : Set (E × (E →L[ℝ] E))) := fun _ _ => mem_univ _
  have hfinal : ContDiffOn ℝ k
      ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2)))) U :=
    hsnd_Ck.comp hcomp hmaps
  -- The composition equals `fromAugFlow aΦ`.
  have heq : ((fun p : E × (E →L[ℝ] E) => p.2) ∘ (aΦ ∘ (fun q : E × ℝ =>
        ((q.1, ContinuousLinearMap.id ℝ E), q.2))))
      = fromAugFlow aΦ := by
    funext q
    rfl
  rw [heq] at hfinal
  exact hfinal

end AugFlowProjection

/-! ## Wrapping everything: the abstract unconditional `C^k` theorem

We now provide the cleanest abstract packaging of "from an augmented-flow input, the
ordinary flow is `C^{k+1}` jointly".

The input is a candidate `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` together with:

* a `ContDiffOn ℝ k` smoothness assertion on `aΦ` on an open neighbourhood;
* a pointwise variational identification of `(aΦ ⟨(x, id), t⟩).2` with the spatial
  partial Fréchet derivative of `Φ` (via the coproduct identity for `fderiv ℝ Φ`).

The conclusion is `ContDiffOn ℝ (k+1) Φ U` on the strictly-interior open neighbourhood.

Discharging the second hypothesis — variational identification — concretely requires
the uniqueness lemma for the linear ODE on `E →L[ℝ] E`.  When the underlying `aΦ` is
the Picard–Lindelöf flow of the augmented vector field `augVF f`, uniqueness follows
from `ODE_solution_unique_of_mem_Ioo` (Mathlib) applied at every fixed `δ ∈ E`.  We do
not embed that pointwise argument into the public signature here; it is left to the
caller, where any specific construction of the augmented flow can supply the
identification directly. -/

section UnconditionalAbstract

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Unconditional `C^{k+1}` flow theorem via an augmented-flow candidate.**

If we have a candidate `aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)` that is jointly
`C^k` on an open neighbourhood `Ω` of `((x₀, id), t₀)`, and whose second-component
projection `fromAugFlow aΦ` is a level-`k` variational-flow projection of `Φ`, then
`Φ` is jointly `C^{k+1}` on the strictly-interior open neighbourhood.

The hypothesis is exactly what an inductive argument on the augmented-flow theorem
delivers; the conclusion plugs back into the same induction at the next level.  In
particular, for `k = 1`, the augmented flow's `C^1` regularity is supplied by V.2.c.2
applied to the augmented vector field `augVF f` (provided `uncurry f` is `C^2`), and
the level-`1` variational identification is the pointwise variational ODE
identification described above. -/
theorem contDiffOn_flow_succ_of_augFlow_candidate
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    {k : ℕ∞}
    (hf_succ : ContDiffOn ℝ (k + 1) (uncurry f) (Set.univ : Set (ℝ × E)))
    (hΦ_Ck : ContDiffOn ℝ k Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)))
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {Ω : Set ((E × (E →L[ℝ] E)) × ℝ)}
    (haΦ_Ck : ContDiffOn ℝ k aΦ Ω)
    (hmap : MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) Ω)
    (h_fderiv_eq : ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow aΦ q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k + 1) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Build the variational-flow projection from `aΦ`.
  have hY_Ck : ContDiffOn ℝ k (fromAugFlow aΦ)
      ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := contDiffOn_fromAugFlow haΦ_Ck hmap
  have hY : IsVariationalFlowProjection hΦ T ρ (fromAugFlow aΦ) k :=
    { contDiffOn := hY_Ck, fderiv_eq := h_fderiv_eq }
  -- Plug into the recursive step.
  exact contDiffOn_flow_succ_of_isVariationalFlowProjection hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd hf_succ hΦ_Ck hY

end UnconditionalAbstract

/-! ## Aggregated public headline (general `k : ℕ`, parametrised by augmented-flow data)

The cleanest public form of the `C^k` flow theorem in this file consumes:

* the standard `IsLocalFlow` and `ContDiffOn` hypotheses on `f`;
* a *sequence* of augmented-flow candidates, one per level, each jointly `C^j` on its
  open neighbourhood with the variational identification at level `j`.

This is precisely the `Lsp_seq` interface from `FlowCk.lean`, restated through the
augmented-flow lens.  For practical use, this is the public theorem to call: it
factors out all the inductive machinery, and the user supplies only the
parametric-ODE-smoothness data of the augmented system. -/

section AggregatedPublic

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- **Public headline `C^k` flow theorem (general `k : ℕ`).**

This theorem packages the inductive structural argument cleanly: given a sequence of
augmented-flow candidates `aΦ_seq j`, each jointly `C^j` on its respective open
neighbourhood `Ω j`, whose second-component projections `fromAugFlow (aΦ_seq j)` satisfy
the variational identification with `fderiv ℝ Φ` at every level, the flow `Φ` is
jointly `C^k` on the strictly-interior open neighbourhood. -/
theorem contDiffOn_flow_of_augFlow_seq
    (hΦ : IsLocalFlow f t₀ x₀ r tmin tmax Φ)
    {T_out T_mid T M : ℝ} (hT : 0 < T) (hT_lt_mid : T < T_mid) (hT_mid_lt_out : T_mid < T_out)
    (hM : 0 ≤ M) (hMT_mid : M * T_mid < 1)
    (hsub : Icc (t₀ - T_out) (t₀ + T_out) ⊆ Icc tmin tmax)
    {ρ_out ρ_mid ρ : ℝ≥0} {r' : ℝ≥0} (hr' : 0 < r')
    (hρ_lt_mid : (ρ : ℝ) < (ρ_mid : ℝ)) (hρ_mid_lt_out : (ρ_mid : ℝ) < (ρ_out : ℝ))
    (hρρ' : (ρ_mid : ℝ) + (r' : ℝ) ≤ (r : ℝ))
    (hρ_out_le_r : (ρ_out : ℝ) ≤ (r : ℝ))
    (hA_bd : ∀ x ∈ closedBall x₀ (ρ_out : ℝ), ∀ τ ∈ Icc (t₀ - T_out) (t₀ + T_out),
      ‖fderiv ℝ (f τ) (Φ ⟨x, τ⟩)‖ ≤ M)
    (k : ℕ)
    (hf_Ck : ContDiffOn ℝ (k : ℕ∞) (uncurry f) (Set.univ : Set (ℝ × E)))
    (aΦ_seq : ℕ → (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E))
    (Ω_seq : ℕ → Set ((E × (E →L[ℝ] E)) × ℝ))
    (haΦ_Ck : ∀ j : ℕ, j + 1 ≤ k →
      ContDiffOn ℝ (j : ℕ∞) (aΦ_seq j) (Ω_seq j))
    (hmap_seq : ∀ j : ℕ, j + 1 ≤ k →
      MapsTo (fun q : E × ℝ => ((q.1, ContinuousLinearMap.id ℝ E), q.2))
        ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) (Ω_seq j))
    (h_fderiv_eq_seq : ∀ j : ℕ, j + 1 ≤ k →
      ∀ q ∈ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)),
      fderiv ℝ Φ q = (fromAugFlow (aΦ_seq j) q).coprod (timePieceFn f Φ q)) :
    ContDiffOn ℝ (k : ℕ∞) Φ ((ball x₀ (ρ : ℝ)) ×ˢ Ioo (t₀ - T) (t₀ + T)) := by
  -- Build the `Y_seq` by projection and supply it to the sequence theorem.
  set Y_seq : ℕ → E × ℝ → (E →L[ℝ] E) := fun j => fromAugFlow (aΦ_seq j) with hY_seq_def
  refine contDiffOn_flow_of_isVariationalFlowProjection_seq hΦ hT hT_lt_mid hT_mid_lt_out hM
    hMT_mid hsub hr' hρ_lt_mid hρ_mid_lt_out hρρ' hρ_out_le_r hA_bd k hf_Ck Y_seq ?_
  intro j hj
  refine
  { contDiffOn := contDiffOn_fromAugFlow (haΦ_Ck j hj) (hmap_seq j hj),
    fderiv_eq := h_fderiv_eq_seq j hj }

end AggregatedPublic

/-! ## Operator-valued variational solutions and the identification lemma

We now provide the pointwise variational identification connecting an operator-valued
curve that satisfies the linear ODE on `E →L[ℝ] E` with the per-`δ` variational
linear map.

Concretely: if `Z : ℝ → E →L[ℝ] E` is differentiable in `t` on `Icc (t₀ - T) (t₀ + T)`
with `Z(t₀) = id` and the operator-valued ODE `Z'(t) = A(t) ∘ Z(t)` where
`A(t) := fderiv ℝ (f t) (α t)`, then for every `δ ∈ E`, the curve `t ↦ Z(t) δ` is a
variational solution along `α` with initial variation `δ`.  Uniqueness on the closed
interval then identifies `Z(t) δ = variationalLinearMapAt(...) δ`, hence
`Z(t) = variationalLinearMapAt(...)` as CLMs by extensionality. -/

section OperatorVariational

variable {f : ℝ → E → E} {α : ℝ → E} {t₀ : ℝ}

/-- The application `Z(·) δ` of a CLM-curve `Z : ℝ → E →L[ℝ] E` to a fixed vector
`δ ∈ E` has, at every point where `Z` has the operator-valued derivative `Z'(t)`,
ordinary derivative `Z'(t) δ : E`. -/
lemma hasDerivWithinAt_apply {Z Z' : ℝ → (E →L[ℝ] E)} {s : Set ℝ} {t : ℝ} {δ : E}
    (hZ : HasDerivWithinAt Z (Z' t) s t) :
    HasDerivWithinAt (fun τ => Z τ δ) ((Z' t) δ) s t := by
  -- Apply the continuous linear map `apply δ : (E →L[ℝ] E) →L[ℝ] E` to `hZ`.
  set applyδ : (E →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E δ
  have happ : HasFDerivAt applyδ applyδ (Z t) := applyδ.hasFDerivAt
  have hZ_fd : HasFDerivWithinAt Z
      (ContinuousLinearMap.toSpanSingleton ℝ (Z' t)) s t := hZ.hasFDerivWithinAt
  have happ_fd := happ.comp_hasFDerivWithinAt t hZ_fd
  -- The composition has Fréchet derivative `applyδ.comp (toSpanSingleton (Z' t))`,
  -- which equals `toSpanSingleton ((Z' t) δ)`.
  have heq : applyδ.comp (ContinuousLinearMap.toSpanSingleton ℝ (Z' t))
      = ContinuousLinearMap.toSpanSingleton ℝ ((Z' t) δ) := by
    apply ContinuousLinearMap.ext
    intro r
    simp [applyδ, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply]
  rw [heq] at happ_fd
  -- Convert the Fréchet derivative back to the directional derivative.
  rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
  exact happ_fd

/-- **Operator-valued variational ODE → pointwise variational solutions.**

Suppose `Z : ℝ → E →L[ℝ] E` satisfies, on `Icc (t₀ - T) (t₀ + T)`:
* `Z(t₀) = id`,
* for every `t` in the interval, `Z` has the operator-valued derivative
  `(fderiv ℝ (f t) (α t)).comp (Z t)`.

Then for every `δ ∈ E`, the curve `t ↦ Z(t) δ` is a variational solution along the
central curve `α` with initial variation `δ` on the same interval. -/
theorem isVariationalSolutionOn_apply
    {T : ℝ}
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    (δ : E) :
    IsVariationalSolutionOn f α δ t₀ (fun s => Z s δ) (Icc (t₀ - T) (t₀ + T)) := by
  refine ⟨?_, ?_⟩
  · -- Initial value: `Z(t₀) δ = id δ = δ`.
    have : Z t₀ δ = ContinuousLinearMap.id ℝ E δ := by rw [hZ_init]
    simpa using this
  · intro t ht
    have hZ_d := hZ_deriv t ht
    have happ := hasDerivWithinAt_apply (Z := Z)
      (Z' := fun s => (fderiv ℝ (f s) (α s)).comp (Z s)) (δ := δ) hZ_d
    -- The derivative we get is `((fderiv ℝ (f t) (α t)).comp (Z t)) δ`, which equals
    -- `(fderiv ℝ (f t) (α t)) (Z t δ)` by `comp_apply`.
    have hsimp : ((fderiv ℝ (f t) (α t)).comp (Z t)) δ
        = (fderiv ℝ (f t) (α t)) (Z t δ) := by rfl
    rw [hsimp] at happ
    exact happ

/-- **Identification of `Z` with the variational linear map.**

Under the hypotheses of `isVariationalSolutionOn_apply` (operator-valued variational
ODE with `Z(t₀) = id`), at every `t ∈ Icc (t₀ - T) (t₀ + T)`, the CLM `Z t` agrees
with the variational linear map `variationalLinearMapAt(...)`.

The proof: by `isVariationalSolutionOn_apply`, `t ↦ Z t δ` is a variational solution
on the closed interval; by `variationalSolutionFun_isSolution`,
`t ↦ variationalSolutionFun(...) δ t` is also one; by `unique_Icc`, they agree at every
`t`; hence `Z t δ = variationalLinearMapAt(...) δ` for every `δ`; CLM extensionality
finishes. -/
theorem Z_eq_variationalLinearMapAt
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t) (α t)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖fderiv ℝ (f t) (α t)‖ ≤ M)
    {Z : ℝ → E →L[ℝ] E}
    (hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E)
    (hZ_deriv : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f t) (α t)).comp (Z t))
        (Icc (t₀ - T) (t₀ + T)) t)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    Z t = variationalLinearMapAt (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd ht := by
  -- Extensionality: show pointwise equality for every `δ`.
  apply ContinuousLinearMap.ext
  intro δ
  have h_Z_sol := isVariationalSolutionOn_apply (T := T) (Z := Z) hZ_init hZ_deriv δ
  have h_var_sol := variationalSolutionFun_isSolution hT hM hMT hA_cont hA_bd δ
  have h_eq := IsVariationalSolutionOn.unique_Icc hT hA_cont h_Z_sol h_var_sol
  have hZδ_t : Z t δ
      = variationalSolutionFun (f := f) (α := α) (t₀ := t₀) hT hM hMT hA_cont hA_bd δ t :=
    h_eq ht
  rw [hZδ_t]
  exact (variationalLinearMapAt_apply hT hM hMT hA_cont hA_bd ht δ).symm

end OperatorVariational

/-! ## Putting it all together: the augmented-flow-based projection lemma

Given an `IsLocalFlow` for the augmented vector field `augVF f`, the second component
of its orbit starting at `(x, id)` is, on the time interval `Icc (t₀ - T) (t₀ + T)`,
*exactly* the variational linear map.  This is the cleanest concrete way to discharge
the spatial-piece smoothness hypothesis at any level for which the augmented flow's
smoothness is available. -/

section AugFlowVariationalIdentification

variable {f : ℝ → E → E} {t₀ : ℝ} {x₀ : E} {r : ℝ≥0} {tmin tmax : ℝ} {Φ : E × ℝ → E}

/-- Given a local flow `aΦ` of the augmented vector field `augVF f`, started at
`(x, id)`, the second component is, at every time `t` in the operating interval,
equal to the variational linear map along the central orbit `t ↦ (aΦ ⟨(x, id), t⟩).1`.

The hypothesis structure mirrors `IsLocalFlow`: the augmented flow has, for every
`p ∈ closedBall p₀ R`, the derivative property
`(aΦ ⟨p, ·⟩)'(t) = augVF f t (aΦ ⟨p, t⟩)`.  Specialising to `p = (x, id)`, the second
component evolves by the operator-valued variational ODE, so
`Z_eq_variationalLinearMapAt` applies. -/
theorem augFlow_snd_eq_variationalLinearMapAt
    {aΦ : (E × (E →L[ℝ] E)) × ℝ → E × (E →L[ℝ] E)}
    {R : ℝ≥0} {tmin' tmax' : ℝ}
    {p₀ : E × (E →L[ℝ] E)}
    (haΦ : IsLocalFlow (augVF f) t₀ p₀ R tmin' tmax' aΦ)
    {T M : ℝ} (hT : 0 < T) (hM : 0 ≤ M) (hMT : M * T < 1)
    (hsub : Icc (t₀ - T) (t₀ + T) ⊆ Icc tmin' tmax')
    {x : E} (hx : (x, ContinuousLinearMap.id ℝ E) ∈ closedBall p₀ (R : ℝ))
    (hA_cont : ContinuousOn (fun t => fderiv ℝ (f t)
      ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)) (Icc (t₀ - T) (t₀ + T)))
    (hA_bd : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖fderiv ℝ (f t) ((aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).1)‖ ≤ M)
    {t : ℝ} (ht : t ∈ Icc (t₀ - T) (t₀ + T)) :
    (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), t⟩).2
      = variationalLinearMapAt (f := f)
          (α := fun s => (aΦ ⟨(x, ContinuousLinearMap.id ℝ E), s⟩).1) (t₀ := t₀)
          hT hM hMT hA_cont hA_bd ht := by
  -- The augmented orbit starting at `(x, id)`.
  set p : E × (E →L[ℝ] E) := (x, ContinuousLinearMap.id ℝ E) with hp_def
  set orbit : ℝ → E × (E →L[ℝ] E) := fun s => aΦ ⟨p, s⟩ with horbit_def
  -- The second component of the orbit.
  set Z : ℝ → E →L[ℝ] E := fun s => (orbit s).2 with hZ_def
  -- The central orbit (first component).
  set α : ℝ → E := fun s => (orbit s).1 with hα_def
  -- Initial value: at `t₀`, `orbit t₀ = p = (x, id)`, so `Z t₀ = id`.
  have hZ_init : Z t₀ = ContinuousLinearMap.id ℝ E := by
    have h_init : orbit t₀ = p := haΦ.apply_initial p hx
    change (orbit t₀).2 = ContinuousLinearMap.id ℝ E
    rw [h_init]
  -- The orbit satisfies the augmented ODE on `Icc tmin' tmax'`.
  have h_orbit_deriv : ∀ s ∈ Icc tmin' tmax',
      HasDerivWithinAt orbit (augVF f s (orbit s)) (Icc tmin' tmax') s :=
    fun s hs => haΦ.hasDerivWithinAt p hx s hs
  -- Specialise to `Icc (t₀ - T) (t₀ + T)` via mono.
  have h_orbit_deriv' : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt orbit (augVF f s (orbit s)) (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    exact (h_orbit_deriv s (hsub hs)).mono hsub
  -- Project to the second component.  `Z(s) = orbit(s).2`, so `Z'(s)` is the second
  -- component of `(orbit s)'`, which equals the second component of `augVF f s (orbit s)`.
  -- The second component of `augVF f s (orbit s)` is `(fderiv ℝ (f s) α(s)).comp Z(s)`.
  have hZ_deriv : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt Z ((fderiv ℝ (f s) (α s)).comp (Z s))
        (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have h := h_orbit_deriv' s hs
    -- Apply the continuous linear map `snd` to `h`'s Fréchet form, then convert back.
    set sndCLM : (E × (E →L[ℝ] E)) →L[ℝ] (E →L[ℝ] E) :=
      ContinuousLinearMap.snd ℝ E (E →L[ℝ] E)
    have h_fd := h.hasFDerivWithinAt
    have h_snd_at := (sndCLM.hasFDerivAt).comp_hasFDerivWithinAt s h_fd
    -- `h_snd_at` has derivative `sndCLM.comp (toSpanSingleton ℝ (orbit')) = toSpanSingleton ℝ (orbit').2`.
    have heq : sndCLM.comp (ContinuousLinearMap.toSpanSingleton ℝ (augVF f s (orbit s)))
        = ContinuousLinearMap.toSpanSingleton ℝ ((augVF f s (orbit s)).2) := by
      apply ContinuousLinearMap.ext
      intro r
      change (sndCLM (r • augVF f s (orbit s)))
        = r • (augVF f s (orbit s)).2
      change (r • augVF f s (orbit s)).2 = r • (augVF f s (orbit s)).2
      rfl
    rw [heq] at h_snd_at
    have h_aug_snd : (augVF f s (orbit s)).2
        = (fderiv ℝ (f s) (α s)).comp (Z s) := rfl
    rw [h_aug_snd] at h_snd_at
    -- Convert HasFDerivWithinAt back to HasDerivWithinAt.
    rw [hasDerivWithinAt_iff_hasFDerivWithinAt]
    exact h_snd_at
  exact Z_eq_variationalLinearMapAt hT hM hMT hA_cont hA_bd hZ_init hZ_deriv ht

end AugFlowVariationalIdentification

end Flow
end ODE
end Analysis
end RicciFlower

end
