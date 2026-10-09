import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# A locally trivial bundle over a closed interval is trivial

Lane C14-ROWS-S (input of FC40, blueprint `master207B.tex` B:7457: a circle-bundle surface over a
base interval is an annulus). A map `p : E → C` is locally trivial with fibre `F` in the form used
by the tree's circle-bundle statements (`isOpenMap_of_localTrivialization`): every `c` has a
neighbourhood `U` and a homeomorphism `p⁻¹(U) ≃ₜ U × F` over `U`. If `C` is homeomorphic to
`[0, 1]`, there is a global homeomorphism `E ≃ₜ C × F` over `C`.

Proof: a finite subdivision `0 = t₀ ≤ t₁ ≤ …` with each `[tₙ, tₙ₊₁]` inside one trivializing set
(`exists_monotone_Icc_subset_open_cover_unitInterval`); a trivialization over `{t ≤ tₙ}` is glued
to the local one over `[tₙ, tₙ₊₁]` after correcting the latter by the fibre homeomorphism over the
single common point `tₙ` (`glue_trivPair_RWS`). Trivializations are carried as pairs of maps
`φ : E → F`, `ψ : C → F → E` that are continuous on the relevant closed sets and mutually inverse
there.

* `exists_trivPair_of_homeomorph_RWS`, `trivPair_mono_RWS`, `glue_trivPair_RWS`;
* `exists_homeomorph_unitInterval_prod_RWS`: the case `C = [0, 1]`;
* `exists_homeomorph_prod_of_homeomorph_unitInterval_RWS`: `C ≃ₜ [0, 1]`.
-/

set_option autoImplicit false

open Set Topology Function
open scoped unitInterval

namespace DifferentialGeometry.Topology.Surface

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

section Pair

variable {B : Type*} [TopologicalSpace B]

/-- **A local trivialization as a pair of maps**: from `e : p⁻¹(U) ≃ₜ U × F` over `U`, maps
`φ : E → F`, `ψ : B → F → E` with `φ` continuous on `p⁻¹(U)`, `(t, f) ↦ ψ t f` continuous on
`U × F`, `p (ψ t f) = t`, `ψ (p x) (φ x) = x` and `φ (ψ t f) = f` over `U`. -/
theorem exists_trivPair_of_homeomorph_RWS [Nonempty F] (p : E → B) {U : Set B}
    (hU : U.Nonempty) (e : p ⁻¹' U ≃ₜ U × F) (he : ∀ x : p ⁻¹' U, ((e x).1 : B) = p x) :
    ∃ (φ : E → F) (ψ : B → F → E), ContinuousOn φ (p ⁻¹' U) ∧
      ContinuousOn (uncurry ψ) (U ×ˢ univ) ∧ (∀ t ∈ U, ∀ f, p (ψ t f) = t) ∧
      (∀ x, p x ∈ U → ψ (p x) (φ x) = x) ∧ (∀ t ∈ U, ∀ f, φ (ψ t f) = f) := by
  classical
  obtain ⟨t₀, ht₀⟩ := hU
  obtain ⟨φ, hφ⟩ : ∃ φ : E → F, ∀ x (h : p x ∈ U), φ x = (e ⟨x, h⟩).2 :=
    ⟨fun x => if h : p x ∈ U then (e ⟨x, h⟩).2 else Classical.arbitrary F,
      fun x h => dite_eq_left h⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : B → F → E, ∀ t (h : t ∈ U) f, ψ t f = (e.symm (⟨t, h⟩, f)).1 :=
    ⟨fun t f => if h : t ∈ U then (e.symm (⟨t, h⟩, f)).1 else (e.symm (⟨t₀, ht₀⟩, f)).1,
      fun t h f => dite_eq_left h⟩
  have hkey : ∀ (u : U) f, p (e.symm (u, f)).1 = u := fun u f => by
    have h := he (e.symm (u, f))
    rw [e.apply_symm_apply] at h
    exact h.symm
  refine ⟨φ, ψ, ?_, ?_, fun t ht f => ?_, fun x hx => ?_, fun t ht f => ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hres : (p ⁻¹' U).domRestrict φ = fun x => (e x).2 := funext fun x => hφ x.1 x.2
    rw [hres]
    exact continuous_snd.comp e.continuous
  · rw [continuousOn_iff_continuous_domRestrict]
    have hres : (U ×ˢ (univ : Set F)).domRestrict (uncurry ψ) =
        fun q => (e.symm (⟨q.1.1, q.2.1⟩, q.1.2)).1 :=
      funext fun q => hψ q.1.1 q.2.1 q.1.2
    rw [hres]
    refine continuous_subtype_val.comp (e.symm.continuous.comp ?_)
    exact (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  · rw [hψ t ht f]
    exact hkey ⟨t, ht⟩ f
  · rw [hφ x hx, hψ (p x) hx]
    have hq : e ⟨x, hx⟩ = (⟨p x, hx⟩, (e ⟨x, hx⟩).2) :=
      Prod.ext (Subtype.ext (he ⟨x, hx⟩)) rfl
    rw [← hq, e.symm_apply_apply]
  · have hy : p (ψ t f) ∈ U := by
      rw [hψ t ht f, hkey ⟨t, ht⟩ f]
      exact ht
    rw [hφ _ hy]
    have hsub : (⟨ψ t f, hy⟩ : p ⁻¹' U) = e.symm (⟨t, ht⟩, f) :=
      Subtype.ext (hψ t ht f)
    rw [hsub, e.apply_symm_apply]

/-- A trivialization pair over `T` is one over every `S ⊆ T`. -/
theorem trivPair_mono_RWS {p : E → B} {S T : Set B} (hST : S ⊆ T) {φ : E → F} {ψ : B → F → E}
    (h : ContinuousOn φ (p ⁻¹' T) ∧ ContinuousOn (uncurry ψ) (T ×ˢ univ) ∧
      (∀ t ∈ T, ∀ f, p (ψ t f) = t) ∧ (∀ x, p x ∈ T → ψ (p x) (φ x) = x) ∧
      (∀ t ∈ T, ∀ f, φ (ψ t f) = f)) :
    ContinuousOn φ (p ⁻¹' S) ∧ ContinuousOn (uncurry ψ) (S ×ˢ univ) ∧
      (∀ t ∈ S, ∀ f, p (ψ t f) = t) ∧ (∀ x, p x ∈ S → ψ (p x) (φ x) = x) ∧
      (∀ t ∈ S, ∀ f, φ (ψ t f) = f) :=
  ⟨h.1.mono (preimage_mono hST), h.2.1.mono (prod_mono hST le_rfl),
    fun t ht => h.2.2.1 t (hST ht), fun x hx => h.2.2.2.1 x (hST hx),
    fun t ht => h.2.2.2.2 t (hST ht)⟩

end Pair

/-- **Gluing two trivialization pairs over `[0, 1]`** along the single common point `a₀`
(`a = a₀ ≤ b`): pairs over `{t ≤ a}` and `{a ≤ t ≤ b}` give one over `{t ≤ b}`. The second pair is
corrected by the fibre homeomorphism `g = φ₁ ∘ ψ₂(a₀, ·)` (inverse `g' = φ₂ ∘ ψ₁(a₀, ·)`). -/
theorem glue_trivPair_RWS {p : E → I} (hp : Continuous p) {a b : ℝ} (hab : a ≤ b) (a₀ : I)
    (ha₀ : (a₀ : ℝ) = a) {φ₁ φ₂ : E → F} {ψ₁ ψ₂ : I → F → E}
    (h₁ : ContinuousOn φ₁ (p ⁻¹' {t | (t : ℝ) ≤ a}) ∧
      ContinuousOn (uncurry ψ₁) ({t : I | (t : ℝ) ≤ a} ×ˢ univ) ∧
      (∀ t ∈ {t : I | (t : ℝ) ≤ a}, ∀ f, p (ψ₁ t f) = t) ∧
      (∀ x, p x ∈ {t : I | (t : ℝ) ≤ a} → ψ₁ (p x) (φ₁ x) = x) ∧
      (∀ t ∈ {t : I | (t : ℝ) ≤ a}, ∀ f, φ₁ (ψ₁ t f) = f))
    (h₂ : ContinuousOn φ₂ (p ⁻¹' {t | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}) ∧
      ContinuousOn (uncurry ψ₂) ({t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} ×ˢ univ) ∧
      (∀ t ∈ {t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}, ∀ f, p (ψ₂ t f) = t) ∧
      (∀ x, p x ∈ {t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} → ψ₂ (p x) (φ₂ x) = x) ∧
      (∀ t ∈ {t : I | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b}, ∀ f, φ₂ (ψ₂ t f) = f)) :
    ∃ (φ : E → F) (ψ : I → F → E), ContinuousOn φ (p ⁻¹' {t | (t : ℝ) ≤ b}) ∧
      ContinuousOn (uncurry ψ) ({t : I | (t : ℝ) ≤ b} ×ˢ univ) ∧
      (∀ t ∈ {t : I | (t : ℝ) ≤ b}, ∀ f, p (ψ t f) = t) ∧
      (∀ x, p x ∈ {t : I | (t : ℝ) ≤ b} → ψ (p x) (φ x) = x) ∧
      (∀ t ∈ {t : I | (t : ℝ) ≤ b}, ∀ f, φ (ψ t f) = f) := by
  classical
  obtain ⟨hφ₁, hψ₁, h31, h41, h51⟩ := h₁
  obtain ⟨hφ₂, hψ₂, h32, h42, h52⟩ := h₂
  set S₁ : Set I := {t | (t : ℝ) ≤ a} with hS₁
  set S₂ : Set I := {t | a ≤ (t : ℝ) ∧ (t : ℝ) ≤ b} with hS₂
  have ha₁ : a₀ ∈ S₁ := le_of_eq ha₀
  have ha₂ : a₀ ∈ S₂ := ⟨ha₀.ge, ha₀.le.trans hab⟩
  have hpa : ∀ x, (p x : ℝ) = a → p x = a₀ := fun x hx => Subtype.ext (hx.trans ha₀.symm)
  -- the fibre maps over `a₀` and their continuity
  have hc₁ : Continuous (ψ₁ a₀) :=
    hψ₁.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨ha₁, trivial⟩
  have hc₂ : Continuous (ψ₂ a₀) :=
    hψ₂.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨ha₂, trivial⟩
  have hg : Continuous fun f => φ₁ (ψ₂ a₀ f) := by
    refine hφ₁.comp_continuous hc₂ fun f => ?_
    change p (ψ₂ a₀ f) ∈ S₁
    rw [h32 a₀ ha₂ f]
    exact ha₁
  have hg' : Continuous fun f => φ₂ (ψ₁ a₀ f) := by
    refine hφ₂.comp_continuous hc₁ fun f => ?_
    change p (ψ₁ a₀ f) ∈ S₂
    rw [h31 a₀ ha₁ f]
    exact ha₂
  have hgg' : ∀ f, φ₁ (ψ₂ a₀ (φ₂ (ψ₁ a₀ f))) = f := fun f => by
    have hx : p (ψ₁ a₀ f) = a₀ := h31 a₀ ha₁ f
    have h := h42 (ψ₁ a₀ f) (by rw [hx]; exact ha₂)
    rw [hx] at h
    rw [h, h51 a₀ ha₁ f]
  have hg'g : ∀ f, φ₂ (ψ₁ a₀ (φ₁ (ψ₂ a₀ f))) = f := fun f => by
    have hx : p (ψ₂ a₀ f) = a₀ := h32 a₀ ha₂ f
    have h := h41 (ψ₂ a₀ f) (by rw [hx]; exact ha₁)
    rw [hx] at h
    rw [h, h52 a₀ ha₂ f]
  -- agreement over the common fibre
  have hovφ : ∀ x, p x = a₀ → φ₁ x = φ₁ (ψ₂ a₀ (φ₂ x)) := fun x hx => by
    have h := h42 x (by rw [hx]; exact ha₂)
    rw [hx] at h
    rw [h]
  have hovψ : ∀ f, ψ₁ a₀ f = ψ₂ a₀ (φ₂ (ψ₁ a₀ f)) := fun f => by
    have hx : p (ψ₁ a₀ f) = a₀ := h31 a₀ ha₁ f
    have h := h42 (ψ₁ a₀ f) (by rw [hx]; exact ha₂)
    rw [hx] at h
    rw [h]
  let φ : E → F := fun x => if (p x : ℝ) ≤ a then φ₁ x else φ₁ (ψ₂ a₀ (φ₂ x))
  let ψ : I → F → E := fun t f => if (t : ℝ) ≤ a then ψ₁ t f else ψ₂ t (φ₂ (ψ₁ a₀ f))
  have hSu : {t : I | (t : ℝ) ≤ b} = S₁ ∪ S₂ := by
    ext t
    simp only [hS₁, hS₂, mem_ofPred_eq, mem_union]
    constructor
    · intro ht
      by_cases hta : (t : ℝ) ≤ a
      · exact Or.inl hta
      · exact Or.inr ⟨(lt_of_not_ge hta).le, ht⟩
    · rintro (ht | ht)
      · exact ht.trans hab
      · exact ht.2
  have hcl₁ : IsClosed (p ⁻¹' S₁) :=
    isClosed_le (continuous_subtype_val.comp hp) continuous_const
  have hcl₂ : IsClosed (p ⁻¹' S₂) :=
    (isClosed_le continuous_const (continuous_subtype_val.comp hp)).inter
      (isClosed_le (continuous_subtype_val.comp hp) continuous_const)
  have hcl₁' : IsClosed (S₁ ×ˢ (univ : Set F)) :=
    (isClosed_le continuous_subtype_val continuous_const).prod isClosed_univ
  have hcl₂' : IsClosed (S₂ ×ˢ (univ : Set F)) :=
    ((isClosed_le continuous_const continuous_subtype_val).inter
      (isClosed_le continuous_subtype_val continuous_const)).prod isClosed_univ
  refine ⟨φ, ψ, ?_, ?_, fun t ht f => ?_, fun x hx => ?_, fun t ht f => ?_⟩
  · rw [hSu, preimage_union]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hcl₁ hcl₂
    · exact hφ₁.congr fun x hx => ite_eq_left hx
    · refine (hg.comp_continuousOn hφ₂).congr fun x hx => ?_
      change (if (p x : ℝ) ≤ a then φ₁ x else φ₁ (ψ₂ a₀ (φ₂ x))) = φ₁ (ψ₂ a₀ (φ₂ x))
      by_cases hxa : (p x : ℝ) ≤ a
      · rw [ite_eq_left hxa]
        exact hovφ x (hpa x (le_antisymm hxa hx.1))
      · rw [ite_eq_right hxa]
  · rw [hSu, union_prod]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hcl₁' hcl₂'
    · exact hψ₁.congr fun q hq => ite_eq_left hq.1
    · have hcomp : ContinuousOn (fun q : I × F => uncurry ψ₂ (q.1, φ₂ (ψ₁ a₀ q.2)))
          (S₂ ×ˢ univ) :=
        hψ₂.comp (continuous_fst.prodMk (hg'.comp continuous_snd)).continuousOn
          fun q hq => ⟨hq.1, trivial⟩
      refine hcomp.congr fun q hq => ?_
      change (if (q.1 : ℝ) ≤ a then ψ₁ q.1 q.2 else ψ₂ q.1 (φ₂ (ψ₁ a₀ q.2))) =
        ψ₂ q.1 (φ₂ (ψ₁ a₀ q.2))
      by_cases hqa : (q.1 : ℝ) ≤ a
      · rw [ite_eq_left hqa]
        have hq1 : q.1 = a₀ := Subtype.ext ((le_antisymm hqa hq.1.1).trans ha₀.symm)
        rw [hq1]
        exact hovψ q.2
      · rw [ite_eq_right hqa]
  · change p (if (t : ℝ) ≤ a then ψ₁ t f else ψ₂ t (φ₂ (ψ₁ a₀ f))) = t
    by_cases hta : (t : ℝ) ≤ a
    · rw [ite_eq_left hta]
      exact h31 t hta f
    · rw [ite_eq_right hta]
      exact h32 t ⟨(lt_of_not_ge hta).le, ht⟩ _
  · change (if (p x : ℝ) ≤ a then ψ₁ (p x) (φ x) else ψ₂ (p x) (φ₂ (ψ₁ a₀ (φ x)))) = x
    by_cases hxa : (p x : ℝ) ≤ a
    · rw [ite_eq_left hxa]
      change ψ₁ (p x) (if (p x : ℝ) ≤ a then φ₁ x else φ₁ (ψ₂ a₀ (φ₂ x))) = x
      rw [ite_eq_left hxa]
      exact h41 x hxa
    · rw [ite_eq_right hxa]
      change ψ₂ (p x) (φ₂ (ψ₁ a₀ (if (p x : ℝ) ≤ a then φ₁ x else φ₁ (ψ₂ a₀ (φ₂ x))))) = x
      rw [ite_eq_right hxa, hg'g]
      exact h42 x ⟨(lt_of_not_ge hxa).le, hx⟩
  · change (if (p (ψ t f) : ℝ) ≤ a then φ₁ (ψ t f) else φ₁ (ψ₂ a₀ (φ₂ (ψ t f)))) = f
    by_cases hta : (t : ℝ) ≤ a
    · have hψt : ψ t f = ψ₁ t f := ite_eq_left hta
      rw [hψt, h31 t hta f, ite_eq_left hta]
      exact h51 t hta f
    · have ht2 : t ∈ S₂ := ⟨(lt_of_not_ge hta).le, ht⟩
      have hψt : ψ t f = ψ₂ t (φ₂ (ψ₁ a₀ f)) := ite_eq_right hta
      rw [hψt, h32 t ht2 _, ite_eq_right hta, h52 t ht2 _]
      exact hgg' f

/-- **A locally trivial bundle over `[0, 1]` is trivial**: for continuous `p : E → [0, 1]` with
local trivializations `p⁻¹(U) ≃ₜ U × F` over `U` (`F` nonempty), there is a homeomorphism
`Θ : E ≃ₜ [0, 1] × F` with `(Θ x).1 = p x`. -/
theorem exists_homeomorph_unitInterval_prod_RWS [Nonempty F] (p : E → I) (hp : Continuous p)
    (hloc : ∀ t, ∃ U ∈ 𝓝 t, ∃ e : p ⁻¹' U ≃ₜ U × F, ∀ x : p ⁻¹' U, ((e x).1 : I) = p x) :
    ∃ Θ : E ≃ₜ I × F, ∀ x, (Θ x).1 = p x := by
  choose U hU e he using hloc
  obtain ⟨T, hT0, hTm, ⟨m, hm⟩, hTsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (c := fun t => interior (U t)) (fun _ => isOpen_interior)
    (fun t _ => mem_iUnion.2 ⟨t, mem_interior_iff_mem_nhds.2 (hU t)⟩)
  have hpair : ∀ t, ∃ (φ : E → F) (ψ : I → F → E), ContinuousOn φ (p ⁻¹' U t) ∧
      ContinuousOn (uncurry ψ) (U t ×ˢ univ) ∧ (∀ s ∈ U t, ∀ f, p (ψ s f) = s) ∧
      (∀ x, p x ∈ U t → ψ (p x) (φ x) = x) ∧ (∀ s ∈ U t, ∀ f, φ (ψ s f) = f) := fun t =>
    exists_trivPair_of_homeomorph_RWS p ⟨t, mem_of_mem_nhds (hU t)⟩ (e t) (he t)
  have hstep : ∀ n, ∃ (φ : E → F) (ψ : I → F → E),
      ContinuousOn φ (p ⁻¹' {s | (s : ℝ) ≤ T n}) ∧
      ContinuousOn (uncurry ψ) ({s : I | (s : ℝ) ≤ T n} ×ˢ univ) ∧
      (∀ s ∈ {s : I | (s : ℝ) ≤ T n}, ∀ f, p (ψ s f) = s) ∧
      (∀ x, p x ∈ {s : I | (s : ℝ) ≤ T n} → ψ (p x) (φ x) = x) ∧
      (∀ s ∈ {s : I | (s : ℝ) ≤ T n}, ∀ f, φ (ψ s f) = f) := by
    intro n
    induction n with
    | zero =>
      obtain ⟨i, hi⟩ := hTsub 0
      obtain ⟨φ, ψ, hP⟩ := hpair i
      refine ⟨φ, ψ, trivPair_mono_RWS (fun s hs => ?_) hP⟩
      have hs0 : s = T 0 := by
        rw [hT0]
        exact Subtype.ext (le_antisymm (by rw [hT0] at hs; exact hs) s.2.1)
      exact interior_subset (hi ⟨hs0.ge, hs0.le.trans (hTm (Nat.zero_le 1))⟩)
    | succ n ih =>
      obtain ⟨φ₁, ψ₁, h₁⟩ := ih
      obtain ⟨i, hi⟩ := hTsub n
      obtain ⟨φ₂, ψ₂, hP⟩ := hpair i
      have h₂ := trivPair_mono_RWS (S := {s : I | (T n : ℝ) ≤ s ∧ (s : ℝ) ≤ T (n + 1)})
        (fun s hs => interior_subset (hi ⟨hs.1, hs.2⟩)) hP
      exact glue_trivPair_RWS hp (hTm (Nat.le_succ n)) (T n) rfl h₁ h₂
  obtain ⟨φ, ψ, hP⟩ := hstep m
  have huniv : (univ : Set I) ⊆ {s : I | (s : ℝ) ≤ T m} := fun s _ => by
    change (s : ℝ) ≤ T m
    rw [hm m le_rfl]
    exact s.2.2
  obtain ⟨hφ, hψ, h3, h4, h5⟩ := trivPair_mono_RWS huniv hP
  rw [preimage_univ, continuousOn_univ] at hφ
  rw [univ_prod_univ, continuousOn_univ] at hψ
  exact ⟨{ toFun := fun x => (p x, φ x)
           invFun := fun q => ψ q.1 q.2
           left_inv := fun x => h4 x (mem_univ _)
           right_inv := fun q => Prod.ext (h3 q.1 (mem_univ _) q.2) (h5 q.1 (mem_univ _) q.2)
           continuous_toFun := hp.prodMk hφ
           continuous_invFun := hψ }, fun _ => rfl⟩

/-- **A locally trivial bundle over a space homeomorphic to `[0, 1]` is trivial.** -/
theorem exists_homeomorph_prod_of_homeomorph_unitInterval_RWS [Nonempty F] {C : Type*}
    [TopologicalSpace C] (φC : C ≃ₜ I) (p : E → C) (hp : Continuous p)
    (hloc : ∀ c, ∃ U ∈ 𝓝 c, ∃ e : p ⁻¹' U ≃ₜ U × F, ∀ x : p ⁻¹' U, ((e x).1 : C) = p x) :
    ∃ Θ : E ≃ₜ C × F, ∀ x, (Θ x).1 = p x := by
  have hloc' : ∀ t : I, ∃ U ∈ 𝓝 t, ∃ e : (φC ∘ p) ⁻¹' U ≃ₜ U × F,
      ∀ x : (φC ∘ p) ⁻¹' U, ((e x).1 : I) = (φC ∘ p) x := by
    intro t
    obtain ⟨U, hU, e, he⟩ := hloc (φC.symm t)
    have hU' : φC '' U ∈ 𝓝 t := by
      have h := φC.isOpenMap.image_mem_nhds hU
      rwa [φC.apply_symm_apply] at h
    have hset : (φC ∘ p) ⁻¹' (φC '' U) = p ⁻¹' U := by
      ext x
      simp only [mem_preimage, comp_apply, φC.injective.mem_set_image]
    refine ⟨φC '' U, hU', (Homeomorph.setCongr hset).trans
      (e.trans ((φC.image U).prodCongr (Homeomorph.refl F))), fun x => ?_⟩
    change φC ((e ⟨x.1, _⟩).1 : C) = φC (p x.1)
    rw [he]
  obtain ⟨Θ', hΘ'⟩ := exists_homeomorph_unitInterval_prod_RWS (φC ∘ p) (φC.continuous.comp hp)
    hloc'
  refine ⟨Θ'.trans (φC.symm.prodCongr (Homeomorph.refl F)), fun x => ?_⟩
  change φC.symm (Θ' x).1 = p x
  rw [hΘ', comp_apply, φC.symm_apply_apply]

end DifferentialGeometry.Topology.Surface
