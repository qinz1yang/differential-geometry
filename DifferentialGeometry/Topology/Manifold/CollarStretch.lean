import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Stretching an internal collar over an external one

Let `X` be a manifold with an internal half collar `c : B × [0, 1) → X` of (a union of components
of) its boundary, `B` compact and boundaryless. Suppose `X` sits in a manifold `Y` through a map
`F` which is a local diffeomorphism off the collar, and that `Y` contains an external collar
`ℓ : B × [0, 1 + a) → Y`, a local diffeomorphism and injective on its domain, which continues the
collar of `X`: `F (c (b, s)) = ℓ (b, s + a)`. If `Y` is the disjoint union of the image of `F`
off the collar and the image of `ℓ`, then `X` and `Y` are diffeomorphic
(`exists_diffeomorph_collarStretch`): this is `X ∪_∂ (∂X × [0, a]) ≅ X`.

The diffeomorphism is `F` off the half collar `c (B × [0, 1/2])` and `ℓ ∘ (id × g) ∘ c⁻¹` on the
collar, where the stretch `g = collarStretch a`, `g s = s + a φ (2 s)` with `φ` the smooth
transition, is the identity near `0`, the translation by `a` on `[1/2, ∞)`, and has derivative
`≥ 1`; so it is a diffeomorphism of the line (`collarStretchIso`, smooth inverse by
`Homeomorph.contDiff_symm_deriv`) preserving `[0, ∞)` (`halfStretch`). The two formulas agree on
`c (B × (1/2, 1))`, the map is a local diffeomorphism everywhere and bijective, hence a
diffeomorphism. It is `F` outside `c (B × [0, 1/2])` and sends `c (b, 0)` to `ℓ (b, 0)`.

`isLocalDiffeomorphAt_of_comp` cancels a local diffeomorphism on the left: if `g` and `g ∘ f` are
local diffeomorphisms at `f x` and `x` and `f` is continuous at `x`, so is `f`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

def collarStretch (a s : ℝ) : ℝ := s + a * Real.smoothTransition (2 * s)

theorem collarStretch_of_nonpos (a : ℝ) {s : ℝ} (hs : s ≤ 0) : collarStretch a s = s := by
  rw [collarStretch, Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero, add_zero]

theorem collarStretch_of_half_le (a : ℝ) {s : ℝ} (hs : 1 / 2 ≤ s) :
    collarStretch a s = s + a := by
  rw [collarStretch, Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem contDiff_collarStretch (a : ℝ) : ContDiff ℝ ∞ (collarStretch a) :=
  contDiff_id.add (contDiff_const.mul
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_const.mul contDiff_id)))

theorem strictMono_collarStretch {a : ℝ} (ha : 0 ≤ a) : StrictMono (collarStretch a) := by
  intro s t hst
  have h := Real.smoothTransition.monotone (show 2 * s ≤ 2 * t by linarith)
  have h' := mul_le_mul_of_nonneg_left h ha
  unfold collarStretch
  linarith

theorem hasDerivAt_collarStretch (a s : ℝ) :
    HasDerivAt (collarStretch a) (1 + a * (deriv Real.smoothTransition (2 * s) * 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => 2 * s) 2 s := by
    simpa using (hasDerivAt_id s).const_mul (2 : ℝ)
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 * s)) (2 * s) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) (2 * s)).hasDerivAt
  exact (hasDerivAt_id s).add ((h2.comp s h1).const_mul a)

theorem collarStretch_deriv_ne_zero {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    1 + a * (deriv Real.smoothTransition (2 * s) * 2) ≠ 0 := by
  have h : 0 ≤ deriv Real.smoothTransition (2 * s) := Real.smoothTransition.monotone.deriv_nonneg
  have h' := mul_nonneg ha (mul_nonneg h (show (0 : ℝ) ≤ 2 by norm_num))
  exact ne_of_gt (by linarith)

theorem surjective_collarStretch {a : ℝ} (ha : 0 ≤ a) : Surjective (collarStretch a) := by
  refine (contDiff_collarStretch a).continuous.surjective ?_ ?_
  · refine tendsto_atTop_mono (fun s => ?_) tendsto_id
    have h := mul_nonneg ha (Real.smoothTransition.nonneg (2 * s))
    change s ≤ s + a * Real.smoothTransition (2 * s)
    linarith
  · refine tendsto_atBot_mono (fun s => ?_) (tendsto_atBot_add_const_right _ a tendsto_id)
    have h := mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (2 * s)) ha
    change s + a * Real.smoothTransition (2 * s) ≤ id s + a
    simp only [id, mul_one] at h ⊢
    linarith

def collarStretchIso {a : ℝ} (ha : 0 ≤ a) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (collarStretch a) (strictMono_collarStretch ha)
    (surjective_collarStretch ha)

theorem collarStretchIso_apply {a : ℝ} (ha : 0 ≤ a) (s : ℝ) :
    collarStretchIso ha s = collarStretch a s := rfl

theorem contDiff_collarStretchIso_symm {a : ℝ} (ha : 0 ≤ a) :
    ContDiff ℝ ∞ (collarStretchIso ha).symm :=
  Homeomorph.contDiff_symm_deriv (collarStretchIso ha).toHomeomorph
    (collarStretch_deriv_ne_zero ha) (hasDerivAt_collarStretch a) (contDiff_collarStretch a)

theorem collarStretch_zero (a : ℝ) : collarStretch a 0 = 0 :=
  collarStretch_of_nonpos a le_rfl

theorem collarStretch_one (a : ℝ) : collarStretch a 1 = 1 + a :=
  collarStretch_of_half_le a (by norm_num)

theorem collarStretch_nonneg {a : ℝ} (ha : 0 ≤ a) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ collarStretch a s := by
  rw [← collarStretch_zero a]
  exact (strictMono_collarStretch ha).monotone hs

theorem collarStretchIso_symm_nonneg {a : ℝ} (ha : 0 ≤ a) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ (collarStretchIso ha).symm u := by
  have h := (collarStretchIso ha).symm.monotone hu
  rwa [← collarStretch_zero a, ← collarStretchIso_apply ha, OrderIso.symm_apply_apply] at h

theorem collarStretchIso_symm_lt_one {a : ℝ} (ha : 0 ≤ a) {u : ℝ} (hu : u < 1 + a) :
    (collarStretchIso ha).symm u < 1 := by
  have h := (collarStretchIso ha).symm.strictMono hu
  rwa [← collarStretch_one a, ← collarStretchIso_apply ha, OrderIso.symm_apply_apply] at h

private theorem lift_val (t : ℝ) : (halfSpaceOneLift t).val 0 = max t 0 := rfl

private theorem lift_coord (h : EuclideanHalfSpace 1) : halfSpaceOneLift (h.val 0) = h := by
  apply Subtype.ext
  apply PiLp.ext
  intro i
  rw [Subsingleton.elim i 0]
  exact max_eq_left h.2

private theorem lift_val_of_nonneg {t : ℝ} (ht : 0 ≤ t) : (halfSpaceOneLift t).val 0 = t :=
  max_eq_left ht

private theorem continuous_lift : Continuous halfSpaceOneLift :=
  (𝓡∂ 1).continuous_symm.comp (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.continuous

def halfStretch {a : ℝ} (ha : 0 ≤ a) :
    EuclideanHalfSpace 1 ≃ₘ⟮𝓡∂ 1, 𝓡∂ 1⟯ EuclideanHalfSpace 1 where
  toFun h := halfSpaceOneLift (collarStretch a (h.val 0))
  invFun h := halfSpaceOneLift ((collarStretchIso ha).symm (h.val 0))
  left_inv h := by
    change halfSpaceOneLift ((collarStretchIso ha).symm
      ((halfSpaceOneLift (collarStretch a (h.val 0))).val 0)) = h
    rw [lift_val_of_nonneg (collarStretch_nonneg ha h.2), ← collarStretchIso_apply ha,
      OrderIso.symm_apply_apply, lift_coord]
  right_inv h := by
    change halfSpaceOneLift (collarStretch a
      ((halfSpaceOneLift ((collarStretchIso ha).symm (h.val 0))).val 0)) = h
    rw [lift_val_of_nonneg (collarStretchIso_symm_nonneg ha h.2), ← collarStretchIso_apply ha,
      OrderIso.apply_symm_apply, lift_coord]
  contMDiff_toFun := contMDiffOn_halfSpaceOneLift.comp_contMDiff
    ((contDiff_collarStretch a).contMDiff.comp contMDiff_halfSpaceOneCoordinate)
    (fun h => collarStretch_nonneg ha h.2)
  contMDiff_invFun := contMDiffOn_halfSpaceOneLift.comp_contMDiff
    ((contDiff_collarStretchIso_symm ha).contMDiff.comp contMDiff_halfSpaceOneCoordinate)
    (fun h => collarStretchIso_symm_nonneg ha h.2)

theorem halfStretch_apply {a : ℝ} (ha : 0 ≤ a) (h : EuclideanHalfSpace 1) :
    halfStretch ha h = halfSpaceOneLift (collarStretch a (h.val 0)) := rfl

theorem halfStretch_symm_apply {a : ℝ} (ha : 0 ≤ a) (h : EuclideanHalfSpace 1) :
    (halfStretch ha).symm h = halfSpaceOneLift ((collarStretchIso ha).symm (h.val 0)) := rfl

section Cancel

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E''] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E'' H''} {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]

theorem isLocalDiffeomorphAt_of_comp {f : M → N} {g : N → P} {x : M} (hf : ContinuousAt f x)
    (hg : IsLocalDiffeomorphAt J K ∞ g (f x)) (hgf : IsLocalDiffeomorphAt I K ∞ (g ∘ f) x) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨φ, hφx, hφ⟩ := hg
  obtain ⟨ψ, hψx, hψ⟩ := hgf
  have hU : ∀ᶠ y in 𝓝 x, f y ∈ φ.source ∧ y ∈ ψ.source :=
    Filter.Eventually.and (hf.preimage_mem_nhds (φ.open_source.mem_nhds hφx))
      (ψ.open_source.mem_nhds hψx)
  have key : ∀ y, f y ∈ φ.source → y ∈ ψ.source → ψ y = φ (f y) := fun y h1 h2 =>
    (hψ h2).symm.trans (hφ h1)
  have hx : x ∈ (ψ.trans φ.symm).source := by
    rw [PartialDiffeomorph.trans_source]
    refine ⟨hψx, ?_⟩
    change ψ x ∈ φ.target
    rw [key x hφx hψx]
    exact φ.map_source' hφx
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
    ((ψ.trans φ.symm).isLocalDiffeomorphAt I J ∞ hx)
  filter_upwards [hU] with y hy
  rw [PartialDiffeomorph.trans_apply, key y hy.1 hy.2, PartialDiffeomorph.symm_apply_apply φ hy.1]

end Cancel

section Stretch

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {K : ModelWithCorners ℝ EB HB} {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} {Y : Type*} [TopologicalSpace Y] [ChartedSpace H' Y]

def collarStretchMap {a : ℝ} (ha : 0 ≤ a) [IsManifold K ∞ B] :
    (B × EuclideanHalfSpace 1) ≃ₘ⟮K.prod (𝓡∂ 1), K.prod (𝓡∂ 1)⟯ (B × EuclideanHalfSpace 1) :=
  (Diffeomorph.refl K B ∞).prodCongr (halfStretch ha)

theorem collarStretchMap_apply {a : ℝ} (ha : 0 ≤ a) [IsManifold K ∞ B]
    (p : B × EuclideanHalfSpace 1) :
    collarStretchMap (K := K) ha p = (p.1, halfSpaceOneLift (collarStretch a (p.2.val 0))) :=
  rfl

theorem collarStretchMap_symm_apply {a : ℝ} (ha : 0 ≤ a) [IsManifold K ∞ B]
    (p : B × EuclideanHalfSpace 1) :
    (collarStretchMap (K := K) ha).symm p =
      (p.1, halfSpaceOneLift ((collarStretchIso ha).symm (p.2.val 0))) :=
  rfl

theorem exists_diffeomorph_collarStretch [IsManifold K ∞ B] [CompactSpace B] [T2Space X]
    (c : PartialDiffeomorph (K.prod (𝓡∂ 1)) I (B × EuclideanHalfSpace 1) X ∞)
    (hc : c.source = {p | p.2.val 0 < 1}) (F : X → Y) (ℓ : B × EuclideanHalfSpace 1 → Y)
    {a : ℝ} (ha : 0 ≤ a)
    (hFc : ∀ p : B × EuclideanHalfSpace 1, p.2.val 0 < 1 →
      F (c p) = ℓ (p.1, halfSpaceOneLift (p.2.val 0 + a)))
    (hℓ : ∀ q : B × EuclideanHalfSpace 1, q.2.val 0 < 1 + a →
      IsLocalDiffeomorphAt (K.prod (𝓡∂ 1)) J ∞ ℓ q)
    (hF : ∀ x, x ∉ c.target → IsLocalDiffeomorphAt I J ∞ F x)
    (hℓinj : InjOn ℓ {q | q.2.val 0 < 1 + a}) (hFinj : InjOn F c.targetᶜ)
    (hdisj : ∀ x, x ∉ c.target → ∀ q : B × EuclideanHalfSpace 1, q.2.val 0 < 1 + a →
      F x ≠ ℓ q)
    (hcover : ∀ y, (∃ x, x ∉ c.target ∧ F x = y) ∨
      ∃ q : B × EuclideanHalfSpace 1, q.2.val 0 < 1 + a ∧ ℓ q = y) :
    ∃ Φ : X ≃ₘ⟮I, J⟯ Y,
      (∀ x, (∀ p : B × EuclideanHalfSpace 1, p.2.val 0 ≤ 1 / 2 → c p ≠ x) → Φ x = F x) ∧
        ∀ b, Φ (c (b, halfSpaceOneLift 0)) = ℓ (b, halfSpaceOneLift 0) := by
  classical
  set G := collarStretchMap (K := K) (B := B) ha with hGdef
  let Φ : X → Y := fun x => if x ∈ c.target then ℓ (G (c.symm x)) else F x
  have hΦin : ∀ x, x ∈ c.target → Φ x = ℓ (G (c.symm x)) := fun x hx => by simp [Φ, hx]
  have hΦout : ∀ x, x ∉ c.target → Φ x = F x := fun x hx => by simp [Φ, hx]
  have hsrc : ∀ p : B × EuclideanHalfSpace 1, p ∈ c.source ↔ p.2.val 0 < 1 := by
    intro p
    rw [hc]
    rfl
  have hGlt : ∀ p : B × EuclideanHalfSpace 1, p.2.val 0 < 1 → (G p).2.val 0 < 1 + a := by
    intro p hp
    rw [collarStretchMap_apply, lift_val_of_nonneg (collarStretch_nonneg ha p.2.2),
      ← collarStretch_one a]
    exact strictMono_collarStretch ha hp
  have hGslt : ∀ q : B × EuclideanHalfSpace 1, q.2.val 0 < 1 + a →
      (G.symm q).2.val 0 < 1 := by
    intro q hq
    rw [collarStretchMap_symm_apply, lift_val_of_nonneg (collarStretchIso_symm_nonneg ha q.2.2)]
    exact collarStretchIso_symm_lt_one ha hq
  let L : Set (B × EuclideanHalfSpace 1) := univ ×ˢ (halfSpaceOneLift '' Icc 0 (1 / 2))
  have hLmem : ∀ p : B × EuclideanHalfSpace 1, p ∈ L ↔ p.2.val 0 ≤ 1 / 2 := by
    intro p
    constructor
    · rintro ⟨-, t, ht, hpt⟩
      rw [← hpt, lift_val_of_nonneg ht.1]
      exact ht.2
    · intro hp
      exact ⟨mem_univ _, p.2.val 0, ⟨p.2.2, hp⟩, lift_coord p.2⟩
  have hLsrc : L ⊆ c.source := fun p hp => (hsrc p).mpr (((hLmem p).mp hp).trans_lt
    (by norm_num))
  have hKc : IsClosed (c '' L) :=
    ((isCompact_univ.prod (isCompact_Icc.image continuous_lift)).image_of_continuousOn
      (c.contMDiffOn.continuousOn.mono hLsrc)).isClosed
  have hKt : c '' L ⊆ c.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact c.map_source' (hLsrc hp)
  have hΦF : ∀ x, x ∉ c '' L → Φ x = F x := by
    intro x hx
    by_cases hxt : x ∈ c.target
    · rw [hΦin x hxt]
      have hpx : c.symm x ∈ c.source := c.map_target' hxt
      have hcx : c (c.symm x) = x := PartialDiffeomorph.apply_symm_apply c hxt
      have hhalf : 1 / 2 < (c.symm x).2.val 0 := by
        by_contra hle
        exact hx ⟨c.symm x, (hLmem _).mpr (not_lt.mp hle), hcx⟩
      rw [← hcx, PartialDiffeomorph.symm_apply_apply c hpx, hFc _ ((hsrc _).mp hpx),
        collarStretchMap_apply, collarStretch_of_half_le a hhalf.le]
    · exact hΦout x hxt
  have hloc : IsLocalDiffeomorph I J ∞ Φ := by
    intro x
    by_cases hxt : x ∈ c.target
    · have hpx : c.symm x ∈ c.source := c.map_target' hxt
      have h1 : IsLocalDiffeomorphAt I (K.prod (𝓡∂ 1)) ∞ c.symm x :=
        c.symm.isLocalDiffeomorphAt I (K.prod (𝓡∂ 1)) ∞ hxt
      have h2 := h1.comp (K := K.prod (𝓡∂ 1)) (P := B × EuclideanHalfSpace 1)
        (G.isLocalDiffeomorph (c.symm x))
      have h3 := h2.comp (K := J) (P := Y) (hℓ _ (hGlt _ ((hsrc _).mp hpx)))
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ h3
      filter_upwards [c.open_target.mem_nhds hxt] with y hy
      exact hΦin y hy
    · have hxK : x ∉ c '' L := fun h => hxt (hKt h)
      refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_ (hF x hxt)
      filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with y hy
      exact hΦF y hy
  have hbij : Bijective Φ := by
    constructor
    · intro x x' hxx
      by_cases hx : x ∈ c.target <;> by_cases hx' : x' ∈ c.target
      · rw [hΦin x hx, hΦin x' hx'] at hxx
        have hp := c.map_target' hx
        have hp' := c.map_target' hx'
        have h1 := hℓinj (hGlt _ ((hsrc _).mp hp)) (hGlt _ ((hsrc _).mp hp')) hxx
        have h2 := G.injective h1
        rw [← PartialDiffeomorph.apply_symm_apply c hx, ← PartialDiffeomorph.apply_symm_apply c hx']
        exact congrArg c h2
      · rw [hΦin x hx, hΦout x' hx'] at hxx
        exact (hdisj x' hx' _ (hGlt _ ((hsrc _).mp (c.map_target' hx))) hxx.symm).elim
      · rw [hΦout x hx, hΦin x' hx'] at hxx
        exact (hdisj x hx _ (hGlt _ ((hsrc _).mp (c.map_target' hx'))) hxx).elim
      · rw [hΦout x hx, hΦout x' hx'] at hxx
        exact hFinj hx hx' hxx
    · intro y
      rcases hcover y with ⟨x, hx, rfl⟩ | ⟨q, hq, rfl⟩
      · exact ⟨x, hΦout x hx⟩
      · have hp : G.symm q ∈ c.source := (hsrc _).mpr (hGslt q hq)
        refine ⟨c (G.symm q), ?_⟩
        rw [hΦin _ (c.map_source' hp), PartialDiffeomorph.symm_apply_apply c hp,
          G.apply_symm_apply]
  refine ⟨hloc.diffeomorphOfBijective hbij, fun x hx => hΦF x ?_, fun b => ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact hx p ((hLmem p).mp hp) rfl
  · have hp : (b, halfSpaceOneLift 0) ∈ c.source := by
      rw [hsrc, lift_val_of_nonneg le_rfl]
      norm_num
    change Φ _ = _
    rw [hΦin _ (c.map_source' hp), PartialDiffeomorph.symm_apply_apply c hp,
      collarStretchMap_apply, lift_val_of_nonneg le_rfl, collarStretch_zero]

end Stretch

end DifferentialGeometry.Topology.Manifold
