import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobiusTwist
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates
import DifferentialGeometry.Topology.Manifold.Interval.Tangent

/-!
# Circle bundles over a Möbius base: the twisted chart

Chapter 6, lane MD5, tier T4 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3, errata after
review 8), final file; the construction is spread over `SF/PlanarBundleMobiusCover.lean` (the
double cover of the Möbius model by the annulus), `SF/PlanarBundleMobiusPullback.lean` (the
pulled-back fibration) and `SF/PlanarBundleMobiusTwist.lean` (positive and twisted coordinates).

Review 8, item 4: an arbitrary trivialisation of the pulled-back bundle gives a deck-cocycle
family, not one circle map. Here a positive global coordinate `τ` of the pulled-back fibration
and its positive twist `twistCoord τ = (deck × conj) ∘ τ ∘ deck` are glued once by
`FibreCoordinate.glue` over the two half annuli `rightOpen` and `leftOpen` (their overlap is a
contractible sector, `isSimplyConnected_sector`), giving `τu` that equals `τ` near the ray
`arg = 0` and the twist near `arg = π`. On the closed upper half annulus the chart is `τu⁻¹`,
on the lower half it is `deck ∘ τu⁻¹ ∘ (deck × conj)` (`assembled`); the two formulas agree on
the seam (`seam_agree`), so the result is smooth (`contMDiff_assembled`) and deck-equivariant
(`assembled_annDeck`). Composed with `unwrap z t = (1/2 + 5t/2) z` and the projection of the fibre
product this is the twisted chart (`isTwistedChart_chartMap`): smooth, onto, identifying exactly
`p` and `mobiusDeck p`, with injective differential (a smooth local left inverse, through a sheet
of the covering, `injective_mfderiv_pullSndU_assembled`, and `injective_mfderiv_unwrapA`).

Main results: `circleBundlesOverPlanarBases_mobius` (the frozen Möbius clause, by relabelling the
base along `e`, `CircleFibration.relabelBase`) and `circleBundlesOverPlanarBasesStandard`
(T1 together with T4).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

namespace MobiusCover

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} {F : CircleFibration C U}
  {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
  {hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E} {hrange : range E = mobiusModel}

section Assembly

variable (τ : FibreCoordinate (pullFibration F hE hrange) ⊤)
  (τu : FibreCoordinate (pullFibration F hE hrange) (rightOpen ⊔ leftOpen))

open Classical in
def assembled (p : annulusSurface.{u}.Carrier × Circle) :
    (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) :=
  if 0 ≤ (annEmb p.1).im then τu.symmFn p.1 p.2
  else deckT F hE hrange (τu.symmFn (annDeck p.1) p.2⁻¹)

theorem assembled_of_nonneg {p : annulusSurface.{u}.Carrier × Circle} (h : 0 ≤ (annEmb p.1).im) :
    assembled τu p = τu.symmFn p.1 p.2 := ite_eq_left h

theorem assembled_of_neg {p : annulusSurface.{u}.Carrier × Circle} (h : (annEmb p.1).im < 0) :
    assembled τu p = deckT F hE hrange (τu.symmFn (annDeck p.1) p.2⁻¹) :=
  ite_eq_right (not_le.mpr h)

theorem im_annDeck_pos_of_neg {w : annulusSurface.{u}.Carrier} (h : (annEmb w).im < 0) :
    0 < (annEmb (annDeck w)).im := by
  rw [im_annEmb_annDeck]
  nlinarith [deck_factor_pos w]

variable {τ τu}
variable (hU0 : ∀ w v, seamCutoff w = 0 → w ∈ rightOpen → τu.symmFn w v = τ.symmFn w v)
  (hU1 : ∀ w v, seamCutoff w = 1 → w ∈ leftOpen → τu.symmFn w v = (twistCoord τ).symmFn w v)

include hU0 hU1 in
theorem seam_agree {w : annulusSurface.{u}.Carrier} (hw : w ∈ seamZone) (v : Circle) :
    τu.symmFn w v = deckT F hE hrange (τu.symmFn (annDeck w) v⁻¹) := by
  have hre : (annEmb w).re ≠ 0 := by
    intro h
    have := hw
    change |(annEmb w).im| < |(annEmb w).re| at this
    rw [h, abs_zero] at this
    exact absurd this (not_lt.mpr (abs_nonneg _))
  rcases hre.lt_or_gt with hr | hr
  · obtain ⟨h1, hl, h0, hr'⟩ := seamZone_left hw hr
    rw [hU1 w v h1 hl, twistCoord_symmFn, hU0 (annDeck w) v⁻¹ h0 hr']
  · obtain ⟨h0, hr', h1, hl⟩ := seamZone_right hw hr
    rw [hU0 w v h0 hr', hU1 (annDeck w) v⁻¹ h1 hl, twistCoord_symmFn, annDeck_annDeck, inv_inv,
      deckT_deckT]

include hU0 hU1 in
theorem assembled_annDeck (w : annulusSurface.{u}.Carrier) (v : Circle) :
    assembled τu (annDeck w, v⁻¹) = deckT F hE hrange (assembled τu (w, v)) := by
  rcases lt_trichotomy (annEmb w).im 0 with h | h | h
  · have h' : 0 ≤ (annEmb (annDeck w)).im := (im_annDeck_pos_of_neg h).le
    rw [assembled_of_nonneg τu h', assembled_of_neg τu h, deckT_deckT]
  · have h' : (annEmb (annDeck w)).im = 0 := (im_annDeck_eq_zero_iff w).mpr h
    rw [assembled_of_nonneg τu h'.ge, assembled_of_nonneg τu h.ge,
      seam_agree hU0 hU1 (mem_seamZone_of_im_eq_zero h) v, deckT_deckT]
  · have h' : (annEmb (annDeck w)).im < 0 := (im_annDeck_neg_iff w).mpr h
    rw [assembled_of_neg τu h', assembled_of_nonneg τu h.le, annDeck_annDeck, inv_inv]

omit hU0 hU1 in
theorem projection_assembled (p : annulusSurface.{u}.Carrier × Circle) :
    (pullFibration F hE hrange).projection (assembled τu p) = p.1 := by
  by_cases h : 0 ≤ (annEmb p.1).im
  · rw [assembled_of_nonneg τu h]
    exact τu.projection_symmFn _ _
  · rw [assembled_of_neg τu (not_le.mp h), projection_deckT]
    exact (congrArg annDeck (τu.projection_symmFn (annDeck p.1) p.2⁻¹)).trans (annDeck_annDeck _)

theorem annDeck_mem_sup_of_neg {w : annulusSurface.{u}.Carrier} (h : (annEmb w).im < 0) :
    annDeck w ∈ rightOpen.{u} ⊔ leftOpen.{u} := by
  exact mem_sup_of_im_nonneg (im_annDeck_pos_of_neg h).le

omit hU0 hU1 in
theorem assembled_injective_fibre (w : annulusSurface.{u}.Carrier) {v v' : Circle}
    (h : assembled τu (w, v) = assembled τu (w, v')) : v = v' := by
  by_cases hw : 0 ≤ (annEmb w).im
  · rw [assembled_of_nonneg τu hw, assembled_of_nonneg τu hw] at h
    have h' := congrArg τu.angle h
    rwa [τu.angle_symmFn (mem_sup_of_im_nonneg hw), τu.angle_symmFn (mem_sup_of_im_nonneg hw)]
      at h'
  · have hw' := not_le.mp hw
    rw [assembled_of_neg τu hw', assembled_of_neg τu hw'] at h
    have h2 := congrArg (deckT F hE hrange) h
    rw [deckT_deckT, deckT_deckT] at h2
    have h' := congrArg τu.angle h2
    rw [τu.angle_symmFn (annDeck_mem_sup_of_neg hw'),
      τu.angle_symmFn (annDeck_mem_sup_of_neg hw')] at h'
    exact inv_injective h'

omit hU0 hU1 in
theorem exists_assembled_eq (y : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    ∃ v, assembled τu ((pullFibration F hE hrange).projection y, v) = y := by
  by_cases hw : 0 ≤ (annEmb ((pullFibration F hE hrange).projection y)).im
  · refine ⟨τu.angle y, ?_⟩
    rw [assembled_of_nonneg τu hw]
    exact τu.symmFn_angle y (mem_sup_of_im_nonneg hw)
  · have hw' := not_le.mp hw
    refine ⟨(τu.angle (deckT F hE hrange y))⁻¹, ?_⟩
    rw [assembled_of_neg τu hw', inv_inv, ← projection_deckT,
      τu.symmFn_angle _ (by rw [projection_deckT]; exact annDeck_mem_sup_of_neg hw'),
      deckT_deckT]

include hU0 hU1 in
theorem eventually_assembled_A {p₀ : annulusSurface.{u}.Carrier × Circle}
    (h : 0 ≤ (annEmb p₀.1).im) :
    ∀ᶠ q in 𝓝 p₀, assembled τu q = τu.symmFn q.1 q.2 ∧ q.1 ∈ rightOpen.{u} ⊔ leftOpen.{u} := by
  rcases h.lt_or_eq with h | h
  · have ho : IsOpen {q : annulusSurface.{u}.Carrier × Circle | 0 < (annEmb q.1).im} :=
      isOpen_lt continuous_const ((Complex.continuous_im.comp continuous_annEmb).comp
        continuous_fst)
    filter_upwards [ho.mem_nhds h] with q hq
    exact ⟨assembled_of_nonneg τu hq.le, mem_sup_of_im_nonneg hq.le⟩
  · have hz := mem_seamZone_of_im_eq_zero h.symm
    have hv := mem_sup_of_im_nonneg h.le
    have ho : IsOpen {q : annulusSurface.{u}.Carrier × Circle |
        q.1 ∈ seamZone.{u} ∩ (rightOpen.{u} ⊔ leftOpen.{u} : Set annulusSurface.{u}.Carrier)} :=
      (isOpen_seamZone.inter (rightOpen ⊔ leftOpen).isOpen).preimage continuous_fst
    filter_upwards [ho.mem_nhds ⟨hz, hv⟩] with q hq
    refine ⟨?_, hq.2⟩
    by_cases hq' : 0 ≤ (annEmb q.1).im
    · exact assembled_of_nonneg τu hq'
    · rw [assembled_of_neg τu (not_le.mp hq')]
      exact (seam_agree hU0 hU1 hq.1 q.2).symm

omit hU0 hU1 in
theorem eventually_assembled_B {p₀ : annulusSurface.{u}.Carrier × Circle}
    (h : (annEmb p₀.1).im < 0) :
    ∀ᶠ q in 𝓝 p₀, assembled τu q = deckT F hE hrange (τu.symmFn (annDeck q.1) q.2⁻¹) ∧
      annDeck q.1 ∈ rightOpen.{u} ⊔ leftOpen.{u} := by
  have ho : IsOpen {q : annulusSurface.{u}.Carrier × Circle | (annEmb q.1).im < 0} :=
    isOpen_lt ((Complex.continuous_im.comp continuous_annEmb).comp continuous_fst)
      continuous_const
  filter_upwards [ho.mem_nhds h] with q hq
  exact ⟨assembled_of_neg τu hq, annDeck_mem_sup_of_neg hq⟩

omit hU0 hU1 in
theorem contMDiffAt_branchA {p : annulusSurface.{u}.Carrier × Circle}
    (hp : p.1 ∈ rightOpen.{u} ⊔ leftOpen.{u}) :
    ContMDiffAt ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (pullCarrier F hE hrange).model ∞ (fun q => τu.symmFn q.1 q.2) p :=
  (τu.contMDiffOn_symmFn p ⟨hp, trivial⟩).contMDiffAt
    (((rightOpen ⊔ leftOpen).isOpen.prod isOpen_univ).mem_nhds ⟨hp, mem_univ _⟩)

omit hU0 hU1 in
theorem contMDiffAt_branchB {p : annulusSurface.{u}.Carrier × Circle}
    (hp : annDeck p.1 ∈ rightOpen.{u} ⊔ leftOpen.{u}) :
    ContMDiffAt ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (pullCarrier F hE hrange).model ∞
      (fun q => deckT F hE hrange (τu.symmFn (annDeck q.1) q.2⁻¹)) p := by
  have hm : ContMDiff ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞
      (fun q : annulusSurface.{u}.Carrier × Circle => (annDeck q.1, q.2⁻¹)) :=
    (contMDiff_annDeck.comp contMDiff_fst).prodMk ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_snd)
  have hA := contMDiffAt_branchA (τu := τu) (p := (annDeck p.1, p.2⁻¹)) hp
  exact ((contMDiff_deckT F hE hrange) _).comp p (hA.comp p (hm p))

include hU0 hU1 in
theorem contMDiff_assembled :
    ContMDiff ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      (pullCarrier F hE hrange).model ∞ (assembled τu) := by
  intro p
  by_cases h : 0 ≤ (annEmb p.1).im
  · have hev := eventually_assembled_A hU0 hU1 h
    exact (contMDiffAt_branchA (mem_sup_of_im_nonneg h)).congr_of_eventuallyEq
      (hev.mono fun q hq => hq.1)
  · have hev := eventually_assembled_B (τu := τu) (not_le.mp h)
    exact (contMDiffAt_branchB (annDeck_mem_sup_of_neg (not_le.mp h))).congr_of_eventuallyEq
      (hev.mono fun q hq => hq.1)

end Assembly

section Unwrap

theorem injective_mfderiv_of_leftInverse {EM HM M EN HN N : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M]
    [ChartedSpace HM M] [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
    {J : ModelWithCorners ℝ EN HN} [TopologicalSpace N] [ChartedSpace HN N]
    {f : M → N} {g : N → M} {x : M} (hf : MDifferentiableAt I J f x)
    (hg : MDifferentiableAt J I g (f x)) (hgf : g ∘ f =ᶠ[𝓝 x] id) :
    Function.Injective (mfderiv I J f x) := by
  intro v w h
  have h1 := mfderiv_comp x hg hf
  rw [hgf.mfderiv_eq, mfderiv_id] at h1
  have hv := DFunLike.congr_fun h1 v
  have hw := DFunLike.congr_fun h1 w
  change v = mfderiv J I g (f x) (mfderiv I J f x v) at hv
  change w = mfderiv J I g (f x) (mfderiv I J f x w) at hw
  rw [hv, hw, h]

def unwrapA (p : Circle × unitInterval) : annulusSurface.{u}.Carrier :=
  annMk (unwrap p.1 p.2) (unwrap_mem_annulus p.1 p.2)

theorem annEmb_unwrapA (p : Circle × unitInterval) : annEmb (unwrapA.{u} p) = unwrap p.1 p.2 :=
  rfl

theorem contMDiff_unwrap :
    ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) ∞ (fun p : Circle × unitInterval => unwrap p.1 p.2) := by
  have h1 : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Circle × unitInterval => (1 / 2 + 5 / 2 * (p.2 : ℝ))) :=
    contMDiff_const.add (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  have h2 : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : Circle × unitInterval => (p.1 : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_fst
  exact h1.smul h2

theorem contMDiff_unwrapA :
    ContMDiff ((𝓡 1).prod (𝓡∂ 1)) (SurfaceModel.model annulusSurface.{u}.kind) ∞ unwrapA.{u} :=
  (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_annEmb.isImmersion).mpr
    ⟨continuous_annMk contMDiff_unwrap.continuous _, contMDiff_unwrap⟩

theorem unwrapA_symm (z : Circle) (t : unitInterval) :
    unwrapA.{u} (-z, unitInterval.symm t) = annDeck (unwrapA (z, t)) :=
  injective_annEmb (unwrap_symm z t)

theorem injective_unwrapA : Function.Injective unwrapA.{u} := by
  intro p q h
  have h' : unwrap p.1 p.2 = unwrap q.1 q.2 := congrArg annEmb h
  have hz : (p.1 : ℂ) = q.1 := by rw [← dir_unwrap p.1 p.2, h', dir_unwrap]
  have ht : (p.2 : ℝ) = q.2 := by
    have := congrArg norm h'
    rw [norm_unwrap, norm_unwrap] at this
    linarith
  exact Prod.ext (Circle.ext hz) (Subtype.ext ht)

theorem surjective_unwrapA : Function.Surjective unwrapA.{u} := by
  intro x
  have hx := annEmb_mem x
  have hn := norm_pos_of_mem_annulus hx
  refine ⟨(unitOf (annEmb x), ⟨(2 * ‖annEmb x‖ - 1) / 5, ?_, ?_⟩), ?_⟩
  · linarith [hx.1]
  · linarith [hx.2]
  · apply injective_annEmb
    rw [annEmb_unwrapA, unwrap]
    change (1 / 2 + 5 / 2 * ((2 * ‖annEmb x‖ - 1) / 5)) • (unitOf (annEmb x) : ℂ) = annEmb x
    rw [show (1 / 2 + 5 / 2 * ((2 * ‖annEmb x‖ - 1) / 5) : ℝ) = ‖annEmb x‖ by ring,
      norm_smul_unitOf]

theorem injective_mfderiv_unwrapA (p : Circle × unitInterval) :
    Function.Injective (mfderiv ((𝓡 1).prod (𝓡∂ 1))
      (SurfaceModel.model annulusSurface.{u}.kind) unwrapA.{u} p) := by
  have : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  let h2 : Circle × ℝ → ℂ := fun q => (1 / 2 + 5 / 2 * q.2) • (q.1 : ℂ)
  let κ : Circle × unitInterval → Circle × ℝ := fun p => (p.1, (p.2 : ℝ))
  let r2 : ℂ → Circle × ℝ := fun w => (unitOf w, (2 * ‖w‖ - 1) / 5)
  have hh2 : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) ∞ h2 :=
    (contMDiff_const.add (contMDiff_const.mul contMDiff_snd)).smul
      (contMDiff_circle_coe.comp contMDiff_fst)
  have hκ : ContMDiff ((𝓡 1).prod (𝓡∂ 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ κ :=
    contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd)
  have hpos : 0 < 1 / 2 + 5 / 2 * (p.2 : ℝ) := by linarith [p.2.2.1]
  have hw0 : h2 (κ p) ≠ 0 := by
    change (1 / 2 + 5 / 2 * (p.2 : ℝ)) • (p.1 : ℂ) ≠ 0
    exact smul_ne_zero hpos.ne' (Circle.coe_ne_zero p.1)
  have hr2 : MDifferentiableAt 𝓘(ℝ, ℂ) ((𝓡 1).prod 𝓘(ℝ, ℝ)) r2 (h2 (κ p)) := by
    have hu := (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hw0)).mdifferentiableAt
      (by simp)
    have hn : ContDiffAt ℝ ∞ (fun w : ℂ => (2 * ‖w‖ - 1) / 5) (h2 (κ p)) :=
      ((contDiffAt_const.mul (contDiffAt_norm ℝ hw0)).sub contDiffAt_const).div_const _
    exact hu.prodMk (hn.contMDiffAt.mdifferentiableAt (by simp))
  have hinv : r2 ∘ h2 =ᶠ[𝓝 (κ p)] id := by
    have ho : IsOpen {q : Circle × ℝ | 0 < 1 / 2 + 5 / 2 * q.2} :=
      isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_snd))
    filter_upwards [ho.mem_nhds hpos] with q hq
    change (unitOf ((1 / 2 + 5 / 2 * q.2) • (q.1 : ℂ)),
      (2 * ‖(1 / 2 + 5 / 2 * q.2) • (q.1 : ℂ)‖ - 1) / 5) = q
    rw [unitOf_smul hq, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hq.le]
    exact Prod.ext rfl (by ring)
  have hinj2 := injective_mfderiv_of_leftInverse ((hh2.mdifferentiable (by simp)) (κ p)) hr2 hinv
  have hinjκ : Function.Injective (mfderiv ((𝓡 1).prod (𝓡∂ 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) κ p) := by
    have hm : mfderiv ((𝓡 1).prod (𝓡∂ 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) κ p =
        (mfderiv (𝓡 1) (𝓡 1) id p.1).prodMap
          (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) p.2) :=
      mfderiv_prodMap mdifferentiableAt_id
        (((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiable (by simp)) p.2)
    rw [hm, mfderiv_id]
    intro v w h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    change (v.1 : EuclideanSpace ℝ (Fin 1)) = w.1 at h1
    change mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) p.2 v.2 =
      mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : unitInterval → ℝ) p.2 w.2 at h2
    refine Prod.ext h1 ?_
    apply (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (a := 0) (b := 1)
      p.2).injective
    exact congrArg (NormedSpace.fromTangentSpace ((p.2 : unitInterval) : ℝ)) h2
  have hcomp : mfderiv ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) (fun p : Circle × unitInterval =>
      unwrap p.1 p.2) p = (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℂ) h2 (κ p)).comp
        (mfderiv ((𝓡 1).prod (𝓡∂ 1)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) κ p) :=
    mfderiv_comp p ((hh2.mdifferentiable (by simp)) _) ((hκ.mdifferentiable (by simp)) p)
  have hcomp2 := mfderiv_comp p ((isSmoothEmbedding_annEmb.isImmersion.contMDiff.mdifferentiable
    (by simp)) (unwrapA.{u} p)) ((contMDiff_unwrapA.mdifferentiable (by simp)) p)
  intro v w h
  have h1 : mfderiv ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) (fun p : Circle × unitInterval =>
      unwrap p.1 p.2) p v = mfderiv ((𝓡 1).prod (𝓡∂ 1)) 𝓘(ℝ, ℂ)
        (fun p : Circle × unitInterval => unwrap p.1 p.2) p w := by
    have e1 := DFunLike.congr_fun hcomp2 v
    have e2 := DFunLike.congr_fun hcomp2 w
    exact e1.trans ((DFunLike.congr_arg (mfderiv (SurfaceModel.model annulusSurface.{u}.kind)
      𝓘(ℝ, ℂ) annEmb (unwrapA p)) h).trans e2.symm)
  have e3 := DFunLike.congr_fun hcomp v
  have e4 := DFunLike.congr_fun hcomp w
  exact hinjκ (hinj2 (e3.symm.trans (h1.trans e4)))

end Unwrap

section Chart

variable {τ : FibreCoordinate (pullFibration F hE hrange) ⊤}
  {τu : FibreCoordinate (pullFibration F hE hrange) (rightOpen ⊔ leftOpen)}
  (hU0 : ∀ w v, seamCutoff w = 0 → w ∈ rightOpen → τu.symmFn w v = τ.symmFn w v)
  (hU1 : ∀ w v, seamCutoff w = 1 → w ∈ leftOpen → τu.symmFn w v = (twistCoord τ).symmFn w v)

def pullSndU (y : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) : U :=
  y.val.val.2

omit hU0 hU1 in
theorem contMDiff_pullSndU :
    ContMDiff (pullCarrier F hE hrange).model C.model ∞ (pullSndU (hE := hE) (hrange := hrange)) :=
  (contMDiff_pullSnd F hE hrange).comp contMDiff_subtype_val

omit hU0 hU1 in
theorem pullTop_ext {y y' : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)}
    (h1 : y.val.val.1 = y'.val.val.1) (h2 : y.val.val.2 = y'.val.val.2) : y = y' :=
  Subtype.ext (Subtype.ext (Prod.ext h1 h2))

omit hU0 hU1 in
theorem projection_pullSndU (y : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) :
    F.projection (pullSndU y) = cover hrange ((pullFibration F hE hrange).projection y) :=
  y.val.2.symm

include hU0 hU1 in
theorem injective_mfderiv_pullSndU_assembled (q₀ : annulusSurface.{u}.Carrier × Circle) :
    Function.Injective (mfderiv ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      C.model (fun q => pullSndU (assembled τu q)) q₀) := by
  set y₀ := assembled τu q₀
  set hl := isLocalHomeomorph_pullProj F hE hrange
  let := Manifold.coveringChartedSpace (H := C.kind.Space) hl
  let := Manifold.covering_isManifold hl C.model
  set e := hl.localInverseAt y₀.val
  have he : (e.symm : (pullCarrier F hE hrange).Carrier → C.Carrier) = pullProj F hrange :=
    hl.localInverseAt_symm y₀.val
  have hes := Manifold.covering_sheetInverse_contMDiff hl C.model e.symm (fun y _ => by
    rw [he])
  have hmem : (pullSndU y₀ : C.Carrier) ∈ e.source := hl.apply_self_mem_localInverseAt_source
  let sec : U → (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) :=
    fun x => ⟨e x.val, trivial⟩
  have hsec : ContMDiffAt C.model (pullCarrier F hE hrange).model ∞ sec (pullSndU y₀) := by
    have h1 : ContMDiffAt C.model (pullCarrier F hE hrange).model ∞
        (Subtype.val ∘ sec) (pullSndU y₀) := by
      have h2 := (hes.contMDiffAt (e.symm.open_target.mem_nhds hmem)).comp (pullSndU y₀)
        (contMDiff_subtype_val (I := C.model) (U := U) (n := ∞)).contMDiffAt
      exact h2
    exact (ContMDiffAt.subtypeVal_comp_iff ⊤ sec (pullSndU y₀)).mp h1
  have hsec0 : sec (pullSndU y₀) = y₀ := by
    apply Subtype.ext
    change e (pullProj F hrange y₀.val) = y₀.val
    rw [← he]
    exact e.right_inv hl.self_mem_localInverseAt_target
  have hev_sec : ∀ᶠ q in 𝓝 q₀, sec (pullSndU (assembled τu q)) = assembled τu q := by
    have hc : ContinuousAt (fun q => ((assembled τu q).val : (pullCarrier F hE hrange).Carrier))
        q₀ := (continuous_subtype_val.comp (contMDiff_assembled hU0 hU1).continuous).continuousAt
    filter_upwards [hc (e.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with q hq
    apply Subtype.ext
    change e (pullProj F hrange (assembled τu q).val) = (assembled τu q).val
    rw [← he]
    exact e.right_inv hq
  have hf : MDifferentiableAt ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
      C.model (fun q => pullSndU (assembled τu q)) q₀ :=
    ((contMDiff_pullSndU.comp (contMDiff_assembled hU0 hU1)).mdifferentiable (by simp)) q₀
  by_cases h : 0 ≤ (annEmb q₀.1).im
  · let G : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) →
        annulusSurface.{u}.Carrier × Circle :=
      fun y => ((pullFibration F hE hrange).projection y, τu.angle y)
    have hv0 : (pullFibration F hE hrange).projection y₀ ∈ rightOpen.{u} ⊔ leftOpen.{u} := by
      rw [projection_assembled]
      exact mem_sup_of_im_nonneg h
    have hG : ContMDiffAt (pullCarrier F hE hrange).model
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞ G y₀ :=
      (pullFibration F hE hrange).smooth.contMDiffAt.prodMk
        ((τu.contMDiffOn_angle _ hv0).contMDiffAt
          ((FibreCoordinate.isOpen_preimage _).mem_nhds hv0))
    have hH : MDifferentiableAt C.model
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) (G ∘ sec) (pullSndU y₀) := by
      have := (hsec0 ▸ hG).comp (pullSndU y₀) hsec
      exact this.mdifferentiableAt (by simp)
    refine injective_mfderiv_of_leftInverse hf hH ?_
    filter_upwards [hev_sec, eventually_assembled_A hU0 hU1 h] with q h1 h2
    change G (sec (pullSndU (assembled τu q))) = q
    rw [h1]
    change ((pullFibration F hE hrange).projection (assembled τu q),
      τu.angle (assembled τu q)) = q
    rw [projection_assembled, h2.1, τu.angle_symmFn h2.2]
  · have h' := not_le.mp h
    let G : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) →
        annulusSurface.{u}.Carrier × Circle :=
      fun y => ((pullFibration F hE hrange).projection y, (τu.angle (deckT F hE hrange y))⁻¹)
    have hv0 : (pullFibration F hE hrange).projection (deckT F hE hrange y₀) ∈
        rightOpen.{u} ⊔ leftOpen.{u} := by
      rw [projection_deckT, projection_assembled]
      exact annDeck_mem_sup_of_neg h'
    have hG : ContMDiffAt (pullCarrier F hE hrange).model
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞ G y₀ :=
      (pullFibration F hE hrange).smooth.contMDiffAt.prodMk
        (((contMDiff_inv (𝓡 1) ∞).contMDiffAt).comp y₀
          (((τu.contMDiffOn_angle _ hv0).contMDiffAt
            ((FibreCoordinate.isOpen_preimage _).mem_nhds hv0)).comp y₀
              ((contMDiff_deckT F hE hrange) y₀)))
    have hH : MDifferentiableAt C.model
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) (G ∘ sec) (pullSndU y₀) := by
      have := (hsec0 ▸ hG).comp (pullSndU y₀) hsec
      exact this.mdifferentiableAt (by simp)
    refine injective_mfderiv_of_leftInverse hf hH ?_
    filter_upwards [hev_sec, eventually_assembled_B (τu := τu) h'] with q h1 h2
    change G (sec (pullSndU (assembled τu q))) = q
    rw [h1]
    change ((pullFibration F hE hrange).projection (assembled τu q),
      (τu.angle (deckT F hE hrange (assembled τu q)))⁻¹) = q
    rw [projection_assembled, h2.1, deckT_deckT, τu.angle_symmFn h2.2, inv_inv]

end Chart

section TwistedChart

variable {τ : FibreCoordinate (pullFibration F hE hrange) ⊤}
  {τu : FibreCoordinate (pullFibration F hE hrange) (rightOpen ⊔ leftOpen)}
  (hU0 : ∀ w v, seamCutoff w = 0 → w ∈ rightOpen → τu.symmFn w v = τ.symmFn w v)
  (hU1 : ∀ w v, seamCutoff w = 1 → w ∈ leftOpen → τu.symmFn w v = (twistCoord τ).symmFn w v)

variable (τu) in
def chartMap (p : (Circle × unitInterval) × Circle) : U :=
  pullSndU (assembled τu (unwrapA p.1, p.2))

include hU0 hU1 in
theorem isTwistedChart_chartMap : IsTwistedChart F E (chartMap τu) := by
  have hsm : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1))
      ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞
      (fun p : (Circle × unitInterval) × Circle => (unwrapA p.1, p.2)) :=
    (contMDiff_unwrapA.comp contMDiff_fst).prodMk contMDiff_snd
  refine ⟨contMDiff_pullSndU.comp ((contMDiff_assembled hU0 hU1).comp hsm), ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨w, hw⟩ := surjective_cover hE hrange (F.projection x)
    let y : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) :=
      ⟨⟨(w, x), hw⟩, trivial⟩
    obtain ⟨v, hv⟩ := exists_assembled_eq (τu := τu) y
    obtain ⟨pz, hpz⟩ := surjective_unwrapA w
    refine ⟨(pz, v), ?_⟩
    change pullSndU (assembled τu (unwrapA pz, v)) = x
    rw [hpz]
    change pullSndU (assembled τu ((pullFibration F hE hrange).projection y, v)) = x
    rw [hv]
    rfl
  · intro p q
    constructor
    · intro h
      have hc : cover hrange (unwrapA p.1) = cover hrange (unwrapA q.1) := by
        have e1 := projection_pullSndU (assembled τu (unwrapA p.1, p.2))
        have e2 := projection_pullSndU (assembled τu (unwrapA q.1, q.2))
        rw [projection_assembled] at e1 e2
        rw [← e1, ← e2]
        exact congrArg F.projection h
      rcases (cover_eq_cover_iff hE hrange _ _).mp hc with h1 | h1
      · left
        have hq1 : q.1 = p.1 := injective_unwrapA h1
        have hy : assembled τu (unwrapA q.1, q.2) = assembled τu (unwrapA p.1, p.2) :=
          pullTop_ext (by
            change (pullFibration F hE hrange).projection (assembled τu (unwrapA q.1, q.2)) =
              (pullFibration F hE hrange).projection (assembled τu (unwrapA p.1, p.2))
            rw [projection_assembled, projection_assembled, h1]) h.symm
        rw [hq1] at hy
        exact Prod.ext hq1 (assembled_injective_fibre _ hy)
      · right
        have hq1 : q.1 = (-p.1.1, unitInterval.symm p.1.2) := by
          apply injective_unwrapA
          rw [h1, unwrapA_symm]
        have hy : assembled τu (unwrapA q.1, q.2) =
            deckT F hE hrange (assembled τu (unwrapA p.1, p.2)) :=
          pullTop_ext (by
            change (pullFibration F hE hrange).projection (assembled τu (unwrapA q.1, q.2)) =
              annDeck ((pullFibration F hE hrange).projection (assembled τu (unwrapA p.1, p.2)))
            rw [projection_assembled, projection_assembled, h1]) h.symm
        rw [← assembled_annDeck hU0 hU1, ← h1] at hy
        exact Prod.ext hq1 (assembled_injective_fibre _ hy)
    · rintro (rfl | rfl)
      · rfl
      · change pullSndU (assembled τu (unwrapA p.1, p.2)) =
          pullSndU (assembled τu (unwrapA (-p.1.1, unitInterval.symm p.1.2), p.2⁻¹))
        rw [unwrapA_symm, assembled_annDeck hU0 hU1]
        rfl
  · intro p
    have h1 := injective_mfderiv_pullSndU_assembled hU0 hU1 (unwrapA p.1, p.2)
    have hm : mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1))
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
        (fun p : (Circle × unitInterval) × Circle => (unwrapA p.1, p.2)) p =
        (mfderiv ((𝓡 1).prod (𝓡∂ 1)) (SurfaceModel.model annulusSurface.{u}.kind)
          unwrapA.{u} p.1).prodMap (mfderiv (𝓡 1) (𝓡 1) id p.2) :=
      mfderiv_prodMap ((contMDiff_unwrapA.mdifferentiable (by simp)) p.1) mdifferentiableAt_id
    have h2 : Function.Injective (mfderiv (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1))
        ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1))
        (fun p : (Circle × unitInterval) × Circle => (unwrapA p.1, p.2)) p) := by
      rw [hm, mfderiv_id]
      intro v w h
      have e1 := congrArg Prod.fst h
      have e2 := congrArg Prod.snd h
      change mfderiv ((𝓡 1).prod (𝓡∂ 1)) (SurfaceModel.model annulusSurface.{u}.kind)
        unwrapA.{u} p.1 v.1 = mfderiv ((𝓡 1).prod (𝓡∂ 1))
          (SurfaceModel.model annulusSurface.{u}.kind) unwrapA.{u} p.1 w.1 at e1
      change (v.2 : EuclideanSpace ℝ (Fin 1)) = w.2 at e2
      exact Prod.ext (injective_mfderiv_unwrapA p.1 e1) e2
    have hc := mfderiv_comp p
      (((contMDiff_pullSndU.comp (contMDiff_assembled hU0 hU1)).mdifferentiable (by simp))
        (unwrapA p.1, p.2)) ((hsm.mdifferentiable (by simp)) p)
    intro v w h
    have e1 := DFunLike.congr_fun hc v
    have e2 := DFunLike.congr_fun hc w
    exact h2 (h1 (e1.symm.trans (h.trans e2)))
  · intro p
    change E (F.projection (pullSndU (assembled τu (unwrapA p.1, p.2)))) = mobiusPoint p.1.1 p.1.2
    rw [projection_pullSndU, projection_assembled, E_cover hrange, annEmb_unwrapA, model_unwrap]

end TwistedChart

theorem exists_isTwistedChart (F : CircleFibration C U)
    {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
    (hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E) (hrange : range E = mobiusModel) :
    ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F E Ψ := by
  obtain ⟨τ, hτ⟩ := exists_positive_pullCoord F hE hrange
  obtain ⟨τu, hU0, hU1⟩ := exists_upperCoord F hE hrange τ hτ
  exact ⟨chartMap τu, isTwistedChart_chartMap hU0 hU1⟩

end MobiusCover

section Transport

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def CircleFibration.baseNbhd (F : CircleFibration C U) (B : CompactSurface.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind, SurfaceModel.model B.kind⟯ B.Carrier)
    (b : B.Carrier) : TopologicalSpace.Opens B.Carrier :=
  ⟨e '' F.neighborhood (e.symm b), e.toHomeomorph.isOpenMap _ (F.neighborhood _).isOpen⟩

theorem CircleFibration.mem_baseNbhd_iff (F : CircleFibration C U) (B : CompactSurface.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind, SurfaceModel.model B.kind⟯ B.Carrier)
    (b : B.Carrier) (y : F.base.Carrier) :
    e y ∈ CircleFibration.baseNbhd F B e b ↔ y ∈ F.neighborhood (e.symm b) := by
  constructor
  · rintro ⟨y', hy', hyy⟩
    rwa [← e.injective hyy]
  · intro hy
    exact ⟨y, hy, rfl⟩

theorem CircleFibration.symm_mem_neighborhood (F : CircleFibration C U) (B : CompactSurface.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind, SurfaceModel.model B.kind⟯ B.Carrier)
    (b : B.Carrier) (y : CircleFibration.baseNbhd F B e b) :
    e.symm y.val ∈ F.neighborhood (e.symm b) := by
  have h := y.2
  rw [← e.apply_symm_apply y.val] at h
  exact (CircleFibration.mem_baseNbhd_iff F B e b _).mp h

def CircleFibration.relabelBase (F : CircleFibration C U) (B : CompactSurface.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind, SurfaceModel.model B.kind⟯ B.Carrier) :
    CircleFibration C U where
  base := B
  projection := ⟨fun x => e (F.projection x), e.continuous.comp F.projection.continuous⟩
  surjective b := by
    obtain ⟨x, hx⟩ := F.surjective (e.symm b)
    exact ⟨x, by simp only [ContinuousMap.coe_mk, hx, Diffeomorph.apply_symm_apply]⟩
  smooth := e.contMDiff.comp F.smooth
  neighborhood := CircleFibration.baseNbhd F B e
  mem_neighborhood b := ⟨e.symm b, F.mem_neighborhood _, e.apply_symm_apply b⟩
  trivialization b :=
    { toFun := fun x => (⟨e (F.projection x.val), x.2⟩,
        (F.trivialization (e.symm b) ⟨x.val,
          (CircleFibration.mem_baseNbhd_iff F B e b (F.projection x.val)).mp x.2⟩).2)
      invFun := fun p => ⟨((F.trivialization (e.symm b)).symm (⟨e.symm p.1.val,
          CircleFibration.symm_mem_neighborhood F B e b p.1⟩, p.2)).val, by
          change e (F.projection _) ∈ CircleFibration.baseNbhd F B e b
          rw [← F.projection_trivialization, Diffeomorph.apply_symm_apply]
          change e (e.symm p.1.val) ∈ CircleFibration.baseNbhd F B e b
          rw [e.apply_symm_apply]
          exact p.1.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        have hx := (CircleFibration.mem_baseNbhd_iff F B e b (F.projection x.val)).mp x.2
        have hpair : ((⟨e.symm (e (F.projection x.val)), CircleFibration.symm_mem_neighborhood F
            B e b ⟨e (F.projection x.val), x.2⟩⟩ : F.neighborhood (e.symm b)),
            (F.trivialization (e.symm b) ⟨x.val, hx⟩).2) =
            F.trivialization (e.symm b) ⟨x.val, hx⟩ :=
          Prod.ext (Subtype.ext (by rw [F.projection_trivialization]; exact e.symm_apply_apply _))
            rfl
        change ((F.trivialization (e.symm b)).symm (⟨e.symm (e (F.projection x.val)),
          CircleFibration.symm_mem_neighborhood F B e b ⟨e (F.projection x.val), x.2⟩⟩,
          (F.trivialization (e.symm b) ⟨x.val, hx⟩).2)).val = x.val
        rw [hpair, Diffeomorph.symm_apply_apply]
      right_inv := fun p => by
        apply Prod.ext
        · apply Subtype.ext
          change e (F.projection ((F.trivialization (e.symm b)).symm _).val) = p.1.val
          rw [← F.projection_trivialization, Diffeomorph.apply_symm_apply]
          exact e.apply_symm_apply p.1.val
        · change ((F.trivialization (e.symm b)) ((F.trivialization (e.symm b)).symm
            (⟨e.symm p.1.val, CircleFibration.symm_mem_neighborhood F B e b p.1⟩, p.2))).2 = p.2
          rw [Diffeomorph.apply_symm_apply]
      contMDiff_toFun := by
        refine ContMDiff.prodMk ?_ ?_
        · apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact e.contMDiff.comp (F.smooth.comp contMDiff_subtype_val)
        · refine contMDiff_snd.comp ((F.trivialization (e.symm b)).contMDiff.comp ?_)
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact contMDiff_subtype_val
      contMDiff_invFun := by
        apply (ContMDiff.subtypeVal_comp_iff _ _).mp
        have hN : ContMDiff ((SurfaceModel.model B.kind).prod (𝓡 1))
            (SurfaceModel.model F.base.kind) ∞
            (fun p : CircleFibration.baseNbhd F B e b × Circle =>
              (⟨e.symm p.1.val, CircleFibration.symm_mem_neighborhood F B e b p.1⟩ :
                F.neighborhood (e.symm b))) := by
          apply (ContMDiff.subtypeVal_comp_iff _ _).mp
          exact e.symm.contMDiff.comp (contMDiff_subtype_val.comp contMDiff_fst)
        have h : ContMDiff ((SurfaceModel.model B.kind).prod (𝓡 1)) C.model ∞
            (fun p : CircleFibration.baseNbhd F B e b × Circle =>
              ((F.trivialization (e.symm b)).symm (⟨e.symm p.1.val,
                CircleFibration.symm_mem_neighborhood F B e b p.1⟩, p.2)).val) :=
          contMDiff_subtype_val.comp
            ((F.trivialization (e.symm b)).symm.contMDiff.comp (hN.prodMk contMDiff_snd))
        exact h }
  projection_trivialization _ _ := rfl

end Transport

theorem circleBundlesOverPlanarBases_mobius (C : CompactCarrier.{u})
    (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U) (M : MobiusBase.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model M.surface.kind⟯ M.surface.Carrier) :
    ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F (M.embedding ∘ e) Ψ :=
  MobiusCover.exists_isTwistedChart (CircleFibration.relabelBase F M.surface e) M.isSmoothEmbedding
    M.range_embedding

theorem circleBundlesOverPlanarBasesStandard : CircleBundlesOverPlanarBasesStandard.{u} :=
  fun C U F => ⟨fun k hk P e => circleBundlesOverPlanarBases_planar C U F k hk P e,
    fun M e => circleBundlesOverPlanarBases_mobius C U F M e⟩

end GC.Seifert
