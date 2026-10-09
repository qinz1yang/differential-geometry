import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypSurj
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatMoves

/-!
# The generator moves of a hyperbolic closed triangle fold

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3–4; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatMoves`, one proof for both rows). For the
fold `F = hypMap` on `N = hypDomain` and the model metric, the local composite relation
`FoldRel` holds between a point and its image under each generator move, on an open piece where
the move preserves `F`:
* the deck translations `h^n = fibreTranslation (n ℓ)` on all of `N` (`foldRel_deck`);
* the screws `S₁`, `S₂`, `S₃` on the discs about `v₁`, `v₂`, `0` (`foldRel_screwOne`, …): in the
  Möbius coordinates the screws rotate by `e^{-2πi/p}` (`HypDatum.rotOne_screwOne`) and the
  adapted fibre coordinate `sⱼ` drops by `kⱼ` (the gauge terms cancel by the screw contract), which
  the Bézout identity absorbs (`tube_rot`);
* `S₃` on the disc about `v₁` (it carries the disc to its mirror, where `F = F ∘ S₃⁻¹` by
  definition) and on the wall-1 patch (wall rule `HypPhase.theta_wallOne`, gauge oddness `ψ₁ ∘ r₁`);
* `S₂⁻¹` on the wall-2 patch: its base action is `conj ∘ r₂` (`hb_screwTwo_symm`, by injectivity
  of `rotTwo` on the disc) and the wall rule is `HypPhase.theta_wallTwo` with the real period
  identity of the datum (`liftM_screwTwo_symm`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

namespace HypDatum

variable (K : HypDatum)

section Deck

def deck (n : ℤ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates := fibreTranslation (n * K.ℓ)

theorem metric_deck (n : ℤ) :
    Diffeomorph.pullbackMetric K.m.coneProfile.metric (K.deck n) = K.m.coneProfile.metric :=
  fibreTranslation_isometry _ _

theorem hb_deck (n : ℤ) (x : ModelCoordinates) : hb (K.deck n x) = hb x := by
  rw [hb, hb, deck, planeOf_fibreTranslation]

theorem planeOf_deck (n : ℤ) (x : ModelCoordinates) : planeOf (K.deck n x) = planeOf x :=
  planeOf_fibreTranslation _ _

theorem two_deck (n : ℤ) (x : ModelCoordinates) : K.deck n x 2 = x 2 + n * K.ℓ :=
  fibreTranslation_two _ _

theorem div_deck (n : ℤ) (x : ModelCoordinates) : K.deck n x 2 / K.ℓ = x 2 / K.ℓ + n := by
  rw [two_deck, add_div, mul_div_cancel_right₀ _ K.ℓ_ne]

theorem liftP_shift {y y' : ModelCoordinates} (n : ℤ) (hp : hb y' = hb y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.liftP y' = K.liftP y := by
  unfold liftP
  rw [hp, h2, eC_add, eC_int, mul_one]

theorem liftP_deck (n : ℤ) (x : ModelCoordinates) : K.liftP (K.deck n x) = K.liftP x :=
  K.liftP_shift n (K.hb_deck n x) (K.div_deck n x)

theorem liftM_deck (n : ℤ) (x : ModelCoordinates) : K.liftM (K.deck n x) = K.liftM x := by
  unfold liftM
  congr 1
  apply K.liftP_shift (-n)
  · rw [hb_reflectMap, hb_reflectMap, hb_deck]
  · rw [reflectMap_two, reflectMap_two, sub_div, sub_div, K.div_deck]
    push_cast
    ring

theorem tubeOne_shift {y y' : ModelCoordinates} (n : ℤ) (hp : hb y' = hb y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeOne y' = K.tubeOne y := by
  unfold tubeOne sOne
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaOne (hb y) =
    y 2 / K.ℓ + K.betaOne (hb y) + n by ring, eC_int_mul_add,
    show ((K.σ.p₁ : ℕ) : ℝ) = ((K.σ.p₁ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeTwo_shift {y y' : ModelCoordinates} (n : ℤ) (hp : hb y' = hb y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeTwo y' = K.tubeTwo y := by
  unfold tubeTwo sTwo
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaTwo (hb y) =
    y 2 / K.ℓ + K.betaTwo (hb y) + n by ring, eC_int_mul_add,
    show ((K.σ.p₂ : ℕ) : ℝ) = ((K.σ.p₂ : ℤ) : ℝ) by push_cast; rfl, eC_int_mul_add]

theorem tubeThree_shift {y y' : ModelCoordinates} (n : ℤ) (hp : hb y' = hb y)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : K.tubeThree y' = K.tubeThree y := by
  unfold tubeThree sThree
  rw [hp, h2, show y 2 / K.ℓ + n + K.betaThree = y 2 / K.ℓ + K.betaThree + n by ring,
    eC_int_mul_add, show ((K.σ.p₃ : ℕ) : ℝ) = ((K.σ.p₃ : ℤ) : ℝ) by push_cast; rfl,
    eC_int_mul_add]

theorem rotThreeInv_deck (n : ℤ) (x : ModelCoordinates) :
    K.tubeOne (K.rotThreeInv (K.deck n x)) = K.tubeOne (K.rotThreeInv x) := by
  refine K.tubeOne_shift n ?_ ?_
  · rw [hb_rotThreeInv, hb_rotThreeInv, hb_deck]
  · rw [rotThreeInv, rotThreeInv, ofPlane_apply_two, ofPlane_apply_two, add_div, add_div,
      K.div_deck]
    ring

end Deck

section Screws

theorem apexOne_screwOne (x : ModelCoordinates) :
    hypApexOne K.σ (hb (K.screwOne x)) = hypApexOne K.σ (hb x) := by
  rw [hypApexOne, hypApexOne, K.rotOne_screwOne, mul_pow, circle_exp_pow_eq_one K.p₁_pos, one_mul]

theorem apexTwo_screwTwo (x : ModelCoordinates) :
    hypApexTwo K.σ (hb (K.screwTwo x)) = hypApexTwo K.σ (hb x) := by
  rw [hypApexTwo, hypApexTwo, K.rotTwo_screwTwo, mul_pow, circle_exp_pow_eq_one K.p₂_pos, one_mul]

theorem sOne_screwOne (x : ModelCoordinates) :
    K.sOne (K.screwOne x) = K.sOne x - K.q₁ / K.σ.p₁ := by
  unfold sOne betaOne
  rw [K.apexOne_screwOne, K.two_screwOne' x]
  have hℓ := K.ℓ_ne
  rw [show (K.q₁ : ℝ) / K.σ.p₁ = K.k₁ from rfl]
  field_simp
  ring

theorem sTwo_screwTwo (x : ModelCoordinates) :
    K.sTwo (K.screwTwo x) = K.sTwo x - K.q₂ / K.σ.p₂ := by
  unfold sTwo betaTwo
  rw [K.apexTwo_screwTwo, K.two_screwTwo' x]
  have hℓ := K.ℓ_ne
  rw [show (K.q₂ : ℝ) / K.σ.p₂ = K.k₂ from rfl]
  field_simp
  ring

theorem sThree_screwThree (x : ModelCoordinates) :
    K.sThree (K.screwThree x) = K.sThree x - K.q₃ / K.σ.p₃ := by
  unfold sThree
  rw [K.two_screwThree, show (K.q₃ : ℝ) / K.σ.p₃ = K.k₃ from rfl]
  have hℓ := K.ℓ_ne
  field_simp
  ring

theorem tubeOne_screwOne (x : ModelCoordinates) : K.tubeOne (K.screwOne x) = K.tubeOne x := by
  unfold tubeOne
  rw [K.rotOne_screwOne, K.sOne_screwOne]
  exact tube_rot K.p₁_pos K.bez₁ _ _

theorem tubeTwo_screwTwo (x : ModelCoordinates) : K.tubeTwo (K.screwTwo x) = K.tubeTwo x := by
  unfold tubeTwo
  rw [K.rotTwo_screwTwo, K.sTwo_screwTwo]
  exact tube_rot K.p₂_pos K.bez₂ _ _

theorem tubeThree_screwThree (x : ModelCoordinates) :
    K.tubeThree (K.screwThree x) = K.tubeThree x := by
  unfold tubeThree
  rw [K.hb_screwThree, K.sThree_screwThree, mul_left_comm]
  have := tube_rot K.p₃_pos K.bez₃ ((Circle.exp (Real.pi / K.σ.p₃) : ℂ) * hb x) (K.sThree x)
  rw [← mul_assoc] at this ⊢
  exact this

theorem screwOne_mem_discOne {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    hb (K.screwOne x) ∈ discOne K.D :=
  ⟨norm_hypDisc_lt_one _, by rw [K.rotOne_screwOne, norm_circle_mul]; exact hd.2⟩

theorem screwTwo_mem_discTwo {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    hb (K.screwTwo x) ∈ discTwo K.D :=
  ⟨norm_hypDisc_lt_one _, by rw [K.rotTwo_screwTwo, norm_circle_mul]; exact hd.2⟩

theorem screwThree_mem_discThree {x : ModelCoordinates} (hd : hb x ∈ discThree K.D) :
    hb (K.screwThree x) ∈ discThree K.D := by
  change ‖hb (K.screwThree x)‖ < _
  rw [K.hb_screwThree, norm_circle_mul]
  exact hd

theorem conj_hb_screwThree (x : ModelCoordinates) :
    conj (hb (K.screwThree x)) = K.σ.refl 1 (hb x) := by
  rw [K.hb_screwThree, map_mul, ← Circle.coe_inv_eq_conj, ← Circle.exp_neg]
  change _ = exp (2 * (K.σ.θ₃ : ℂ) * I) * conj (hb x)
  rw [Circle.coe_exp, FlatDatum.p_inv_eq K.p₃_pos (HypFold.θ₃_mul K.σ)]
  congr 2
  push_cast
  ring

theorem screwThree_mem_discOneMirror {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    hb (K.screwThree x) ∈ discOneMirror K.D := by
  rw [mem_discOneMirror_iff, K.conj_hb_screwThree]
  exact refl_one_mem_discOne K.hσ hd

end Screws

section Walls

theorem liftM_screwThree {y : ModelCoordinates} (hp : hb y ∈ patchOne K.D) :
    K.liftM (K.screwThree y) = K.liftP y := by
  set z := hb y with hz
  have hV : z ∈ K.D.V 1 := patchOne_subset_V K.D hp
  have hz1 : ‖z‖ < 1 := norm_lt_one_of_mem_V K.hσ hV
  have hre : 3 / 2 < (K.D.f z).re := hp.2.2.2.2.2.1
  have hfl : K.D.f (K.σ.refl 1 z) = conj (K.D.f z) := K.D.f_refl 1 z hV
  have hθ := K.phase.theta_wallOne (z := z) (z' := K.σ.refl 1 z) hre (K.ψ₁_refl z hz1)
  unfold liftM liftP conjPair
  rw [hb_reflectMap, K.conj_hb_screwThree, ← hz, hfl, Complex.conj_conj,
    reflectMap_two, K.two_screwThree]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  have hA : (K.c₀ - (y 2 - K.ℓ * K.k₃)) / K.ℓ = K.k₁ + K.k₂ + K.k₃ - y 2 / K.ℓ := by
    unfold c₀
    field_simp
    ring
  rw [hA]
  rw [phase_e] at hθ
  linear_combination hθ

theorem rotTwo_injOn {a b : ℂ} (ha : ‖a‖ < 1) (hb' : ‖b‖ < 1) (h : K.σ.rotTwo a = K.σ.rotTwo b) :
    a = b := by
  rw [HypFold.rotTwo_eq_mul_mob K.hσ, HypFold.rotTwo_eq_mul_mob K.hσ] at h
  have hm := mul_left_cancel₀ (neg_ne_zero.2 (Complex.exp_ne_zero _)) h
  have hv := HypFold.normSq_vertexTwo_ne_one K.hσ
  have hda : 1 - conj K.σ.vertexTwo * a ≠ 0 := by
    rw [HypFold.conj_vertexTwo (σ := K.σ)]; exact HypFold.one_sub_vertexTwo_mul_ne_zero K.hσ ha
  have hdb : 1 - conj K.σ.vertexTwo * b ≠ 0 := by
    rw [HypFold.conj_vertexTwo (σ := K.σ)]; exact HypFold.one_sub_vertexTwo_mul_ne_zero K.hσ hb'
  rw [← HypFold.mobInv_mob hv hda, hm, HypFold.mobInv_mob hv hdb]

theorem rotTwo_conj_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    K.σ.rotTwo (conj (K.σ.refl 2 z)) =
      (Circle.exp (2 * Real.pi / K.σ.p₂) : ℂ) * K.σ.rotTwo z := by
  have h0 : K.σ.rotTwo (conj (K.σ.refl 2 z)) =
      exp (2 * (K.σ.θ₂ : ℂ) * I) * conj (K.σ.rotTwo (K.σ.refl 2 z)) :=
    HypFold.rotTwo_refl_zero K.hσ _
  rw [h0, HypFold.rotTwo_refl_two K.hσ hz, Complex.conj_conj, Circle.coe_exp,
    FlatDatum.p_inv_eq K.p₂_pos (HypFold.θ₂_mul K.σ)]
  congr 2
  push_cast
  ring

theorem hb_screwTwo_symm (y : ModelCoordinates) :
    hb (K.screwTwo.symm y) = conj (K.σ.refl 2 (hb y)) := by
  have hy1 : ‖hb y‖ < 1 := norm_hypDisc_lt_one _
  have h := K.rotTwo_screwTwo (K.screwTwo.symm y)
  rw [Diffeomorph.apply_symm_apply] at h
  apply K.rotTwo_injOn (norm_hypDisc_lt_one _)
    (by rw [Complex.norm_conj]; exact HypFold.norm_refl_lt_one K.hσ 2 hy1)
  rw [K.rotTwo_conj_refl_two hy1, h, ← mul_assoc, ← Circle.coe_mul, ← Circle.exp_add,
    show 2 * Real.pi / K.σ.p₂ + -2 * Real.pi / K.σ.p₂ = 0 by ring, Circle.exp_zero,
    Circle.coe_one, one_mul]
  rfl

theorem two_screwTwo_symm (y : ModelCoordinates) :
    K.screwTwo.symm y 2 = y 2 + K.ℓ * K.k₂ - K.ψ₂ (hb y) + K.ψ₂ (conj (K.σ.refl 2 (hb y))) := by
  have h := K.two_screwTwo' (K.screwTwo.symm y)
  rw [Diffeomorph.apply_symm_apply, K.hb_screwTwo_symm] at h
  linarith

theorem liftM_screwTwo_symm {y : ModelCoordinates} (hp : hb y ∈ patchTwo K.D) :
    K.liftM (K.screwTwo.symm y) = K.liftP y := by
  set z := hb y with hz
  have hV : z ∈ K.D.V 2 := patchTwo_subset_V K.D hp
  have hz1 : ‖z‖ < 1 := norm_lt_one_of_mem_V K.hσ hV
  have hz2 : ‖K.σ.refl 2 z‖ < 1 := HypFold.norm_refl_lt_one K.hσ 2 hz1
  have hre1 : -(3 / 2) < (K.D.f z).re := hp.2.2.2.2.2.1
  have hre2 : (K.D.f z).re < 3 / 2 := hp.2.2.2.2.2.2.1
  have hn : normSq (K.D.f z) ≤ 25 / 4 := le_of_lt hp.2.2.2.2.2.2.2.1
  have hfl : K.D.f (K.σ.refl 2 z) = conj (K.D.f z) := K.D.f_refl 2 z hV
  have hθ := K.phase.theta_wallTwo (z := z) (z' := K.σ.refl 2 z) hre1 hre2 hn K.ℓ_ne
    (K.wallTwo' hz1)
  have hψ := K.ψ₂_conj (K.σ.refl 2 z) hz2
  unfold liftM liftP conjPair
  rw [hb_reflectMap, K.hb_screwTwo_symm, Complex.conj_conj, ← hz, hfl, Complex.conj_conj,
    reflectMap_two, K.two_screwTwo_symm, ← hz, hψ]
  congr 1
  rw [psiC, hfl, mul_inv, ← Circle.exp_neg, neg_neg, eC, eC, ← Circle.exp_neg, ← Circle.exp_add,
    psiC, ← Circle.exp_add]
  congr 1
  have hℓ := K.ℓ_ne
  have hA : (K.c₀ - (y 2 + K.ℓ * K.k₂ - K.ψ₂ z + -K.ψ₂ (K.σ.refl 2 z))) / K.ℓ =
      K.k₁ - y 2 / K.ℓ + (K.ψ₂ z + K.ψ₂ (K.σ.refl 2 z)) / K.ℓ := by
    unfold c₀
    field_simp
    ring
  rw [hA]
  simp only [phase_k₁, phase_ℓ, phase_ψ₂] at hθ
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at hθ ⊢
  linear_combination hθ

end Walls

end HypDatum

section Moves

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)

theorem hypMap_deck (K : HypDatum) (n : ℤ) (x : ModelCoordinates) :
    hypMap C hc h3 K (K.deck n x) = hypMap C hc h3 K x := by
  unfold hypMap
  rw [K.hb_deck, K.liftP_deck, K.liftM_deck, K.rotThreeInv_deck,
    K.tubeOne_shift n (K.hb_deck n x) (K.div_deck n x),
    K.tubeTwo_shift n (K.hb_deck n x) (K.div_deck n x),
    K.tubeThree_shift n (K.hb_deck n x) (K.div_deck n x)]

theorem foldRel_deck (K : HypDatum) (n : ℤ) {x : ModelCoordinates} (hx : x ∈ hypDomain K) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.deck n x) := by
  refine ⟨K.deck n, K.metric_deck n, rfl, hypDomain K, (hypDomain K).isOpen, hx, subset_rfl,
    fun y hy => ?_, fun y _ => hypMap_deck C hc h3 K n y⟩
  change hb (K.deck n y) ∈ hypBase K
  rw [K.hb_deck]
  exact hy

theorem foldRel_screwOne (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discOne K.D) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwOne x) := by
  have hU : IsOpen (hb ⁻¹' discOne K.D) := (isOpen_discOne K.hσ).preimage continuous_hb
  have hsub : hb ⁻¹' discOne K.D ⊆ hypDomain K := fun y hy => by
    change hb y ∈ hypBase K
    simp only [hypBase, mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hy)))
  refine ⟨K.screwOne, K.metric_screwOne, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwOne_mem_discOne hy), fun y hy => ?_⟩
  rw [hypMap_of_discOne C hc h3 K (K.screwOne_mem_discOne hy), hypMap_of_discOne C hc h3 K hy,
    K.tubeOne_screwOne]

theorem foldRel_screwTwo (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discTwo K.D) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwTwo x) := by
  have hU : IsOpen (hb ⁻¹' discTwo K.D) := (isOpen_discTwo K.hσ).preimage continuous_hb
  have hsub : hb ⁻¹' discTwo K.D ⊆ hypDomain K := fun y hy => by
    change hb y ∈ hypBase K
    simp only [hypBase, mem_union]
    exact Or.inl (Or.inr hy)
  refine ⟨K.screwTwo, K.metric_screwTwo, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwTwo_mem_discTwo hy), fun y hy => ?_⟩
  rw [hypMap_of_discTwo C hc h3 K (K.screwTwo_mem_discTwo hy), hypMap_of_discTwo C hc h3 K hy,
    K.tubeTwo_screwTwo]

theorem foldRel_screwThree (K : HypDatum) {x : ModelCoordinates} (hd : hb x ∈ discThree K.D) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwThree x) := by
  have hU : IsOpen (hb ⁻¹' discThree K.D) := isOpen_discThree.preimage continuous_hb
  have hsub : hb ⁻¹' discThree K.D ⊆ hypDomain K := fun y hy => by
    change hb y ∈ hypBase K
    simp only [hypBase, mem_union]
    exact Or.inr hy
  refine ⟨K.screwThree, K.metric_screwThree, rfl, _, hU, hd, hsub,
    fun y hy => hsub (K.screwThree_mem_discThree hy), fun y hy => ?_⟩
  rw [hypMap_of_discThree C hc h3 K (K.screwThree_mem_discThree hy),
    hypMap_of_discThree C hc h3 K hy, K.tubeThree_screwThree]

theorem foldRel_screwThree_discOne (K : HypDatum) {x : ModelCoordinates}
    (hd : hb x ∈ discOne K.D) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x (K.screwThree x) := by
  have hU : IsOpen (hb ⁻¹' discOne K.D) := (isOpen_discOne K.hσ).preimage continuous_hb
  refine ⟨K.screwThree, K.metric_screwThree, rfl, _, hU, hd, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_⟩
  · change hb y ∈ hypBase K
    simp only [hypBase, mem_union]
    exact Or.inl (Or.inl (Or.inl (Or.inr hy)))
  · change hb (K.screwThree y) ∈ hypBase K
    simp only [hypBase, mem_union]
    exact Or.inl (Or.inl (Or.inr (K.screwThree_mem_discOneMirror hy)))
  · rw [hypMap_of_discOneMirror C hc h3 K (K.screwThree_mem_discOneMirror hy),
      hypMap_of_discOne C hc h3 K hy, ← K.screwThree_symm, Diffeomorph.symm_apply_apply]

end Moves

section PatchMoves

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

theorem main_subset_hypBase (K : HypDatum) {z : ℂ} (hm : z ∈ mainSet K.D) :
    z ∈ hypBase K := by
  simp only [hypBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hm))))

theorem conjMain_subset_hypBase (K : HypDatum) {z : ℂ} (hm : conj z ∈ mainSet K.D) :
    z ∈ hypBase K := by
  simp only [hypBase, mem_union]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hm))))

theorem foldRel_screwThree_patchOne {x : ModelCoordinates} (hp : hb x ∈ patchOne (𝒦).D) :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x
      ((𝒦).screwThree x) := by
  have hU : IsOpen (hb ⁻¹' patchOne (𝒦).D) :=
    (isOpen_patchOne (𝒦).hσ).preimage continuous_hb
  have hmain : ∀ {z : ℂ}, z ∈ patchOne (𝒦).D → z ∈ mainSet (𝒦).D :=
    fun h => Or.inl (Or.inr h)
  have hconj : ∀ {y : ModelCoordinates}, hb y ∈ patchOne (𝒦).D →
      conj (hb ((𝒦).screwThree y)) ∈ mainSet (𝒦).D := fun hy => by
    rw [HypDatum.conj_hb_screwThree]
    exact hmain (refl_mem_patchOne (𝒦).hσ hy)
  refine ⟨(𝒦).screwThree, (𝒦).metric_screwThree, rfl, _, hU, hp,
    fun y hy => main_subset_hypBase _ (hmain hy),
    fun y hy => conjMain_subset_hypBase _ (hconj hy), fun y hy => ?_⟩
  rw [hypMap_of_conjMain C hc h3 hχ D (hconj hy), hypMap_of_main C hc h3 hχ D (hmain hy),
    (𝒦).liftM_screwThree hy]

theorem foldRel_screwTwoInv_patchTwo {x : ModelCoordinates} (hp : hb x ∈ patchTwo (𝒦).D) :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x
      ((𝒦).screwTwo.symm x) := by
  have hU : IsOpen (hb ⁻¹' patchTwo (𝒦).D) :=
    (isOpen_patchTwo (𝒦).hσ).preimage continuous_hb
  have hmain : ∀ {z : ℂ}, z ∈ patchTwo (𝒦).D → z ∈ mainSet (𝒦).D := fun h => Or.inr h
  have hconj : ∀ {y : ModelCoordinates}, hb y ∈ patchTwo (𝒦).D →
      conj (hb ((𝒦).screwTwo.symm y)) ∈ mainSet (𝒦).D := fun hy => by
    rw [HypDatum.hb_screwTwo_symm, Complex.conj_conj]
    exact hmain (refl_mem_patchTwo (𝒦).hσ hy)
  refine ⟨(𝒦).screwTwo.symm, FoldRel.isometry_symm (𝒦).metric_screwTwo, rfl, _, hU, hp,
    fun y hy => main_subset_hypBase _ (hmain hy),
    fun y hy => conjMain_subset_hypBase _ (hconj hy), fun y hy => ?_⟩
  rw [hypMap_of_conjMain C hc h3 hχ D (hconj hy), hypMap_of_main C hc h3 hχ D (hmain hy),
    (𝒦).liftM_screwTwo_symm hy]

end PatchMoves

end Hyp

end ClosedTriangle

end GC.Seifert
