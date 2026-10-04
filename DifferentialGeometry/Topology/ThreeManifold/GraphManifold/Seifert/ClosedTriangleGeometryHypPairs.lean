import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypReduce
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatPairs

/-!
# Same-image pairs of a hyperbolic closed triangle fold

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatPairs`, both rows at once). Two points of
the fold domain with the same image are related by the local composite relation
(`foldRel_of_hypMap_eq`): both reduce to the vertex fibres or the doubled triangle minus its
vertices (`exists_foldRel_reduced`). Over a vertex the fibre coordinates differ by `n/p`, and the
Bézout identity writes the difference as a power of the screw times a deck translation
(`foldRel_vertex_fibre`; the screw fixes the vertex fibre and shifts it by `ℓ q/p`, the gauge
terms cancelling at the centre). A core circle is never in the image of the punctured chart.
Over the doubled triangle the closed punctured chart is injective, so equal images give equal
base lifts: the fold is injective on the triangle minus `0`, `Im f > 0` inside and the walls go to
the real line, so a point of the triangle and one of the mirror with the same image lie on a wall,
and the matching pairing (`S₃` for wall 1, `S₂⁻¹` for wall 2, the identity for wall 0) relates them
(`foldRel_TC`).
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

theorem eq_deck_of {y y' : ModelCoordinates} (hp : hb y' = hb y) {n : ℤ}
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : y' = K.deck n y := by
  apply modelCoordinates_ext
  · rw [K.planeOf_deck, ← hypDiscInv_hypDisc (planeOf y'), ← hypDiscInv_hypDisc (planeOf y)]
    exact congrArg hypDiscInv hp
  · rw [K.two_deck]
    have hℓ := K.ℓ_ne
    field_simp at h2
    linarith

theorem screwOne_vertex {y : ModelCoordinates} (hy : hb y = K.σ.vertexOne) :
    hb (K.screwOne y) = K.σ.vertexOne ∧ K.screwOne y 2 = y 2 - K.ℓ * K.q₁ / K.σ.p₁ := by
  have h1 : hb (K.screwOne y) = K.σ.vertexOne := by
    by_contra hne
    apply rotOne_ne_zero K.hσ (norm_hypDisc_lt_one _) hne
    change K.σ.rotOne (hb (K.screwOne y)) = 0
    rw [K.rotOne_screwOne, hy, rotOne_vertexOne K.hσ, mul_zero]
  refine ⟨h1, ?_⟩
  rw [K.two_screwOne', h1, hy, HypDatum.k₁]
  ring

theorem screwTwo_vertex {y : ModelCoordinates} (hy : hb y = K.σ.vertexTwo) :
    hb (K.screwTwo y) = K.σ.vertexTwo ∧ K.screwTwo y 2 = y 2 - K.ℓ * K.q₂ / K.σ.p₂ := by
  have h1 : hb (K.screwTwo y) = K.σ.vertexTwo := by
    by_contra hne
    apply rotTwo_ne_zero K.hσ (norm_hypDisc_lt_one _) hne
    change K.σ.rotTwo (hb (K.screwTwo y)) = 0
    rw [K.rotTwo_screwTwo, hy, rotTwo_vertexTwo K.hσ, mul_zero]
  refine ⟨h1, ?_⟩
  rw [K.two_screwTwo', h1, hy, HypDatum.k₂]
  ring

theorem screwThree_vertex {y : ModelCoordinates} (hy : hb y = 0) :
    hb (K.screwThree y) = 0 ∧ K.screwThree y 2 = y 2 - K.ℓ * K.q₃ / K.σ.p₃ := by
  refine ⟨by rw [K.hb_screwThree, hy, mul_zero], ?_⟩
  rw [K.two_screwThree, HypDatum.k₃]
  ring

end HypDatum

section VertexFibre

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : HypDatum)

theorem foldRel_vertex_fibre (S : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates) (v : ℂ)
    {p : ℕ} (hp : 0 < p) {q a b : ℤ} (hbez : (p : ℤ) * b - a * q = 1)
    (hS : ∀ y : ModelCoordinates, hb y = v →
      FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) y (S y) ∧
        hb (S y) = v ∧ S y 2 = y 2 - K.ℓ * q / p)
    {y y' : ModelCoordinates} (hy : hb y = v) (hy' : hb y' = v) (n : ℤ)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n / p) :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) y y' := by
  have hit : ∀ k : ℕ, FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) y
      (S^[k] y) ∧ hb (S^[k] y) = v ∧ (S^[k] y) 2 = y 2 - k * (K.ℓ * q / p) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, hy, by simp⟩
      obtain ⟨hr, -, -⟩ := hS y hy
      exact FoldRel.refl (hypDomain K).isOpen hr.mem_left
    | succ k ih =>
      obtain ⟨hr, hv, h2k⟩ := ih
      obtain ⟨hr', hv', h2'⟩ := hS _ hv
      rw [Function.iterate_succ_apply']
      refine ⟨hr.trans hr', hv', ?_⟩
      rw [h2', h2k]
      push_cast
      ring
  set r := (n * a) % (p : ℤ) with hr
  set Q := (n * a) / (p : ℤ) with hQ
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
  have hdiv : n * a = p * Q + r := by
    have := Int.mul_ediv_add_emod (n * a) p
    linarith
  obtain ⟨hrel, hv, h2k⟩ := hit r.toNat
  have hcast : ((r.toNat : ℕ) : ℝ) = (r : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hr0
  have hy'eq : y' = K.deck (n * b - Q * q) (S^[r.toNat] y) := by
    apply K.eq_deck_of (by rw [hv, hy'])
    rw [h2k, hcast, h2]
    have hℓ := K.ℓ_ne
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hb' : (p : ℝ) * b - a * q = 1 := by exact_mod_cast hbez
    have hdiv' : (n : ℝ) * a = p * Q + r := by exact_mod_cast hdiv
    have key : (n : ℝ) = -(r : ℝ) * q + p * (n * b - Q * q) := by
      linear_combination (-(n : ℝ)) * hb' - (q : ℝ) * hdiv'
    have e1 : (y 2 - (r : ℝ) * (K.ℓ * q / p)) / K.ℓ = y 2 / K.ℓ - (r : ℝ) * q / p := by
      field_simp
    have e2 : (n : ℝ) / p = -(r : ℝ) * q / p + (n * b - Q * q) := by
      field_simp
      linear_combination key
    rw [e1]
    push_cast
    linear_combination e2
  rw [hy'eq]
  exact hrel.trans (foldRel_deck C hc h3 K _ hrel.mem_right)

theorem tubeOne_snd_eq {x x' : ModelCoordinates} (K : HypDatum)
    (hx : hb x = K.σ.vertexOne) (hx' : hb x' = K.σ.vertexOne)
    (h : K.tubeOne x = K.tubeOne x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₁ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₁ : ℝ) ≠ 0 := by exact_mod_cast K.p₁_pos.ne'
  simp only [HypDatum.sOne, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeTwo_snd_eq {x x' : ModelCoordinates} (K : HypDatum)
    (hx : hb x = K.σ.vertexTwo) (hx' : hb x' = K.σ.vertexTwo)
    (h : K.tubeTwo x = K.tubeTwo x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₂ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
  simp only [HypDatum.sTwo, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeThree_snd_eq {x x' : ModelCoordinates} (K : HypDatum)
    (h : K.tubeThree x = K.tubeThree x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₃ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  simp only [HypDatum.sThree] at hn
  field_simp
  linear_combination hn

theorem vertexOne_mem_discOne (K : HypDatum) : K.σ.vertexOne ∈ discOne K.D :=
  mem_discOne_vertexOne K.hσ

theorem vertexTwo_mem_discTwo (K : HypDatum) : K.σ.vertexTwo ∈ discTwo K.D :=
  mem_discTwo_vertexTwo K.hσ

theorem zero_mem_discThree' (K : HypDatum) : (0 : ℂ) ∈ discThree K.D :=
  zero_mem_discThree

theorem foldRel_vertexOne {x x' : ModelCoordinates} (hx : hb x = K.σ.vertexOne)
    (hx' : hb x' = K.σ.vertexOne) (h : hypMap C hc h3 K x = hypMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x x' := by
  have hd := vertexOne_mem_discOne K
  rw [hypMap_of_discOne C hc h3 K (hx ▸ hd), hypMap_of_discOne C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeOne_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeOne_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeOne_snd_eq K hx hx' ht
  refine foldRel_vertex_fibre C hc h3 K K.screwOne K.σ.vertexOne K.p₁_pos K.bez₁ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwOne_vertex hy
  exact ⟨foldRel_screwOne C hc h3 K (hy ▸ hd), h1, h2⟩

theorem foldRel_vertexTwo {x x' : ModelCoordinates} (hx : hb x = K.σ.vertexTwo)
    (hx' : hb x' = K.σ.vertexTwo) (h : hypMap C hc h3 K x = hypMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x x' := by
  have hd := vertexTwo_mem_discTwo K
  rw [hypMap_of_discTwo C hc h3 K (hx ▸ hd), hypMap_of_discTwo C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeTwo_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeTwo_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeTwo_snd_eq K hx hx' ht
  refine foldRel_vertex_fibre C hc h3 K K.screwTwo K.σ.vertexTwo K.p₂_pos K.bez₂ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwTwo_vertex hy
  exact ⟨foldRel_screwTwo C hc h3 K (hy ▸ hd), h1, h2⟩

theorem foldRel_vertexThree {x x' : ModelCoordinates} (hx : hb x = 0)
    (hx' : hb x' = 0) (h : hypMap C hc h3 K x = hypMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x x' := by
  have hd := zero_mem_discThree' K
  rw [hypMap_of_discThree C hc h3 K (hx ▸ hd), hypMap_of_discThree C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeThree_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeThree_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeThree_snd_eq K ht
  refine foldRel_vertex_fibre C hc h3 K K.screwThree 0 K.p₃_pos K.bez₃ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwThree_vertex hy
  exact ⟨foldRel_screwThree C hc h3 K (hy ▸ hd), h1, h2⟩

theorem hypMap_vertex_core {x : ModelCoordinates}
    (hx : hb x = K.σ.vertexOne ∨ hb x = K.σ.vertexTwo ∨ hb x = 0) :
    ∃ j : Fin 3, ∃ w : Circle, hypMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 j) (0, w) ∧
      hb x = (if j = 1 then K.σ.vertexOne else if j = 2 then K.σ.vertexTwo else 0) := by
  rcases hx with hx | hx | hx
  · refine ⟨1, (K.tubeOne x).2, ?_, by simp [hx]⟩
    rw [hypMap_of_discOne C hc h3 K (hx ▸ vertexOne_mem_discOne K)]
    congr 1
    refine Prod.ext ?_ rfl
    change K.σ.rotOne (hb x) * _ = 0
    rw [hx, rotOne_vertexOne K.hσ, zero_mul]
  · refine ⟨2, (K.tubeTwo x).2, ?_, by simp [hx]⟩
    rw [hypMap_of_discTwo C hc h3 K (hx ▸ vertexTwo_mem_discTwo K)]
    congr 1
    refine Prod.ext ?_ rfl
    change K.σ.rotTwo (hb x) * _ = 0
    rw [hx, rotTwo_vertexTwo K.hσ, zero_mul]
  · refine ⟨0, (K.tubeThree x).2, ?_, by simp [hx]⟩
    rw [hypMap_of_discThree C hc h3 K (hx ▸ zero_mem_discThree' K)]
    congr 1
    refine Prod.ext ?_ rfl
    change _ * hb x * _ = 0
    rw [hx, mul_zero, zero_mul]

end VertexFibre

section Regular

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : HypDatum)

theorem liftP_mem_closedDomain_of_T {x : ModelCoordinates} (hT : hb x ∈ K.σ.triangle)
    (h0 : hb x ≠ 0) (h1 : hb x ≠ K.σ.vertexOne) (h2 : hb x ≠ K.σ.vertexTwo) :
    K.liftP x ∈ closedDomain := by
  refine ⟨(K.D.bijOn_f.mapsTo ⟨hT, h0⟩).1, fun h => h1 ?_, fun h => h2 ?_⟩
  · exact K.D.eq_of_f_eq ⟨hT, h0⟩ (CompactShape.vertexOne_mem_diff (σ := K.σ))
      (h.trans K.D.f_vertexOne.symm)
  · exact K.D.eq_of_f_eq ⟨hT, h0⟩ (CompactShape.vertexTwo_mem_diff (σ := K.σ))
      (h.trans K.D.f_vertexTwo.symm)

theorem liftM_fst (x : ModelCoordinates) :
    (K.liftM x).1 = conj (K.D.f (conj (hb x))) := by
  change conj (K.D.f (hb (reflectMap K.c₀ x))) = _
  rw [HypDatum.hb_reflectMap]

theorem liftM_mem_closedDomain_of_T {x : ModelCoordinates}
    (hT : conj (hb x) ∈ K.σ.triangle) (h0 : conj (hb x) ≠ 0)
    (h1 : conj (hb x) ≠ K.σ.vertexOne) (h2 : conj (hb x) ≠ K.σ.vertexTwo) :
    K.liftM x ∈ closedDomain := by
  have hP := liftP_mem_closedDomain_of_T K (x := reflectMap K.c₀ x)
    (by rw [HypDatum.hb_reflectMap]; exact hT) (by rw [HypDatum.hb_reflectMap]; exact h0)
    (by rw [HypDatum.hb_reflectMap]; exact h1) (by rw [HypDatum.hb_reflectMap]; exact h2)
  obtain ⟨a, b, c⟩ := hP
  change ‖conj (K.liftP (reflectMap K.c₀ x)).1‖ < 7 / 2 ∧
    conj (K.liftP (reflectMap K.c₀ x)).1 ≠ 3 / 2 ∧ conj (K.liftP (reflectMap K.c₀ x)).1 ≠ -(3 / 2)
  rw [Complex.norm_conj]
  refine ⟨a, fun h => b ?_, fun h => c ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

theorem foldRel_of_liftP_eq {x x' : ModelCoordinates} (hx : x ∈ hypDomain K)
    (hT : hb x ∈ K.σ.triangle) (h0 : hb x ≠ 0)
    (hT' : hb x' ∈ K.σ.triangle) (h0' : hb x' ≠ 0) (h : K.liftP x = K.liftP x') :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x x' := by
  have hz : hb x' = hb x :=
    (K.D.eq_of_f_eq ⟨hT, h0⟩ ⟨hT', h0'⟩ (congrArg Prod.fst h)).symm
  have h2 := congrArg Prod.snd h
  change eC (x 2 / K.ℓ) * K.psiC (hb x) = eC (x' 2 / K.ℓ) * K.psiC (hb x') at h2
  rw [hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [K.eq_deck_of hz hn]
  exact foldRel_deck C hc h3 K n hx

theorem foldRel_of_liftM_eq {x x' : ModelCoordinates} (hx : x ∈ hypDomain K)
    (hT : conj (hb x) ∈ K.σ.triangle) (h0 : conj (hb x) ≠ 0)
    (hT' : conj (hb x') ∈ K.σ.triangle) (h0' : conj (hb x') ≠ 0)
    (h : K.liftM x = K.liftM x') :
    FoldRel K.m.coneProfile.metric (hypDomain K) (hypMap C hc h3 K) x x' := by
  have h' : K.liftP (reflectMap K.c₀ x) = K.liftP (reflectMap K.c₀ x') := by
    have := congrArg conjPair h
    simpa only [HypDatum.liftM, conjPair_conjPair] using this
  have hz : conj (hb x') = conj (hb x) := by
    have := (K.D.eq_of_f_eq ⟨hT, h0⟩ ⟨hT', h0'⟩ (by
      have := congrArg Prod.fst h'
      simpa only [HypDatum.liftP, HypDatum.hb_reflectMap] using this)).symm
    exact this
  have hz' : hb x' = hb x := by simpa using congrArg conj hz
  have h2 := congrArg Prod.snd h'
  change eC (reflectMap K.c₀ x 2 / K.ℓ) * K.psiC (hb (reflectMap K.c₀ x)) =
    eC (reflectMap K.c₀ x' 2 / K.ℓ) * K.psiC (hb (reflectMap K.c₀ x')) at h2
  rw [HypDatum.hb_reflectMap, HypDatum.hb_reflectMap, hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [reflectMap_two, reflectMap_two] at hn
  have hn' : x' 2 / K.ℓ = x 2 / K.ℓ + ((-n : ℤ) : ℝ) := by
    have hℓ := K.ℓ_ne
    push_cast
    field_simp at hn ⊢
    linarith
  rw [K.eq_deck_of hz' hn']
  exact foldRel_deck C hc h3 K _ hx

theorem rotOne_injOn {a b : ℂ} (ha : ‖a‖ < 1) (hb' : ‖b‖ < 1) (h : K.σ.rotOne a = K.σ.rotOne b) :
    a = b := by
  rw [HypFold.rotOne_eq_mul_mob K.hσ, HypFold.rotOne_eq_mul_mob K.hσ] at h
  have hm := mul_left_cancel₀ (neg_ne_zero.2 (Complex.exp_ne_zero _)) h
  have hv := HypFold.normSq_vertexOne_ne_one K.hσ
  rw [← HypFold.mobInv_mob hv (HypFold.one_sub_conj_vertexOne_mul_ne_zero K.hσ ha), hm,
    HypFold.mobInv_mob hv (HypFold.one_sub_conj_vertexOne_mul_ne_zero K.hσ hb')]

theorem hb_screwOne_of_wallTwo {x : ModelCoordinates} (hw : K.σ.wallSide 2 (hb x) = 0) :
    hb (K.screwOne x) = K.σ.refl 1 (hb x) := by
  have hz : ‖hb x‖ < 1 := norm_hypDisc_lt_one _
  apply rotOne_injOn K (norm_hypDisc_lt_one _) (HypFold.norm_refl_lt_one K.hσ 1 hz)
  change K.σ.rotOne (hb (K.screwOne x)) = _
  rw [K.rotOne_screwOne, HypFold.rotOne_refl_one K.hσ]
  set w := K.σ.rotOne (hb x)
  set u := exp (-((K.σ.θ₁ : ℂ) * I)) * w with hu
  have h2 : (K.σ.rotTwo (hb x)).im = 0 := by
    have e := HypFold.wallSide_two_eq_rotTwo K.hσ (hb x)
    rw [hw] at e
    exact (mul_eq_zero.mp e.symm).resolve_right
      (HypFold.normSq_pos_of_ne (HypFold.one_sub_vertexTwo_mul_ne_zero K.hσ hz)).ne'
  have hui : u.im = 0 := by
    have e := HypFold.rotOne_rot_im_mul_normSq K.hσ hz
    rw [h2, mul_zero, neg_zero] at e
    have hs0 := HypFold.sideOneTwo_pos K.hσ
    have hne : (1 : ℂ) - (HypFold.sideOneTwo K.σ : ℂ) * K.σ.rotTwo (hb x) ≠ 0 := by
      intro h0
      have hn := HypFold.norm_rotTwo_lt_one K.hσ hz
      have : (HypFold.sideOneTwo K.σ : ℂ) * K.σ.rotTwo (hb x) = 1 := by linear_combination -h0
      have := congrArg norm this
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs0.le, norm_one] at this
      nlinarith [norm_nonneg (K.σ.rotTwo (hb x)), HypFold.sideOneTwo_lt_one K.hσ]
    exact (mul_eq_zero.mp e).resolve_right (HypFold.normSq_pos_of_ne hne).ne'
  have hcu : conj u = u := Complex.conj_eq_iff_im.mpr hui
  have hE : exp ((K.σ.θ₁ : ℂ) * I) * exp (-((K.σ.θ₁ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hw' : w = exp ((K.σ.θ₁ : ℂ) * I) * u := by
    rw [hu, ← mul_assoc, hE, one_mul]
  have hω : (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) =
      exp (-((K.σ.θ₁ : ℂ) * I)) * exp (-((K.σ.θ₁ : ℂ) * I)) := by
    rw [Circle.coe_exp, ← Complex.exp_add, FlatDatum.p_inv_eq K.p₁_pos (HypFold.θ₁_mul K.σ)]
    congr 1
    push_cast
    ring
  have hcE : conj (exp ((K.σ.θ₁ : ℂ) * I)) = exp (-((K.σ.θ₁ : ℂ) * I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, conj_ofReal, conj_I]
  rw [hω, hw', map_mul, hcE, hcu]
  linear_combination (exp (-((K.σ.θ₁ : ℂ) * I)) * u) * hE

end Regular

section Final

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3)
  (hχ : d.orbChi < 0) (D : (C.closedHypShape hc h3 hχ).FoldData)

set_option hygiene false in
local notation "𝒦" => hypDatum C hc h3 hχ D

theorem foldRel_TT {x x' : ModelCoordinates} (hT : hb x ∈ (𝒦).σ.triangle)
    (h0' : hb x ≠ 0) (h1 : hb x ≠ (𝒦).σ.vertexOne) (h2 : hb x ≠ (𝒦).σ.vertexTwo)
    (hT' : hb x' ∈ (𝒦).σ.triangle) (h0'' : hb x' ≠ 0)
    (h1' : hb x' ≠ (𝒦).σ.vertexOne) (h2' : hb x' ≠ (𝒦).σ.vertexTwo)
    (h : hypMap C hc h3 (𝒦) x = hypMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x' := by
  obtain ⟨hF, hx⟩ := hypMap_of_triangle C hc h3 hχ D hT h0' h1 h2
  obtain ⟨hF', -⟩ := hypMap_of_triangle C hc h3 hχ D hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftP_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  exact foldRel_of_liftP_eq C hc h3 _ hx hT h0' hT' h0'' hL

theorem foldRel_CC {x x' : ModelCoordinates} (hT : conj (hb x) ∈ (𝒦).σ.triangle)
    (h0' : conj (hb x) ≠ 0) (h1 : conj (hb x) ≠ (𝒦).σ.vertexOne)
    (h2 : conj (hb x) ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (hb x') ∈ (𝒦).σ.triangle) (h0'' : conj (hb x') ≠ 0)
    (h1' : conj (hb x') ≠ (𝒦).σ.vertexOne) (h2' : conj (hb x') ≠ (𝒦).σ.vertexTwo)
    (h : hypMap C hc h3 (𝒦) x = hypMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x' := by
  obtain ⟨hF, hx⟩ := hypMap_of_conjTriangle C hc h3 hχ D hT h0' h1 h2
  obtain ⟨hF', -⟩ := hypMap_of_conjTriangle C hc h3 hχ D hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftM_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  exact foldRel_of_liftM_eq C hc h3 _ hx hT h0' hT' h0'' hL

theorem foldRel_TC {x x' : ModelCoordinates} (hT : hb x ∈ (𝒦).σ.triangle)
    (h0' : hb x ≠ 0) (h1 : hb x ≠ (𝒦).σ.vertexOne) (h2 : hb x ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (hb x') ∈ (𝒦).σ.triangle) (h0'' : conj (hb x') ≠ 0)
    (h1' : conj (hb x') ≠ (𝒦).σ.vertexOne) (h2' : conj (hb x') ≠ (𝒦).σ.vertexTwo)
    (h : hypMap C hc h3 (𝒦) x = hypMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x' := by
  have hk := kap_pos (𝒦).D (𝒦).hσ
  have hρ := rhoZero_pos (σ := (𝒦).σ)
  obtain ⟨hF, hx⟩ := hypMap_of_triangle C hc h3 hχ D hT h0' h1 h2
  obtain ⟨hF', hx'⟩ := hypMap_of_conjTriangle C hc h3 hχ D hT' h0'' h1' h2'
  have h₀ := h
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  set z := hb x with hz
  set w := conj (hb x') with hw
  have hf : (𝒦).D.f z = conj ((𝒦).D.f w) := by
    have := congrArg Prod.fst hL
    rw [liftM_fst] at this
    exact this
  have a1 := ((𝒦).D.bijOn_f.mapsTo ⟨hT, h0'⟩).2
  have a2 := ((𝒦).D.bijOn_f.mapsTo ⟨hT', h0''⟩).2
  have him : ((𝒦).D.f z).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have himw : ((𝒦).D.f w).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have hzw : z = w := (𝒦).D.eq_of_f_eq ⟨hT, h0'⟩ ⟨hT', h0''⟩
    (hf.trans (Complex.conj_eq_iff_im.mpr himw))
  have hx'z : conj (hb x') = z := hzw.symm
  have hwall : ∃ i, (𝒦).σ.wallSide i z = 0 := by
    have hnot : ¬ ∀ i, 0 < (𝒦).σ.wallSide i z := fun hi =>
      ((𝒦).D.im_f_pos hT.1 hi).ne' him
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, le_antisymm hi (hT.2 i)⟩
  have finish : ∀ x₁ : ModelCoordinates,
      FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x₁ →
      conj (hb x₁) = z →
      FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x' := by
    intro x₁ hr hp
    refine hr.trans (foldRel_CC C hc h3 hχ D (hp ▸ hT) (hp ▸ h0') (hp ▸ h1) (hp ▸ h2) hT' h0''
      h1' h2' ?_)
    rw [hr.map_eq]
    exact h₀
  obtain ⟨i, hwi⟩ := hwall
  fin_cases i
  · change (𝒦).σ.wallSide 0 z = 0 at hwi
    have hcz : conj z = z := Complex.conj_eq_iff_im.mpr hwi
    have hpx' : hb x' = z := by
      have := congrArg conj hx'z
      rwa [Complex.conj_conj, hcz] at this
    have hV : hb x' ∈ (𝒦).D.V 0 := by
      rw [hpx']; exact (𝒦).D.foldWall_diff_subset_V 0 ⟨⟨hT, hwi⟩, h0'⟩
    have hre : ((𝒦).D.f (hb x')).re < -(3 / 2) := by
      rw [hpx']; exact ((𝒦).D.re_f_wallZero ⟨hT, hwi⟩ h0' h2).2
    rw [(𝒦).liftM_eq_liftP hV hre] at hL
    exact foldRel_of_liftP_eq C hc h3 _ hx hT h0' (hpx' ▸ hT) (hpx' ▸ h0') hL
  · change (𝒦).σ.wallSide 1 z = 0 at hwi
    have hr1 : (𝒦).σ.refl 1 z = z :=
      HypFold.refl_eq_self (𝒦).hσ 1 (HypFold.norm_lt_one_of_mem (𝒦).hσ hT) hwi
    have hS3 : conj (hb ((𝒦).screwThree x)) = z := by
      rw [HypDatum.conj_hb_screwThree, ← hz, hr1]
    have hcov := mem_cover_of_wallOne (𝒦).hσ (D := (𝒦).D) hT hwi h0'
    simp only [mem_union] at hcov
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm.2 1).ne'
      · have := hm.2.1; rw [hwi] at this; linarith
      · exact finish _ (foldRel_screwThree_patchOne C hc h3 hχ D hm) hS3
      · have := hm.2.2.1; rw [hwi] at this; linarith
    · exact finish _ (foldRel_screwThree_discOne C hc h3 _ hd) hS3
    · have := wallSide_one_of_mem_discTwo (𝒦).hσ hd; rw [hwi] at this; linarith
    · exact finish _ (foldRel_screwThree C hc h3 _ hd) hS3
  · change (𝒦).σ.wallSide 2 z = 0 at hwi
    have hr2 : (𝒦).σ.refl 2 z = z :=
      HypFold.refl_eq_self (𝒦).hσ 2 (HypFold.norm_lt_one_of_mem (𝒦).hσ hT) hwi
    have hS2 : conj (hb ((𝒦).screwTwo.symm x)) = z := by
      rw [HypDatum.hb_screwTwo_symm, Complex.conj_conj, ← hz, hr2]
    have hcov := mem_cover_of_wallTwo (𝒦).hσ (D := (𝒦).D) hT hwi h0'
    simp only [mem_union] at hcov
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm.2 2).ne'
      · have := hm.2.2.1; rw [hwi] at this; linarith
      · have := hm.2.2.1; rw [hwi] at this; linarith
      · exact finish _ (foldRel_screwTwoInv_patchTwo C hc h3 hχ D hm) hS2
    · have hd1 := (𝒦).screwOne_mem_discOne hd
      refine finish _ ((foldRel_screwOne C hc h3 _ hd).trans
        (foldRel_screwThree_discOne C hc h3 _ hd1)) ?_
      rw [HypDatum.conj_hb_screwThree, hb_screwOne_of_wallTwo (𝒦) hwi, ← hz,
        HypFold.refl_refl (𝒦).hσ 1 (HypFold.norm_lt_one_of_mem (𝒦).hσ hT)]
    · have hd2 : hb ((𝒦).screwTwo.symm x) ∈ discTwo (𝒦).D := by
        rw [HypDatum.hb_screwTwo_symm, ← hz, hr2]; exact conj_mem_discTwo (𝒦).hσ hd
      have hr := foldRel_screwTwo C hc h3 _ hd2
      rw [Diffeomorph.apply_symm_apply] at hr
      exact finish _ hr.symm hS2
    · have := wallSide_two_of_mem_discThree (𝒦).hσ hd; rw [hwi] at this; linarith

theorem hypMap_regular {x : ModelCoordinates}
    (hx : (hb x ∈ (𝒦).σ.triangle ∧ hb x ≠ 0 ∧ hb x ≠ (𝒦).σ.vertexOne ∧
      hb x ≠ (𝒦).σ.vertexTwo) ∨
      (conj (hb x) ∈ (𝒦).σ.triangle ∧ conj (hb x) ≠ 0 ∧
        conj (hb x) ≠ (𝒦).σ.vertexOne ∧ conj (hb x) ≠ (𝒦).σ.vertexTwo)) :
    ∃ Y ∈ closedDomain, hypMap C hc h3 (𝒦) x = C.closedChart hc h3 Y := by
  rcases hx with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩
  · exact ⟨_, liftP_mem_closedDomain_of_T _ a b c e,
      (hypMap_of_triangle C hc h3 hχ D a b c e).1⟩
  · exact ⟨_, liftM_mem_closedDomain_of_T _ a b c e,
      (hypMap_of_conjTriangle C hc h3 hχ D a b c e).1⟩

theorem foldRel_of_reduced {x x' : ModelCoordinates} (hx : x ∈ reducedSet (𝒦))
    (hx' : x' ∈ reducedSet (𝒦)) (h : hypMap C hc h3 (𝒦) x = hypMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) x x' := by
  have hcore : ∀ {y : ModelCoordinates}, y ∈ reducedSet (𝒦) →
      (hb y = (𝒦).σ.vertexOne ∨ hb y = (𝒦).σ.vertexTwo ∨ hb y = 0) ∨
      ((hb y ∈ (𝒦).σ.triangle ∧ hb y ≠ 0 ∧ hb y ≠ (𝒦).σ.vertexOne ∧
        hb y ≠ (𝒦).σ.vertexTwo) ∨
      (conj (hb y) ∈ (𝒦).σ.triangle ∧ conj (hb y) ≠ 0 ∧
        conj (hb y) ≠ (𝒦).σ.vertexOne ∧ conj (hb y) ≠ (𝒦).σ.vertexTwo)) := by
    intro y hy
    rcases hy with hy | hy | hy | hy | hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr (Or.inl hy))
    · exact Or.inl (Or.inr (Or.inr hy))
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  rcases hcore hx with hv | hr <;> rcases hcore hx' with hv' | hr'
  · obtain ⟨j, w, hF, hp⟩ := hypMap_vertex_core C hc h3 _ hv
    obtain ⟨j', w', hF', hp'⟩ := hypMap_vertex_core C hc h3 _ hv'
    have h₁ := h
    rw [hF, hF'] at h₁
    have h00 : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have h00' : ‖((0 : ℂ), w').1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have hjj := (C.closedHoleEquiv hc h3).injective ((C.tubeMap_eq_iff_of_core h00 h00').1 h₁).1
    subst hjj
    have hpp : hb x = hb x' := hp.trans hp'.symm
    rcases hv with hv | hv | hv
    · exact foldRel_vertexOne C hc h3 _ hv (hpp ▸ hv) h
    · exact foldRel_vertexTwo C hc h3 _ hv (hpp ▸ hv) h
    · exact foldRel_vertexThree C hc h3 _ hv (hpp ▸ hv) h
  · obtain ⟨j, w, hF, -⟩ := hypMap_vertex_core C hc h3 _ hv
    obtain ⟨Y, hY, hF'⟩ := hypMap_regular C hc h3 hχ D hr'
    rw [hF, hF'] at h
    exact absurd h.symm (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · obtain ⟨j, w, hF', -⟩ := hypMap_vertex_core C hc h3 _ hv'
    obtain ⟨Y, hY, hF⟩ := hypMap_regular C hc h3 hχ D hr
    rw [hF, hF'] at h
    exact absurd h (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · rcases hr with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩ <;>
      rcases hr' with ⟨a', b', c', e'⟩ | ⟨a', b', c', e'⟩
    · exact foldRel_TT C hc h3 hχ D a b c e a' b' c' e' h
    · exact foldRel_TC C hc h3 hχ D a b c e a' b' c' e' h
    · exact (foldRel_TC C hc h3 hχ D a' b' c' e' a b c e h.symm).symm
    · exact foldRel_CC C hc h3 hχ D a b c e a' b' c' e' h

theorem foldRel_of_hypMap_eq {y y' : ModelCoordinates} (hy : y ∈ hypDomain (𝒦))
    (hy' : y' ∈ hypDomain (𝒦)) (h : hypMap C hc h3 (𝒦) y = hypMap C hc h3 (𝒦) y') :
    FoldRel (𝒦).m.coneProfile.metric (hypDomain (𝒦)) (hypMap C hc h3 (𝒦)) y y' := by
  obtain ⟨y₀, r, hy₀⟩ := exists_foldRel_reduced C hc h3 hχ D hy
  obtain ⟨y₀', r', hy₀'⟩ := exists_foldRel_reduced C hc h3 hχ D hy'
  have h₀ : hypMap C hc h3 (𝒦) y₀ = hypMap C hc h3 (𝒦) y₀' := by
    rw [r.map_eq, r'.map_eq, h]
  exact r.trans ((foldRel_of_reduced C hc h3 hχ D hy₀ hy₀' h₀).trans r'.symm)

end Final

end Hyp

end ClosedTriangle

end GC.Seifert
