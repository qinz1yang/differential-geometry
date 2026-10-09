import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatReduce

/-!
# Same-image pairs of a flat closed triangle fold

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§3 steps 1, 3, 4, with review 27). Two points of the fold domain with the same image are related by
the local composite relation (`foldRel_of_flatMap_eq`). By the reduction both are related to
reduced points (over a vertex, over the triangle minus its vertices, or over its mirror), and two
reduced points with the same image are related:
* over a vertex: the image is a core circle, the tube coordinates agree, and with the Bézout
  column a power of the screw of the vertex followed by a deck translation moves one to the other
  (`foldRel_vertex_fibre`);
* over the triangle or its mirror: `P` is injective, so the base lifts agree; `f` is injective on
  the triangle and real exactly on the walls, so the base points agree, or they are a wall-1 pair
  (`S₃`), a wall-2 pair (`S₂⁻¹`, or `S₃ S₁` near `v₁`), or the same point of wall 0; then the fibre
  coordinates differ by a deck translation.
-/

set_option autoImplicit false

noncomputable section
open Set Complex
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

theorem exists_int_of_eC_eq {a b : ℝ} (h : eC a = eC b) : ∃ n : ℤ, b = a + n := by
  rw [eC, eC, Circle.exp_eq_exp] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨-m, ?_⟩
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  have : 2 * Real.pi * (a - b - m) = 0 := by linear_combination hm
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h hπ
  · linear_combination -h

namespace FlatDatum

variable (K : FlatDatum)

theorem eq_deck_of {y y' : ModelCoordinates} (hp : planeOf y' = planeOf y) {n : ℤ}
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n) : y' = K.deck n y := by
  apply modelCoordinates_ext
  · rw [K.planeOf_deck, hp]
  · rw [K.two_deck]
    have hℓ := K.ℓ_ne
    field_simp at h2
    linarith

theorem screwOne_vertex {y : ModelCoordinates} (hy : planeOf y = K.σ.vertexOne) :
    planeOf (K.screwOne y) = K.σ.vertexOne ∧ K.screwOne y 2 = y 2 - K.ℓ * K.q₁ / K.σ.p₁ := by
  constructor
  · rw [K.planeOf_screwOne, hy, sub_self, mul_zero, add_zero]
  · have h2 := K.two_screw K.σ.vertexOne K.pOne K.q₁ y
    rw [K.coe_pOne] at h2
    change K.screwOne y 2 = _ at h2
    rw [h2, hy, sub_self, mul_zero, sub_zero]
    simp [planeCrossC]

theorem screwTwo_vertex {y : ModelCoordinates} (hy : planeOf y = K.σ.vertexTwo) :
    planeOf (K.screwTwo y) = K.σ.vertexTwo ∧ K.screwTwo y 2 = y 2 - K.ℓ * K.q₂ / K.σ.p₂ := by
  constructor
  · rw [K.planeOf_screwTwo, hy, sub_self, mul_zero, add_zero]
  · have h2 := K.two_screw K.σ.vertexTwo K.pTwo K.q₂ y
    rw [K.coe_pTwo] at h2
    change K.screwTwo y 2 = _ at h2
    rw [h2, hy, sub_self, mul_zero, sub_zero]
    simp [planeCrossC]

theorem screwThree_vertex {y : ModelCoordinates} (hy : planeOf y = 0) :
    planeOf (K.screwThree y) = 0 ∧ K.screwThree y 2 = y 2 - K.ℓ * K.q₃ / K.σ.p₃ :=
  ⟨by rw [K.planeOf_screwThree, hy, mul_zero], K.two_screwThree y⟩

end FlatDatum

section VertexFibre

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : FlatDatum)

theorem foldRel_vertex_fibre (S : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates) (v : ℂ)
    {p : ℕ} (hp : 0 < p) {q a b : ℤ} (hb : (p : ℤ) * b - a * q = 1)
    (hS : ∀ y : ModelCoordinates, planeOf y = v →
      FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) y (S y) ∧
        planeOf (S y) = v ∧ S y 2 = y 2 - K.ℓ * q / p)
    {y y' : ModelCoordinates} (hy : planeOf y = v) (hy' : planeOf y' = v) (n : ℤ)
    (h2 : y' 2 / K.ℓ = y 2 / K.ℓ + n / p) :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) y y' := by
  have hit : ∀ k : ℕ, FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) y
      (S^[k] y) ∧ planeOf (S^[k] y) = v ∧ (S^[k] y) 2 = y 2 - k * (K.ℓ * q / p) := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, hy, by simp⟩
      obtain ⟨hr, -, -⟩ := hS y hy
      exact FoldRel.refl (flatDomain K).isOpen hr.mem_left
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
    have hb' : (p : ℝ) * b - a * q = 1 := by exact_mod_cast hb
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

theorem tubeOne_snd_eq {x x' : ModelCoordinates} (K : FlatDatum)
    (hx : planeOf x = K.σ.vertexOne) (hx' : planeOf x' = K.σ.vertexOne)
    (h : K.tubeOne x = K.tubeOne x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₁ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₁ : ℝ) ≠ 0 := by exact_mod_cast K.p₁_pos.ne'
  simp only [FlatDatum.sOne, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeTwo_snd_eq {x x' : ModelCoordinates} (K : FlatDatum)
    (hx : planeOf x = K.σ.vertexTwo) (hx' : planeOf x' = K.σ.vertexTwo)
    (h : K.tubeTwo x = K.tubeTwo x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₂ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₂ : ℝ) ≠ 0 := by exact_mod_cast K.p₂_pos.ne'
  simp only [FlatDatum.sTwo, hx, hx'] at hn
  field_simp
  linear_combination hn

theorem tubeThree_snd_eq {x x' : ModelCoordinates} (K : FlatDatum)
    (h : K.tubeThree x = K.tubeThree x') : ∃ n : ℤ, x' 2 / K.ℓ = x 2 / K.ℓ + n / K.σ.p₃ := by
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (congrArg Prod.snd h)
  refine ⟨n, ?_⟩
  have hp0 : (K.σ.p₃ : ℝ) ≠ 0 := by exact_mod_cast K.p₃_pos.ne'
  simp only [FlatDatum.sThree] at hn
  field_simp
  linear_combination hn

theorem vertexOne_mem_discOne (K : FlatDatum) : K.σ.vertexOne ∈ discOne K.D := by
  change ‖K.σ.vertexOne - K.σ.vertexOne‖ < _
  rw [sub_self, norm_zero]; exact radOne_pos K.D

theorem vertexTwo_mem_discTwo (K : FlatDatum) : K.σ.vertexTwo ∈ discTwo K.D := by
  change ‖K.σ.vertexTwo - K.σ.vertexTwo‖ < _
  rw [sub_self, norm_zero]; exact radTwo_pos K.D

theorem zero_mem_discThree (K : FlatDatum) : (0 : ℂ) ∈ discThree K.D := by
  change ‖(0 : ℂ)‖ < _
  rw [norm_zero]; exact radThree_pos K.D

theorem foldRel_vertexOne {x x' : ModelCoordinates} (hx : planeOf x = K.σ.vertexOne)
    (hx' : planeOf x' = K.σ.vertexOne) (h : flatMap C hc h3 K x = flatMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x x' := by
  have hd := vertexOne_mem_discOne K
  rw [flatMap_of_discOne C hc h3 K (hx ▸ hd), flatMap_of_discOne C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeOne_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeOne_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeOne_snd_eq K hx hx' ht
  refine foldRel_vertex_fibre C hc h3 K K.screwOne K.σ.vertexOne K.p₁_pos K.bez₁ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwOne_vertex hy
  exact ⟨foldRel_screwOne C hc h3 K (hy ▸ hd), h1, h2⟩

theorem foldRel_vertexTwo {x x' : ModelCoordinates} (hx : planeOf x = K.σ.vertexTwo)
    (hx' : planeOf x' = K.σ.vertexTwo) (h : flatMap C hc h3 K x = flatMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x x' := by
  have hd := vertexTwo_mem_discTwo K
  rw [flatMap_of_discTwo C hc h3 K (hx ▸ hd), flatMap_of_discTwo C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeTwo_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeTwo_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeTwo_snd_eq K hx hx' ht
  refine foldRel_vertex_fibre C hc h3 K K.screwTwo K.σ.vertexTwo K.p₂_pos K.bez₂ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwTwo_vertex hy
  exact ⟨foldRel_screwTwo C hc h3 K (hy ▸ hd), h1, h2⟩

theorem foldRel_vertexThree {x x' : ModelCoordinates} (hx : planeOf x = 0)
    (hx' : planeOf x' = 0) (h : flatMap C hc h3 K x = flatMap C hc h3 K x') :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x x' := by
  have hd := zero_mem_discThree K
  rw [flatMap_of_discThree C hc h3 K (hx ▸ hd), flatMap_of_discThree C hc h3 K (hx' ▸ hd)] at h
  have ht := ((C.tubeMap_eq_iff_of_core (by linarith [C.ε_pos, norm_tubeThree_fst K (hx ▸ hd)])
    (by linarith [C.ε_pos, norm_tubeThree_fst K (hx' ▸ hd)])).1 h).2
  obtain ⟨n, hn⟩ := tubeThree_snd_eq K ht
  refine foldRel_vertex_fibre C hc h3 K K.screwThree 0 K.p₃_pos K.bez₃ ?_ hx hx' n hn
  intro y hy
  obtain ⟨h1, h2⟩ := K.screwThree_vertex hy
  exact ⟨foldRel_screwThree C hc h3 K (hy ▸ hd), h1, h2⟩

theorem flatMap_vertex_core {x : ModelCoordinates}
    (hx : planeOf x = K.σ.vertexOne ∨ planeOf x = K.σ.vertexTwo ∨ planeOf x = 0) :
    ∃ j : Fin 3, ∃ w : Circle, flatMap C hc h3 K x = C.tubeMap (C.closedHoleEquiv hc h3 j) (0, w) ∧
      planeOf x = (if j = 1 then K.σ.vertexOne else if j = 2 then K.σ.vertexTwo else 0) := by
  rcases hx with hx | hx | hx
  · refine ⟨1, (K.tubeOne x).2, ?_, by simp [hx]⟩
    rw [flatMap_of_discOne C hc h3 K (hx ▸ vertexOne_mem_discOne K)]
    congr 1
    refine Prod.ext ?_ rfl
    change K.σ.rotOne (planeOf x) * _ = 0
    rw [hx, K.σ.rotOne_vertexOne, zero_mul]
  · refine ⟨2, (K.tubeTwo x).2, ?_, by simp [hx]⟩
    rw [flatMap_of_discTwo C hc h3 K (hx ▸ vertexTwo_mem_discTwo K)]
    congr 1
    refine Prod.ext ?_ rfl
    change K.σ.rotTwo (planeOf x) * _ = 0
    rw [hx, K.σ.rotTwo_vertexTwo, zero_mul]
  · refine ⟨0, (K.tubeThree x).2, ?_, by simp [hx]⟩
    rw [flatMap_of_discThree C hc h3 K (hx ▸ zero_mem_discThree K)]
    congr 1
    refine Prod.ext ?_ rfl
    change _ * planeOf x * _ = 0
    rw [hx, mul_zero, zero_mul]

end VertexFibre

section Regular

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (hc : d.ports = 0) (h3 : d.cones.length = 3) (K : FlatDatum)

theorem liftP_mem_closedDomain_of_T {x : ModelCoordinates} (hT : planeOf x ∈ K.σ.triangle)
    (h0 : planeOf x ≠ 0) (h1 : planeOf x ≠ K.σ.vertexOne) (h2 : planeOf x ≠ K.σ.vertexTwo) :
    K.liftP x ∈ closedDomain := by
  refine ⟨norm_f_lt K.D hT h0, fun h => h1 ?_, fun h => h2 ?_⟩
  · exact eq_of_f_eq K.D hT h0 K.σ.vertexOne_mem_triangle vertexOne_ne_zero
      (h.trans (f_vertexOne K.D).symm)
  · exact eq_of_f_eq K.D hT h0 K.σ.vertexTwo_mem_triangle vertexTwo_ne_zero
      (h.trans (f_vertexTwo K.D).symm)

theorem liftM_fst (x : ModelCoordinates) :
    (K.liftM x).1 = conj (K.D.f (conj (planeOf x))) := by
  change conj (K.D.f (planeOf (reflectMap K.c₀ x))) = _
  rw [planeOf_reflectMap]

theorem liftM_mem_closedDomain_of_T {x : ModelCoordinates}
    (hT : conj (planeOf x) ∈ K.σ.triangle) (h0 : conj (planeOf x) ≠ 0)
    (h1 : conj (planeOf x) ≠ K.σ.vertexOne) (h2 : conj (planeOf x) ≠ K.σ.vertexTwo) :
    K.liftM x ∈ closedDomain := by
  have hP := liftP_mem_closedDomain_of_T K (x := reflectMap K.c₀ x)
    (by rw [planeOf_reflectMap]; exact hT) (by rw [planeOf_reflectMap]; exact h0)
    (by rw [planeOf_reflectMap]; exact h1) (by rw [planeOf_reflectMap]; exact h2)
  obtain ⟨a, b, c⟩ := hP
  change ‖conj (K.liftP (reflectMap K.c₀ x)).1‖ < 7 / 2 ∧
    conj (K.liftP (reflectMap K.c₀ x)).1 ≠ 3 / 2 ∧ conj (K.liftP (reflectMap K.c₀ x)).1 ≠ -(3 / 2)
  rw [Complex.norm_conj]
  refine ⟨a, fun h => b ?_, fun h => c ?_⟩
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_div₀, map_ofNat, map_ofNat] at this
  · have := congrArg conj h
    rwa [Complex.conj_conj, map_neg, map_div₀, map_ofNat, map_ofNat] at this

theorem foldRel_of_liftP_eq {x x' : ModelCoordinates} (hx : x ∈ flatDomain K)
    (hT : planeOf x ∈ K.σ.triangle) (h0 : planeOf x ≠ 0)
    (hT' : planeOf x' ∈ K.σ.triangle) (h0' : planeOf x' ≠ 0) (h : K.liftP x = K.liftP x') :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x x' := by
  have hz : planeOf x' = planeOf x :=
    (eq_of_f_eq K.D hT h0 hT' h0' (congrArg Prod.fst h)).symm
  have h2 := congrArg Prod.snd h
  change eC (x 2 / K.ℓ) * K.psiC (planeOf x) = eC (x' 2 / K.ℓ) * K.psiC (planeOf x') at h2
  rw [hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [K.eq_deck_of hz hn]
  exact foldRel_deck C hc h3 K n hx

theorem foldRel_of_liftM_eq {x x' : ModelCoordinates} (hx : x ∈ flatDomain K)
    (hT : conj (planeOf x) ∈ K.σ.triangle) (h0 : conj (planeOf x) ≠ 0)
    (hT' : conj (planeOf x') ∈ K.σ.triangle) (h0' : conj (planeOf x') ≠ 0)
    (h : K.liftM x = K.liftM x') :
    FoldRel K.m.coneProfile.metric (flatDomain K) (flatMap C hc h3 K) x x' := by
  have h' : K.liftP (reflectMap K.c₀ x) = K.liftP (reflectMap K.c₀ x') := by
    have := congrArg conjPair h
    simpa only [FlatDatum.liftM, conjPair_conjPair] using this
  have hz : conj (planeOf x') = conj (planeOf x) := by
    have := (eq_of_f_eq K.D hT h0 hT' h0' (by
      have := congrArg Prod.fst h'
      simpa only [FlatDatum.liftP, planeOf_reflectMap] using this)).symm
    exact this
  have hz' : planeOf x' = planeOf x := by simpa using congrArg conj hz
  have h2 := congrArg Prod.snd h'
  change eC (reflectMap K.c₀ x 2 / K.ℓ) * K.psiC (planeOf (reflectMap K.c₀ x)) =
    eC (reflectMap K.c₀ x' 2 / K.ℓ) * K.psiC (planeOf (reflectMap K.c₀ x')) at h2
  rw [planeOf_reflectMap, planeOf_reflectMap, hz] at h2
  obtain ⟨n, hn⟩ := exists_int_of_eC_eq (mul_right_cancel h2)
  rw [reflectMap_two, reflectMap_two] at hn
  have hn' : x' 2 / K.ℓ = x 2 / K.ℓ + ((-n : ℤ) : ℝ) := by
    have hℓ := K.ℓ_ne
    push_cast
    field_simp at hn ⊢
    linarith
  rw [K.eq_deck_of hz' hn']
  exact foldRel_deck C hc h3 K _ hx

theorem rotOne_injective (σ : EuclidShape) : Function.Injective σ.rotOne := by
  intro a b h
  unfold EuclidShape.rotOne at h
  have hne := Complex.exp_ne_zero (-((σ.θ₃ : ℂ) * I))
  have : exp (-((σ.θ₃ : ℂ) * I)) * (a - b) = 0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hne)

theorem planeOf_screwOne_of_wallTwo {x : ModelCoordinates}
    (hw : K.σ.wallSide 2 (planeOf x) = 0) :
    planeOf (K.screwOne x) = K.σ.refl 1 (planeOf x) := by
  apply rotOne_injective K.σ
  rw [K.rotOne_screwOne, K.σ.rotOne_refl_one]
  set w := K.σ.rotOne (planeOf x)
  set u := exp (-((K.σ.θ₁ : ℂ) * I)) * w with hu
  have hui : u.im = 0 := by
    rw [K.σ.wallSide_two_eq_rotOne] at hw
    linarith
  have hcu : conj u = u := Complex.conj_eq_iff_im.mpr hui
  have hE : exp ((K.σ.θ₁ : ℂ) * I) * exp (-((K.σ.θ₁ : ℂ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hw' : w = exp ((K.σ.θ₁ : ℂ) * I) * u := by
    rw [hu, ← mul_assoc, hE, one_mul]
  have hω : (Circle.exp (-2 * Real.pi / K.σ.p₁) : ℂ) =
      exp (-((K.σ.θ₁ : ℂ) * I)) * exp (-((K.σ.θ₁ : ℂ) * I)) := by
    rw [Circle.coe_exp, ← Complex.exp_add, FlatDatum.p_inv_eq K.p₁_pos K.σ.θ₁_mul]
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
  (h0 : d.orbChi = 0) (D : (C.closedEuclidShape hc h3 h0).toCompactShape.FoldData)

set_option hygiene false in
local notation "𝒦" => flatDatum C hc h3 h0 D

theorem foldRel_TT {x x' : ModelCoordinates} (hT : planeOf x ∈ (𝒦).σ.triangle)
    (h0' : planeOf x ≠ 0) (h1 : planeOf x ≠ (𝒦).σ.vertexOne) (h2 : planeOf x ≠ (𝒦).σ.vertexTwo)
    (hT' : planeOf x' ∈ (𝒦).σ.triangle) (h0'' : planeOf x' ≠ 0)
    (h1' : planeOf x' ≠ (𝒦).σ.vertexOne) (h2' : planeOf x' ≠ (𝒦).σ.vertexTwo)
    (h : flatMap C hc h3 (𝒦) x = flatMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x' := by
  obtain ⟨hF, hx⟩ := flatMap_of_triangle C hc h3 h0 D hT h0' h1 h2
  obtain ⟨hF', -⟩ := flatMap_of_triangle C hc h3 h0 D hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftP_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  exact foldRel_of_liftP_eq C hc h3 _ hx hT h0' hT' h0'' hL

theorem foldRel_CC {x x' : ModelCoordinates} (hT : conj (planeOf x) ∈ (𝒦).σ.triangle)
    (h0' : conj (planeOf x) ≠ 0) (h1 : conj (planeOf x) ≠ (𝒦).σ.vertexOne)
    (h2 : conj (planeOf x) ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (planeOf x') ∈ (𝒦).σ.triangle) (h0'' : conj (planeOf x') ≠ 0)
    (h1' : conj (planeOf x') ≠ (𝒦).σ.vertexOne) (h2' : conj (planeOf x') ≠ (𝒦).σ.vertexTwo)
    (h : flatMap C hc h3 (𝒦) x = flatMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x' := by
  obtain ⟨hF, hx⟩ := flatMap_of_conjTriangle C hc h3 h0 D hT h0' h1 h2
  obtain ⟨hF', -⟩ := flatMap_of_conjTriangle C hc h3 h0 D hT' h0'' h1' h2'
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftM_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  exact foldRel_of_liftM_eq C hc h3 _ hx hT h0' hT' h0'' hL

theorem foldRel_TC {x x' : ModelCoordinates} (hT : planeOf x ∈ (𝒦).σ.triangle)
    (h0' : planeOf x ≠ 0) (h1 : planeOf x ≠ (𝒦).σ.vertexOne) (h2 : planeOf x ≠ (𝒦).σ.vertexTwo)
    (hT' : conj (planeOf x') ∈ (𝒦).σ.triangle) (h0'' : conj (planeOf x') ≠ 0)
    (h1' : conj (planeOf x') ≠ (𝒦).σ.vertexOne) (h2' : conj (planeOf x') ≠ (𝒦).σ.vertexTwo)
    (h : flatMap C hc h3 (𝒦) x = flatMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x' := by
  have hk := kap_pos (𝒦).D
  have hρ := rhoZero_pos (σ := (𝒦).σ)
  obtain ⟨hF, hx⟩ := flatMap_of_triangle C hc h3 h0 D hT h0' h1 h2
  obtain ⟨hF', hx'⟩ := flatMap_of_conjTriangle C hc h3 h0 D hT' h0'' h1' h2'
  have h₀ := h
  rw [hF, hF'] at h
  have hL := C.closedChart_injOn hc h3 (liftP_mem_closedDomain_of_T _ hT h0' h1 h2)
    (liftM_mem_closedDomain_of_T _ hT' h0'' h1' h2') h
  set z := planeOf x with hz
  set w := conj (planeOf x') with hw
  have hf : (𝒦).D.f z = conj ((𝒦).D.f w) := by
    have := congrArg Prod.fst hL
    rw [liftM_fst] at this
    exact this
  have a1 := im_f_nonneg (𝒦).D hT h0'
  have a2 := im_f_nonneg (𝒦).D hT' h0''
  have him : ((𝒦).D.f z).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have himw : ((𝒦).D.f w).im = 0 := by
    have := congrArg Complex.im hf
    rw [conj_im] at this
    linarith
  have hzw : z = w := eq_of_f_eq (𝒦).D hT h0' hT' h0''
    (hf.trans (Complex.conj_eq_iff_im.mpr himw))
  have hx'z : conj (planeOf x') = z := hzw.symm
  have hwall : ∃ i, (𝒦).σ.wallSide i z = 0 := by
    have hnot : ¬ ∀ i, 0 < (𝒦).σ.wallSide i z := fun hi =>
      (im_f_pos_of_intT (𝒦).D hi).ne' him
    push Not at hnot
    obtain ⟨i, hi⟩ := hnot
    exact ⟨i, le_antisymm hi (hT i)⟩
  have finish : ∀ x₁ : ModelCoordinates,
      FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x₁ →
      conj (planeOf x₁) = z →
      FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x' := by
    intro x₁ hr hp
    refine hr.trans (foldRel_CC C hc h3 h0 D (hp ▸ hT) (hp ▸ h0') (hp ▸ h1) (hp ▸ h2) hT' h0''
      h1' h2' ?_)
    rw [hr.map_eq]
    exact h₀
  obtain ⟨i, hwi⟩ := hwall
  fin_cases i
  · change (𝒦).σ.wallSide 0 z = 0 at hwi
    have hcz : conj z = z := Complex.conj_eq_iff_im.mpr hwi
    have hpx' : planeOf x' = z := by
      have := congrArg conj hx'z
      rwa [Complex.conj_conj, hcz] at this
    have hV : planeOf x' ∈ (𝒦).D.V 0 := by
      rw [hpx']; exact foldWall_diff_subset_V' (𝒦).D 0 ⟨⟨hT, hwi⟩, h0'⟩
    have hre : ((𝒦).D.f (planeOf x')).re < -(3 / 2) := by
      rw [hpx']; exact (re_f_wallZero (𝒦).D hT hwi h0' h2).2
    rw [(𝒦).liftM_eq_liftP hV hre] at hL
    exact foldRel_of_liftP_eq C hc h3 _ hx hT h0' (hpx' ▸ hT) (hpx' ▸ h0') hL
  · change (𝒦).σ.wallSide 1 z = 0 at hwi
    have hr1 : (𝒦).σ.refl 1 z = z := (𝒦).σ.refl_of_wallSide_eq_zero hwi
    have hS3 : conj (planeOf ((𝒦).screwThree x)) = z := by
      rw [FlatDatum.conj_planeOf_screwThree, ← hz, hr1]
    have hcov := mem_cover_of_wallOne (𝒦).D hT hwi h0'
    simp only [mem_union] at hcov
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm 1).ne'
      · have := hm.2.1; rw [hwi] at this; linarith
      · exact finish _ (foldRel_screwThree_patchOne C hc h3 h0 D hm) hS3
      · have := hm.2.2.1; rw [hwi] at this; linarith
    · exact finish _ (foldRel_screwThree_discOne C hc h3 _ hd) hS3
    · have := wallSide_one_of_mem_discTwo (𝒦).D hd; rw [hwi] at this; linarith
    · exact finish _ (foldRel_screwThree C hc h3 _ hd) hS3
  · change (𝒦).σ.wallSide 2 z = 0 at hwi
    have hr2 : (𝒦).σ.refl 2 z = z := (𝒦).σ.refl_of_wallSide_eq_zero hwi
    have hS2 : conj (planeOf ((𝒦).screwTwo.symm x)) = z := by
      rw [planeOf_screwTwo_symm, Complex.conj_conj, ← hz, hr2]
    have hcov := mem_cover_of_wallTwo (𝒦).D hT hwi h0'
    simp only [mem_union] at hcov
    rcases hcov with ((hm | hd) | hd) | hd
    · rcases hm with ((hm | hm) | hm) | hm
      · exact absurd hwi (hm 2).ne'
      · have := hm.2.2.1; rw [hwi] at this; linarith
      · have := hm.2.2.1; rw [hwi] at this; linarith
      · exact finish _ (foldRel_screwTwoInv_patchTwo C hc h3 h0 D hm) hS2
    · have hd1 := (𝒦).screwOne_mem_discOne hd
      refine finish _ ((foldRel_screwOne C hc h3 _ hd).trans
        (foldRel_screwThree_discOne C hc h3 _ hd1)) ?_
      rw [FlatDatum.conj_planeOf_screwThree, planeOf_screwOne_of_wallTwo _ hwi, ← hz,
        (𝒦).σ.refl_refl]
    · have hd2 : planeOf ((𝒦).screwTwo.symm x) ∈ discTwo (𝒦).D := by
        rw [planeOf_screwTwo_symm, ← hz, hr2]; exact conj_mem_discTwo _ hd
      have hr := foldRel_screwTwo C hc h3 _ hd2
      rw [Diffeomorph.apply_symm_apply] at hr
      exact finish _ hr.symm hS2
    · have := wallSide_two_of_mem_discThree (𝒦).D hd; rw [hwi] at this; linarith

theorem flatMap_regular {x : ModelCoordinates}
    (hx : (planeOf x ∈ (𝒦).σ.triangle ∧ planeOf x ≠ 0 ∧ planeOf x ≠ (𝒦).σ.vertexOne ∧
      planeOf x ≠ (𝒦).σ.vertexTwo) ∨
      (conj (planeOf x) ∈ (𝒦).σ.triangle ∧ conj (planeOf x) ≠ 0 ∧
        conj (planeOf x) ≠ (𝒦).σ.vertexOne ∧ conj (planeOf x) ≠ (𝒦).σ.vertexTwo)) :
    ∃ Y ∈ closedDomain, flatMap C hc h3 (𝒦) x = C.closedChart hc h3 Y := by
  rcases hx with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩
  · exact ⟨_, liftP_mem_closedDomain_of_T _ a b c e,
      (flatMap_of_triangle C hc h3 h0 D a b c e).1⟩
  · exact ⟨_, liftM_mem_closedDomain_of_T _ a b c e,
      (flatMap_of_conjTriangle C hc h3 h0 D a b c e).1⟩

theorem foldRel_of_reduced {x x' : ModelCoordinates} (hx : x ∈ reducedSet (𝒦))
    (hx' : x' ∈ reducedSet (𝒦)) (h : flatMap C hc h3 (𝒦) x = flatMap C hc h3 (𝒦) x') :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) x x' := by
  have hcore : ∀ {y : ModelCoordinates}, y ∈ reducedSet (𝒦) →
      (planeOf y = (𝒦).σ.vertexOne ∨ planeOf y = (𝒦).σ.vertexTwo ∨ planeOf y = 0) ∨
      ((planeOf y ∈ (𝒦).σ.triangle ∧ planeOf y ≠ 0 ∧ planeOf y ≠ (𝒦).σ.vertexOne ∧
        planeOf y ≠ (𝒦).σ.vertexTwo) ∨
      (conj (planeOf y) ∈ (𝒦).σ.triangle ∧ conj (planeOf y) ≠ 0 ∧
        conj (planeOf y) ≠ (𝒦).σ.vertexOne ∧ conj (planeOf y) ≠ (𝒦).σ.vertexTwo)) := by
    intro y hy
    rcases hy with hy | hy | hy | hy | hy
    · exact Or.inl (Or.inl hy)
    · exact Or.inl (Or.inr (Or.inl hy))
    · exact Or.inl (Or.inr (Or.inr hy))
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  rcases hcore hx with hv | hr <;> rcases hcore hx' with hv' | hr'
  · obtain ⟨j, w, hF, hp⟩ := flatMap_vertex_core C hc h3 _ hv
    obtain ⟨j', w', hF', hp'⟩ := flatMap_vertex_core C hc h3 _ hv'
    have h₁ := h
    rw [hF, hF'] at h₁
    have h00 : ‖((0 : ℂ), w).1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have h00' : ‖((0 : ℂ), w').1‖ < 1 + C.ε := by
      change ‖(0 : ℂ)‖ < _; rw [norm_zero]; linarith [C.ε_pos]
    have hjj := (C.closedHoleEquiv hc h3).injective ((C.tubeMap_eq_iff_of_core h00 h00').1 h₁).1
    subst hjj
    have hpp : planeOf x = planeOf x' := hp.trans hp'.symm
    rcases hv with hv | hv | hv
    · exact foldRel_vertexOne C hc h3 _ hv (hpp ▸ hv) h
    · exact foldRel_vertexTwo C hc h3 _ hv (hpp ▸ hv) h
    · exact foldRel_vertexThree C hc h3 _ hv (hpp ▸ hv) h
  · obtain ⟨j, w, hF, -⟩ := flatMap_vertex_core C hc h3 _ hv
    obtain ⟨Y, hY, hF'⟩ := flatMap_regular C hc h3 h0 D hr'
    rw [hF, hF'] at h
    exact absurd h.symm (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · obtain ⟨j, w, hF', -⟩ := flatMap_vertex_core C hc h3 _ hv'
    obtain ⟨Y, hY, hF⟩ := flatMap_regular C hc h3 h0 D hr
    rw [hF, hF'] at h
    exact absurd h (C.closedChart_ne_tubeMap_zero hc h3 hY _ w)
  · rcases hr with ⟨a, b, c, e⟩ | ⟨a, b, c, e⟩ <;>
      rcases hr' with ⟨a', b', c', e'⟩ | ⟨a', b', c', e'⟩
    · exact foldRel_TT C hc h3 h0 D a b c e a' b' c' e' h
    · exact foldRel_TC C hc h3 h0 D a b c e a' b' c' e' h
    · exact (foldRel_TC C hc h3 h0 D a' b' c' e' a b c e h.symm).symm
    · exact foldRel_CC C hc h3 h0 D a b c e a' b' c' e' h

theorem foldRel_of_flatMap_eq {y y' : ModelCoordinates} (hy : y ∈ flatDomain (𝒦))
    (hy' : y' ∈ flatDomain (𝒦)) (h : flatMap C hc h3 (𝒦) y = flatMap C hc h3 (𝒦) y') :
    FoldRel (𝒦).m.coneProfile.metric (flatDomain (𝒦)) (flatMap C hc h3 (𝒦)) y y' := by
  obtain ⟨y₀, r, hy₀⟩ := exists_foldRel_reduced C hc h3 h0 D hy
  obtain ⟨y₀', r', hy₀'⟩ := exists_foldRel_reduced C hc h3 h0 D hy'
  have h₀ : flatMap C hc h3 (𝒦) y₀ = flatMap C hc h3 (𝒦) y₀' := by
    rw [r.map_eq, r'.map_eq, h]
  exact r.trans ((foldRel_of_reduced C hc h3 h0 D hy₀ hy₀' h₀).trans r'.symm)

end Final

end ClosedTriangle

end GC.Seifert
