import DifferentialGeometry.Geometry.Thurston.Models
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SeifertArithmetic

/-!
# Seifert data and the model tables

Chapter 6, S3 and the closed and open model tables. `SeifertData` is a product-fibred piece over
the planar surface `Pₖ`, `k ∈ {1, 2, 3}`: `ports` boundary circles stay free, the others are
filled by genuine cones `(p, q)`, `p ≥ 2`, `gcd (p, q) = 1`, or by normal fillings `(1, q)`,
recorded by `q`; a filling sends the meridian to `p • s + q • f` (the convention of `Slope.lean`).
`orbChi = 2 - ports - ∑ (1 - 1/pᵢ)` over the cones and `euler = -∑ qᵢ/pᵢ` over all fillings.
Changing the trivialization by `Pₖ → S¹` with boundary degrees `δᵢ`, `∑ δᵢ = 0`, sends `qᵢ` to
`qᵢ - pᵢ δᵢ` (`retwist`) and fixes both invariants (`orbChi_retwist`, `euler_retwist`).

The tables are typed by their domains: `closedTable` on `ClosedData` (`ports = 0`) reads the sign
of `orbChi` and whether `euler = 0` (Scott, Table 4.1); `openTable` on `OpenGoodData` (`ports > 0`,
not a solid torus, equivalently `orbChi ≤ 0`) gives `.euclidean` exactly for `T² × I` and
`D²(2, 2)`, else `.hyperbolicProduct` with `orbChi < 0`. Three genuine cones never give
`.sphericalProduct` (`modelOf_three_cones_ne_sphericalProduct`).
-/

set_option autoImplicit false

open GC.Geometry

namespace GC.Seifert

structure SeifertData where
  k : ℕ
  ports : ℕ
  cones : List (ℕ × ℤ)
  normals : List ℤ
  one_le_k : 1 ≤ k
  k_le_three : k ≤ 3
  two_le_of_mem_cones : ∀ c ∈ cones, 2 ≤ c.1
  gcd_eq_one_of_mem_cones : ∀ c ∈ cones, Int.gcd (c.1 : ℤ) c.2 = 1
  ports_add_length_add_length : ports + cones.length + normals.length = k

namespace SeifertData

def orbChi (d : SeifertData) : ℚ :=
  2 - d.ports - (d.cones.map fun c : ℕ × ℤ => 1 - 1 / (c.1 : ℚ)).sum

def euler (d : SeifertData) : ℚ :=
  -((d.cones.map fun c : ℕ × ℤ => (c.2 : ℚ) / c.1).sum +
    (d.normals.map fun q : ℤ => (q : ℚ)).sum)

def retwist (d : SeifertData) (δ : Fin (d.cones.length + d.normals.length) → ℤ) :
    SeifertData where
  k := d.k
  ports := d.ports
  cones := List.ofFn fun i : Fin d.cones.length =>
    (d.cones[i].1, d.cones[i].2 - d.cones[i].1 * δ (Fin.castAdd _ i))
  normals := List.ofFn fun j : Fin d.normals.length => d.normals[j] - δ (Fin.natAdd _ j)
  one_le_k := d.one_le_k
  k_le_three := d.k_le_three
  two_le_of_mem_cones c hc := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact d.two_le_of_mem_cones d.cones[i] (List.getElem_mem _)
  gcd_eq_one_of_mem_cones c hc := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    rw [Int.gcd_sub_mul_left_right]
    exact d.gcd_eq_one_of_mem_cones d.cones[i] (List.getElem_mem _)
  ports_add_length_add_length := by simpa using d.ports_add_length_add_length

private lemma sum_map_eq_sum_fin {α : Type*} (l : List α) (f : α → ℚ) :
    (l.map f).sum = ∑ i : Fin l.length, f l[i] := by
  rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
  rfl

theorem orbChi_retwist (d : SeifertData) (δ : Fin (d.cones.length + d.normals.length) → ℤ) :
    (d.retwist δ).orbChi = d.orbChi := by
  simp only [orbChi, retwist, List.map_ofFn, List.sum_ofFn, sum_map_eq_sum_fin d.cones]
  rfl

theorem euler_retwist (d : SeifertData) (δ : Fin (d.cones.length + d.normals.length) → ℤ)
    (hδ : ∑ i, δ i = 0) : (d.retwist δ).euler = d.euler := by
  have hδ' : ∑ i : Fin d.cones.length, (δ (Fin.castAdd _ i) : ℚ) +
      ∑ j : Fin d.normals.length, (δ (Fin.natAdd _ j) : ℚ) = 0 := by
    rw [← Fin.sum_univ_add (fun i => (δ i : ℚ))]
    exact_mod_cast hδ
  have hterm : ∀ i : Fin d.cones.length,
      (((d.cones[i].2 - d.cones[i].1 * δ (Fin.castAdd _ i) : ℤ) : ℚ) / (d.cones[i].1 : ℚ)) =
        (d.cones[i].2 : ℚ) / d.cones[i].1 - δ (Fin.castAdd _ i) := by
    intro i
    have h2 : 2 ≤ d.cones[i].1 := d.two_le_of_mem_cones _ (List.getElem_mem _)
    have hp : (d.cones[i].1 : ℚ) ≠ 0 := by exact_mod_cast (by omega : d.cones[i].1 ≠ 0)
    push_cast
    field_simp
  simp only [euler, retwist, List.map_ofFn, List.sum_ofFn, sum_map_eq_sum_fin d.cones,
    sum_map_eq_sum_fin d.normals, Function.comp_def]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp only [Int.cast_sub, Finset.sum_sub_distrib]
  linarith

def IsSolidTorus (d : SeifertData) : Prop := d.ports = 1 ∧ d.cones.length ≤ 1

end SeifertData

abbrev ClosedData : Type := {d : SeifertData // d.ports = 0}

abbrev OpenGoodData : Type := {d : SeifertData // 0 < d.ports ∧ ¬ d.IsSolidTorus}

def closedTable (d : ClosedData) : ThurstonModel :=
  if 0 < d.1.orbChi then (if d.1.euler = 0 then .sphericalProduct else .spherical)
  else if d.1.orbChi = 0 then (if d.1.euler = 0 then .euclidean else .nil)
  else if d.1.euler = 0 then .hyperbolicProduct else .universalSL2

def openTable (d : OpenGoodData) : ThurstonModel :=
  if d.1.orbChi = 0 then .euclidean else .hyperbolicProduct

namespace SeifertData

def modelOf (d : SeifertData) (hclosed : d.ports = 0) : ThurstonModel :=
  closedTable ⟨d, hclosed⟩

def openModelOf (d : SeifertData) (hopen : 0 < d.ports) (hgood : ¬ d.IsSolidTorus) :
    ThurstonModel :=
  openTable ⟨d, hopen, hgood⟩

theorem modelOf_retwist (d : SeifertData) (hclosed : d.ports = 0)
    (δ : Fin (d.cones.length + d.normals.length) → ℤ) (hδ : ∑ i, δ i = 0) :
    (d.retwist δ).modelOf hclosed = d.modelOf hclosed := by
  simp only [modelOf, closedTable, orbChi_retwist, euler_retwist d δ hδ]

theorem euler_ne_zero_of_three_cones (d : SeifertData) (hclosed : d.ports = 0)
    (hthree : d.cones.length = 3) (hχ : 0 < d.orbChi) : d.euler ≠ 0 := by
  have hc := d.ports_add_length_add_length
  have hk := d.k_le_three
  have hn : d.normals = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨a, b, c, hl⟩ := List.length_eq_three.1 hthree
  have hp : ∀ i, 2 ≤ (![a.1, b.1, c.1] : Fin 3 → ℕ) i := fun i => by
    fin_cases i <;> exact d.two_le_of_mem_cones _ (by simp [hl])
  have hcop : ∀ i, Int.gcd ((![a.1, b.1, c.1] : Fin 3 → ℕ) i : ℤ)
      ((![a.2, b.2, c.2] : Fin 3 → ℤ) i) = 1 := fun i => by
    fin_cases i <;> exact d.gcd_eq_one_of_mem_cones _ (by simp [hl])
  have hsum : (1 : ℚ) < ∑ i, (1 : ℚ) / ((![a.1, b.1, c.1] : Fin 3 → ℕ) i : ℚ) := by
    simp only [orbChi, hl, hclosed] at hχ
    simp only [Fin.sum_univ_three]
    norm_num at hχ ⊢
    linarith
  have h := sum_div_ne_zero_of_three_cones _ _ hp hcop hsum
  norm_num [Fin.sum_univ_three] at h
  norm_num [euler, hl, hn]
  contrapose! h
  linarith

theorem modelOf_eq_spherical_of_three_cones (d : SeifertData) (hclosed : d.ports = 0)
    (hthree : d.cones.length = 3) (hχ : 0 < d.orbChi) : d.modelOf hclosed = .spherical := by
  simp [modelOf, closedTable, hχ, d.euler_ne_zero_of_three_cones hclosed hthree hχ]

theorem modelOf_three_cones_ne_sphericalProduct (d : SeifertData) (hclosed : d.ports = 0)
    (hthree : d.cones.length = 3) : d.modelOf hclosed ≠ .sphericalProduct := by
  by_cases hχ : 0 < d.orbChi
  · simp [d.modelOf_eq_spherical_of_three_cones hclosed hthree hχ]
  · simp only [modelOf, closedTable, hχ, ite_false]
    split_ifs <;> decide

private lemma one_div_le_half {p : ℕ} (hp : 2 ≤ p) : (1 : ℚ) / p ≤ 1 / 2 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)

private lemma one_div_le_third {p : ℕ} (hp : 3 ≤ p) : (1 : ℚ) / p ≤ 1 / 3 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp)

private lemma open_cases (d : SeifertData) (hopen : 0 < d.ports) (hgood : ¬ d.IsSolidTorus) :
    (d.ports = 3 ∧ d.cones = []) ∨ (d.ports = 2 ∧ d.cones = []) ∨
      (d.ports = 2 ∧ ∃ a, d.cones = [a]) ∨ (d.ports = 1 ∧ ∃ a b, d.cones = [a, b]) := by
  have hc := d.ports_add_length_add_length
  have hk := d.k_le_three
  simp only [IsSolidTorus, not_and, not_le] at hgood
  rcases hcs : d.cones with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp only [hcs, List.length_nil, List.length_cons] at hc hgood
  · by_cases h3 : d.ports = 3
    · exact Or.inl ⟨h3, rfl⟩
    · exact Or.inr (Or.inl ⟨by omega, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, a, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, a, b, rfl⟩))
  · omega

theorem orbChi_nonpos_of_open (d : SeifertData) (hopen : 0 < d.ports)
    (hgood : ¬ d.IsSolidTorus) : d.orbChi ≤ 0 := by
  rcases open_cases d hopen hgood with ⟨hp, hl⟩ | ⟨hp, hl⟩ | ⟨hp, a, hl⟩ | ⟨hp, a, b, hl⟩ <;>
    simp only [orbChi, hp, hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
    push_cast
  · norm_num
  · norm_num
  · linarith [one_div_le_half (d.two_le_of_mem_cones a (by simp [hl]))]
  · linarith [one_div_le_half (d.two_le_of_mem_cones a (by simp [hl])),
      one_div_le_half (d.two_le_of_mem_cones b (by simp [hl]))]

theorem orbChi_eq_zero_iff_of_open (d : SeifertData) (hopen : 0 < d.ports)
    (hgood : ¬ d.IsSolidTorus) : d.orbChi = 0 ↔
      (d.ports = 2 ∧ d.cones = []) ∨ (d.ports = 1 ∧ d.cones.map Prod.fst = [2, 2]) := by
  rcases open_cases d hopen hgood with ⟨hp, hl⟩ | ⟨hp, hl⟩ | ⟨hp, a, hl⟩ | ⟨hp, a, b, hl⟩ <;>
    simp only [orbChi, hp, hl, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  · norm_num
  · norm_num
  · have ha := one_div_le_half (d.two_le_of_mem_cones a (by simp [hl]))
    refine ⟨fun h => ?_, fun h => ?_⟩
    · push_cast at h
      linarith
    · rcases h with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h (List.cons_ne_nil _ _)
      · omega
  · have ha := d.two_le_of_mem_cones a (by simp [hl])
    have hb := d.two_le_of_mem_cones b (by simp [hl])
    refine ⟨fun h => Or.inr ⟨trivial, ?_⟩, fun h => ?_⟩
    · push_cast at h
      have key : a.1 = 2 ∧ b.1 = 2 := by
        by_contra hne
        rcases (by omega : 3 ≤ a.1 ∨ 3 ≤ b.1) with h3 | h3
        · linarith [one_div_le_third h3, one_div_le_half hb]
        · linarith [one_div_le_third h3, one_div_le_half ha]
      rw [key.1, key.2]
    · rcases h with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · simp only [List.cons.injEq, and_true] at h
        rw [h.1, h.2]
        norm_num

theorem pos_orbChi_of_isSolidTorus (d : SeifertData) (h : d.IsSolidTorus) : 0 < d.orbChi := by
  obtain ⟨hp, hl⟩ := h
  rcases hcs : d.cones with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp [orbChi, hp, hcs]
  · have := d.two_le_of_mem_cones a (by simp [hcs])
    norm_num [orbChi, hp, hcs]
    omega
  · simp [hcs] at hl

theorem orbChi_nonpos_iff_of_open (d : SeifertData) (hopen : 0 < d.ports) :
    d.orbChi ≤ 0 ↔ ¬ d.IsSolidTorus :=
  ⟨fun h hs => (pos_orbChi_of_isSolidTorus d hs).not_ge h, orbChi_nonpos_of_open d hopen⟩

theorem openModelOf_eq_euclidean_iff (d : SeifertData) (hopen : 0 < d.ports)
    (hgood : ¬ d.IsSolidTorus) :
    d.openModelOf hopen hgood = .euclidean ↔
      (d.ports = 2 ∧ d.cones = []) ∨ (d.ports = 1 ∧ d.cones.map Prod.fst = [2, 2]) := by
  rw [← orbChi_eq_zero_iff_of_open d hopen hgood]
  simp only [openModelOf, openTable]
  split_ifs with h <;> simp [h]

theorem openModelOf_eq_hyperbolicProduct_iff (d : SeifertData) (hopen : 0 < d.ports)
    (hgood : ¬ d.IsSolidTorus) :
    d.openModelOf hopen hgood = .hyperbolicProduct ↔ d.orbChi < 0 := by
  have := orbChi_nonpos_of_open d hopen hgood
  simp only [openModelOf, openTable]
  split_ifs with h <;> simp [h, lt_iff_le_and_ne, this]

private def sphereProductExample : SeifertData :=
  ⟨3, 0, [(2, 1), (2, -1)], [0], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : sphereProductExample.orbChi = 1 ∧ sphereProductExample.euler = 0 ∧
    sphereProductExample.modelOf rfl = .sphericalProduct := by
  norm_num [sphereProductExample, orbChi, euler, modelOf, closedTable]

private def flatTriangleExample : SeifertData :=
  ⟨3, 0, [(3, 1), (3, 1), (3, -2)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : flatTriangleExample.orbChi = 0 ∧ flatTriangleExample.euler = 0 ∧
    flatTriangleExample.modelOf rfl = .euclidean := by
  norm_num [flatTriangleExample, orbChi, euler, modelOf, closedTable]

private def hyperbolicTriangleExample : SeifertData :=
  ⟨3, 0, [(5, 1), (5, 1), (5, -2)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : hyperbolicTriangleExample.orbChi = -2 / 5 ∧ hyperbolicTriangleExample.euler = 0 ∧
    hyperbolicTriangleExample.modelOf rfl = .hyperbolicProduct := by
  norm_num [hyperbolicTriangleExample, orbChi, euler, modelOf, closedTable]

private def platonicExample : SeifertData :=
  ⟨3, 0, [(2, 1), (3, 1), (5, 1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : platonicExample.orbChi = 1 / 30 ∧ platonicExample.euler = -31 / 30 ∧
    platonicExample.modelOf rfl = .spherical := by
  norm_num [platonicExample, orbChi, euler, modelOf, closedTable]

private def collarExample : SeifertData :=
  ⟨2, 2, [], [], by norm_num, by norm_num, by decide, by decide, rfl⟩

example : collarExample.openModelOf (by decide) (by simp [IsSolidTorus, collarExample]) =
    .euclidean := (openModelOf_eq_euclidean_iff _ _ _).2 (Or.inl ⟨rfl, rfl⟩)

private def twistedBundleExample : SeifertData :=
  ⟨3, 1, [(2, 1), (2, 1)], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : twistedBundleExample.openModelOf (by decide)
    (by simp [IsSolidTorus, twistedBundleExample]) = .euclidean :=
  (openModelOf_eq_euclidean_iff _ _ _).2 (Or.inr ⟨rfl, rfl⟩)

private def pantsExample : SeifertData :=
  ⟨3, 3, [], [], by norm_num, le_rfl, by decide, by decide, rfl⟩

example : pantsExample.openModelOf (by decide) (by simp [IsSolidTorus, pantsExample]) =
    .hyperbolicProduct :=
  (openModelOf_eq_hyperbolicProduct_iff _ _ _).2 (by norm_num [pantsExample, orbChi])

end SeifertData

end GC.Seifert
