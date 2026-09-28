/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Subdivision

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_of_singleton_mem_faces_of_mem_convexHull
    {K : Geometry.SimplicialComplex ℝ E} {v : E} (hv : ({v} : Finset E) ∈ K.faces)
    {σ : Finset E} (hσ : σ ∈ K.faces) (hvσ : v ∈ convexHull ℝ (σ : Set E)) : v ∈ σ := by
  classical
  have h := K.inter_subset_convexHull hv hσ ⟨by simp, hvσ⟩
  rw [← Finset.coe_inter] at h
  by_contra hvn
  have hempty : ({v} : Finset E) ∩ σ = ∅ := by
    ext u
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro rfl
    exact hvn
  rw [hempty, Finset.coe_empty, convexHull_empty] at h
  exact h

theorem IsSubdivision.exists_path_of_edge [DecidableEq E] {K K' : Geometry.SimplicialComplex ℝ E}
    (hsub : IsSubdivision K' K) (hK' : K'.faces.Finite) {x y : E} (hxy : x ≠ y)
    (hε : ({x, y} : Finset E) ∈ K.faces) :
    ∃ (n : ℕ) (c : ℕ → ℝ), 0 < n ∧ c 0 = 0 ∧ c n = 1 ∧ StrictMonoOn c (Iic n) ∧
      (∀ i ≤ n, ({AffineMap.lineMap x y (c i)} : Finset E) ∈ K'.faces) ∧
      (∀ i < n, ({AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} : Finset E) ∈
        K'.faces) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ({AffineMap.lineMap x y t} : Finset E) ∈ K'.faces →
        ∃ i ≤ n, c i = t) ∧
      ∀ σ ∈ K'.faces, convexHull ℝ (σ : Set E) ⊆ segment ℝ x y → σ.card = 2 →
        ∃ i < n, σ = {AffineMap.lineMap x y (c i), AffineMap.lineMap x y (c (i + 1))} := by
  classical
  set L := AffineMap.lineMap (k := ℝ) x y
  have hLinj : Function.Injective L := AffineMap.lineMap_injective ℝ hxy
  have hseg : segment ℝ x y = L '' Icc 0 1 := segment_eq_image_lineMap ℝ x y
  have hL0 : L 0 = x := AffineMap.lineMap_apply_zero x y
  have hL1 : L 1 = y := AffineMap.lineMap_apply_one x y
  have hxK : ({x} : Finset E) ∈ K'.faces := hsub.singleton_mem
    (K.down_closed hε (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self x {y}))
      (Finset.singleton_nonempty x))
  have hyK : ({y} : Finset E) ∈ K'.faces := hsub.singleton_mem
    (K.down_closed hε (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self y))) (Finset.singleton_nonempty y))
  set Λ : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ ({L t} : Finset E) ∈ K'.faces}
  have hΛfin : Λ.Finite := by
    refine Set.Finite.of_finite_image (f := fun t => ({L t} : Finset E))
      (hK'.subset ?_) ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact ht.2
    · intro s _ t _ hst
      exact hLinj (Finset.singleton_injective hst)
  set Λf := hΛfin.toFinset with hΛf
  have hmemΛ : ∀ t, t ∈ Λf ↔ t ∈ Icc (0 : ℝ) 1 ∧ ({L t} : Finset E) ∈ K'.faces := fun t => by
    rw [hΛf, Set.Finite.mem_toFinset]
    rfl
  have h0 : (0 : ℝ) ∈ Λf := (hmemΛ 0).mpr ⟨⟨le_rfl, zero_le_one⟩, by rw [hL0]; exact hxK⟩
  have h1 : (1 : ℝ) ∈ Λf := (hmemΛ 1).mpr ⟨⟨zero_le_one, le_rfl⟩, by rw [hL1]; exact hyK⟩
  have hcard : 2 ≤ Λf.card := by
    have : ({0, 1} : Finset ℝ) ⊆ Λf := by
      intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact h0
      · rw [Finset.mem_singleton.mp ht]
        exact h1
    have h2 : ({0, 1} : Finset ℝ).card = 2 := Finset.card_pair zero_ne_one
    exact h2 ▸ Finset.card_le_card this
  set n := Λf.card - 1
  have hn : Λf.card = n + 1 := by omega
  set s := Λf.orderEmbOfFin hn with hsdef
  set c : ℕ → ℝ := fun i => if h : i < n + 1 then s ⟨i, h⟩ else 1 with hcdef
  have hc : ∀ i (h : i < n + 1), c i = s ⟨i, h⟩ := fun i h => by
    change (if h' : i < n + 1 then s ⟨i, h'⟩ else 1) = s ⟨i, h⟩
    rw [dite_eq_left h]
  have hcmem : ∀ i ≤ n, c i ∈ Λf := fun i hi => by
    rw [hc i (by omega)]
    exact Λf.orderEmbOfFin_mem hn _
  have hmono : StrictMonoOn c (Iic n) := by
    intro i hi j hj hij
    rw [hc i (by simp only [mem_Iic] at hi; omega), hc j (by simp only [mem_Iic] at hj; omega)]
    exact s.strictMono (Fin.mk_lt_mk.mpr hij)
  have hsurj : ∀ t ∈ Λf, ∃ i ≤ n, c i = t := by
    intro t ht
    have ht' : t ∈ Set.range s := by
      rw [hsdef, Finset.range_orderEmbOfFin]
      exact ht
    obtain ⟨⟨i, hi⟩, rfl⟩ := ht'
    exact ⟨i, by omega, hc i hi⟩
  have hΛIcc : ∀ t ∈ Λf, t ∈ Icc (0 : ℝ) 1 := fun t ht => ((hmemΛ t).mp ht).1
  have hc0 : c 0 = 0 := by
    rw [hc 0 (by omega), hsdef, Finset.orderEmbOfFin_zero hn (by omega)]
    exact le_antisymm (Finset.min'_le Λf 0 h0) (hΛIcc _ (Finset.min'_mem Λf _)).1
  have hcn : c n = 1 := by
    have hlast := Finset.orderEmbOfFin_last hn (by omega : 0 < n + 1)
    have hcn' : c n = Λf.max' ⟨0, h0⟩ := by
      rw [hc n (by omega), hsdef]
      exact hlast
    rw [hcn']
    exact le_antisymm (hΛIcc _ (Finset.max'_mem Λf _)).2 (Finset.le_max' Λf 1 h1)
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have : c 0 = c n := by rw [hn0]
    rw [hc0, hcn] at this
    exact zero_ne_one this
  have hgap : ∀ i < n, ∀ t ∈ Λf, ¬ (c i < t ∧ t < c (i + 1)) := by
    rintro i hi t ht ⟨hlt, hgt⟩
    obtain ⟨j, hj, rfl⟩ := hsurj t ht
    have h1' : i < j := by
      by_contra h
      have hle : j ≤ i := by omega
      rcases hle.lt_or_eq with h' | h'
      · exact absurd (hmono (by simp only [mem_Iic]; omega) (by simp only [mem_Iic]; omega) h')
          (not_lt.mpr hlt.le)
      · rw [h'] at hlt
        exact lt_irrefl _ hlt
    have h2' : j < i + 1 := by
      by_contra h
      have hle : i + 1 ≤ j := by omega
      rcases hle.lt_or_eq with h' | h'
      · exact absurd (hmono (by simp only [mem_Iic]; omega) (by simp only [mem_Iic]; omega) h')
          (not_lt.mpr hgt.le)
      · rw [h'] at hgt
        exact lt_irrefl _ hgt
    omega
  have hparam : ∀ v ∈ segment ℝ x y, ∃ t ∈ Icc (0 : ℝ) 1, L t = v := by
    intro v hv
    rw [hseg] at hv
    obtain ⟨t, ht, rfl⟩ := hv
    exact ⟨t, ht, rfl⟩
  have hside : ∀ {σ : Finset E}, (σ : Set E) ⊆ segment ℝ x y → ∀ {m : ℝ},
      L m ∈ convexHull ℝ (σ : Set E) →
      (∃ u ∈ σ, ∃ tu ∈ Icc (0 : ℝ) 1, L tu = u ∧ tu ≤ m) ∧
        ∃ v ∈ σ, ∃ tv ∈ Icc (0 : ℝ) 1, L tv = v ∧ m ≤ tv := by
    intro σ hσ m hm
    constructor
    · by_contra hno
      push Not at hno
      have hsub' : (σ : Set E) ⊆ L '' Ioi m := by
        intro u hu
        obtain ⟨tu, htu, rfl⟩ := hparam u (hσ hu)
        exact ⟨tu, hno _ hu tu htu rfl, rfl⟩
      have hconv : convexHull ℝ (σ : Set E) ⊆ L '' Ioi m :=
        convexHull_min hsub' ((convex_Ioi m).affine_image L)
      obtain ⟨t, ht, htm⟩ := hconv hm
      exact lt_irrefl m (hLinj htm ▸ ht)
    · by_contra hno
      push Not at hno
      have hsub' : (σ : Set E) ⊆ L '' Iio m := by
        intro u hu
        obtain ⟨tu, htu, rfl⟩ := hparam u (hσ hu)
        exact ⟨tu, hno _ hu tu htu rfl, rfl⟩
      have hconv : convexHull ℝ (σ : Set E) ⊆ L '' Iio m :=
        convexHull_min hsub' ((convex_Iio m).affine_image L)
      obtain ⟨t, ht, htm⟩ := hconv hm
      exact lt_irrefl m (hLinj htm ▸ ht)
  have hbetween : ∀ {σ : Finset E} {a b t : ℝ}, a ≤ t → t ≤ b → L a ∈ σ → L b ∈ σ →
      L t ∈ convexHull ℝ (σ : Set E) := by
    intro σ a b t hat htb ha hb
    have hsegab : L t ∈ segment ℝ (L a) (L b) := by
      rw [← image_segment ℝ L a b, segment_eq_Icc (hat.trans htb)]
      exact ⟨t, ⟨hat, htb⟩, rfl⟩
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ha)
      (subset_convexHull ℝ _ hb) hsegab
  have hvert : ∀ i ≤ n, ({L (c i)} : Finset E) ∈ K'.faces := fun i hi =>
    ((hmemΛ _).mp (hcmem i hi)).2
  refine ⟨n, c, hnpos, hc0, hcn, hmono, hvert, ?_, ?_, ?_⟩
  · intro i hi
    set m := (c i + c (i + 1)) / 2 with hmdef
    have hci : c i < c (i + 1) := hmono (by simp only [mem_Iic]; omega)
      (by simp only [mem_Iic]; omega) (by omega)
    have hm1 : c i < m := by rw [hmdef]; linarith
    have hm2 : m < c (i + 1) := by rw [hmdef]; linarith
    have hmIcc : m ∈ Icc (0 : ℝ) 1 :=
      ⟨(hΛIcc _ (hcmem i hi.le)).1.trans hm1.le, hm2.le.trans (hΛIcc _ (hcmem (i + 1) hi)).2⟩
    have hmε : L m ∈ convexHull ℝ (({x, y} : Finset E) : Set E) := by
      rw [Finset.coe_pair, convexHull_pair, hseg]
      exact ⟨m, hmIcc, rfl⟩
    obtain ⟨σ, hσK, hmσ, hσε⟩ := hsub.exists_face_subset_of_mem hε hmε
    have hσseg : (σ : Set E) ⊆ segment ℝ x y := by
      rw [← convexHull_pair, ← Finset.coe_pair]
      exact (subset_convexHull ℝ _).trans hσε
    obtain ⟨⟨u, hu, tu, htu, rfl, htum⟩, ⟨v, hv, tv, htv, rfl, htvm⟩⟩ := hside hσseg hmσ
    have htuΛ : tu ∈ Λf := (hmemΛ tu).mpr ⟨htu, K'.down_closed hσK
      (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty _)⟩
    have htvΛ : tv ∈ Λf := (hmemΛ tv).mpr ⟨htv, K'.down_closed hσK
      (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)⟩
    have htu' : tu ≤ c i := by
      by_contra h
      exact hgap i hi tu htuΛ ⟨lt_of_not_ge h, htum.trans_lt hm2⟩
    have htv' : c (i + 1) ≤ tv := by
      by_contra h
      exact hgap i hi tv htvΛ ⟨hm1.trans_le htvm, lt_of_not_ge h⟩
    have hpi : L (c i) ∈ σ := mem_of_singleton_mem_faces_of_mem_convexHull
      (hvert i hi.le) hσK (hbetween htu' (hci.le.trans htv') hu hv)
    have hpi1 : L (c (i + 1)) ∈ σ := mem_of_singleton_mem_faces_of_mem_convexHull
      (hvert (i + 1) hi) hσK (hbetween (htu'.trans hci.le) htv' hu hv)
    refine K'.down_closed hσK ?_ (Finset.insert_nonempty _ _)
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hpi
    · rw [Finset.mem_singleton.mp hz]
      exact hpi1
  · intro t ht htK
    exact hsurj t ((hmemΛ t).mpr ⟨ht, htK⟩)
  · intro σ hσK hσseg hσcard
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp hσcard
    have hσseg' : (({u, v} : Finset E) : Set E) ⊆ segment ℝ x y :=
      (subset_convexHull ℝ _).trans hσseg
    obtain ⟨tu, htu, rfl⟩ := hparam u (hσseg' (by simp))
    obtain ⟨tv, htv, rfl⟩ := hparam v (hσseg' (by simp))
    have htuΛ : tu ∈ Λf := (hmemΛ tu).mpr ⟨htu, K'.down_closed hσK (by simp)
      (Finset.singleton_nonempty _)⟩
    have htvΛ : tv ∈ Λf := (hmemΛ tv).mpr ⟨htv, K'.down_closed hσK (by simp)
      (Finset.singleton_nonempty _)⟩
    obtain ⟨i, hi, rfl⟩ := hsurj tu htuΛ
    obtain ⟨j, hj, rfl⟩ := hsurj tv htvΛ
    have hij : i ≠ j := fun h => huv (by rw [h])
    have key : ∀ i j, i ≤ n → j ≤ n → i < j →
        ({L (c i), L (c j)} : Finset E) ∈ K'.faces → j = i + 1 := by
      intro i j hi hj hij hK
      by_contra hne
      have hlt : i + 1 < j := by omega
      have h1' : c i < c (i + 1) := hmono (by simp only [mem_Iic]; omega)
        (by simp only [mem_Iic]; omega) (by omega)
      have h2' : c (i + 1) < c j := hmono (by simp only [mem_Iic]; omega)
        (by simp only [mem_Iic]; omega) hlt
      have hmem := mem_of_singleton_mem_faces_of_mem_convexHull
        (hvert (i + 1) (by omega)) hK (hbetween h1'.le h2'.le (by simp) (by simp))
      rcases Finset.mem_insert.mp hmem with h | h
      · exact absurd (hLinj h) h1'.ne'
      · exact absurd (hLinj (Finset.mem_singleton.mp h)) h2'.ne
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, by have := key i j hi hj h hσK; omega, by rw [key i j hi hj h hσK]⟩
    · refine ⟨j, by have := key j i hj hi h (by rw [Finset.pair_comm]; exact hσK); omega, ?_⟩
      rw [key j i hj hi h (by rw [Finset.pair_comm]; exact hσK), Finset.pair_comm]

end DifferentialGeometry.Topology.PiecewiseLinear
