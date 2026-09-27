/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TwoFoldCrossing
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFaces
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smul_mem_linearHalfSpace {S : Submodule ℝ E} {u x : E} (hx : x ∈ linearHalfSpace S u)
    {t : ℝ} (ht : 0 ≤ t) : t • x ∈ linearHalfSpace S u := by
  obtain ⟨s, hs, r, hr, rfl⟩ := hx
  exact ⟨t • s, S.smul_mem t hs, t * r, mul_nonneg ht hr, by rw [smul_add, mul_smul]⟩

theorem eq_of_eventually_sub_mem_iff {D D' : Submodule ℝ E} {p : E}
    (h : ∀ᶠ y in 𝓝 p, (y - p ∈ D ↔ y - p ∈ D')) : D = D' := by
  ext v
  have hcont : Filter.Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • v) := by fun_prop
    simpa using hc.tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually h)
  have hmem : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have key := hball hmem
  simp only [add_sub_cancel_left] at key
  rwa [Submodule.smul_mem_iff _ (by positivity : ε / 2 ≠ 0),
    Submodule.smul_mem_iff _ (by positivity : ε / 2 ≠ 0)] at key

theorem linearHalfSpace_inter_subset_of_eventually {D : Submodule ℝ E} {u u' p : E}
    (h : ∀ᶠ y in 𝓝 p, y - p ∈ linearHalfSpace D u → y - p ∈ linearHalfSpace D u' →
      y - p ∈ D) :
    linearHalfSpace D u ∩ linearHalfSpace D u' ⊆ D := by
  rintro v ⟨hv, hv'⟩
  have hcont : Filter.Tendsto (fun t : ℝ => p + t • v) (𝓝 0) (𝓝 p) := by
    have hc : Continuous (fun t : ℝ => p + t • v) := by fun_prop
    simpa using hc.tendsto 0
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually h)
  have hmem : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have key := hball hmem
  simp only [add_sub_cancel_left] at key
  have hpos : (0 : ℝ) ≤ ε / 2 := by positivity
  exact (Submodule.smul_mem_iff _ (by positivity : ε / 2 ≠ 0)).mp
    (key (smul_mem_linearHalfSpace hv hpos) (smul_mem_linearHalfSpace hv' hpos))

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_mem_boundaryComplex_space_notMem
    [FiniteDimensional ℝ E] [inst : DecidableEq E] {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hne : (boundaryComplex 2 K).space.Nonempty) {V : Set E} (hV : V.Finite) :
    ∃ p ∈ (boundaryComplex 2 K).space, p ∉ V := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  obtain ⟨p₀, hp₀⟩ := hne
  obtain ⟨s, hs, -⟩ := (boundaryComplex 2 K).mem_space_iff.mp hp₀
  obtain ⟨v, hv⟩ := (boundaryComplex 2 K).nonempty_of_mem_faces hs
  have hvB : {v} ∈ (boundaryComplex 2 K).faces := (boundaryComplex 2 K).down_closed hs
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨x, hx⟩ := (isCombinatorialManifold_boundaryComplex K hK v hvB).nonempty
  obtain ⟨t, ht, -⟩ :=
    (SimplicialComplex.geometricLink (boundaryComplex 2 K) {v}).mem_space_iff.mp hx
  obtain ⟨⟨w, hw⟩, hvt, hins⟩ :=
    (SimplicialComplex.mem_geometricLink_singleton (boundaryComplex 2 K) v t).mp ht
  have hvw : v ≠ w := fun h => hvt (by rw [h]; exact hw)
  have hedge : ({v, w} : Finset E) ∈ (boundaryComplex 2 K).faces :=
    (boundaryComplex 2 K).down_closed hins
      (Finset.insert_subset_insert v (Finset.singleton_subset_iff.mpr hw))
      (Finset.insert_nonempty v {w})
  have hseg : segment ℝ v w ⊆ (boundaryComplex 2 K).space :=
    (segment_subset_convexHull (by simp) (by simp)).trans
      ((boundaryComplex 2 K).convexHull_subset_space hedge)
  have hinj : Function.Injective (fun θ : ℝ => v + θ • (w - v)) := fun a b hab =>
    smul_left_injective ℝ (sub_ne_zero.mpr hvw.symm) (add_left_cancel hab)
  have hinf : (segment ℝ v w).Infinite := by
    rw [segment_eq_image']
    exact (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).image hinj.injOn
  obtain ⟨p, hp, hpV⟩ := (hinf.sdiff hV).nonempty
  exact ⟨p, hseg hp, hpV⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_halfSpace_germ_of_mem_boundaryComplex
    [FiniteDimensional ℝ E] [inst : DecidableEq E] {K : Geometry.SimplicialComplex ℝ E}
    [Finite K.faces] (hK : IsCombinatorialManifoldWithBoundary 2 K) {p : E}
    (hp : p ∈ (boundaryComplex 2 K).space) (hpv : ∀ v, {v} ∈ K.faces → v ≠ p) :
    ∃ d u : E, d ≠ 0 ∧ u ∉ Submodule.span ℝ {d} ∧ ∀ᶠ y in 𝓝 p,
      (y ∈ K.space ↔ y - p ∈ linearHalfSpace (Submodule.span ℝ {d}) u) ∧
        (y ∈ (boundaryComplex 2 K).space ↔ y - p ∈ Submodule.span ℝ {d}) := by
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  have hpK : p ∈ K.space := boundaryComplex_space_subset 2 K hp
  obtain ⟨σ, hσ, hpσ⟩ := exists_face_mem_openSimplex K hpK
  obtain ⟨t, ht, hpt⟩ := (boundaryComplex 2 K).mem_space_iff.mp hp
  have hσB : σ ∈ (boundaryComplex 2 K).faces := (boundaryComplex 2 K).down_closed ht
    (face_subset_of_mem_openSimplex_of_mem_convexHull K hσ (boundaryComplex_faces_subset 2 K ht)
      hpσ hpt) (K.nonempty_of_mem_faces hσ)
  obtain ⟨-, hσle, hball⟩ := (hK.mem_boundaryComplex_faces_iff K).mp hσB
  have hcard : σ.card = 2 := by
    rcases Nat.lt_or_ge σ.card 2 with hlt | hge
    · have hpos := (K.nonempty_of_mem_faces hσ).card_pos
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp (show σ.card = 1 by omega)
      obtain ⟨w, -, hw1, hwp⟩ := hpσ
      rw [Finset.sum_singleton] at hw1 hwp
      rw [hw1, one_smul] at hwp
      exact absurd hwp (hpv v hσ)
    · omega
  have hbound : ∀ u ∈ K.faces, σ ⊆ u → u.card ≤ σ.card + 1 := by
    intro u hu _
    have := hK.card_le K hu
    omega
  rw [geometricLink_space_eq_coface_vertices_of_card_le K σ hbound, hcard] at hball
  obtain ⟨a, ha⟩ := isPLBall_zero_iff.mp hball
  have hac : a ∉ σ ∧ insert a σ ∈ K.faces := by
    have hmem : a ∈ ({a} : Set E) := rfl
    rw [← ha] at hmem
    exact hmem
  have hlocal := eventually_mem_space_iff_mem_codimension_one_cone K hσ hbound ⟨a, hac⟩ hpσ
  let _ : Finite (boundaryComplex 2 K).faces := (boundaryComplex_faces_finite 2 K).to_subtype
  have hmax : ∀ u ∈ (boundaryComplex 2 K).faces, σ ⊆ u → u.card ≤ σ.card := by
    intro u hu _
    rw [hcard]
    exact ((hK.mem_boundaryComplex_faces_iff K).mp hu).2.1
  have hlocalB := eventually_mem_space_iff_sub_mem_vectorSpan (boundaryComplex 2 K) hσB hmax hpσ
  obtain ⟨v₀, v₁, hv01, hσeq⟩ := Finset.card_eq_two.mp hcard
  have hspan : vectorSpan ℝ (σ : Set E) = Submodule.span ℝ {v₀ - v₁} := by
    rw [hσeq, Finset.coe_pair, vectorSpan_pair, vsub_eq_sub]
  have haff : a ∉ affineSpan ℝ (σ : Set E) :=
    notMem_affineSpan_of_affineIndependent_insert hac.1 (K.indep hac.2)
  have hpaff : p ∈ affineSpan ℝ (σ : Set E) :=
    convexHull_subset_affineSpan _ (openSimplex_subset_convexHull σ hpσ)
  have hu : a - p ∉ vectorSpan ℝ (σ : Set E) := by
    intro h
    apply haff
    have hdir : a - p ∈ (affineSpan ℝ (σ : Set E)).direction := by
      rw [direction_affineSpan]
      exact h
    have hmem := AffineSubspace.vadd_mem_of_mem_direction hdir hpaff
    rwa [vadd_eq_add, sub_add_cancel] at hmem
  refine ⟨v₀ - v₁, a - p, sub_ne_zero.mpr hv01, hspan ▸ hu, ?_⟩
  filter_upwards [hlocal, hlocalB] with y hy hyB
  rw [← hspan]
  refine ⟨hy.trans ⟨?_, ?_⟩, hyB⟩
  · rintro ⟨w, hw, hwface, hcone⟩
    have hwa : w ∈ ({a} : Set E) := by
      rw [← ha]
      exact ⟨hw, hwface⟩
    rw [mem_singleton_iff] at hwa
    subst hwa
    exact hcone
  · intro hcone
    exact ⟨a, hac.1, hac.2, hcone⟩

end Germs

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLHomeomorphOn_triod_straightening {d : E3} (hd : d ≠ 0) (u : Fin 3 → E3)
    (hu : ∀ i, u i ∉ Submodule.span ℝ {d})
    (hcone : ∀ i j, i ≠ j → linearHalfSpace (Submodule.span ℝ {d}) (u i) ∩
      linearHalfSpace (Submodule.span ℝ {d}) (u j) ⊆ Submodule.span ℝ {d}) :
    ∃ Φ : E3 → E3, IsPLHomeomorphOn Φ univ univ ∧ Φ 0 = 0 ∧ ∀ i y,
      y ∈ linearHalfSpace (Submodule.span ℝ {d}) (u i) ↔
        Φ y ∈ (![{w : E3 | w 1 = 0 ∧ 0 ≤ w 0},
          {w : E3 | w 1 = 0 ∧ w 0 ≤ 0},
          {w : E3 | w 0 = 0 ∧ 0 ≤ w 1}] : Fin 3 → Set E3) i := by
  set D : Submodule ℝ E3 := Submodule.span ℝ {d} with hDdef
  have hdD : d ∈ D := Submodule.mem_span_singleton_self d
  obtain ⟨T, hDT⟩ := Submodule.exists_isCompl D
  have hsplit : ∀ i, ∃ t ∈ T, u i - t ∈ D := by
    intro i
    have hmem : u i ∈ D ⊔ T := by
      rw [hDT.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hmem
    refine ⟨z, hz, ?_⟩
    rw [← hyz, add_sub_cancel_right]
    exact hy
  choose t htT htD using hsplit
  have hCt : ∀ i, linearHalfSpace D (u i) = linearHalfSpace D (t i) :=
    fun i => linearHalfSpace_eq_of_sub_mem D (htD i)
  have htDnot : ∀ i, t i ∉ D := by
    intro i hti
    apply hu i
    have hsum := D.add_mem (htD i) hti
    rwa [sub_add_cancel] at hsum
  have ht0 : ∀ i, t i ≠ 0 := fun i h => htDnot i (h ▸ D.zero_mem)
  have hself : ∀ v : E3, v ∈ linearHalfSpace D v :=
    fun v => ⟨0, D.zero_mem, 1, zero_le_one, by rw [zero_add, one_smul]⟩
  have hcone' : ∀ i j, i ≠ j → ∀ y, y ∈ linearHalfSpace D (t i) →
      y ∈ linearHalfSpace D (t j) → y ∈ D := by
    intro i j hij y hi hj
    rw [← hCt] at hi hj
    exact hcone i j hij ⟨hi, hj⟩
  have hnot : ∀ c : ℝ, 0 < c → t 1 ≠ c • t 0 := by
    intro c hc h
    apply htDnot 0
    refine hcone' 0 1 (by decide) (t 0) (hself _) ?_
    rw [h, linearHalfSpace_smul_of_pos D (t 0) hc]
    exact hself _
  obtain ⟨ℓ, hℓD, hℓ0, hℓ1⟩ :=
    exists_linearMap_eq_one_neg_of_disjoint hDT.disjoint (htT 0) (htT 1) (ht0 0) (ht0 1) hnot
  have hℓpos : 0 < ℓ (t 0) := by
    rw [hℓ0]
    exact one_pos
  obtain ⟨h, hh, hfix, hru, hrv, hadd, -⟩ := exists_isPLHomeomorphOn_straighten_rays ℓ hℓpos hℓ1
  have hkerD : ∀ z ∈ D, ℓ z = 0 := fun z hz => LinearMap.mem_ker.mp (hℓD hz)
  have hformula : ∀ y, h y = y + min (ℓ y) 0 • (t 0 - (ℓ (t 1))⁻¹ • t 1) := by
    intro y
    rcases le_or_gt 0 (ℓ y) with hy | hy
    · rw [min_eq_right hy, zero_smul, add_zero]
      have hk : ℓ (y - ℓ y • t 0) = 0 := by
        rw [map_sub, map_smul, hℓ0, smul_eq_mul, mul_one, sub_self]
      calc h y = h ((y - ℓ y • t 0) + ℓ y • t 0) := by rw [sub_add_cancel]
        _ = (y - ℓ y • t 0) + h (ℓ y • t 0) := hadd _ _ hk
        _ = (y - ℓ y • t 0) + ℓ y • t 0 := by rw [hru _ hy]
        _ = y := sub_add_cancel _ _
    · rw [min_eq_left hy.le]
      have hne : ℓ (t 1) ≠ 0 := hℓ1.ne
      have hc : 0 ≤ ℓ y / ℓ (t 1) := div_nonneg_of_nonpos hy.le hℓ1.le
      have hk : ℓ (y - (ℓ y / ℓ (t 1)) • t 1) = 0 := by
        rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hne, sub_self]
      calc h y = h ((y - (ℓ y / ℓ (t 1)) • t 1) + (ℓ y / ℓ (t 1)) • t 1) := by
            rw [sub_add_cancel]
        _ = (y - (ℓ y / ℓ (t 1)) • t 1) + h ((ℓ y / ℓ (t 1)) • t 1) := hadd _ _ hk
        _ = (y - (ℓ y / ℓ (t 1)) • t 1) + ((ℓ y / ℓ (t 1)) * (ℓ (t 1) / ℓ (t 0))) • t 0 := by
            rw [hrv _ hc]
        _ = y + ℓ y • (t 0 - (ℓ (t 1))⁻¹ • t 1) := by
            rw [hℓ0, div_one, div_mul_cancel₀ _ hne, smul_sub, smul_smul, ← div_eq_mul_inv]
            abel
  have hhom : ∀ (y : E3) (r : ℝ), 0 ≤ r → h (r • y) = r • h y := by
    intro y r hr
    have hmin : min (r * ℓ y) 0 = r * min (ℓ y) 0 := by
      rw [mul_min_of_nonneg _ _ hr, mul_zero]
    rw [hformula, hformula, map_smul, smul_eq_mul, hmin, mul_smul, smul_add]
  have hinj : Function.Injective h := fun a b hab =>
    hh.bijOn.injOn (mem_univ a) (mem_univ b) hab
  have hmemiff : ∀ (C : Set E3) (y : E3), y ∈ C ↔ h y ∈ h '' C :=
    fun C y => hinj.mem_set_image.symm
  have himage : ∀ v v' : E3, (∀ r : ℝ, 0 ≤ r → h (r • v) = r • v') →
      h '' linearHalfSpace D v = linearHalfSpace D v' := by
    intro v v' hv
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, r, hr, rfl⟩, rfl⟩
      exact ⟨z, hz, r, hr, by rw [hadd z (r • v) (hkerD z hz), hv r hr]⟩
    · rintro ⟨z, hz, r, hr, rfl⟩
      exact ⟨z + r • v, ⟨z, hz, r, hr, rfl⟩, by rw [hadd z (r • v) (hkerD z hz), hv r hr]⟩
  have hC0 : h '' linearHalfSpace D (t 0) = linearHalfSpace D (t 0) := himage _ _ hru
  have hC1 : h '' linearHalfSpace D (t 1) = linearHalfSpace D (-t 0) := by
    have hneg : ℓ (t 1) • t 0 = (-ℓ (t 1)) • -t 0 := (neg_smul_neg _ _).symm
    rw [himage (t 1) (ℓ (t 1) • t 0) (fun r hr => by rw [hrv r hr, hℓ0, div_one, mul_smul]),
      hneg, linearHalfSpace_smul_of_pos D (-t 0) (neg_pos.mpr hℓ1)]
  have hC2 : h '' linearHalfSpace D (t 2) = linearHalfSpace D (h (t 2)) :=
    himage _ _ fun r hr => hhom (t 2) r hr
  have hw : h (t 2) ∉ D ⊔ Submodule.span ℝ {t 0} := by
    intro hmem
    obtain ⟨z, hz, x, hx, hzx⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rcases le_or_gt 0 c with hc | hc
    · have h2 : t 2 ∈ linearHalfSpace D (t 0) := by
        refine (hmemiff _ _).mpr ?_
        rw [hC0]
        exact ⟨z, hz, c, hc, hzx.symm⟩
      exact htDnot 2 (hcone' 2 0 (by decide) (t 2) (hself _) h2)
    · have h2 : t 2 ∈ linearHalfSpace D (t 1) := by
        refine (hmemiff _ _).mpr ?_
        rw [hC1]
        exact ⟨z, hz, -c, by linarith, by rw [← hzx, neg_smul_neg]⟩
      exact htDnot 2 (hcone' 2 1 (by decide) (t 2) (hself _) h2)
  have hli : LinearIndependent ℝ (![t 0, h (t 2), d] : Fin 3 → E3) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • t 0 + g 1 • h (t 2) + g 2 • d = 0 := by
      simpa [Fin.sum_univ_three] using hg
    have hg1 : g 1 = 0 := by
      by_contra hne
      apply hw
      have heq : g 1 • h (t 2) = -(g 2 • d) - g 0 • t 0 :=
        eq_sub_of_add_eq' (eq_neg_of_add_eq_zero_left hg')
      have hmem : g 1 • h (t 2) ∈ D ⊔ Submodule.span ℝ {t 0} := by
        rw [heq]
        exact Submodule.sub_mem _ (Submodule.neg_mem _ (Submodule.mem_sup_left (D.smul_mem _ hdD)))
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      exact (Submodule.smul_mem_iff _ hne).mp hmem
    have hg0 : g 0 = 0 := by
      rw [hg1, zero_smul, add_zero] at hg'
      by_contra hne
      apply htDnot 0
      have heq : g 0 • t 0 = -(g 2 • d) := eq_neg_of_add_eq_zero_left hg'
      have hmem : g 0 • t 0 ∈ D := by
        rw [heq]
        exact D.neg_mem (D.smul_mem _ hdD)
      exact (Submodule.smul_mem_iff _ hne).mp hmem
    have hg2 : g 2 = 0 := by
      simp only [hg0, hg1, zero_smul, zero_add] at hg'
      exact (smul_eq_zero.mp hg').resolve_right hd
    intro i
    fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  let bas := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hbas : ∀ c : Fin 3 → ℝ, bas.equivFun.symm c = c 0 • t 0 + c 1 • h (t 2) + c 2 • d := by
    intro c
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_three]
    simp [bas]
  let L : E3 ≃ₗ[ℝ] E3 := bas.equivFun.trans (EuclideanSpace.equiv (Fin 3) ℝ).symm.toLinearEquiv
  have hLx : ∀ (x : E3) (i : Fin 3), L x i = bas.equivFun x i := fun _ _ => rfl
  have hLc : ∀ (c : Fin 3 → ℝ) (i : Fin 3), L (bas.equivFun.symm c) i = c i := by
    intro c i
    rw [hLx, LinearEquiv.apply_symm_apply]
  have hLeq : ∀ (a b c : ℝ) (i : Fin 3), L (a • t 0 + b • h (t 2) + c • d) i = ![a, b, c] i := by
    intro a b c i
    have hi := hLc ![a, b, c] i
    rw [hbas] at hi
    simpa using hi
  have hcoord : ∀ x : E3, x = L x 0 • t 0 + L x 1 • h (t 2) + L x 2 • d := by
    intro x
    have hx := hbas (bas.equivFun x)
    rw [LinearEquiv.symm_apply_apply] at hx
    rw [hLx, hLx, hLx]
    exact hx
  have hH0 : ∀ x : E3, x ∈ linearHalfSpace D (t 0) ↔ L x 1 = 0 ∧ 0 ≤ L x 0 := by
    intro x
    constructor
    · rintro ⟨z, hz, r, hr, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have e : s • d + r • t 0 = r • t 0 + (0 : ℝ) • h (t 2) + s • d := by
        rw [zero_smul, add_zero, add_comm]
      rw [e, hLeq, hLeq]
      exact ⟨by simp, by simpa using hr⟩
    · rintro ⟨h1, h0⟩
      refine ⟨L x 2 • d, D.smul_mem _ hdD, L x 0, h0, ?_⟩
      conv_lhs => rw [hcoord x]
      rw [h1, zero_smul, add_zero]
      exact add_comm _ _
  have hH1 : ∀ x : E3, x ∈ linearHalfSpace D (-t 0) ↔ L x 1 = 0 ∧ L x 0 ≤ 0 := by
    intro x
    constructor
    · rintro ⟨z, hz, r, hr, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have e : s • d + r • -t 0 = (-r) • t 0 + (0 : ℝ) • h (t 2) + s • d := by
        rw [zero_smul, add_zero, smul_neg, neg_smul, add_comm]
      rw [e, hLeq, hLeq]
      exact ⟨by simp, by simpa using hr⟩
    · rintro ⟨h1, h0⟩
      refine ⟨L x 2 • d, D.smul_mem _ hdD, -L x 0, by linarith, ?_⟩
      conv_lhs => rw [hcoord x]
      rw [h1, zero_smul, add_zero, neg_smul_neg]
      exact add_comm _ _
  have hH2 : ∀ x : E3, x ∈ linearHalfSpace D (h (t 2)) ↔ L x 0 = 0 ∧ 0 ≤ L x 1 := by
    intro x
    constructor
    · rintro ⟨z, hz, r, hr, rfl⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
      have e : s • d + r • h (t 2) = (0 : ℝ) • t 0 + r • h (t 2) + s • d := by
        rw [zero_smul, zero_add, add_comm]
      rw [e, hLeq, hLeq]
      exact ⟨by simp, by simpa using hr⟩
    · rintro ⟨h0, h1⟩
      refine ⟨L x 2 • d, D.smul_mem _ hdD, L x 1, h1, ?_⟩
      conv_lhs => rw [hcoord x]
      rw [h0, zero_smul, zero_add]
      exact add_comm _ _
  have hL : IsPLHomeomorphOn L univ univ := by
    refine ⟨Set.bijOn_univ.mpr L.bijective, ?_, ?_⟩
    · exact (isPiecewiseAffineOn_of_affine L.toLinearMap.toAffineMap isOpen_univ).congr
        fun _ _ => rfl
    · refine (isPiecewiseAffineOn_of_affine L.symm.toLinearMap.toAffineMap isOpen_univ).congr
        fun y _ => ?_
      apply L.injective
      rw [Function.invFunOn_eq ⟨L.symm y, mem_univ _, L.apply_symm_apply y⟩]
      exact (L.apply_symm_apply y).symm
  have hfin0 : ∀ y, y ∈ linearHalfSpace D (u 0) ↔
      (L ∘ h) y ∈ {w : E3 | w 1 = 0 ∧ 0 ≤ w 0} := by
    intro y
    rw [hCt 0, hmemiff _ y, hC0]
    exact hH0 (h y)
  have hfin1 : ∀ y, y ∈ linearHalfSpace D (u 1) ↔
      (L ∘ h) y ∈ {w : E3 | w 1 = 0 ∧ w 0 ≤ 0} := by
    intro y
    rw [hCt 1, hmemiff _ y, hC1]
    exact hH1 (h y)
  have hfin2 : ∀ y, y ∈ linearHalfSpace D (u 2) ↔
      (L ∘ h) y ∈ {w : E3 | w 0 = 0 ∧ 0 ≤ w 1} := by
    intro y
    rw [hCt 2, hmemiff _ y, hC2]
    exact hH2 (h y)
  refine ⟨L ∘ h, hh.trans hL, ?_, ?_⟩
  · change L (h 0) = 0
    rw [show h 0 = 0 from hfix (LinearMap.ker ℓ).zero_mem, map_zero]
  · intro i y
    fin_cases i
    · exact hfin0 y
    · exact hfin1 y
    · exact hfin2 y

open Classical in
theorem exists_triod_chart_at_common_boundary
    (M : Fin 3 → Geometry.SimplicialComplex ℝ E3)
    (hfin : ∀ i, (M i).faces.Finite)
    (hM : ∀ i, IsCombinatorialManifoldWithBoundary 2 (M i))
    (hboundary : ∀ i j, (boundaryComplex 2 (M i)).space =
      (boundaryComplex 2 (M j)).space)
    (hne : (boundaryComplex 2 (M 0)).space.Nonempty)
    (hdisjoint : ∀ i j, i ≠ j →
      Disjoint ((M i).space \ (boundaryComplex 2 (M i)).space)
        ((M j).space \ (boundaryComplex 2 (M j)).space)) :
    ∃ (p : E3) (e : OpenPartialHomeomorph E3 E3),
      p ∈ (boundaryComplex 2 (M 0)).space ∧ p ∈ e.source ∧ e p = 0 ∧
        IsPLHomeomorphOn e e.source e.target ∧
        ∀ i, ∀ z ∈ e.source, z ∈ (M i).space ↔
          e z ∈ (![{w : E3 | w 1 = 0 ∧ 0 ≤ w 0},
            {w : E3 | w 1 = 0 ∧ w 0 ≤ 0},
            {w : E3 | w 0 = 0 ∧ 0 ≤ w 1}] : Fin 3 → Set E3) i := by
  let V : Set E3 := ⋃ i, ⋃ s ∈ (M i).faces, (s : Set E3)
  have hV : V.Finite := Set.finite_iUnion fun i => (hfin i).biUnion fun s _ => s.finite_toSet
  let _ : Finite (M 0).faces := (hfin 0).to_subtype
  obtain ⟨p, hpB, hpV⟩ := (hM 0).exists_mem_boundaryComplex_space_notMem hne hV
  have hpv : ∀ i v, {v} ∈ (M i).faces → v ≠ p := by
    intro i v hv hvp
    apply hpV
    refine mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr ⟨{v}, hv, ?_⟩⟩
    rw [hvp]
    simp
  have hpBi : ∀ i, p ∈ (boundaryComplex 2 (M i)).space := fun i => (hboundary 0 i) ▸ hpB
  have hgerm : ∀ i, ∃ d u : E3, d ≠ 0 ∧ u ∉ Submodule.span ℝ {d} ∧ ∀ᶠ y in 𝓝 p,
      (y ∈ (M i).space ↔ y - p ∈ linearHalfSpace (Submodule.span ℝ {d}) u) ∧
        (y ∈ (boundaryComplex 2 (M i)).space ↔ y - p ∈ Submodule.span ℝ {d}) := by
    intro i
    let _ : Finite (M i).faces := (hfin i).to_subtype
    exact (hM i).exists_halfSpace_germ_of_mem_boundaryComplex (hpBi i) (hpv i)
  choose d u hd hu hev using hgerm
  have hspan : ∀ i, Submodule.span ℝ {d i} = Submodule.span ℝ {d 0} := by
    intro i
    apply eq_of_eventually_sub_mem_iff (p := p)
    filter_upwards [hev i, hev 0] with y hyi hy0
    rw [← hyi.2, ← hy0.2, hboundary i 0]
  have hu0 : ∀ i, u i ∉ Submodule.span ℝ {d 0} := fun i => by
    rw [← hspan i]
    exact hu i
  have hev' : ∀ i, ∀ᶠ y in 𝓝 p,
      (y ∈ (M i).space ↔ y - p ∈ linearHalfSpace (Submodule.span ℝ {d 0}) (u i)) ∧
        (y ∈ (boundaryComplex 2 (M i)).space ↔ y - p ∈ Submodule.span ℝ {d 0}) := fun i => by
    rw [← hspan i]
    exact hev i
  have hcone : ∀ i j, i ≠ j → linearHalfSpace (Submodule.span ℝ {d 0}) (u i) ∩
      linearHalfSpace (Submodule.span ℝ {d 0}) (u j) ⊆ Submodule.span ℝ {d 0} := by
    intro i j hij
    apply linearHalfSpace_inter_subset_of_eventually (p := p)
    filter_upwards [hev' i, hev' j] with y hyi hyj hi hj
    by_contra hyD
    exact disjoint_left.mp (hdisjoint i j hij) ⟨hyi.1.mpr hi, fun hB => hyD (hyi.2.mp hB)⟩
      ⟨hyj.1.mpr hj, fun hB => hyD (hyj.2.mp hB)⟩
  obtain ⟨Φ, hΦ, hΦ0, hΦmem⟩ := exists_isPLHomeomorphOn_triod_straightening (hd 0) u hu0 hcone
  have hΨ : IsPLHomeomorphOn (fun y => Φ (y - p)) univ univ := by
    have hcomp := (isPLHomeomorphOn_add_const (-p)).trans hΦ
    refine hcomp.congr fun y _ => ?_
    change Φ (y - p) = Φ (y + -p)
    rw [sub_eq_add_neg]
  have hN : {y | ∀ i,
      (y ∈ (M i).space ↔ y - p ∈ linearHalfSpace (Submodule.span ℝ {d 0}) (u i))} ∈ 𝓝 p :=
    Filter.eventually_all.mpr fun i => (hev' i).mono fun y hy => hy.1
  obtain ⟨O, hOsub, hO, hpO⟩ := mem_nhds_iff.mp hN
  have hO' : IsOpen ((fun y => Φ (y - p)) '' O) :=
    hΨ.isOpen_image_of_isOpen isOpen_univ hO (subset_univ O)
  have hΨO := hΨ.restrict_isOpen hO (subset_univ O) hO'
  refine ⟨p, hΨO.toOpenPartialHomeomorph hO hO', hpB, hpO, ?_, hΨO, ?_⟩
  · change Φ (p - p) = 0
    rw [sub_self, hΦ0]
  · intro i z hz
    have hzO : ∀ i, (z ∈ (M i).space ↔
        z - p ∈ linearHalfSpace (Submodule.span ℝ {d 0}) (u i)) := hOsub hz
    exact (hzO i).trans (hΦmem i (z - p))

end DifferentialGeometry.Topology.PiecewiseLinear
