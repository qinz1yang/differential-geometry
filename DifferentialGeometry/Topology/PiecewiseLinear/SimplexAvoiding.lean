/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexComplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem nonempty_of_mem_openSimplex {s : Finset E} {p : E} (hp : p ∈ openSimplex s) :
    s.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  obtain ⟨w, -, hw1, -⟩ := hp
  rw [h, Finset.sum_empty] at hw1
  exact zero_ne_one hw1

section Avoiding

variable (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) (A : Finset (Finset E))

def simplexAvoiding : Geometry.SimplicialComplex ℝ E where
  faces := {s | s.Nonempty ∧ s ⊆ T ∧ ∀ σ ∈ A, ¬ σ ⊆ s}
  isRelLowerSet_faces := by
    rintro s ⟨hne, hsT, hA⟩
    exact ⟨hne, fun t hts ht => ⟨ht, hts.trans hsT, fun σ hσ hσt => hA σ hσ (hσt.trans hts)⟩⟩
  indep hs := affineIndependent_of_subset hT hs.2.1
  inter_subset_convexHull hs ht := convexHull_inter_subset_of_affineIndependent hT hs.2.1 ht.2.1

theorem mem_simplexAvoiding_faces_iff {s : Finset E} :
    s ∈ (simplexAvoiding T hT A).faces ↔ s.Nonempty ∧ s ⊆ T ∧ ∀ σ ∈ A, ¬ σ ⊆ s := Iff.rfl

theorem simplexAvoiding_faces_subset :
    (simplexAvoiding T hT A).faces ⊆ (simplexComplex T hT).faces := fun _ hs => ⟨hs.1, hs.2.1⟩

theorem simplexAvoiding_faces_finite : (simplexAvoiding T hT A).faces.Finite :=
  (simplexComplex_faces_finite T hT).subset (simplexAvoiding_faces_subset T hT A)

theorem simplexAvoiding_faces_mono {B : Finset (Finset E)} (hAB : A ⊆ B) :
    (simplexAvoiding T hT B).faces ⊆ (simplexAvoiding T hT A).faces :=
  fun _ hs => ⟨hs.1, hs.2.1, fun σ hσ => hs.2.2 σ (hAB hσ)⟩

theorem simplexAvoiding_space_subset :
    (simplexAvoiding T hT A).space ⊆ convexHull ℝ (T : Set E) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (simplexAvoiding T hT A).mem_space_iff.mp hx
  exact convexHull_mono (Finset.coe_subset.mpr hs.2.1) hxs

theorem simplexAvoiding_singleton_self : simplexAvoiding T hT {T} = simplexBoundary T hT := by
  ext s
  rw [mem_simplexAvoiding_faces_iff, mem_simplexBoundary_faces_iff]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨hne, hsT, hTs⟩
    refine ⟨hsT, hne, fun h => hTs ?_⟩
    subst h
    exact Finset.Subset.refl _
  · rintro ⟨hsT, hne, hsT'⟩
    exact ⟨hne, hsT, fun h => hsT' (Finset.Subset.antisymm hsT h)⟩

end Avoiding

section Weights

variable {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))

include hT

theorem weights_pos_of_mem_openSimplex_of_subset {σ₀ : Finset E} (hσ₀T : σ₀ ⊆ T) {p : E}
    (hp : p ∈ openSimplex σ₀) {v : E} (hv : v ∈ σ₀) : 0 < weights T p v := by
  have hpσ : p ∈ convexHull ℝ (σ₀ : Set E) := openSimplex_subset_convexHull _ hp
  have hpos := (mem_openSimplex_self_iff (affineIndependent_of_subset hT hσ₀T) hpσ).mp hp v hv
  rwa [← weights_eq_of_subset_of_mem hT hσ₀T hpσ hv] at hpos

theorem exists_mem_convexHull_insert_erase_of_mem_openSimplex [DecidableEq E] {σ₀ : Finset E}
    (hσ₀T : σ₀ ⊆ T)
    {p : E} (hp : p ∈ openSimplex σ₀) {x : E} (hx : x ∈ convexHull ℝ (T : Set E)) :
    ∃ v ∈ σ₀, x ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  have hpσ : p ∈ convexHull ℝ (σ₀ : Set E) := openSimplex_subset_convexHull _ hp
  have hpT : p ∈ convexHull ℝ (T : Set E) := convexHull_mono (Finset.coe_subset.mpr hσ₀T) hpσ
  have hpos : ∀ v ∈ σ₀, 0 < weights T p v := fun v hv =>
    weights_pos_of_mem_openSimplex_of_subset hT hσ₀T hp hv
  have hzero : ∀ v ∈ T, v ∉ σ₀ → weights T p v = 0 := fun v hv hvσ =>
    weights_eq_zero_of_subset_of_notMem hT hσ₀T hpσ hv hvσ
  have hne : σ₀.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hpσ
    exact hpσ
  obtain ⟨v₀, hv₀, hmin⟩ :=
    Finset.exists_min_image σ₀ (fun v => weights T x v / weights T p v) hne
  set s : ℝ := weights T x v₀ / weights T p v₀ with hs
  have hv₀T : v₀ ∈ T := hσ₀T hv₀
  have hs0 : 0 ≤ s := div_nonneg (weights_nonneg hx hv₀T) (hpos v₀ hv₀).le
  have hcoef : ∀ v ∈ T, 0 ≤ weights T x v - s * weights T p v := fun v hv => by
    by_cases hvσ : v ∈ σ₀
    · have h := hmin v hvσ
      rw [le_div_iff₀ (hpos v hvσ)] at h
      linarith
    · rw [hzero v hv hvσ, mul_zero, sub_zero]
      exact weights_nonneg hx hv
  have hcoef₀ : weights T x v₀ - s * weights T p v₀ = 0 := by
    rw [hs, div_mul_cancel₀ _ (hpos v₀ hv₀).ne', sub_self]
  have hpv₀ : p ∉ T.erase v₀ := by
    intro hpv
    have hpT' : p ∈ T := Finset.mem_of_mem_erase hpv
    have h0 : weights T p v₀ = 0 :=
      weights_eq_zero_of_subset_of_notMem hT (Finset.singleton_subset_iff.mpr hpT')
        (subset_convexHull ℝ _ (by simp)) hv₀T
        (fun h => (Finset.mem_erase.mp hpv).1 (Finset.mem_singleton.mp h).symm)
    exact (hpos v₀ hv₀).ne' h0
  have hsumT : ∑ v ∈ T, (weights T x v - s * weights T p v) = 1 - s := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weights hx, sum_weights hpT, mul_one]
  have hsum_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) = 1 - s := by
    rw [← hsumT, ← Finset.add_sum_erase T _ hv₀T, hcoef₀, zero_add]
  have hsmulT : ∑ v ∈ T, (weights T x v - s * weights T p v) • v = x - s • p := by
    simp_rw [sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, sum_weights_smul hx, sum_weights_smul hpT]
  have hsmul_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) • v = x - s • p := by
    rw [← hsmulT, ← Finset.add_sum_erase T _ hv₀T, hcoef₀, zero_smul, zero_add]
  set c : E → ℝ := fun u => if u = p then s else weights T x u - s * weights T p u with hc
  have hcp : c p = s := by simp only [hc, ite_true]
  have hcu : ∀ u ∈ T.erase v₀, c u = weights T x u - s * weights T p u := fun u hu => by
    simp only [hc, ite_eq_right (ne_of_mem_of_not_mem hu hpv₀)]
  refine ⟨v₀, hv₀, mem_convexHull_iff_exists_weights.mpr ⟨c, ?_, ?_, ?_⟩⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, hcp]
      exact hs0
    · rw [hcu u h]
      exact hcoef u (Finset.mem_of_mem_erase h)
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl hcu, hsum_erase]
    ring
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl fun u hu => by rw [hcu u hu],
      hsmul_erase]
    abel

theorem affineIndependent_insert_of_not_subset [DecidableEq E] {σ₀ : Finset E} (hσ₀T : σ₀ ⊆ T)
    {p : E}
    (hp : p ∈ openSimplex σ₀) {s : Finset E} (hsT : s ⊆ T) (hs : ¬ σ₀ ⊆ s) :
    AffineIndependent ℝ ((↑) : {x // x ∈ (insert p s : Finset E)} → E) := by
  obtain ⟨v, hvσ, hvs⟩ := Finset.not_subset.mp hs
  have hpT : p ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hσ₀T) (openSimplex_subset_convexHull _ hp)
  have hpos : 0 < weights T p v := weights_pos_of_mem_openSimplex_of_subset hT hσ₀T hp hvσ
  have hps : p ∉ s := by
    intro hps
    have h0 : weights T p v = 0 :=
      weights_eq_zero_of_subset_of_notMem hT hsT
        (subset_convexHull ℝ _ (Finset.mem_coe.mpr hps)) (hσ₀T hvσ) hvs
    exact hpos.ne' h0
  rw [affineIndependent_insert_iff hps (affineIndependent_of_subset hT hsT)]
  rintro ⟨c, hc1, hcp⟩
  have hw : ∀ u ∈ T, weights T p u = if u ∈ s then c u else 0 := by
    refine weights_eq hT hpT ?_ ?_
    · rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsT, hc1]
    · simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsT, hcp]
  have h := hw v (hσ₀T hvσ)
  rw [ite_eq_right hvs] at h
  exact hpos.ne' h

variable {A : Finset (Finset E)} {σ₀ : Finset E} (hσ₀ : σ₀ ∈ A) (hσ₀T : σ₀ ⊆ T) {p : E}
  (hp : p ∈ openSimplex σ₀)

include hσ₀ hσ₀T

theorem exists_weights_eq_zero_of_mem_simplexAvoiding_space {x : E}
    (hx : x ∈ (simplexAvoiding T hT A).space) : ∃ v ∈ σ₀, weights T x v = 0 := by
  obtain ⟨s, ⟨-, hsT, hA⟩, hxs⟩ := (simplexAvoiding T hT A).mem_space_iff.mp hx
  obtain ⟨v, hvσ, hvs⟩ := Finset.not_subset.mp (hA σ₀ hσ₀)
  exact ⟨v, hvσ, weights_eq_zero_of_subset_of_notMem hT hsT hxs (hσ₀T hvσ) hvs⟩

include hp

theorem notMem_simplexAvoiding_space : p ∉ (simplexAvoiding T hT A).space := by
  intro h
  obtain ⟨v, hv, hv0⟩ := exists_weights_eq_zero_of_mem_simplexAvoiding_space hT hσ₀ hσ₀T h
  exact (weights_pos_of_mem_openSimplex_of_subset hT hσ₀T hp hv).ne' hv0

theorem not_radial_lt_one_simplexAvoiding {x y : E} (hx : x ∈ (simplexAvoiding T hT A).space)
    (hy : y ∈ (simplexAvoiding T hT A).space) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hyx : y = p + t • (x - p)) : False := by
  obtain ⟨v, hv, hyv0⟩ := exists_weights_eq_zero_of_mem_simplexAvoiding_space hT hσ₀ hσ₀T hy
  have hxT : x ∈ convexHull ℝ (T : Set E) := simplexAvoiding_space_subset T hT A hx
  have hpT : p ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr hσ₀T) (openSimplex_subset_convexHull _ hp)
  have hpv : 0 < weights T p v := weights_pos_of_mem_openSimplex_of_subset hT hσ₀T hp hv
  have hxv : 0 ≤ weights T x v := weights_nonneg hxT (hσ₀T hv)
  have hcombo := weights_combo hT hpT hxT (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring) v
    (hσ₀T hv)
  rw [← add_smul_sub_eq_combo, ← hyx, hyv0] at hcombo
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) hpv, mul_nonneg ht0.le hxv]

theorem isRadiallyInjective_simplexAvoiding :
    IsRadiallyInjective p (simplexAvoiding T hT A).space := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_simplexAvoiding hT hσ₀ hσ₀T hp hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_simplexAvoiding hT hσ₀ hσ₀T hp hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

theorem isConeBase_simplexAvoiding : IsConeBase p (simplexAvoiding T hT A) where
  notMem_space := notMem_simplexAvoiding_space hT hσ₀ hσ₀T hp
  indep s hs := by
    classical
    have h : AffineIndependent ℝ ((↑) : ((insert p s : Finset E) : Set E) → E) :=
      affineIndependent_insert_of_not_subset hT hσ₀T hp hs.2.1 (hs.2.2 σ₀ hσ₀)
    rwa [Finset.coe_insert] at h
  radial := isRadiallyInjective_simplexAvoiding hT hσ₀ hσ₀T hp

end Weights

section Ball

variable {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))

theorem simplexAvoiding_singleton_space [DecidableEq E] (σ₀ : Finset E) :
    (simplexAvoiding T hT {σ₀}).space =
      ⋃ v ∈ σ₀, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff, mem_iUnion₂]
  constructor
  · rintro ⟨s, ⟨-, hsT, hA⟩, hxs⟩
    obtain ⟨v, hvσ, hvs⟩ := Finset.not_subset.mp (hA σ₀ (Finset.mem_singleton_self σ₀))
    refine ⟨v, hvσ, convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_) hxs⟩
    exact Finset.mem_erase.mpr ⟨fun h => hvs (h ▸ hu), hsT hu⟩
  · rintro ⟨v, hvσ, hxv⟩
    rcases (T.erase v).eq_empty_or_nonempty with h | hne
    · rw [h, Finset.coe_empty, convexHull_empty] at hxv
      exact hxv.elim
    · refine ⟨T.erase v, ⟨hne, Finset.erase_subset v T, ?_⟩, hxv⟩
      simp only [Finset.mem_singleton, forall_eq]
      intro h
      exact Finset.notMem_erase v T (h hvσ)

theorem IsConeBase.of_faces_subset {p : E} {L L' : Geometry.SimplicialComplex ℝ E}
    (h : IsConeBase p L) (hL' : L'.faces ⊆ L.faces) : IsConeBase p L' := by
  have hsp : L'.space ⊆ L.space := fun x hx => by
    obtain ⟨s, hs, hxs⟩ := L'.mem_space_iff.mp hx
    exact L.convexHull_subset_space (hL' hs) hxs
  exact ⟨fun hp => h.notMem_space (hsp hp), fun σ hσ => h.indep σ (hL' hσ),
    fun x hx y hy t ht hyx => h.radial x (hsp hx) y (hsp hy) t ht hyx⟩

theorem simplexAvoiding_singleton_eq_coneComplex [DecidableEq E] {σ₀ : Finset E} {a : E}
    (ha : a ∈ T) (haσ : a ∉ σ₀) (hne : σ₀.Nonempty)
    (hL : IsConeBase a
      (simplexAvoiding (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T))
        {σ₀})) :
    simplexAvoiding T hT {σ₀} = coneComplex hL := by
  ext s
  rw [mem_coneComplex_faces_iff]
  simp only [mem_simplexAvoiding_faces_iff, Finset.mem_singleton, forall_eq]
  constructor
  · rintro ⟨hsne, hsT, hσs⟩
    by_cases has : a ∈ s
    · rcases (s.erase a).eq_empty_or_nonempty with h | h
      · exact Or.inr (Or.inl (((Finset.erase_eq_empty_iff s a).mp h).resolve_left hsne.ne_empty))
      · refine Or.inr (Or.inr ⟨s.erase a, ⟨h, Finset.erase_subset_erase a hsT, fun hσ => ?_⟩,
          (Finset.insert_erase has).symm⟩)
        exact hσs (hσ.trans (Finset.erase_subset a s))
    · exact Or.inl ⟨hsne, fun u hu => Finset.mem_erase.mpr ⟨fun h => has (h ▸ hu), hsT hu⟩, hσs⟩
  · rintro (⟨hsne, hsT, hσs⟩ | rfl | ⟨σ, ⟨hσne, hσT, hσσ⟩, rfl⟩)
    · exact ⟨hsne, hsT.trans (Finset.erase_subset a T), hσs⟩
    · refine ⟨Finset.singleton_nonempty a, Finset.singleton_subset_iff.mpr ha, fun h => haσ ?_⟩
      obtain ⟨v, hv⟩ := hne
      have hva := Finset.mem_singleton.mp (h hv)
      exact hva ▸ hv
    · refine ⟨Finset.insert_nonempty a σ,
        Finset.insert_subset ha (hσT.trans (Finset.erase_subset a T)), fun h => hσσ ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp (h hv) with rfl | hvσ
      · exact absurd hv haσ
      · exact hvσ

theorem isPLBall_simplexAvoiding_singleton [FiniteDimensional ℝ E] {n : ℕ}
    (hcard : T.card = n + 2) {σ₀ : Finset E} (hσ₀T : σ₀ ⊆ T) (hne : σ₀.Nonempty)
    (hσ₀ : σ₀ ≠ T) : IsPLBall n (simplexAvoiding T hT {σ₀}).space := by
  classical
  induction n generalizing T σ₀ with
  | zero =>
    obtain ⟨a, haT, haσ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσ₀T, hσ₀⟩)
    have hσ₀T' : σ₀ ⊆ T.erase a := fun v hv =>
      Finset.mem_erase.mpr ⟨fun h => haσ (h ▸ hv), hσ₀T hv⟩
    have hcase : T.erase a = σ₀ := by
      refine (Finset.eq_of_subset_of_card_le hσ₀T' ?_).symm
      have h1 := Finset.card_erase_of_mem haT
      have h2 := Finset.card_pos.mpr hne
      omega
    rw [simplexAvoiding_singleton_space hT σ₀, ← hcase]
    exact isPLBall_far hT haT hcard
  | succ m ih =>
    obtain ⟨a, haT, haσ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hσ₀T, hσ₀⟩)
    have hσ₀T' : σ₀ ⊆ T.erase a := fun v hv =>
      Finset.mem_erase.mpr ⟨fun h => haσ (h ▸ hv), hσ₀T hv⟩
    by_cases hcase : T.erase a = σ₀
    · rw [simplexAvoiding_singleton_space hT σ₀, ← hcase]
      exact isPLBall_far hT haT hcard
    · have hT' : AffineIndependent ℝ ((↑) : T.erase a → E) :=
        affineIndependent_of_subset hT (Finset.erase_subset a T)
      have hind : AffineIndependent ℝ
          ((↑) : {x // x ∈ (insert a (T.erase a) : Finset E)} → E) := by
        rw [Finset.insert_erase haT]
        exact hT
      have hL : IsConeBase a (simplexAvoiding (T.erase a) hT' {σ₀}) :=
        (isConeBase_simplexComplex (T.erase a) hT' (Finset.notMem_erase a T) hind).of_faces_subset
          (simplexAvoiding_faces_subset _ _ _)
      have hcard' : (T.erase a).card = m + 2 := by
        have h1 := Finset.card_erase_of_mem haT
        omega
      have hfin := (simplexAvoiding_faces_finite (T.erase a) hT' {σ₀}).to_subtype
      rw [simplexAvoiding_singleton_eq_coneComplex hT haT haσ hne hL]
      exact hL.isPLBall_of_isPLBall (ih hT' hcard' hσ₀T' hne fun h => hcase h.symm)

end Ball

end DifferentialGeometry.Topology.PiecewiseLinear
