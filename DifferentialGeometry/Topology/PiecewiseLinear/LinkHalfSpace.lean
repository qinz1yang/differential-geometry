/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LinkEuclidean
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.StarComplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Facet

variable [DecidableEq E] {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E}
  (ha : a ∈ T) {p : E} (hp : p ∈ openSimplex (T.erase a))
include hT hp

omit hT in
theorem mem_convexHull_of_mem_openSimplex_erase : p ∈ convexHull ℝ (T : Set E) :=
  convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset a T))
    (openSimplex_subset_convexHull _ hp)

theorem weights_pos_of_mem_openSimplex_erase {v : E} (hv : v ∈ T.erase a) : 0 < weights T p v := by
  have hpF : p ∈ convexHull ℝ ((T.erase a : Finset E) : Set E) := openSimplex_subset_convexHull _ hp
  have hpos := (mem_openSimplex_self_iff (affineIndependent_of_subset hT (Finset.erase_subset a T))
    hpF).mp hp v hv
  rwa [← weights_eq_of_subset_of_mem hT (Finset.erase_subset a T) hpF hv] at hpos

include ha in
theorem weights_apex_eq_zero : weights T p a = 0 :=
  weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset a T)
    (openSimplex_subset_convexHull _ hp) ha (Finset.notMem_erase a T)

theorem notMem_far_of_mem_openSimplex_erase :
    p ∉ ⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  intro h
  obtain ⟨v, hv, hpv⟩ := mem_iUnion₂.mp h
  have hpos := weights_pos_of_mem_openSimplex_erase hT hp hv
  have hzero := weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hpv
    (Finset.mem_of_mem_erase hv) (Finset.notMem_erase v T)
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

theorem not_radial_lt_one_far {x y : E}
    (hx : x ∈ ⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E))
    (hy : y ∈ ⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E)) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) (hyx : y = p + t • (x - p)) : False := by
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
  have hxT : x ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u T)) hxu
  have hpT : p ∈ convexHull ℝ (T : Set E) := mem_convexHull_of_mem_openSimplex_erase hp
  have hyv0 : weights T y v = 0 :=
    weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hyv
      (Finset.mem_of_mem_erase hv) (Finset.notMem_erase v T)
  have hpv : 0 < weights T p v := weights_pos_of_mem_openSimplex_erase hT hp hv
  have hxv : 0 ≤ weights T x v := weights_nonneg hxT (Finset.mem_of_mem_erase hv)
  have hcombo := weights_combo hT hpT hxT (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring) v
    (Finset.mem_of_mem_erase hv)
  rw [← add_smul_sub_eq_combo, ← hyx, hyv0] at hcombo
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) hpv, mul_nonneg ht0.le hxv]

theorem isRadiallyInjective_far :
    IsRadiallyInjective p (⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E)) := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_far hT hp hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_far hT hp hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

theorem notMem_erase_of_mem_openSimplex_erase {v : E} (hv : v ∈ T.erase a) : p ∉ T.erase v := by
  intro hpv
  have hpT : p ∈ convexHull ℝ (T : Set E) := mem_convexHull_of_mem_openSimplex_erase hp
  have hpos := weights_pos_of_mem_openSimplex_erase hT hp hv
  have hpT' : p ∈ T := Finset.mem_of_mem_erase hpv
  have hne : v ≠ p := (Finset.ne_of_mem_erase hpv).symm
  have hzero : weights T p v = 0 := by
    have h := weights_eq hT hpT (w := fun u => if u = p then 1 else 0) (by simp [hpT'])
      (by simp [ite_smul, hpT']) v (Finset.mem_of_mem_erase hv)
    simpa [hne] using h
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

theorem affineIndependent_insert_erase_far {v : E} (hv : v ∈ T.erase a) :
    AffineIndependent ℝ ((↑) : {x // x ∈ (insert p (T.erase v) : Finset E)} → E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := mem_convexHull_of_mem_openSimplex_erase hp
  have hpos : 0 < weights T p v := weights_pos_of_mem_openSimplex_erase hT hp hv
  have hpv : p ∉ T.erase v := notMem_erase_of_mem_openSimplex_erase hT hp hv
  have hvT : v ∈ T := Finset.mem_of_mem_erase hv
  refine affineIndependent_of_forall_eq_zero fun c hc₀ hc₁ => ?_
  rw [Finset.sum_insert hpv] at hc₀ hc₁
  let f : E → ℝ := fun u => if u = v then 0 else c u
  have hf : ∀ u ∈ T.erase v, f u = c u := fun u hu => by
    simp only [f, ite_eq_right (Finset.ne_of_mem_erase hu)]
  have hsum_f : ∑ u ∈ T, f u = ∑ u ∈ T.erase v, c u := by
    rw [← Finset.sum_erase T (by simp [f] : f v = 0)]
    exact Finset.sum_congr rfl hf
  have hsmul_f : ∑ u ∈ T, f u • u = ∑ u ∈ T.erase v, c u • u := by
    rw [← Finset.sum_erase (f := fun u => f u • u) (a := v) T (by simp [f])]
    exact Finset.sum_congr rfl fun u hu => by rw [hf u hu]
  let b : E → ℝ := fun u => c p * weights T p u + f u
  have hb₀ : ∑ u ∈ T, b u = 0 := by
    simp only [b]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_weights hpT, mul_one, hsum_f]
    exact hc₀
  have hb₁ : ∑ u ∈ T, b u • u = 0 := by
    simp only [b, add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, sum_weights_smul hpT, hsmul_f]
    exact hc₁
  have hzero := eq_zero_of_sum_eq_zero_of_affineIndependent hT hb₀ hb₁
  have hcp : c p = 0 := by
    have h := hzero v hvT
    simp only [b, f, ite_true, add_zero] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hpos.ne'
  intro u hu
  rcases Finset.mem_insert.mp hu with h | h
  · rw [h]
    exact hcp
  · have h' := hzero u (Finset.mem_of_mem_erase h)
    simp only [b, hcp, zero_mul, zero_add, hf u h] at h'
    exact h'

include ha in
theorem exists_mem_convexHull_insert_erase_far {x : E} (hx : x ∈ convexHull ℝ (T : Set E)) :
    ∃ v ∈ T.erase a, x ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := mem_convexHull_of_mem_openSimplex_erase hp
  have hpos : ∀ v ∈ T.erase a, 0 < weights T p v := fun v hv =>
    weights_pos_of_mem_openSimplex_erase hT hp hv
  have hpa : weights T p a = 0 := weights_apex_eq_zero hT ha hp
  have hne : (T.erase a).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hpF : p ∈ convexHull ℝ ((T.erase a : Finset E) : Set E) :=
      openSimplex_subset_convexHull _ hp
    rw [h, Finset.coe_empty, convexHull_empty] at hpF
    exact hpF
  obtain ⟨v₀, hv₀, hmin⟩ :=
    Finset.exists_min_image (T.erase a) (fun v => weights T x v / weights T p v) hne
  set s : ℝ := weights T x v₀ / weights T p v₀ with hs
  have hv₀T : v₀ ∈ T := Finset.mem_of_mem_erase hv₀
  have hs0 : 0 ≤ s := div_nonneg (weights_nonneg hx hv₀T) (hpos v₀ hv₀).le
  have hcoef : ∀ v ∈ T, 0 ≤ weights T x v - s * weights T p v := fun v hv => by
    by_cases hva : v = a
    · rw [hva, hpa, mul_zero, sub_zero]
      exact weights_nonneg hx ha
    · have h := hmin v (Finset.mem_erase.mpr ⟨hva, hv⟩)
      rw [le_div_iff₀ (hpos v (Finset.mem_erase.mpr ⟨hva, hv⟩))] at h
      linarith
  have hcoef₀ : weights T x v₀ - s * weights T p v₀ = 0 := by
    rw [hs, div_mul_cancel₀ _ (hpos v₀ hv₀).ne', sub_self]
  have hpv₀ : p ∉ T.erase v₀ := notMem_erase_of_mem_openSimplex_erase hT hp hv₀
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

end Facet

section FarComplex

variable [DecidableEq E] {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E}
  (ha : a ∈ T)
include hT ha

omit [DecidableEq E] in
theorem singleton_apex_mem_simplexBoundary_faces (hcard : 2 ≤ T.card) :
    ({a} : Finset E) ∈ (simplexBoundary T hT).faces := by
  refine ⟨Finset.singleton_subset_iff.mpr ha, Finset.singleton_nonempty a, fun h => ?_⟩
  have hc := congrArg Finset.card h
  rw [Finset.card_singleton] at hc
  omega

theorem closedStar_simplexBoundary_apex (hcard : 2 ≤ T.card) :
    closedStar (simplexBoundary T hT) a =
      ⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨⟨hsT, -, hsT'⟩, has⟩, hxs⟩ := mem_iUnion₂.mp hx
    have haS : a ∈ s := mem_of_mem_convexHull_of_affineIndependent hT hsT ha has
    obtain ⟨v, hvT, hvs⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsT, hsT'⟩)
    have hva : v ≠ a := fun h => hvs (h ▸ haS)
    refine mem_iUnion₂.mpr ⟨v, Finset.mem_erase.mpr ⟨hva, hvT⟩, ?_⟩
    refine convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_) hxs
    exact Finset.mem_erase.mpr ⟨fun h => hvs (h ▸ hu), hsT hu⟩
  · intro hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨T.erase v,
      ⟨erase_mem_simplexBoundary_faces hT hcard (Finset.mem_of_mem_erase hv), ?_⟩, hxv⟩
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hv).symm, ha⟩))

theorem geometricLink_simplexBoundary_apex :
    SimplicialComplex.geometricLink (simplexBoundary T hT) {a} =
      simplexBoundary (T.erase a) (affineIndependent_of_subset hT (Finset.erase_subset a T)) := by
  ext τ
  rw [SimplicialComplex.mem_geometricLink_singleton, mem_simplexBoundary_faces_iff,
    mem_simplexBoundary_faces_iff]
  constructor
  · rintro ⟨hne, haτ, hsub, -, hneT⟩
    refine ⟨fun u hu => Finset.mem_erase.mpr ⟨fun h => haτ (h ▸ hu),
      hsub (Finset.mem_insert_of_mem hu)⟩, hne, fun h => hneT ?_⟩
    rw [h, Finset.insert_erase ha]
  · rintro ⟨hsub, hne, hneF⟩
    have haτ : a ∉ τ := fun h => Finset.notMem_erase a T (hsub h)
    refine ⟨hne, haτ, Finset.insert_subset ha (hsub.trans (Finset.erase_subset a T)),
      Finset.insert_nonempty _ _, fun h => hneF ?_⟩
    rw [← h, Finset.erase_insert haτ]

theorem isPLBall_far [FiniteDimensional ℝ E] {n : ℕ} (hcard : T.card = n + 2) :
    IsPLBall n (⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E)) := by
  have hcard2 : 2 ≤ T.card := by omega
  have hcardF : (T.erase a).card = n + 1 := by
    have h1 := Finset.card_erase_of_mem ha
    omega
  cases n with
  | zero =>
    obtain ⟨v₀, hv₀⟩ := Finset.card_eq_one.mp hcardF
    have hv₀T : v₀ ∈ T := Finset.mem_of_mem_erase (hv₀ ▸ Finset.mem_singleton_self v₀)
    rw [hv₀, Finset.set_biUnion_singleton]
    refine isPLBall_convexHull_of_affineIndependent _
      (affineIndependent_of_subset hT (Finset.erase_subset v₀ T)) ?_
    have h1 := Finset.card_erase_of_mem hv₀T
    omega
  | succ m =>
    rw [← closedStar_simplexBoundary_apex hT ha hcard2]
    have hfin := (simplexBoundary_faces_finite T hT).to_subtype
    refine isPLBall_closedStar (simplexBoundary T hT)
      (singleton_apex_mem_simplexBoundary_faces hT ha hcard2) ?_
    rw [geometricLink_simplexBoundary_apex hT ha, simplexBoundary_space (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T)) (by omega)]
    exact isPLSphere_biUnion_erase (T.erase a)
      (affineIndependent_of_subset hT (Finset.erase_subset a T)) (by omega)

theorem isConeBase_far {p : E} (hp : p ∈ openSimplex (T.erase a)) (hcard : 2 ≤ T.card) :
    IsConeBase p (starComplex (simplexBoundary T hT) a) where
  notMem_space := by
    rw [starComplex_space _ _ (singleton_apex_mem_simplexBoundary_faces hT ha hcard),
      closedStar_simplexBoundary_apex hT ha hcard]
    exact notMem_far_of_mem_openSimplex_erase hT hp
  indep := by
    rintro σ ⟨hσ, hsub, -, hne⟩
    obtain ⟨v, hvT, hvσ⟩ :=
      Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    have hva : v ≠ a := fun h => hvσ (h ▸ Finset.mem_insert_self a σ)
    have hσv : σ ⊆ T.erase v := fun u hu =>
      Finset.mem_erase.mpr ⟨fun h => hvσ (h ▸ Finset.mem_insert_of_mem hu), hσ.1 hu⟩
    refine (affineIndependent_insert_erase_far hT hp (Finset.mem_erase.mpr ⟨hva, hvT⟩)).mono
      (t := ((insert p (T.erase v) : Finset E) : Set E)) ?_
    rw [Finset.coe_insert]
    exact Set.insert_subset_insert (Finset.coe_subset.mpr hσv)
  radial := by
    rw [starComplex_space _ _ (singleton_apex_mem_simplexBoundary_faces hT ha hcard),
      closedStar_simplexBoundary_apex hT ha hcard]
    exact isRadiallyInjective_far hT hp

theorem starComplex_simplexBoundary_apex_space (hcard : 2 ≤ T.card) :
    (starComplex (simplexBoundary T hT) a).space =
      ⋃ v ∈ T.erase a, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  rw [starComplex_space _ _ (singleton_apex_mem_simplexBoundary_faces hT ha hcard),
    closedStar_simplexBoundary_apex hT ha hcard]

omit ha in
theorem starComplex_simplexBoundary_apex_faces_finite :
    (starComplex (simplexBoundary T hT) a).faces.Finite :=
  (simplexBoundary_faces_finite T hT).subset (starComplex_faces_subset _ _)

end FarComplex

section HalfSimplex

theorem exists_openSimplex_nhds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (n : ℕ) (hn : Module.finrank ℝ F = n) (p : F) {U : Set F}
    (hU : U ∈ 𝓝 p) :
    ∃ T : Finset F, AffineIndependent ℝ ((↑) : T → F) ∧ T.card = n + 1 ∧ p ∈ openSimplex T ∧
      convexHull ℝ (T : Set F) ⊆ U ∧ convexHull ℝ (T : Set F) ∈ 𝓝 p := by
  classical
  cases n with
  | zero =>
    have hsub : Subsingleton F :=
      ⟨fun x y => ((finrank_zero_iff_forall_zero.mp hn) x).trans
        ((finrank_zero_iff_forall_zero.mp hn) y).symm⟩
    have hsub' : Subsingleton {x // x ∈ ({p} : Finset F)} :=
      ⟨fun x y => Subtype.ext (Subsingleton.elim _ _)⟩
    have huniv : convexHull ℝ (({p} : Finset F) : Set F) = univ :=
      eq_univ_of_forall fun x => by
        rw [Subsingleton.elim x p]
        exact subset_convexHull ℝ _ (by simp)
    refine ⟨{p}, affineIndependent_of_subsingleton ℝ _, Finset.card_singleton p,
      ⟨fun _ => 1, by simp, by simp, by simp⟩, ?_, ?_⟩
    · rw [huniv]
      intro x _
      rw [Subsingleton.elim x p]
      exact mem_of_mem_nhds hU
    · rw [huniv]
      exact Filter.univ_mem
  | succ m => exact exists_affineIndependent_openSimplex_subset hn p hU

theorem exists_halfSimplex [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {p : E} (hp : ℓ p = 0) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ (T : Finset E) (a : E), AffineIndependent ℝ ((↑) : T → E) ∧ T.card = n + 2 ∧ a ∈ T ∧
      p ∈ openSimplex (T.erase a) ∧ convexHull ℝ (T : Set E) ⊆ U ∧
      convexHull ℝ (T : Set E) ⊆ {x | 0 ≤ ℓ x} ∧
      convexHull ℝ (T : Set E) ∈ 𝓝[{x | 0 ≤ ℓ x}] p := by
  classical
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hℓ
  rw [LinearMap.zero_apply] at hx₀
  set e₀ : E := (ℓ x₀)⁻¹ • x₀ with he₀
  have hℓe₀ : ℓ e₀ = 1 := by rw [he₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hx₀]
  have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨c • e₀, by rw [map_smul, hℓe₀, smul_eq_mul, mul_one]⟩
  have hfinW : Module.finrank ℝ (LinearMap.ker ℓ) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, hn] at h
    omega
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨F', hF', hcardF', h0F', hF'ball, hF'nhds⟩ := exists_openSimplex_nhds n hfinW
    (0 : LinearMap.ker ℓ) (Metric.ball_mem_nhds (0 : LinearMap.ker ℓ) (half_pos hr))
  let A : LinearMap.ker ℓ →ᵃ[ℝ] E :=
    (LinearMap.ker ℓ).subtype.toAffineMap + AffineMap.const ℝ (LinearMap.ker ℓ) p
  have hA : ∀ w : LinearMap.ker ℓ, A w = p + w := fun w => by
    simp only [A, AffineMap.coe_add, Pi.add_apply, LinearMap.coe_toAffineMap,
      Submodule.coe_subtype, AffineMap.const_apply, add_comm]
  have hAinj : Function.Injective A := fun w w' h => by
    rw [hA, hA] at h
    exact Subtype.ext (add_left_cancel h)
  set F : Finset E := F'.image A with hFdef
  have hFind : AffineIndependent ℝ ((↑) : F → E) :=
    affineIndependent_image_of_injOn_convexHull A hF' hAinj.injOn
  have hcardF : F.card = n + 1 := by
    rw [hFdef, Finset.card_image_of_injective _ hAinj, hcardF']
  have hpF : p ∈ openSimplex F := by
    obtain ⟨w, hwpos, hwsum, hwzero⟩ := h0F'
    rw [hFdef, mem_openSimplex_image_iff hAinj.injOn]
    refine ⟨w, hwpos, hwsum, ?_⟩
    rw [← affineMap_apply_sum_smul_comp A (fun v => v) hwsum, hwzero, hA, Submodule.coe_zero,
      add_zero]
  set ε : ℝ := r / (2 * (‖e₀‖ + 1)) with hε
  have hεpos : 0 < ε := div_pos hr (by positivity)
  set a : E := p + ε • e₀ with ha
  have hℓa : ℓ a = ε := by
    rw [ha, map_add, hp, map_smul, hℓe₀, smul_eq_mul, mul_one, zero_add]
  have hℓF : ∀ x ∈ F, ℓ x = 0 := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hx
    rw [hA, map_add, hp, zero_add]
    exact LinearMap.mem_ker.mp w.2
  have haF : a ∉ F := fun h => by
    have := hℓF a h
    rw [hℓa] at this
    exact hεpos.ne' this
  set T : Finset E := insert a F with hTdef
  have hTind : AffineIndependent ℝ ((↑) : T → E) := by
    rw [hTdef, affineIndependent_insert_iff haF hFind]
    rintro ⟨c, -, hca⟩
    have h0 : ℓ a = 0 := by
      rw [← hca, map_sum]
      exact Finset.sum_eq_zero fun v hv => by rw [map_smul, hℓF v hv, smul_zero]
    rw [hℓa] at h0
    exact hεpos.ne' h0
  have hcardT : T.card = n + 2 := by
    rw [hTdef, Finset.card_insert_of_notMem haF, hcardF]
  have haT : a ∈ T := Finset.mem_insert_self a F
  have hTerase : T.erase a = F := by rw [hTdef, Finset.erase_insert haF]
  have haconv : a ∈ convexHull ℝ (T : Set E) := subset_convexHull ℝ _ (Finset.mem_coe.mpr haT)
  have hFconv : convexHull ℝ (F : Set E) ⊆ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert a F))
  refine ⟨T, a, hTind, hcardT, haT, by rw [hTerase]; exact hpF, ?_, ?_, ?_⟩
  · refine (convexHull_min ?_ (convex_ball p r)).trans hrU
    intro x hx
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hx) with h | h
    · rw [h, ha, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg hεpos.le]
      calc ε * ‖e₀‖ ≤ ε * (‖e₀‖ + 1) := by nlinarith [norm_nonneg e₀]
        _ = r / 2 := by
          rw [hε]
          field_simp
        _ < r := half_lt_self hr
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp h
      rw [hA, Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      have hwball := hF'ball (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
      rw [Metric.mem_ball, dist_zero_right] at hwball
      exact lt_trans hwball (half_lt_self hr)
  · refine convexHull_subset_nonneg ℓ fun u hu => ?_
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, hℓa]
      exact hεpos.le
    · rw [hℓF u h]
  · obtain ⟨r', hr', hr'F⟩ := Metric.mem_nhds_iff.mp hF'nhds
    let π : E → LinearMap.ker ℓ := fun x => ⟨x - ℓ x • e₀, by
      rw [LinearMap.mem_ker, map_sub, map_smul, hℓe₀, smul_eq_mul, mul_one, sub_self]⟩
    have hℓcont : Continuous ℓ := LinearMap.continuous_of_finiteDimensional ℓ
    have hπcont : Continuous π :=
      Continuous.subtype_mk (continuous_id.sub (hℓcont.smul continuous_const)) _
    have hπ0 : π 0 = 0 := Subtype.ext (by simp [π])
    have hπval : ∀ x, ((π x : LinearMap.ker ℓ) : E) = x - ℓ x • e₀ := fun x => rfl
    let V : Set E := {x | ‖π (x - p)‖ < r' / 2} ∩ {x | ℓ (x - p) < ε / 2}
    have hVopen : IsOpen V := by
      refine IsOpen.inter ?_ ?_
      · exact isOpen_lt (hπcont.comp (continuous_id.sub continuous_const)).norm continuous_const
      · exact isOpen_lt (hℓcont.comp (continuous_id.sub continuous_const)) continuous_const
    have hpV : p ∈ V := by
      refine ⟨?_, ?_⟩
      · change ‖π (p - p)‖ < r' / 2
        rw [sub_self, hπ0, norm_zero]
        exact half_pos hr'
      · change ℓ (p - p) < ε / 2
        rw [sub_self, map_zero]
        exact half_pos hεpos
    refine mem_nhdsWithin.mpr ⟨V, hVopen, hpV, ?_⟩
    rintro x ⟨⟨hx1, hx2⟩, hx0⟩
    change ‖π (x - p)‖ < r' / 2 at hx1
    change ℓ (x - p) < ε / 2 at hx2
    change 0 ≤ ℓ x at hx0
    have ht0 : 0 ≤ ℓ (x - p) := by
      rw [map_sub, hp, sub_zero]
      exact hx0
    set s : ℝ := ℓ (x - p) / ε with hs
    have hs0 : 0 ≤ s := div_nonneg ht0 hεpos.le
    have hs1 : s < 1 / 2 := by
      rw [hs, div_lt_iff₀ hεpos]
      linarith
    have h1s : 0 < 1 - s := by linarith
    have hts : ℓ (x - p) = s * ε := by rw [hs, div_mul_cancel₀ _ hεpos.ne']
    have hwz : (1 - s)⁻¹ • π (x - p) ∈ convexHull ℝ (F' : Set (LinearMap.ker ℓ)) := by
      refine hr'F ?_
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1s.le)]
      have hinv : (1 - s)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ h1s (by norm_num)]
        linarith
      calc (1 - s)⁻¹ * ‖π (x - p)‖ ≤ 2 * ‖π (x - p)‖ := by nlinarith [norm_nonneg (π (x - p))]
        _ < 2 * (r' / 2) := by nlinarith
        _ = r' := by ring
    have hz : A ((1 - s)⁻¹ • π (x - p)) ∈ convexHull ℝ (F : Set E) := by
      rw [hFdef, Finset.coe_image, ← AffineMap.image_convexHull]
      exact ⟨_, hwz, rfl⟩
    have hxcombo : x = (1 - s) • A ((1 - s)⁻¹ • π (x - p)) + s • a := by
      clear_value e₀
      rw [hA, ha, Submodule.coe_smul, hπval, map_sub, hp, sub_zero]
      have hℓx : ℓ x = s * ε := by
        rw [← hts, map_sub, hp, sub_zero]
      rw [hℓx, smul_add, smul_smul, mul_inv_cancel₀ h1s.ne', one_smul, smul_add, smul_smul,
        sub_smul, one_smul]
      abel
    rw [hxcombo]
    exact (convex_convexHull ℝ _) (hFconv hz) haconv h1s.le hs0 (by ring)

end HalfSimplex

section Cover

variable [DecidableEq E]

theorem exists_facet_convexHull_insert_subset_far (K : Geometry.SimplicialComplex ℝ E)
    {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E)) {a : E} (ha : a ∈ T) {p : E}
    (hp : p ∈ openSimplex (T.erase a)) (hTnhds : convexHull ℝ (T : Set E) ∈ 𝓝[K.space] p)
    (hunion : ∀ v ∈ T.erase a, convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) =
      ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆
        convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E)}, convexHull ℝ (s : Set E))
    {σ : Finset E} (hins : insert p σ ∈ K.faces) :
    ∃ v ∈ T.erase a, convexHull ℝ ((insert p σ : Finset E) : Set E) ⊆
      convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  set c := (insert p σ).centroid ℝ id with hc
  have hcopen : c ∈ openSimplex (insert p σ) :=
    centroid_mem_openSimplex (Finset.insert_nonempty p σ)
  have hcconv : c ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    openSimplex_subset_convexHull _ hcopen
  have hpconv : p ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_self p σ))
  have hsegK : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → p + t • (c - p) ∈ K.space := fun t ht0 ht1 => by
    refine K.convexHull_subset_space hins ?_
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpconv hcconv (by linarith) ht0 (by ring)
  have htend : Filter.Tendsto (fun t : ℝ => p + t • (c - p)) (𝓝[>] 0) (𝓝[K.space] p) := by
    have hcont : Continuous fun t : ℝ => p + t • (c - p) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h1 : Filter.Tendsto (fun t : ℝ => p + t • (c - p)) (𝓝[>] 0) (𝓝 p) := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht using hsegK t ht.1.le ht.2.le
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      p + t • (c - p) ∈ convexHull ℝ (T : Set E) ∧ t ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [htend.eventually_mem hTnhds, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t h1 h2
      using ⟨h1, h2⟩
  obtain ⟨t, hxt, ht0, ht1⟩ := hev.exists
  have hxconv : p + t • (c - p) ∈ convexHull ℝ ((insert p σ : Finset E) : Set E) := by
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpconv hcconv (by linarith) ht0.le (by ring)
  have hxopen : p + t • (c - p) ∈ openSimplex (insert p σ) := by
    rw [mem_openSimplex_self_iff (K.indep hins) hxconv]
    intro u hu
    rw [add_smul_sub_eq_combo, weights_combo (K.indep hins) hpconv hcconv (by linarith) ht0.le
      (by ring) u hu]
    have h1 := weights_nonneg hpconv hu
    have h2 := (mem_openSimplex_self_iff (K.indep hins) hcconv).mp hcopen u hu
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - t) h1, mul_pos ht0 h2]
  obtain ⟨v, hv, hxv⟩ := exists_mem_convexHull_insert_erase_far hT ha hp hxt
  refine ⟨v, hv, ?_⟩
  rw [hunion v hv] at hxv
  obtain ⟨s, ⟨hs, hsQ⟩, hxs⟩ := mem_iUnion₂.mp hxv
  have hsub : insert p σ ⊆ s :=
    face_subset_of_mem_openSimplex_of_mem_convexHull K hins hs hxopen hxs
  exact (convexHull_mono (Finset.coe_subset.mpr hsub)).trans hsQ

end Cover

theorem isPLBall_geometricLink_of_halfSpace [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {p : E} (hp : {p} ∈ K.faces) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hpℓ : ℓ p = 0)
    (hK : ∃ V ∈ 𝓝 p, K.space ∩ V = {x | 0 ≤ ℓ x} ∩ V) :
    IsPLBall n (SimplicialComplex.geometricLink K {p}).space := by
  classical
  obtain ⟨V, hV, hKV⟩ := hK
  obtain ⟨Vo, hVoV, hVo, hpVo⟩ := _root_.mem_nhds_iff.mp hV
  obtain ⟨O, hO, hpO, hOstar⟩ := mem_nhdsWithin.mp (closedStar_mem_nhdsWithin K p)
  obtain ⟨T, a, hT, hcard, ha, hpT, hTU, hTH, hTnhds⟩ :=
    exists_halfSimplex hn ℓ hℓ hpℓ (Filter.inter_mem (hO.mem_nhds hpO) (hVo.mem_nhds hpVo))
  have hcard2 : 2 ≤ T.card := by omega
  have hTstar : convexHull ℝ (T : Set E) ⊆ closedStar K p := by
    intro x hx
    have hxOV := hTU hx
    have hxK : x ∈ K.space := by
      have hmem : x ∈ {x | 0 ≤ ℓ x} ∩ V := ⟨hTH hx, hVoV hxOV.2⟩
      rw [← hKV] at hmem
      exact hmem.1
    exact hOstar ⟨hxOV.1, hxK⟩
  have hTK : convexHull ℝ (T : Set E) ⊆ K.space := hTstar.trans (closedStar_subset_space K p)
  have hTnhdsK : convexHull ℝ (T : Set E) ∈ 𝓝[K.space] p := by
    obtain ⟨W, hW, hpW, hWT⟩ := mem_nhdsWithin.mp hTnhds
    refine mem_nhdsWithin.mpr ⟨W ∩ Vo, hW.inter hVo, ⟨hpW, hpVo⟩, ?_⟩
    rintro x ⟨⟨hxW, hxVo⟩, hxK⟩
    have hmem : x ∈ K.space ∩ V := ⟨hxK, hVoV hxVo⟩
    rw [hKV] at hmem
    exact hWT ⟨hxW, hmem.1⟩
  have hpconvT : p ∈ convexHull ℝ (T : Set E) := mem_convexHull_of_mem_openSimplex_erase hpT
  have hconeT : ∀ v ∈ T.erase a, convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) ⊆
      convexHull ℝ (T : Set E) := by
    intro v hv
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro u hu
    rcases Finset.mem_insert.mp (Finset.mem_coe.mp hu) with h | h
    · rw [h]
      exact hpconvT
    · exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_of_mem_erase h))
  let Q : T.erase a → Set E := fun v =>
    convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E)
  have hQ : ∀ v, IsPolyhedron (Q v) := fun v =>
    isPolyhedron_convexHull_of_affineIndependent _ (affineIndependent_insert_erase_far hT hpT v.2)
  have hQK : ∀ v, Q v ⊆ K.space := fun v => (hconeT v v.2).trans hTK
  obtain ⟨K'', hK'', hfin'', hunion⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  have : Finite K''.faces := hfin''.to_subtype
  have hp'' : {p} ∈ K''.faces := hK''.singleton_mem hp
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hK'' hp
  refine IsPLBall.of_isPLHomeomorphOn ?_ hg
  have hfinFar := (starComplex_simplexBoundary_apex_faces_finite hT (a := a)).to_subtype
  have hray : IsRadiallyInjective p (starComplex (simplexBoundary T hT) a).space := by
    rw [starComplex_simplexBoundary_apex_space hT ha hcard2]
    exact isRadiallyInjective_far hT hpT
  have hadapt : ∀ σ ∈ (SimplicialComplex.geometricLink K'' {p}).faces,
      ∃ τ ∈ (starComplex (simplexBoundary T hT) a).faces, ∀ w ∈ σ,
        ∃ s : ℝ, 0 < s ∧ p + s • (w - p) ∈ convexHull ℝ (τ : Set E) := by
    intro σ hσ
    obtain ⟨-, hpσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K'' p σ).mp hσ
    obtain ⟨v, hv, hsub⟩ := exists_facet_convexHull_insert_subset_far K'' hT ha hpT
      (by rw [hK''.space_eq]; exact hTnhdsK) (fun v hv => hunion ⟨v, hv⟩) hins
    refine ⟨T.erase v, ⟨erase_mem_simplexBoundary_faces hT hcard2 (Finset.mem_of_mem_erase hv), ?_⟩,
      fun w hw => ?_⟩
    · rw [Finset.insert_eq_of_mem (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hv).symm, ha⟩)]
      exact erase_mem_simplexBoundary_faces hT hcard2 (Finset.mem_of_mem_erase hv)
    · have hwmem : w ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) :=
        hsub (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem hw)))
      exact exists_ray_mem_convexHull_of_mem_convexHull_insert hwmem (ne_of_mem_of_not_mem hw hpσ)
  have hsurj : ∀ x ∈ (starComplex (simplexBoundary T hT) a).space,
      ∃ s : ℝ, 0 < s ∧ p + s • (x - p) ∈ (SimplicialComplex.geometricLink K'' {p}).space := by
    intro x hx
    rw [starComplex_simplexBoundary_apex_space hT ha hcard2] at hx
    have hxp : x ≠ p := fun h => notMem_far_of_mem_openSimplex_erase hT hpT (h ▸ hx)
    have hxT : x ∈ convexHull ℝ (T : Set E) := by
      obtain ⟨v, -, hxv⟩ := mem_iUnion₂.mp hx
      exact convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v T)) hxv
    refine exists_ray_mem_geometricLink_space K'' hp'' (fun t ht0 ht1 => ?_) hxp
    rw [hK''.space_eq]
    refine hTK ?_
    rw [add_smul_sub_eq_combo]
    exact (convex_convexHull ℝ _) hpconvT hxT (by linarith) ht0.le (by ring)
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_of_radial p (starComplex (simplexBoundary T hT) a)
    (SimplicialComplex.geometricLink K'' {p}) hray (isConeBase_geometricLink K'') hadapt hsurj
  refine IsPLBall.of_isPLHomeomorphOn ?_ hf.symm
  rw [starComplex_simplexBoundary_apex_space hT ha hcard2]
  exact isPLBall_far hT ha hcard

end DifferentialGeometry.Topology.PiecewiseLinear
