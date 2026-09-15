import DifferentialGeometry.Topology.PiecewiseLinear.Cone
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBall
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexHull_inter_subset_of_affineIndependent {T τ₁ τ₂ : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (h₁ : τ₁ ⊆ T) (h₂ : τ₂ ⊆ T) :
    convexHull ℝ (τ₁ : Set E) ∩ convexHull ℝ (τ₂ : Set E) ⊆
      convexHull ℝ ((τ₁ : Set E) ∩ (τ₂ : Set E)) := by
  classical
  rintro x ⟨hx₁, hx₂⟩
  have hxT : x ∈ convexHull ℝ (T : Set E) := convexHull_mono (Finset.coe_subset.mpr h₁) hx₁
  have hzero : ∀ v ∈ T, v ∉ τ₁ ∩ τ₂ → weights T x v = 0 := by
    intro v hv hvν
    rw [Finset.mem_inter, not_and_or] at hvν
    rcases hvν with h | h
    · exact weights_eq_zero_of_subset_of_notMem hT h₁ hx₁ hv h
    · exact weights_eq_zero_of_subset_of_notMem hT h₂ hx₂ hv h
  rw [← Finset.coe_inter]
  refine mem_convexHull_iff_exists_weights.mpr ⟨weights T x,
    fun v hv => weights_nonneg hxT (h₁ (Finset.mem_of_mem_inter_left hv)), ?_, ?_⟩
  · exact (Finset.sum_subset (Finset.inter_subset_left.trans h₁) hzero).trans (sum_weights hxT)
  · refine (Finset.sum_subset (Finset.inter_subset_left.trans h₁) fun v hv hvν => ?_).trans
      (sum_weights_smul hxT)
    rw [hzero v hv hvν, zero_smul]

theorem affineIndependent_of_subset {T τ : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    (hτ : τ ⊆ T) : AffineIndependent ℝ ((↑) : τ → E) :=
  AffineIndependent.mono (t := (T : Set E)) hT (Finset.coe_subset.mpr hτ)

def simplexBoundaryFaces (T : Finset E) : Set (Finset E) := {τ | τ ⊆ T ∧ τ.Nonempty ∧ τ ≠ T}

def simplexBoundary (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := simplexBoundaryFaces T
  isRelLowerSet_faces := by
    rintro τ ⟨hτT, hne, hτ⟩
    exact ⟨hne, fun u huτ hu =>
      ⟨huτ.trans hτT, hu, fun h => hτ (Finset.Subset.antisymm hτT (h ▸ huτ))⟩⟩
  indep := by
    rintro τ ⟨hτT, -, -⟩
    exact affineIndependent_of_subset hT hτT
  inter_subset_convexHull := by
    rintro τ₁ τ₂ ⟨h₁, -, -⟩ ⟨h₂, -, -⟩
    exact convexHull_inter_subset_of_affineIndependent hT h₁ h₂

theorem mem_simplexBoundary_faces_iff {T : Finset E} {hT : AffineIndependent ℝ ((↑) : T → E)}
    {τ : Finset E} : τ ∈ (simplexBoundary T hT).faces ↔ τ ⊆ T ∧ τ.Nonempty ∧ τ ≠ T := Iff.rfl

theorem simplexBoundary_faces_finite (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)) :
    (simplexBoundary T hT).faces.Finite :=
  (Set.toFinite (T.powerset : Set (Finset E))).subset fun _ hτ =>
    Finset.mem_coe.mpr (Finset.mem_powerset.mpr hτ.1)

theorem openSimplex_eq_sdiff_simplexBoundary (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) :
    openSimplex T = convexHull ℝ (T : Set E) \ (simplexBoundary T hT).space := by
  ext x
  constructor
  · intro hx
    refine ⟨openSimplex_subset_convexHull T hx, ?_⟩
    intro hxB
    obtain ⟨s, hs, hxs⟩ := (simplexBoundary T hT).mem_space_iff.mp hxB
    exact hs.2.2 (Finset.Subset.antisymm hs.1
      (subset_of_mem_openSimplex_of_mem_convexHull hT subset_rfl hs.1 hx hxs))
  · rintro ⟨hx, hxB⟩
    obtain ⟨s, hsT, hsne, hxs⟩ := exists_openSimplex_of_mem_convexHull hx
    by_cases hs : s = T
    · rwa [hs] at hxs
    · exact (hxB ((simplexBoundary T hT).convexHull_subset_space ⟨hsT, hsne, hs⟩
        (openSimplex_subset_convexHull s hxs))).elim

section Boundary

theorem interior_convexHull_eq_openSimplex [FiniteDimensional ℝ E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = Module.finrank ℝ E + 1) :
    interior (convexHull ℝ (T : Set E)) = openSimplex T := by
  classical
  have htop : affineSpan ℝ (Set.range ((↑) : T → E)) = ⊤ :=
    hT.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simpa using hcard)
  let b : AffineBasis T ℝ E := ⟨((↑) : T → E), hT, htop⟩
  have hrange : Set.range b = (T : Set E) := by
    change Set.range ((↑) : T → E) = (T : Set E)
    ext x
    simp
  have hcoord (x : E) (hx : x ∈ convexHull ℝ (T : Set E)) (v : T) :
      b.coord v x = weights T x v := by
    have hw : (∑ u : T, weights T x u) = 1 := by
      rw [Finset.sum_coe_sort]
      exact sum_weights hx
    have hsum : Finset.univ.affineCombination ℝ b (fun u : T => weights T x u) = x := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
      change (∑ u : T, weights T x u • (u : E)) = x
      rw [Finset.sum_coe_sort T (fun u => weights T x u • u)]
      exact sum_weights_smul hx
    exact (congrArg (b.coord v) hsum).symm.trans
      (b.coord_apply_combination_of_mem (Finset.mem_univ v) hw)
  ext x
  constructor
  · intro hx
    have hxconv := interior_subset hx
    apply (mem_openSimplex_self_iff hT hxconv).mpr
    rw [← hrange, b.interior_convexHull] at hx
    intro v hv
    rw [← hcoord x hxconv ⟨v, hv⟩]
    exact hx ⟨v, hv⟩
  · intro hx
    have hxconv := openSimplex_subset_convexHull T hx
    rw [← hrange, b.interior_convexHull]
    intro v
    rw [hcoord x hxconv v]
    exact (mem_openSimplex_self_iff hT hxconv).mp hx v v.2

theorem frontier_convexHull_eq_simplexBoundary [FiniteDimensional ℝ E] {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = Module.finrank ℝ E + 1) :
    frontier (convexHull ℝ (T : Set E)) = (simplexBoundary T hT).space := by
  rw [frontier, (T.finite_toSet.isCompact_convexHull ℝ).isClosed.closure_eq,
    interior_convexHull_eq_openSimplex hT hcard]
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨hx, hxnot⟩
    obtain ⟨s, hsT, hsne, hxs⟩ := exists_openSimplex_of_mem_convexHull hx
    exact (simplexBoundary T hT).convexHull_subset_space
      ⟨hsT, hsne, fun hs => hxnot (hs ▸ hxs)⟩ (openSimplex_subset_convexHull s hxs)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (simplexBoundary T hT).mem_space_iff.mp hx
    refine ⟨convexHull_mono (Finset.coe_subset.mpr hs.1) hxs, fun hxopen => ?_⟩
    exact hs.2.2 (Finset.Subset.antisymm hs.1
      (subset_of_mem_openSimplex_of_mem_convexHull hT (Finset.Subset.refl T) hs.1 hxopen hxs))

variable [DecidableEq E]

theorem simplexBoundary_space (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E))
    (hcard : 2 ≤ T.card) :
    (simplexBoundary T hT).space = ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  ext x
  rw [Geometry.SimplicialComplex.mem_space_iff, mem_iUnion₂]
  constructor
  · rintro ⟨τ, ⟨hτT, -, hτ⟩, hx⟩
    obtain ⟨v, hvT, hvτ⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hτT, hτ⟩)
    refine ⟨v, hvT, convexHull_mono (Finset.coe_subset.mpr fun u hu => ?_) hx⟩
    exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem hu hvτ, hτT hu⟩
  · rintro ⟨v, hv, hx⟩
    refine ⟨T.erase v, ⟨Finset.erase_subset v T, ?_, ?_⟩, hx⟩
    · rw [← Finset.card_pos, Finset.card_erase_of_mem hv]
      omega
    · intro h
      have := Finset.notMem_erase v T
      rw [h] at this
      exact this hv

theorem notMem_boundary_of_mem_openSimplex {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {p : E} (hp : p ∈ openSimplex T) :
    p ∉ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
  intro h
  obtain ⟨v, hv, hpv⟩ := mem_iUnion₂.mp h
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp v hv
  have hzero := weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hpv hv
    (Finset.notMem_erase v T)
  rw [hzero] at hpos
  exact lt_irrefl _ hpos

theorem not_radial_lt_one_boundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) {x y : E}
    (hx : x ∈ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E))
    (hy : y ∈ ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E)) {t : ℝ} (ht0 : 0 < t)
    (ht1 : t < 1) (hyx : y = p + t • (x - p)) : False := by
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp hx
  have hxT : x ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u T)) hxu
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hyv0 : weights T y v = 0 :=
    weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hyv hv
      (Finset.notMem_erase v T)
  have hpv : 0 < weights T p v := (mem_openSimplex_self_iff hT hpT).mp hp v hv
  have hxv : 0 ≤ weights T x v := weights_nonneg hxT hv
  have hcombo := weights_combo hT hpT hxT (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring) v hv
  rw [← add_smul_sub_eq_combo, ← hyx, hyv0] at hcombo
  nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - t) hpv, mul_nonneg ht0.le hxv]

theorem isRadiallyInjective_boundary {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) :
    IsRadiallyInjective p (⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E)) := by
  intro x hx y hy t ht hyx
  rcases lt_trichotomy t 1 with h | h | h
  · exact (not_radial_lt_one_boundary hT hp hx hy ht h hyx).elim
  · rw [hyx, h, one_smul, add_sub_cancel]
  · have hxy : x = p + t⁻¹ • (y - p) := by
      rw [hyx, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, add_sub_cancel]
    exact (not_radial_lt_one_boundary hT hp hy hx (inv_pos.mpr ht)
      (inv_lt_one_of_one_lt₀ h) hxy).elim

theorem notMem_erase_of_mem_openSimplex {T : Finset E} (hT : AffineIndependent ℝ ((↑) : T → E))
    {p : E} (hp : p ∈ openSimplex T) {v : E} (hv : v ∈ T) : p ∉ T.erase v := by
  intro hpv
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos := (mem_openSimplex_self_iff hT hpT).mp hp
  have hpT' : p ∈ T := Finset.mem_of_mem_erase hpv
  have hne : v ≠ p := (Finset.ne_of_mem_erase hpv).symm
  have hone : weights T p p = 1 := by
    have h := weights_eq hT hpT (w := fun u => if u = p then 1 else 0) (by simp [hpT'])
      (by simp [ite_smul, hpT']) p hpT'
    simpa using h
  have hsum := sum_weights hpT
  rw [← Finset.add_sum_erase T _ hpT'] at hsum
  have hrest : 0 < ∑ u ∈ T.erase p, weights T p u :=
    Finset.sum_pos' (fun u hu => (hpos u (Finset.mem_of_mem_erase hu)).le)
      ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩, hpos v hv⟩
  linarith

theorem exists_mem_convexHull_insert_erase {T : Finset E}
    (hT : AffineIndependent ℝ ((↑) : T → E)) {p : E} (hp : p ∈ openSimplex T) {x : E}
    (hx : x ∈ convexHull ℝ (T : Set E)) :
    ∃ v ∈ T, x ∈ convexHull ℝ ((insert p (T.erase v) : Finset E) : Set E) := by
  have hpT : p ∈ convexHull ℝ (T : Set E) := openSimplex_subset_convexHull T hp
  have hpos : ∀ v ∈ T, 0 < weights T p v := (mem_openSimplex_self_iff hT hpT).mp hp
  have hne : T.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := sum_weights hpT
    rw [h, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨v₀, hv₀, hmin⟩ :=
    Finset.exists_min_image T (fun v => weights T x v / weights T p v) hne
  set s : ℝ := weights T x v₀ / weights T p v₀ with hs
  have hs0 : 0 ≤ s := div_nonneg (weights_nonneg hx hv₀) (hpos v₀ hv₀).le
  have ha : ∀ v ∈ T, 0 ≤ weights T x v - s * weights T p v := fun v hv => by
    have h := hmin v hv
    rw [le_div_iff₀ (hpos v hv)] at h
    linarith
  have ha₀ : weights T x v₀ - s * weights T p v₀ = 0 := by
    rw [hs, div_mul_cancel₀ _ (hpos v₀ hv₀).ne', sub_self]
  have hpv₀ : p ∉ T.erase v₀ := notMem_erase_of_mem_openSimplex hT hp hv₀
  have hsumT : ∑ v ∈ T, (weights T x v - s * weights T p v) = 1 - s := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_weights hx, sum_weights hpT, mul_one]
  have hsum_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) = 1 - s := by
    rw [← hsumT, ← Finset.add_sum_erase T _ hv₀, ha₀, zero_add]
  have hsmulT : ∑ v ∈ T, (weights T x v - s * weights T p v) • v = x - s • p := by
    simp_rw [sub_smul, mul_smul]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, sum_weights_smul hx, sum_weights_smul hpT]
  have hsmul_erase : ∑ v ∈ T.erase v₀, (weights T x v - s * weights T p v) • v = x - s • p := by
    rw [← hsmulT, ← Finset.add_sum_erase T _ hv₀, ha₀, zero_smul, zero_add]
  set c : E → ℝ := fun u => if u = p then s else weights T x u - s * weights T p u with hc
  have hcp : c p = s := by simp only [hc, if_true]
  have hcu : ∀ u ∈ T.erase v₀, c u = weights T x u - s * weights T p u := fun u hu => by
    simp only [hc, if_neg (ne_of_mem_of_not_mem hu hpv₀)]
  refine ⟨v₀, hv₀, mem_convexHull_iff_exists_weights.mpr ⟨c, ?_, ?_, ?_⟩⟩
  · intro u hu
    rcases Finset.mem_insert.mp hu with h | h
    · rw [h, hcp]
      exact hs0
    · rw [hcu u h]
      exact ha u (Finset.mem_of_mem_erase h)
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl hcu, hsum_erase]
    ring
  · rw [Finset.sum_insert hpv₀, hcp, Finset.sum_congr rfl fun u hu => by rw [hcu u hu],
      hsmul_erase]
    abel

theorem isPLSphere_biUnion_erase [FiniteDimensional ℝ E] {n : ℕ} (T : Finset E)
    (hT : AffineIndependent ℝ ((↑) : T → E)) (hcard : T.card = n + 2) :
    IsPLSphere n (⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E)) := by
  classical
  let e : Fin (n + 2) ≃ T := (Finset.equivFinOfCardEq hcard).symm
  let q : Fin (n + 2) → E := fun i => (e i : E)
  have hq : ∀ i, q i ∈ T := fun i => (e i).2
  have hqe : ∀ i, e.symm ⟨q i, hq i⟩ = i := fun i => by simp [q]
  have hqinj : Function.Injective q := fun i j h => e.injective (Subtype.ext h)
  let A : (Fin (n + 2) → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ q
  have hA : ∀ x, A x = ∑ i, x i • q i := fun x => by simp [A, Fintype.linearCombination_apply]
  let wx : (Fin (n + 2) → ℝ) → E → ℝ := fun x v => if h : v ∈ T then x (e.symm ⟨v, h⟩) else 0
  have hwx : ∀ x i, wx x (q i) = x i := fun x i => by simp only [wx, dif_pos (hq i), hqe]
  have hwx_sum : ∀ x, ∑ v ∈ T, wx x v = ∑ i, x i := fun x => by
    rw [sum_reindex_of_equiv e]
    exact Finset.sum_congr rfl fun i _ => hwx x i
  have hwx_smul : ∀ x, ∑ v ∈ T, wx x v • v = A x := fun x => by
    rw [sum_reindex_of_equiv e, hA]
    exact Finset.sum_congr rfl fun i _ => by rw [hwx x i]
  let g : E → Fin (n + 2) → ℝ := fun y i => weights T y (q i)
  have hg_mem : ∀ y ∈ convexHull ℝ (T : Set E), g y ∈ stdSimplex ℝ (Fin (n + 2)) := fun y hy =>
    ⟨fun i => weights_nonneg hy (hq i),
      (sum_reindex_of_equiv e (weights T y)).symm.trans (sum_weights hy)⟩
  have hAg : ∀ y ∈ convexHull ℝ (T : Set E), A (g y) = y := fun y hy => by
    rw [hA]
    exact (sum_reindex_of_equiv e fun v => weights T y v • v).symm.trans (sum_weights_smul hy)
  have hinj : InjOn A (stdSimplex ℝ (Fin (n + 2))) := fun x hx x' hx' hxx' => by
    have h := eq_on_of_sum_smul_eq hT ((hwx_sum x).trans hx.2) ((hwx_sum x').trans hx'.2)
      (by rw [hwx_smul x, hwx_smul x', hxx'])
    funext i
    rw [← hwx x i, ← hwx x' i]
    exact h (q i) (hq i)
  set Q := ⋃ v ∈ T, convexHull ℝ ((T.erase v : Finset E) : Set E) with hQ
  have hmaps : MapsTo A (stdSimplexBoundary (n + 1)) Q := by
    rintro x ⟨hx, i, hxi⟩
    refine mem_iUnion₂.mpr ⟨q i, hq i, ?_⟩
    rw [hA, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hxi, zero_smul, zero_add]
    have hsum : ∑ j ∈ Finset.univ.erase i, x j = 1 := by
      rw [← hx.2, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hxi, zero_add]
    refine (convex_convexHull ℝ _).sum_mem (fun j _ => hx.1 j) hsum fun j hj =>
      subset_convexHull ℝ _ ?_
    exact Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hj).1 (hqinj h), hq j⟩)
  have hsurj : SurjOn A (stdSimplexBoundary (n + 1)) Q := by
    intro y hy
    obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
    have hyT : y ∈ convexHull ℝ (T : Set E) :=
      convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v T)) hyv
    refine ⟨g y, ⟨hg_mem y hyT, e.symm ⟨v, hv⟩, ?_⟩, hAg y hyT⟩
    have hqv : q (e.symm ⟨v, hv⟩) = v := by simp [q]
    simp only [g, hqv]
    exact weights_eq_zero_of_subset_of_notMem hT (Finset.erase_subset v T) hyv hv
      (Finset.notMem_erase v T)
  have hbij : BijOn A (stdSimplexBoundary (n + 1)) Q := ⟨hmaps, hinj.mono fun x hx => hx.1, hsurj⟩
  refine ⟨A, hbij, ?_, ?_⟩
  · have hSU : stdSimplexBoundary (n + 1) = ⋃ i : Fin (n + 2), (stdSimplex ℝ (Fin (n + 2)) ∩
        (LinearMap.proj i : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ).toAffineMap ⁻¹'
          convexHull ℝ (({0} : Finset ℝ) : Set ℝ)) := by
      ext x
      simp only [stdSimplexBoundary, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage,
        Finset.coe_singleton, convexHull_singleton, mem_singleton_iff, LinearMap.coe_toAffineMap,
        LinearMap.proj_apply]
      exact ⟨fun ⟨hx, i, hi⟩ => ⟨i, hx, hi⟩, fun ⟨i, hx, hi⟩ => ⟨hx, i, hi⟩⟩
    have hsub : Subsingleton {x // x ∈ ({0} : Finset ℝ)} :=
      ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
        (Finset.mem_singleton.mp b.2).symm)⟩
    rw [hSU]
    refine isPiecewiseAffineOn_of_forall_isHPolytope _ (fun i => ?_)
      fun i => ⟨A.toAffineMap, fun _ _ => rfl⟩
    exact (isHPolytope_stdSimplex _).inter_preimage
      (isHPolytope_convexHull_of_affineIndependent _ (affineIndependent_of_subsingleton ℝ _)) _
  · let qv : E → Fin (n + 2) → ℝ := fun v =>
      if h : v ∈ T then Pi.single (e.symm ⟨v, h⟩) (1 : ℝ) else 0
    have hqv : ∀ i, qv (e i) = Pi.single i 1 := fun i => by
      simp only [qv, dif_pos (e i).2, Subtype.coe_eta, Equiv.symm_apply_apply]
    obtain ⟨B, hB⟩ := exists_affineMap_eqOn hT qv
    have hgB : EqOn g B (convexHull ℝ (T : Set E)) := by
      intro y hy
      have hw := sum_weights hy
      have h1 : ∑ v ∈ T, weights T y v • v = T.affineCombination ℝ id (weights T y) :=
        (Finset.affineCombination_eq_linear_combination T id (weights T y) hw).symm
      have h2 : ∑ v ∈ T, weights T y v • B v = T.affineCombination ℝ (B ∘ id) (weights T y) :=
        (Finset.affineCombination_eq_linear_combination T (B ∘ id) (weights T y) hw).symm
      have hBy : B y = ∑ v ∈ T, weights T y v • B v := by
        conv_lhs => rw [← sum_weights_smul hy]
        rw [h1, h2, Finset.map_affineCombination T id (weights T y) hw B]
      rw [hBy, Finset.sum_congr rfl fun v hv => by rw [hB v hv],
        sum_reindex_of_equiv e fun v => weights T y v • qv v]
      funext j
      simp only [g, q, Finset.sum_apply, Pi.smul_apply, hqv, Pi.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hQU : Q = ⋃ v : T, convexHull ℝ ((T.erase v : Finset E) : Set E) := by
      ext y
      rw [hQ, mem_iUnion₂, mem_iUnion]
      exact ⟨fun ⟨v, hv, h⟩ => ⟨⟨v, hv⟩, h⟩, fun ⟨v, h⟩ => ⟨v, v.2, h⟩⟩
    have hpl : IsPiecewiseAffineOn B (⋃ v : T, convexHull ℝ ((T.erase v : Finset E) : Set E)) :=
      isPiecewiseAffineOn_of_forall_isHPolytope _
        (fun v => isHPolytope_convexHull_of_affineIndependent _
          (affineIndependent_of_subset hT (Finset.erase_subset _ T)))
        fun v => ⟨B, fun _ _ => rfl⟩
    rw [← hQU] at hpl
    refine hpl.congr fun y hy => ?_
    obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
    have hyT : y ∈ convexHull ℝ (T : Set E) :=
      convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset v T)) hyv
    rw [← hgB hyT]
    exact hinj (hbij.surjOn.mapsTo_invFunOn hy).1 (hg_mem y hyT)
      ((hbij.invOn_invFunOn.2 hy).trans (hAg y hyT).symm)


end Boundary

theorem exists_affineIndependent_openSimplex_subset [FiniteDimensional ℝ E] {n : ℕ}
    (hn : Module.finrank ℝ E = n + 1) (p : E) {U : Set E} (hU : U ∈ 𝓝 p) :
    ∃ T : Finset E, AffineIndependent ℝ ((↑) : T → E) ∧ T.card = n + 2 ∧
      p ∈ openSimplex T ∧ convexHull ℝ (T : Set E) ⊆ U ∧ convexHull ℝ (T : Set E) ∈ 𝓝 p := by
  classical
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional (ι := Fin (n + 2)) (k := ℝ) (V := E)
    (P := E) (by rw [Fintype.card_fin, hn])
  have hn2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  set c : E := ((n : ℝ) + 2)⁻¹ • ∑ i, b i with hc
  have hsum_c : ∑ i, (b i - c) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_ofNat, hc, smul_smul,
      mul_inv_cancel₀ hn2, one_smul, sub_self]
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  set R : ℝ := ∑ i, ‖b i - c‖ with hR
  have hRi : ∀ i, ‖b i - c‖ ≤ R := fun i =>
    Finset.single_le_sum (fun j _ => norm_nonneg (b j - c)) (Finset.mem_univ i)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => norm_nonneg _
  set ε : ℝ := δ / (2 * (R + 1)) with hε
  have hε0 : 0 < ε := div_pos hδ (by positivity)
  have hεR : ε * R < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  let q : Fin (n + 2) → E := fun i => p + ε • (b i - c)
  have hqinj : Function.Injective q := by
    intro i j hij
    have h1 : ε • (b i - c) = ε • (b j - c) := add_left_cancel hij
    have h2 := smul_right_injective E hε0.ne' h1
    exact b.ind.injective (sub_left_injective h2)
  have hqind : AffineIndependent ℝ q := by
    rw [affineIndependent_iff]
    intro s w hw hs
    refine affineIndependent_iff.mp b.ind s w hw ?_
    have h : ∑ i ∈ s, w i • q i = (∑ i ∈ s, w i) • (p - ε • c) + ε • ∑ i ∈ s, w i • b i := by
      rw [Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [q, smul_add, smul_sub, smul_smul, mul_comm (w i) ε]
      abel
    rw [h, hw, zero_smul, zero_add] at hs
    rcases smul_eq_zero.mp hs with h0 | h0
    · exact absurd h0 hε0.ne'
    · exact h0
  have hpsum : ∑ i, ((n : ℝ) + 2)⁻¹ • q i = p := by
    simp only [q, smul_add, Finset.sum_add_distrib, ← Finset.smul_sum, hsum_c, smul_zero,
      add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_ofNat, smul_smul, inv_mul_cancel₀ hn2,
      one_smul]
  have hrange : Set.range q = ((Finset.univ.image q : Finset E) : Set E) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  refine ⟨Finset.univ.image q, ?_, ?_, ?_, ?_, ?_⟩
  · have h := hqind.range
    rw [hrange] at h
    exact h
  · rw [Finset.card_image_of_injective _ hqinj, Finset.card_univ, Fintype.card_fin]
  · refine ⟨fun _ => ((n : ℝ) + 2)⁻¹, fun _ _ => inv_pos.mpr (by positivity), ?_, ?_⟩
    · rw [Finset.sum_const, Finset.card_image_of_injective _ hqinj, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, mul_inv_cancel₀ hn2]
    · rw [Finset.sum_image fun i _ j _ h => hqinj h]
      exact hpsum
  · refine (convexHull_min ?_ (convex_ball p δ)).trans hball
    intro v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [q, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hε0.le]
    calc ε * ‖b i - c‖ ≤ ε * R := by gcongr; exact hRi i
      _ < δ := hεR
  · have htop : affineSpan ℝ (Set.range q) = ⊤ := by
      rw [hqind.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_fin, hn]
    let b' : AffineBasis (Fin (n + 2)) ℝ E := ⟨q, hqind, htop⟩
    have hb' : ⇑b' = q := rfl
    have hcent : Finset.univ.centroid ℝ q = p := by
      rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
        (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ Finset.univ_nonempty)]
      simp only [Finset.centroidWeights_apply, Finset.card_univ, Fintype.card_fin, Nat.cast_add,
        Nat.cast_ofNat]
      exact hpsum
    have hcoord : ∀ i, 0 < b'.coord i p := by
      intro i
      have h := b'.coord_apply_centroid (s := Finset.univ) (Finset.mem_univ i)
      rw [hb', hcent] at h
      rw [h, Finset.card_univ, Fintype.card_fin]
      positivity
    have hint : p ∈ interior (convexHull ℝ (Set.range q)) := by
      rw [← hb', b'.interior_convexHull]
      exact hcoord
    rw [hrange] at hint
    exact mem_interior_iff_mem_nhds.mp hint

end DifferentialGeometry.Topology.PiecewiseLinear
