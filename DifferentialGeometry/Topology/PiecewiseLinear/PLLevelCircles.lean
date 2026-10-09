/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CofaceSeparation
import DifferentialGeometry.Topology.PiecewiseLinear.CollarSectorPolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalCycles
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_ne_zero_linearMap_apply_eq_zero_of_finrank_eq_two {V : Type*} [AddCommGroup V]
    [Module ℝ V] [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 2) (L : V →ₗ[ℝ] ℝ) :
    ∃ w : V, w ≠ 0 ∧ L w = 0 := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : Module.finrank ℝ (LinearMap.range L) ≤ 1 :=
    (Submodule.finrank_le _).trans (Module.finrank_self ℝ).le
  have hk : LinearMap.ker L ≠ ⊥ := fun hb => by
    rw [hb, finrank_bot] at h
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨w, hw0, hw⟩

theorem exists_eq_smul_of_linearMap_apply_eq_zero_of_finrank_eq_two {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 2)
    {L : V →ₗ[ℝ] ℝ} (hL : L ≠ 0) {w z : V} (hw : w ≠ 0) (hLw : L w = 0) (hLz : L z = 0) :
    ∃ c : ℝ, z = c • w := by
  have h := LinearMap.finrank_range_add_finrank_ker L
  have hr : 1 ≤ Module.finrank ℝ (LinearMap.range L) := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    exact hL (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h0))
  have hle : ℝ ∙ w ≤ LinearMap.ker L := (Submodule.span_singleton_le_iff_mem _ _).mpr hLw
  have heq := Submodule.eq_of_le_of_finrank_le hle (by rw [finrank_span_singleton hw]; omega)
  have hz : z ∈ ℝ ∙ w := by
    rw [heq]
    exact hLz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨c, hc.symm⟩

theorem affineMap_apply_eq_add_linear {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A : V →ᵃ[ℝ] ℝ) (x y : V) : A x = A y + A.linear (x - y) := by
  have h := A.linearMap_vsub x y
  simp only [vsub_eq_sub] at h
  rw [h]
  ring

theorem exists_affineMap_linear_ne_zero_apply_eq_zero_of_finrank_eq_two {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (hV : Module.finrank ℝ V = 2)
    (a b : V) : ∃ ℓ : V →ᵃ[ℝ] ℝ, ℓ.linear ≠ 0 ∧ ℓ a = 0 ∧ ℓ b = 0 := by
  have hdual : Module.finrank ℝ (Module.Dual ℝ V) = 2 := by
    rw [Subspace.dual_finrank_eq, hV]
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_linearMap_apply_eq_zero_of_finrank_eq_two hdual
    (Module.Dual.eval ℝ V (b - a))
  rw [Module.Dual.eval_apply] at hf
  refine ⟨f.toAffineMap - AffineMap.const ℝ V (f a), ?_, ?_, ?_⟩
  · intro h
    apply hf0
    ext v
    have hv := congrArg (fun L : V →ₗ[ℝ] ℝ => L v) h
    simpa using hv
  · simp
  · have hab : f b - f a = 0 := by rw [← map_sub]; exact hf
    simpa using hab

theorem exists_linearMap_apply_eq_zero_pos_of_apply_ne_zero {V : Type*} [AddCommGroup V]
    [Module ℝ V] {L M : V →ₗ[ℝ] ℝ} {d n : V} (hLd : L d ≠ 0) (hMd : M d = 0) (hMn : M n ≠ 0) :
    ∃ v : V, L v = 0 ∧ 0 < M v := by
  set v' : V := L d • n - L n • d
  have hLv : L v' = 0 := by
    simp only [v', map_sub, map_smul, smul_eq_mul]
    ring
  have hMv : M v' = L d * M n := by
    simp only [v', map_sub, map_smul, smul_eq_mul, hMd, mul_zero, sub_zero]
  have hne : M v' ≠ 0 := by
    rw [hMv]
    exact mul_ne_zero hLd hMn
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact ⟨-v', by rw [map_neg, hLv, neg_zero], by rw [map_neg]; linarith⟩
  · exact ⟨v', hLv, hpos⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem exists_ball_subset_forall_mem_convexHull_of_mem_openSimplex
    (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces] {σ : Finset E} (hσ : σ ∈ T.faces)
    {p : E} (hpσ : p ∈ openSimplex σ) (hpT : p ∈ interior T.space) :
    ∃ r > 0, ball p r ⊆ T.space ∧
      ∀ q ∈ ball p r, ∃ τ ∈ T.faces, σ ⊆ τ ∧ q ∈ convexHull ℝ (τ : Set E) := by
  obtain ⟨r₁, hr₁, hr₁T⟩ := Metric.isOpen_iff.mp isOpen_interior p hpT
  let far : Set E := ⋃ τ ∈ {τ ∈ T.faces | p ∉ convexHull ℝ (τ : Set E)},
    convexHull ℝ (τ : Set E)
  have hfar : IsClosed far :=
    ((Set.toFinite T.faces).subset (sep_subset _ _)).isClosed_biUnion fun τ _ =>
      (τ.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  have hpfar : p ∉ far := by
    intro h
    obtain ⟨τ, hτ, hpτ⟩ := mem_iUnion₂.mp h
    exact hτ.2 hpτ
  obtain ⟨r₂, hr₂, hr₂far⟩ := Metric.isOpen_iff.mp hfar.isOpen_compl p hpfar
  have hsub : ball p (min r₁ r₂) ⊆ T.space := fun q hq =>
    interior_subset (hr₁T (ball_subset_ball (min_le_left _ _) hq))
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, hsub, fun q hq => ?_⟩
  obtain ⟨τ, hτ, hqτ⟩ := T.mem_space_iff.mp (hsub hq)
  have hpτ : p ∈ convexHull ℝ (τ : Set E) := by
    by_contra h
    exact hr₂far (ball_subset_ball (min_le_right _ _) hq) (mem_iUnion₂.mpr ⟨τ, ⟨hτ, h⟩, hqτ⟩)
  exact ⟨τ, hτ, face_subset_of_mem_openSimplex_of_mem_convexHull T hσ hτ hpσ hpτ, hqτ⟩

theorem card_le_three_of_mem_faces_of_finrank_eq_two (hE : Module.finrank ℝ E = 2)
    (T : Geometry.SimplicialComplex ℝ E) {τ : Finset E} (hτ : τ ∈ T.faces) : τ.card ≤ 3 := by
  have h := (T.indep hτ).card_le_finrank_succ
  simp only [Fintype.card_coe] at h
  refine h.trans ?_
  have h' := Submodule.finrank_le (vectorSpan ℝ (Set.range ((↑) : τ → E)))
  omega

theorem exists_arc_of_mem_level_of_ball_subset_convexHull (hE : Module.finrank ℝ E = 2)
    {φ : E → ℝ} {Λ H : Set E} {A : E →ᵃ[ℝ] ℝ} (hA : EqOn φ A H) (hA0 : A.linear ≠ 0)
    {p : E} {s r : ℝ} (hr : 0 < r) (hpA : A p = s) (hball : ball p r ⊆ H)
    (hΛ : ∀ q ∈ ball p r, φ q = s → q ∈ Λ) (hΛs : ∀ q ∈ Λ, φ q = s) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc (-1) 1) (γ '' Icc (-1) 1) ∧ γ 0 = p ∧
      γ '' Icc (-1) 1 ⊆ Λ ∧ γ '' Icc (-1) 1 ∈ 𝓝[Λ] p := by
  obtain ⟨w, hw0, hLw⟩ := exists_ne_zero_linearMap_apply_eq_zero_of_finrank_eq_two hE A.linear
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  set δ : ℝ := r / (2 * ‖w‖) with hδdef
  have hδ : 0 < δ := by positivity
  have hδw : δ * ‖w‖ = r / 2 := by
    rw [hδdef]
    field_simp
  let γ : ℝ →ᵃ[ℝ] E := AffineMap.lineMap p (p + δ • w)
  have hγ : ∀ t : ℝ, γ t = p + t • (δ • w) := by
    intro t
    simp only [γ, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left]
    abel
  have hδw0 : δ • w ≠ 0 := smul_ne_zero hδ.ne' hw0
  have hinj : InjOn γ (Icc (-1) 1) := by
    intro t _ t' _ htt'
    rw [hγ, hγ, add_right_inj] at htt'
    exact smul_left_injective ℝ hδw0 htt'
  have hγball : ∀ t ∈ Icc (-1 : ℝ) 1, γ t ∈ ball p r := by
    intro t ht
    rw [mem_ball, dist_eq_norm, hγ, add_sub_cancel_left, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hδ, hδw]
    have habs : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    nlinarith [abs_nonneg t]
  refine ⟨γ, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    (isPiecewiseAffineOn_of_affine_of_isHPolytope γ isHPolytope_Icc) hinj.bijOn_image,
    by rw [hγ, zero_smul, add_zero], ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hq := hγball t ht
    apply hΛ _ hq
    rw [hA (hball hq), affineMap_apply_eq_add_linear A (γ t) p, hγ, add_sub_cancel_left,
      map_smul, map_smul, hLw, smul_zero, smul_zero, add_zero, hpA]
  · refine mem_nhdsWithin.mpr ⟨ball p (r / 2), isOpen_ball, mem_ball_self (by positivity), ?_⟩
    rintro q ⟨hq, hqΛ⟩
    have hqH : q ∈ H := hball (ball_subset_ball (by linarith) hq)
    have hLq : A.linear (q - p) = 0 := by
      have h1 := affineMap_apply_eq_add_linear A q p
      rw [← hA hqH, hΛs q hqΛ, hpA] at h1
      linarith
    obtain ⟨c, hc⟩ := exists_eq_smul_of_linearMap_apply_eq_zero_of_finrank_eq_two hE hA0 hw0
      hLw hLq
    have hcδ : |c| < δ := by
      have hq' := mem_ball.mp hq
      rw [dist_eq_norm, hc, norm_smul, Real.norm_eq_abs, ← hδw] at hq'
      exact lt_of_mul_lt_mul_right hq' hwpos.le
    refine ⟨c / δ, ⟨?_, ?_⟩, ?_⟩
    · rw [le_div_iff₀ hδ]
      linarith [neg_abs_le c]
    · rw [div_le_iff₀ hδ]
      linarith [le_abs_self c]
    · rw [hγ, smul_smul, div_mul_cancel₀ c hδ.ne', ← hc, add_sub_cancel]

open Classical in
theorem exists_coface_pos_of_ball_subset (hE : Module.finrank ℝ E = 2)
    (T : Geometry.SimplicialComplex ℝ E) {a b : E} (h2 : ({a, b} : Finset E).card = 2)
    {p : E} (hpσ : p ∈ convexHull ℝ (({a, b} : Finset E) : Set E)) {r : ℝ} (hr : 0 < r)
    (hN : ∀ q ∈ ball p r, ∃ τ ∈ T.faces, ({a, b} : Finset E) ⊆ τ ∧
      q ∈ convexHull ℝ (τ : Set E))
    (m : E →ᵃ[ℝ] ℝ) (hmL : m.linear ≠ 0) (hma : m a = 0) (hmb : m b = 0) :
    ∃ c, c ∉ ({a, b} : Finset E) ∧ insert c ({a, b} : Finset E) ∈ T.faces ∧ 0 < m c := by
  have hhull : convexHull ℝ (({a, b} : Finset E) : Set E) ⊆ {x | m x = 0} := by
    refine convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage m)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hma
    · rw [Finset.mem_singleton.mp hx]
      exact hmb
  obtain ⟨z, hz⟩ : ∃ z, m.linear z ≠ 0 := by
    by_contra h
    push Not at h
    exact hmL (LinearMap.ext h)
  obtain ⟨n, hn⟩ : ∃ n, 0 < m.linear n := by
    rcases lt_or_gt_of_ne hz with h | h
    · exact ⟨-z, by rw [map_neg]; linarith⟩
    · exact ⟨z, h⟩
  set t₀ : ℝ := r / (2 * (‖n‖ + 1)) with ht₀def
  have ht₀ : 0 < t₀ := by positivity
  have ht₀n : t₀ * (‖n‖ + 1) = r / 2 := by
    rw [ht₀def]
    field_simp
  have hq : p + t₀ • n ∈ ball p r := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht₀]
    nlinarith
  obtain ⟨τ, hτ, hστ, hqτ⟩ := hN _ hq
  have hmq : 0 < m (p + t₀ • n) := by
    rw [affineMap_apply_eq_add_linear m (p + t₀ • n) p, add_sub_cancel_left, map_smul,
      smul_eq_mul, hhull hpσ, zero_add]
    exact mul_pos ht₀ hn
  have hne : ({a, b} : Finset E) ≠ τ := by
    rintro rfl
    have h0 : m (p + t₀ • n) = 0 := hhull hqτ
    linarith
  obtain ⟨c, hcτ, hcσ⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hστ hne)
  have hτeq : insert c ({a, b} : Finset E) = τ :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset hcτ hστ)
      (by rw [Finset.card_insert_of_notMem hcσ, h2]
          exact card_le_three_of_mem_faces_of_finrank_eq_two hE T hτ)
  refine ⟨c, hcσ, hτeq ▸ hτ, ?_⟩
  by_contra hc
  push Not at hc
  have hle : convexHull ℝ ((insert c ({a, b} : Finset E) : Finset E) : Set E) ⊆
      {x | m x ≤ 0} := by
    refine convexHull_min ?_ ((convex_Iic (0 : ℝ)).affine_preimage m)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hc
    · exact le_of_eq (hhull (subset_convexHull ℝ _ hx))
  have h0 : m (p + t₀ • n) ≤ 0 := hle (hτeq ▸ hqτ)
  linarith

open Classical in
theorem exists_cofaces_cover_of_ball_subset (hE : Module.finrank ℝ E = 2)
    (T : Geometry.SimplicialComplex ℝ E) {a b : E} (hσ : ({a, b} : Finset E) ∈ T.faces)
    (h2 : ({a, b} : Finset E).card = 2)
    {p : E} (hpσ : p ∈ convexHull ℝ (({a, b} : Finset E) : Set E)) {r : ℝ} (hr : 0 < r)
    (hN : ∀ q ∈ ball p r, ∃ τ ∈ T.faces, ({a, b} : Finset E) ⊆ τ ∧
      q ∈ convexHull ℝ (τ : Set E))
    (ℓ : E →ᵃ[ℝ] ℝ) (hℓL : ℓ.linear ≠ 0) (hℓa : ℓ a = 0) (hℓb : ℓ b = 0) :
    ∃ cp cm : E, insert cp ({a, b} : Finset E) ∈ T.faces ∧
      insert cm ({a, b} : Finset E) ∈ T.faces ∧ 0 < ℓ cp ∧ ℓ cm < 0 ∧
      ∀ q ∈ ball p r, q ∈ convexHull ℝ ((insert cp ({a, b} : Finset E) : Finset E) : Set E) ∨
        q ∈ convexHull ℝ ((insert cm ({a, b} : Finset E) : Finset E) : Set E) := by
  have hℓσ : EqOn ℓ (fun _ => 0) (({a, b} : Finset E) : Set E) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hℓa
    · rw [Finset.mem_singleton.mp hx]
      exact hℓb
  have hneg : (-ℓ).linear ≠ 0 := by
    rw [AffineMap.neg_linear]
    exact neg_ne_zero.mpr hℓL
  obtain ⟨cp, hcpσ, hcpT, hcp⟩ :=
    exists_coface_pos_of_ball_subset hE T h2 hpσ hr hN ℓ hℓL hℓa hℓb
  obtain ⟨cm, hcmσ, hcmT, hcm'⟩ := exists_coface_pos_of_ball_subset hE T h2 hpσ hr hN (-ℓ) hneg
    (by simp [hℓa]) (by simp [hℓb])
  have hcm : ℓ cm < 0 := by
    have h : 0 < -ℓ cm := by simpa using hcm'
    linarith
  have hsep : ∀ c c', c ∉ ({a, b} : Finset E) → c' ∉ ({a, b} : Finset E) →
      insert c ({a, b} : Finset E) ∈ T.faces → insert c' ({a, b} : Finset E) ∈ T.faces →
      c ≠ c' → ℓ c * ℓ c' < 0 := fun c c' hc hc' hcT hc'T hcc' =>
    affineMap_mul_neg_of_distinct_cofaces_of_card_eq_finrank T hσ (by rw [h2, hE]) hc hc'
      hcc' hcT hc'T ℓ hℓL hℓσ
  refine ⟨cp, cm, hcpT, hcmT, hcp, hcm, fun q hq => ?_⟩
  obtain ⟨τ, hτ, hστ, hqτ⟩ := hN q hq
  by_cases hτσ : ({a, b} : Finset E) = τ
  · subst hτσ
    exact Or.inl (convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _)) hqτ)
  obtain ⟨c, hcτ, hcσ⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hστ hτσ)
  have hτeq : insert c ({a, b} : Finset E) = τ :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset hcτ hστ)
      (by rw [Finset.card_insert_of_notMem hcσ, h2]
          exact card_le_three_of_mem_faces_of_finrank_eq_two hE T hτ)
  rw [← hτeq] at hτ hqτ
  by_cases hccp : c = cp
  · subst hccp
    exact Or.inl hqτ
  have h1 := hsep c cp hcσ hcpσ hτ hcpT hccp
  have hcneg : ℓ c < 0 := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg h hcp.le]
  by_cases hccm : c = cm
  · subst hccm
    exact Or.inr hqτ
  have h2' := hsep c cm hcσ hcmσ hτ hcmT hccm
  nlinarith [mul_pos_of_neg_of_neg hcneg hcm]

omit [FiniteDimensional ℝ E] in
theorem exists_arc_of_two_rays {p vp vm : E} (ℓ : E →ᵃ[ℝ] ℝ) (hℓp : ℓ p = 0)
    (hvp : 0 < ℓ.linear vp) (hvm : ℓ.linear vm < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ γ : ℝ → E, IsPiecewiseAffineOn γ (Icc (-1) 1) ∧ InjOn γ (Icc (-1) 1) ∧ γ 0 = p ∧
      (∀ t ∈ Icc (-1 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) δ, γ t = p + u • vp ∨ γ t = p + u • vm) ∧
      (∀ u ∈ Ico (0 : ℝ) δ, p + u • vp ∈ γ '' Icc (-1) 1 ∧ p + u • vm ∈ γ '' Icc (-1) 1) := by
  classical
  have hℓq : ∀ v : E, ∀ u : ℝ, ℓ (p + u • v) = u * ℓ.linear v := by
    intro v u
    rw [affineMap_apply_eq_add_linear ℓ (p + u • v) p, add_sub_cancel_left, map_smul,
      smul_eq_mul, hℓp, zero_add]
  have hvp0 : vp ≠ 0 := by
    rintro rfl
    simp at hvp
  have hvm0 : vm ≠ 0 := by
    rintro rfl
    simp at hvm
  let γ : ℝ → E := fun t => if t ≤ 0 then p + (-t * δ) • vm else p + (t * δ) • vp
  have hγneg : ∀ t, t ≤ 0 → γ t = p + (-t * δ) • vm := fun t ht => ite_eq_left ht
  have hγpos : ∀ t, 0 < t → γ t = p + (t * δ) • vp := fun t ht => ite_eq_right (not_le.mpr ht)
  have hγ0 : γ 0 = p := by rw [hγneg 0 le_rfl, neg_zero, zero_mul, zero_smul, add_zero]
  have hpl : IsPiecewiseAffineOn γ (Icc (-1) 1) := by
    have hneg_pl : IsPiecewiseAffineOn γ (Icc (-1) 0) := by
      refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (AffineMap.lineMap p (p + (-δ) • vm)) isHPolytope_Icc).congr fun t ht => ?_
      rw [hγneg t ht.2]
      simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left,
        smul_smul]
      rw [add_comm, neg_mul, mul_neg]
    have hpos_pl : IsPiecewiseAffineOn γ (Icc 0 1) := by
      refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (AffineMap.lineMap p (p + δ • vp)) isHPolytope_Icc).congr fun t ht => ?_
      rcases eq_or_lt_of_le ht.1 with h0 | ht0
      · rw [← h0, hγ0]
        simp
      · rw [hγpos t ht0]
        simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_sub_cancel_left,
          smul_smul]
        rw [add_comm]
    have h := hneg_pl.union_of_isClosed hpos_pl isClosed_Icc isClosed_Icc
    rwa [Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)] at h
  have hneg_side : ∀ t, t ≤ 0 → ℓ (γ t) ≤ 0 := by
    intro t ht
    rw [hγneg t ht, hℓq]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) hδ.le) hvm.le
  have hpos_side : ∀ t, 0 < t → 0 < ℓ (γ t) := by
    intro t ht
    rw [hγpos t ht, hℓq]
    exact mul_pos (mul_pos ht hδ) hvp
  have hinj : InjOn γ (Icc (-1) 1) := by
    intro t _ t' _ htt'
    by_cases ht : t ≤ 0 <;> by_cases ht' : t' ≤ 0
    · rw [hγneg t ht, hγneg t' ht', add_right_inj] at htt'
      have h1 : -t * δ = -t' * δ := smul_left_injective ℝ hvm0 htt'
      have h2 := mul_right_cancel₀ hδ.ne' h1
      linarith
    · have h1 := hneg_side t ht
      have h2 := hpos_side t' (not_le.mp ht')
      rw [htt'] at h1
      linarith
    · have h1 := hneg_side t' ht'
      have h2 := hpos_side t (not_le.mp ht)
      rw [htt'] at h2
      linarith
    · rw [hγpos t (not_le.mp ht), hγpos t' (not_le.mp ht'), add_right_inj] at htt'
      have h1 : t * δ = t' * δ := smul_left_injective ℝ hvp0 htt'
      exact mul_right_cancel₀ hδ.ne' h1
  refine ⟨γ, hpl, hinj, hγ0, fun t ht => ?_, fun u hu => ⟨?_, ?_⟩⟩
  · by_cases h0 : t ≤ 0
    · refine ⟨-t * δ, ⟨mul_nonneg (by linarith) hδ.le, ?_⟩, Or.inr (hγneg t h0)⟩
      nlinarith [ht.1]
    · refine ⟨t * δ, ⟨mul_nonneg (by linarith [not_le.mp h0]) hδ.le, ?_⟩,
        Or.inl (hγpos t (not_le.mp h0))⟩
      nlinarith [ht.2]
  · rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [hγ0, ← hu0, zero_smul, add_zero]
    · have hle : u / δ ≤ 1 := (div_le_one hδ).mpr hu.2.le
      have hnn : 0 ≤ u / δ := div_nonneg hu.1 hδ.le
      refine ⟨u / δ, ⟨by linarith, hle⟩, ?_⟩
      rw [hγpos _ (div_pos hu0 hδ), div_mul_cancel₀ u hδ.ne']
  · rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      rw [hγ0, ← hu0, zero_smul, add_zero]
    · have hle : u / δ ≤ 1 := (div_le_one hδ).mpr hu.2.le
      have hnn : 0 ≤ u / δ := div_nonneg hu.1 hδ.le
      refine ⟨-(u / δ), ⟨by linarith, by linarith⟩, ?_⟩
      rw [hγneg _ (by linarith), neg_neg, div_mul_cancel₀ u hδ.ne']

theorem exists_eq_add_smul_of_mem_level_of_nonneg (hE : Module.finrank ℝ E = 2)
    {φ : E → ℝ} {H : Set E} {A : E →ᵃ[ℝ] ℝ} (hA : EqOn φ A H) (hA0 : A.linear ≠ 0)
    {p v q : E} {s : ℝ} (hpA : A p = s) (hv : v ≠ 0) (hAv : A.linear v = 0)
    (ℓ : E →ᵃ[ℝ] ℝ) (hℓp : ℓ p = 0) (hℓv : 0 < ℓ.linear v) (hqH : q ∈ H) (hq : φ q = s)
    (hℓq : 0 ≤ ℓ q) : ∃ c : ℝ, 0 ≤ c ∧ q = p + c • v := by
  have hLq : A.linear (q - p) = 0 := by
    have h1 := affineMap_apply_eq_add_linear A q p
    rw [← hA hqH, hq, hpA] at h1
    linarith
  obtain ⟨c, hc⟩ := exists_eq_smul_of_linearMap_apply_eq_zero_of_finrank_eq_two hE hA0 hv hAv hLq
  have hqeq : q = p + c • v := by rw [← hc, add_sub_cancel]
  refine ⟨c, ?_, hqeq⟩
  have h := affineMap_apply_eq_add_linear ℓ q p
  rw [hc, map_smul, smul_eq_mul, hℓp, zero_add] at h
  by_contra hlt
  push Not at hlt
  nlinarith

open Classical in
theorem exists_arc_of_mem_level_of_edge (hE : Module.finrank ℝ E = 2)
    (T : Geometry.SimplicialComplex ℝ E) {φ : E → ℝ}
    (haff : ∀ σ ∈ T.faces, ∃ A : E →ᵃ[ℝ] ℝ, EqOn φ A (convexHull ℝ (σ : Set E)))
    {s : ℝ} (hs : ∀ v ∈ T.vertices, φ v ≠ s) {a b : E} (hσ : ({a, b} : Finset E) ∈ T.faces)
    (h2 : ({a, b} : Finset E).card = 2) {p : E}
    (hpσ : p ∈ convexHull ℝ (({a, b} : Finset E) : Set E)) (hp : φ p = s) {r : ℝ} (hr : 0 < r)
    (hrT : ball p r ⊆ T.space)
    (hN : ∀ q ∈ ball p r, ∃ τ ∈ T.faces, ({a, b} : Finset E) ⊆ τ ∧
      q ∈ convexHull ℝ (τ : Set E)) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc (-1) 1) (γ '' Icc (-1) 1) ∧ γ 0 = p ∧
      γ '' Icc (-1) 1 ⊆ T.space ∩ φ ⁻¹' {s} ∧
      γ '' Icc (-1) 1 ∈ 𝓝[T.space ∩ φ ⁻¹' {s}] p := by
  obtain ⟨ℓ, hℓL, hℓa, hℓb⟩ :=
    exists_affineMap_linear_ne_zero_apply_eq_zero_of_finrank_eq_two hE a b
  obtain ⟨cp, cm, hcpT, hcmT, hcp, hcm, hcover⟩ :=
    exists_cofaces_cover_of_ball_subset hE T hσ h2 hpσ hr hN ℓ hℓL hℓa hℓb
  have hhull_zero : convexHull ℝ (({a, b} : Finset E) : Set E) ⊆ {x | ℓ x = 0} := by
    refine convexHull_min ?_ ((convex_singleton (0 : ℝ)).affine_preimage ℓ)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hℓa
    · rw [Finset.mem_singleton.mp hx]
      exact hℓb
  have hℓp : ℓ p = 0 := hhull_zero hpσ
  have hside : ∀ (m : E →ᵃ[ℝ] ℝ) (c : E), m a = 0 → m b = 0 → 0 ≤ m c →
      convexHull ℝ ((insert c ({a, b} : Finset E) : Finset E) : Set E) ⊆ {x | 0 ≤ m x} := by
    intro m c hma hmb hmc
    refine convexHull_min ?_ ((convex_Ici (0 : ℝ)).affine_preimage m)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hmc
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_of_eq hma.symm
    · rw [Finset.mem_singleton.mp hx]
      exact le_of_eq hmb.symm
  have hsidep := hside ℓ cp hℓa hℓb hcp.le
  have hsidem := hside (-ℓ) cm (by simp [hℓa]) (by simp [hℓb]) (by simp; linarith)
  obtain ⟨Ap, hAp⟩ := haff _ hcpT
  obtain ⟨Am, hAm⟩ := haff _ hcmT
  have hσsub : ∀ c, convexHull ℝ (({a, b} : Finset E) : Set E) ⊆
      convexHull ℝ ((insert c ({a, b} : Finset E) : Finset E) : Set E) := fun c =>
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
  have hmemab : ∀ c, a ∈ ((insert c ({a, b} : Finset E) : Finset E) : Set E) ∧
      b ∈ ((insert c ({a, b} : Finset E) : Finset E) : Set E) := fun c => ⟨by simp, by simp⟩
  have hApp : Ap p = s := (hAp (hσsub cp hpσ)).symm.trans hp
  have hAmp : Am p = s := (hAm (hσsub cm hpσ)).symm.trans hp
  have hφab : φ b - φ a ≠ 0 := by
    intro h0
    have hsame : φ a = φ b := by linarith
    have hApa : Ap a = φ a := (hAp (subset_convexHull ℝ _ (hmemab cp).1)).symm
    have hApb : Ap b = φ b := (hAp (subset_convexHull ℝ _ (hmemab cp).2)).symm
    have hsub : convexHull ℝ (({a, b} : Finset E) : Set E) ⊆ {x | Ap x = φ a} := by
      refine convexHull_min ?_ ((convex_singleton (φ a)).affine_preimage Ap)
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hApa
      · rw [Finset.mem_singleton.mp hx]
        exact hApb.trans hsame.symm
    have hpa : Ap p = φ a := hsub hpσ
    exact hs a (T.down_closed hσ (by simp) (Finset.singleton_nonempty a)) (hpa.symm.trans hApp)
  have hLd : ∀ (A : E →ᵃ[ℝ] ℝ) (c : E),
      EqOn φ A (convexHull ℝ ((insert c ({a, b} : Finset E) : Finset E) : Set E)) →
      A.linear (b - a) ≠ 0 := by
    intro A c hA h0
    have h := affineMap_apply_eq_add_linear A b a
    rw [← hA (subset_convexHull ℝ _ (hmemab c).1), ← hA (subset_convexHull ℝ _ (hmemab c).2),
      h0, add_zero] at h
    exact hφab (by linarith)
  have hlinab : ℓ.linear (b - a) = 0 := by
    have h := affineMap_apply_eq_add_linear ℓ b a
    rw [hℓa, hℓb] at h
    linarith
  obtain ⟨n, hn⟩ : ∃ n, ℓ.linear n ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓL (LinearMap.ext h)
  obtain ⟨vp, hLvp, hℓvp⟩ :=
    exists_linearMap_apply_eq_zero_pos_of_apply_ne_zero (hLd Ap cp hAp) hlinab hn
  obtain ⟨vm, hLvm, hℓvm'⟩ := exists_linearMap_apply_eq_zero_pos_of_apply_ne_zero
    (hLd Am cm hAm) (show (-ℓ.linear) (b - a) = 0 by rw [LinearMap.neg_apply, hlinab, neg_zero])
    (show (-ℓ.linear) n ≠ 0 by rw [LinearMap.neg_apply]; exact neg_ne_zero.mpr hn)
  have hℓvm : ℓ.linear vm < 0 := by
    rw [LinearMap.neg_apply] at hℓvm'
    linarith
  have hvp0 : vp ≠ 0 := by
    rintro rfl
    simp at hℓvp
  have hvm0 : vm ≠ 0 := by
    rintro rfl
    simp at hℓvm
  have hvppos : 0 < ‖vp‖ := norm_pos_iff.mpr hvp0
  have hvmpos : 0 < ‖vm‖ := norm_pos_iff.mpr hvm0
  have hApL : Ap.linear ≠ 0 := fun h0 => hLd Ap cp hAp (by rw [h0, LinearMap.zero_apply])
  have hAmL : Am.linear ≠ 0 := fun h0 => hLd Am cm hAm (by rw [h0, LinearMap.zero_apply])
  set δ : ℝ := r / (2 * (‖vp‖ + ‖vm‖ + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hδsum : δ * (‖vp‖ + ‖vm‖ + 1) = r / 2 := by
    rw [hδdef]
    field_simp
  have hℓq : ∀ v : E, ∀ u : ℝ, ℓ (p + u • v) = u * ℓ.linear v := by
    intro v u
    rw [affineMap_apply_eq_add_linear ℓ (p + u • v) p, add_sub_cancel_left, map_smul,
      smul_eq_mul, hℓp, zero_add]
  have hball_ray : ∀ v : E, ‖v‖ ≤ ‖vp‖ + ‖vm‖ + 1 → ∀ u ∈ Icc (0 : ℝ) δ,
      p + u • v ∈ ball p r := by
    intro v hv u hu
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hu.1]
    have h1 : u * ‖v‖ ≤ δ * (‖vp‖ + ‖vm‖ + 1) :=
      mul_le_mul hu.2 hv (norm_nonneg v) hδ.le
    linarith
  have hrayp : ∀ u ∈ Icc (0 : ℝ) δ, p + u • vp ∈ T.space ∩ φ ⁻¹' {s} := by
    intro u hu
    have hq := hball_ray vp (by linarith) u hu
    refine ⟨hrT hq, ?_⟩
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · change φ (p + u • vp) = s
      rw [← hu0, zero_smul, add_zero]
      exact hp
    rcases hcover _ hq with h | h
    · change φ (p + u • vp) = s
      rw [hAp h, affineMap_apply_eq_add_linear Ap _ p, add_sub_cancel_left, map_smul, hLvp,
        smul_zero, add_zero, hApp]
    · exfalso
      have h1 : 0 ≤ (-ℓ) (p + u • vp) := hsidem h
      have h2 : 0 < ℓ (p + u • vp) := by rw [hℓq]; exact mul_pos hu0 hℓvp
      simp only [AffineMap.coe_neg, Pi.neg_apply, neg_nonneg] at h1
      linarith
  have hraym : ∀ u ∈ Icc (0 : ℝ) δ, p + u • vm ∈ T.space ∩ φ ⁻¹' {s} := by
    intro u hu
    have hq := hball_ray vm (by linarith) u hu
    refine ⟨hrT hq, ?_⟩
    rcases eq_or_lt_of_le hu.1 with hu0 | hu0
    · change φ (p + u • vm) = s
      rw [← hu0, zero_smul, add_zero]
      exact hp
    rcases hcover _ hq with h | h
    · exfalso
      have h1 : 0 ≤ ℓ (p + u • vm) := hsidep h
      have h2 : ℓ (p + u • vm) < 0 := by rw [hℓq]; exact mul_neg_of_pos_of_neg hu0 hℓvm
      linarith
    · change φ (p + u • vm) = s
      rw [hAm h, affineMap_apply_eq_add_linear Am _ p, add_sub_cancel_left, map_smul, hLvm,
        smul_zero, add_zero, hAmp]
  obtain ⟨γ, hpl, hinj, hγ0, hγray, hrayγ⟩ := exists_arc_of_two_rays ℓ hℓp hℓvp hℓvm hδ
  refine ⟨γ, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
    hpl hinj.bijOn_image, hγ0, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu, h | h⟩ := hγray t ht
    · rw [h]
      exact hrayp u hu
    · rw [h]
      exact hraym u hu
  · set r' : ℝ := δ * min ‖vp‖ ‖vm‖ with hr'def
    have hmin := min_le_left ‖vp‖ ‖vm‖
    have hmin' := min_le_right ‖vp‖ ‖vm‖
    have hr' : 0 < r' := mul_pos hδ (lt_min hvppos hvmpos)
    have hr'r : r' ≤ r := by nlinarith
    refine mem_nhdsWithin.mpr ⟨ball p r', isOpen_ball, mem_ball_self hr', ?_⟩
    rintro q ⟨hq, hqT, hqs⟩
    have hqr : q ∈ ball p r := ball_subset_ball hr'r hq
    have hdist : ‖q - p‖ < r' := by rw [← dist_eq_norm]; exact mem_ball.mp hq
    rcases hcover q hqr with h | h
    · obtain ⟨c, hc0, hqeq⟩ := exists_eq_add_smul_of_mem_level_of_nonneg hE hAp hApL hApp hvp0
        hLvp ℓ hℓp hℓvp h hqs (hsidep h)
      have hcδ : c < δ := by
        rw [hqeq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0] at hdist
        nlinarith
      rw [hqeq]
      exact (hrayγ c ⟨hc0, hcδ⟩).1
    · have hnegℓp : (-ℓ) p = 0 := by simp [hℓp]
      have hnegℓv : 0 < (-ℓ).linear vm := by
        rw [AffineMap.neg_linear, LinearMap.neg_apply]
        linarith
      obtain ⟨c, hc0, hqeq⟩ := exists_eq_add_smul_of_mem_level_of_nonneg hE hAm hAmL hAmp hvm0
        hLvm (-ℓ) hnegℓp hnegℓv h hqs (hsidem h)
      have hcδ : c < δ := by
        rw [hqeq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0] at hdist
        nlinarith
      rw [hqeq]
      exact (hrayγ c ⟨hc0, hcδ⟩).2

open Classical in
theorem exists_arc_of_mem_level_of_affineOn_faces (hE : Module.finrank ℝ E = 2)
    (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces] {φ : E → ℝ}
    (haff : ∀ σ ∈ T.faces, ∃ A : E →ᵃ[ℝ] ℝ, EqOn φ A (convexHull ℝ (σ : Set E)))
    {s : ℝ} (hs : ∀ v ∈ T.vertices, φ v ≠ s) {p : E} (hpT : p ∈ interior T.space)
    (hp : φ p = s) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc (-1) 1) (γ '' Icc (-1) 1) ∧ γ 0 = p ∧
      γ '' Icc (-1) 1 ⊆ T.space ∩ φ ⁻¹' {s} ∧
      γ '' Icc (-1) 1 ∈ 𝓝[T.space ∩ φ ⁻¹' {s}] p := by
  obtain ⟨σ, hσ, hpσ⟩ := exists_face_mem_openSimplex T (interior_subset hpT)
  have hpσh : p ∈ convexHull ℝ (σ : Set E) := openSimplex_subset_convexHull σ hpσ
  have hvert : ∀ v ∈ σ, v ∈ T.vertices := fun v hv =>
    T.down_closed hσ (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  obtain ⟨r, hr, hrT, hN⟩ :=
    exists_ball_subset_forall_mem_convexHull_of_mem_openSimplex T hσ hpσ hpT
  have hσne : σ.Nonempty := T.nonempty_of_mem_faces hσ
  have hσcard := card_le_three_of_mem_faces_of_finrank_eq_two hE T hσ
  have hσ1 : σ.card ≠ 1 := by
    intro h1
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp h1
    have hpv : p = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using hpσh
    exact hs v (hvert v (Finset.mem_singleton_self v)) (hpv ▸ hp)
  have hσpos : 0 < σ.card := Finset.card_pos.mpr hσne
  rcases (by omega : σ.card = 3 ∨ σ.card = 2) with h3 | h2
  · have hballσ : ball p r ⊆ convexHull ℝ (σ : Set E) := by
      intro q hq
      obtain ⟨τ, hτ, hστ, hqτ⟩ := hN q hq
      have heq : σ = τ := Finset.eq_of_subset_of_card_le hστ
        (by rw [h3]; exact card_le_three_of_mem_faces_of_finrank_eq_two hE T hτ)
      exact heq ▸ hqτ
    obtain ⟨A, hA⟩ := haff σ hσ
    have hpA : A p = s := (hA hpσh).symm.trans hp
    have hL : A.linear ≠ 0 := by
      intro h0
      obtain ⟨v, hv⟩ := hσne
      have hvA : A v = A p := by
        rw [affineMap_apply_eq_add_linear A v p, h0, LinearMap.zero_apply, add_zero]
      exact hs v (hvert v hv) ((hA (subset_convexHull ℝ _ hv)).trans (hvA.trans hpA))
    exact exists_arc_of_mem_level_of_ball_subset_convexHull hE hA hL hr hpA hballσ
      (fun q hq hqs => ⟨hrT hq, hqs⟩) (fun q hq => hq.2)
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
    exact exists_arc_of_mem_level_of_edge hE T haff hs hσ h2 hpσh hp hr hrT hN

open Classical in
theorem isCombinatorialManifold_one_of_forall_arc (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces]
    (harc : ∀ p ∈ G.space, ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc (-1) 1) (γ '' Icc (-1) 1) ∧
      γ 0 = p ∧ γ '' Icc (-1) 1 ⊆ G.space ∧ γ '' Icc (-1) 1 ∈ 𝓝[G.space] p) :
    IsCombinatorialManifold 1 G := by
  have hG : IsCombinatorialManifoldWithBoundary 1 G := by
    apply isCombinatorialManifoldWithBoundary_of_isPLBall_neighborhoods G
    intro p hp
    obtain ⟨γ, hγ, -, hsub, hnhds⟩ := harc p hp
    exact ⟨_, (isPLBall_Icc (by norm_num : (-1 : ℝ) < 1)).of_isPLHomeomorphOn hγ, hsub, hnhds⟩
  obtain ⟨R, hRfin, hRspace⟩ :=
    (isHPolytope_Icc (a := (-1 : ℝ)) (b := 1)).isPolyhedron.exists_simplicialComplex
  let _ : Finite R.faces := hRfin.to_subtype
  have hRball : IsPLBall 1 R.space := by
    rw [hRspace]
    exact isPLBall_Icc (by norm_num)
  have hRbd : (boundaryComplex 1 R).space = {(-1 : ℝ), 1} := by
    have hsub : (boundaryComplex 1 R).space ⊆ frontier R.space :=
      boundaryComplex_space_subset_frontier_of_finrank (n := 0) (by simp) R
        hRball.isCombinatorialManifoldWithBoundary
    rw [hRspace, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hsub
    obtain ⟨u, v, huv, hbd⟩ :=
      isPLSphere_zero_iff.mp (isPLSphere_boundaryComplex_space_of_isPLBall R hRball)
    rw [hbd] at hsub ⊢
    have hu : u ∈ ({(-1 : ℝ), 1} : Set ℝ) := hsub (Or.inl rfl)
    have hv : v ∈ ({(-1 : ℝ), 1} : Set ℝ) := hsub (Or.inr rfl)
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (huv rfl).elim
    · rfl
    · exact pair_comm _ _
    · exact (huv rfl).elim
  intro v hv
  rcases hG v hv with hsph | hball
  · exact hsph
  exfalso
  have hvB : v ∈ (boundaryComplex 1 G).space := by
    have hmem : {v} ∈ (boundaryComplex 1 G).faces :=
      (mem_boundaryComplex_faces_iff 1 G).mpr
        ⟨hv, {v}, hv, subset_rfl, by simp, by simpa using hball⟩
    exact (boundaryComplex 1 G).subset_space hmem (Finset.mem_singleton_self v)
  have hvG : v ∈ G.space := G.subset_space hv (Finset.mem_singleton_self v)
  obtain ⟨γ, hγ, hγ0, hsub, hnhds⟩ := harc v hvG
  obtain ⟨TA, hTAfin, hTAspace⟩ := ((isPLBall_Icc (by norm_num : (-1 : ℝ) < 1)).of_isPLHomeomorphOn
    hγ).isPolyhedron.exists_simplicialComplex
  let _ : Finite TA.faces := hTAfin.to_subtype
  have hγR : IsPLHomeomorphOn γ R.space TA.space := by
    rw [hRspace, hTAspace]
    exact hγ
  have hTA : IsCombinatorialManifoldWithBoundary 1 TA :=
    hRball.isCombinatorialManifoldWithBoundary.of_isPLHomeomorphOn hγR
  have hvTA : v ∈ TA.space := by
    rw [hTAspace, ← hγ0]
    exact mem_image_of_mem γ ⟨by norm_num, by norm_num⟩
  have hvTAB : v ∈ (boundaryComplex 1 TA).space :=
    (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin G TA hG hTA (hTAspace ▸ hsub) hvTA
      (hTAspace ▸ hnhds)).mpr hvB
  have h0R : (0 : ℝ) ∈ R.space := by
    rw [hRspace]
    exact ⟨by norm_num, by norm_num⟩
  have hiff := mem_boundaryComplex_space_iff_of_isPLHomeomorphOn R TA
    hRball.isCombinatorialManifoldWithBoundary hγR h0R
  rw [hγ0, hRbd] at hiff
  rcases hiff.mp hvTAB with h | h <;> norm_num at h

theorem IsPiecewiseAffineOn.exists_finite_levels_isPLSphere_decomposition
    {Q : Set Schoenflies.Plane} (hQ : IsPolyhedron Q) {φ : Schoenflies.Plane → ℝ}
    (hφ : IsPiecewiseAffineOn φ Q) :
    ∃ S₀ : Set ℝ, S₀.Finite ∧ ∀ s ∉ S₀, Q ∩ φ ⁻¹' {s} ⊆ interior Q →
      ∃ C : Set (Set Schoenflies.Plane), C.Finite ∧ (∀ c ∈ C, IsPLSphere 1 c) ∧
        C.PairwiseDisjoint id ∧ Q ∩ φ ⁻¹' {s} = ⋃₀ C := by
  obtain ⟨K, hKfin, hKQ⟩ := hQ.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hφK : IsPiecewiseAffineOn φ K.space := by
    rw [hKQ]
    exact hφ
  obtain ⟨T, hT, hTfin, haff⟩ := hφK.exists_isSubdivision_affineOn_faces K
  let _ : Finite T.faces := hTfin.to_subtype
  have hTQ : T.space = Q := hT.space_eq.trans hKQ
  refine ⟨φ '' T.vertices, (SimplicialComplex.finite_vertices T).image φ, fun s hs hint => ?_⟩
  have hsv : ∀ v ∈ T.vertices, φ v ≠ s := fun v hv hvs => hs ⟨v, hv, hvs⟩
  have hΛ : IsPolyhedron (Q ∩ φ ⁻¹' {s}) := by
    refine hφ.isPolyhedron_inter_preimage_of_isPolyhedron hQ ?_
    rw [← Icc_self s]
    exact isHPolytope_Icc.isPolyhedron
  obtain ⟨G, hGfin, hGspace⟩ := hΛ.exists_simplicialComplex
  let _ : Finite G.faces := hGfin.to_subtype
  have hG : IsCombinatorialManifold 1 G := by
    apply isCombinatorialManifold_one_of_forall_arc G
    intro p hp
    rw [hGspace] at hp ⊢
    have hpT : p ∈ interior T.space := by
      rw [hTQ]
      exact hint hp
    obtain ⟨γ, hγ, hγ0, hsub, hnhds⟩ := exists_arc_of_mem_level_of_affineOn_faces
      finrank_euclideanSpace_fin T haff hsv hpT hp.2
    rw [hTQ] at hsub hnhds
    exact ⟨γ, hγ, hγ0, hsub, hnhds⟩
  obtain ⟨C, hCfin, hC, hCdisj, hCG⟩ := exists_finite_isPLSphere_decomposition G hG
  exact ⟨C, hCfin, hC, hCdisj, hGspace.symm.trans hCG⟩

end DifferentialGeometry.Topology.PiecewiseLinear
