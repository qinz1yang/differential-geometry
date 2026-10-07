import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PreparedSheetComplexTriangleFIX
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra

/-!
# S-MY-FIX2 G3：source 复形 `T` 的分层剖分（level triangles `{g = 1/2}`、`{g = 3/4}` 是子复形，`_FIX2`）

revolve 模型 `curve2_FIX2` 的 double locus 在盘上是半径 `1/2` 与 `3/4` 的两个圆；`α = radialGrid_FIX`
满足 `‖α z‖ = g z`，所以它们对应 `T` 里 `g = 1/2`、`g = 3/4` 的两个三角形环。本文件用库的
`exists_simplicialComplex_of_forall_isHPolytope` 造一个 `R`：`|R| = |triComplex_FIX|`（同一个三角形 `Δ`），
`R` 的每个 2-面落在 `triComplex_FIX` 的某个 cone 三角形里（所以 `α` 在其上等于某个扇区映射 `sectorMap ℓ`），
两个 level 三角形边界 = `R` 的子复形，三个角点的缩放 `c • V₁` 是 `R` 的顶点。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Metric
open DifferentialGeometry.Topology DifferentialGeometry.Topology.PiecewiseLinear
open scoped Topology ContDiff NNReal Pointwise

namespace DifferentialGeometry.Geometry

/-- level `b`：`false ↦ 1/2`，`true ↦ 3/4`。 -/
def levelC_FIX2 (b : Bool) : ℝ := if b then 3 / 4 else 1 / 2

theorem levelC_pos_FIX2 (b : Bool) : 0 < levelC_FIX2 b := by
  cases b <;> norm_num [levelC_FIX2]

theorem levelC_lt_one_FIX2 (b : Bool) : levelC_FIX2 b < 1 := by
  cases b <;> norm_num [levelC_FIX2]

/-- 两个 level 三角形边界：`g = 1/2` 或 `g = 3/4`。 -/
def levelSet_FIX2 : Set ℂ := {z | triGauge_FIX z = 1 / 2 ∨ triGauge_FIX z = 3 / 4}

theorem triBoundary_space_eq_FIX2 : triBoundary_FIX.space = {z | triGauge_FIX z = 1} := by
  rw [← frontier_triSet_FIX, convexHull_triVerts_FIX, frontier_triSet_eq_FIX]

/-- 缩放的仿射同胚。 -/
def scaleEquiv_FIX2 (c : ℝ) (hc : c ≠ 0) : ℂ ≃ᵃ[ℝ] ℂ :=
  (LinearEquiv.smulOfNeZero ℝ ℂ c hc).toAffineEquiv

theorem scaleEquiv_image_FIX2 (c : ℝ) (hc : c ≠ 0) (S : Set ℂ) :
    scaleEquiv_FIX2 c hc '' S = c • S := by
  ext x
  simp [scaleEquiv_FIX2, Set.mem_smul_set]

/-- 剖分用的凸多边形族：`triComplex_FIX` 的每个面的凸包，以及两个 level 三角形边界的每个面的缩放凸包。 -/
def famC_FIX2 : (triComplex_FIX.faces ⊕ (triBoundary_FIX.faces × Bool)) → Set ℂ
  | Sum.inl s => convexHull ℝ (s.1 : Set ℂ)
  | Sum.inr p => levelC_FIX2 p.2 • convexHull ℝ (p.1.1 : Set ℂ)

instance finite_triComplex_faces'_FIX2 : Finite triComplex_FIX.faces :=
  triComplex_faces_finite_FIX.to_subtype

instance finite_triBoundary_faces_FIX2 : Finite triBoundary_FIX.faces :=
  (simplexBoundary_faces_finite triVerts_FIX triVerts_indep_FIX).to_subtype

theorem famC_isHPolytope_FIX2 (j : triComplex_FIX.faces ⊕ (triBoundary_FIX.faces × Bool)) :
    IsHPolytope (famC_FIX2 j) := by
  rcases j with s | p
  · exact isHPolytope_convexHull_of_affineIndependent _ (triComplex_FIX.indep s.2)
  · have h := isHPolytope_convexHull_of_affineIndependent (p.1.1) (triBoundary_FIX.indep p.1.2)
    have h2 := h.image_affineEquiv (scaleEquiv_FIX2 (levelC_FIX2 p.2) (levelC_pos_FIX2 _).ne')
    rwa [scaleEquiv_image_FIX2] at h2

/-- level piece 的像：`conv(σ) ⊆ {g = 1}`，所以 `c • conv(σ) ⊆ {g = c}`。 -/
theorem famC_inr_subset_FIX2 (σ : triBoundary_FIX.faces) (b : Bool) :
    famC_FIX2 (Sum.inr (σ, b)) ⊆ {z | triGauge_FIX z = levelC_FIX2 b} := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ triBoundary_FIX.space :=
    triBoundary_FIX.convexHull_subset_space σ.2 hx
  rw [triBoundary_space_eq_FIX2, mem_ofPred_eq] at hx'
  rw [mem_ofPred_eq, triGauge_smul_FIX (levelC_pos_FIX2 b).le, hx', mul_one]

theorem famC_iUnion_FIX2 : (⋃ j, famC_FIX2 j) = triComplex_FIX.space := by
  apply Subset.antisymm
  · rw [iUnion_subset_iff]
    rintro (s | p)
    · exact triComplex_FIX.convexHull_subset_space s.2
    · intro z hz
      have := famC_inr_subset_FIX2 p.1 p.2 hz
      rw [triComplex_space_FIX, mem_ofPred_eq]
      rw [mem_ofPred_eq] at this
      rw [this]
      exact (levelC_lt_one_FIX2 p.2).le
  · intro z hz
    obtain ⟨s, hs, hzs⟩ := triComplex_FIX.mem_space_iff.mp hz
    exact mem_iUnion.mpr ⟨Sum.inl ⟨s, hs⟩, hzs⟩

/-- 一个 `ℝ²` 里的 3 个仿射无关点不能落在 `≤ 2` 点的仿射包里。 -/
theorem card_le_of_hull_subset_FIX2 {s t : Finset ℂ} (hs : AffineIndependent ℝ ((↑) : s → ℂ))
    (h : convexHull ℝ (s : Set ℂ) ⊆ convexHull ℝ (t : Set ℂ)) : s.card ≤ t.card := by
  refine hs.card_le_card_of_subset_affineSpan ?_
  exact (subset_convexHull ℝ _).trans (h.trans (convexHull_subset_affineSpan _))

/-- 剖分 `R` 的存在性与全部要用的性质。 -/
theorem exists_subdiv_FIX2 :
    ∃ R : _root_.Geometry.SimplicialComplex ℝ ℂ, R.faces.Finite ∧
      R.space = triComplex_FIX.space ∧
      (∀ s ∈ R.faces, s.card = 3 → ∃ t ∈ triComplex_FIX.faces, t.card = 3 ∧
        convexHull ℝ (s : Set ℂ) ⊆ convexHull ℝ (t : Set ℂ)) ∧
      (⋃ s ∈ {s ∈ R.faces | convexHull ℝ (s : Set ℂ) ⊆ levelSet_FIX2},
        convexHull ℝ (s : Set ℂ)) = levelSet_FIX2 ∧
      (∀ b, levelC_FIX2 b • triV1_FIX ∈ R.vertices) := by
  classical
  obtain ⟨R, hRfin, hRspace, hcover⟩ :=
    exists_simplicialComplex_of_forall_isHPolytope famC_FIX2 famC_isHPolytope_FIX2
  refine ⟨R, hRfin, hRspace.trans famC_iUnion_FIX2, ?_, ?_, ?_⟩
  · intro s hs hc
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hx : s.centroid ℝ id ∈ openSimplex s := centroid_mem_openSimplex hne
    have hxR : s.centroid ℝ id ∈ R.space :=
      R.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
    rw [hRspace, mem_iUnion] at hxR
    obtain ⟨j, hj⟩ := hxR
    have hj' := hj
    rw [hcover j, mem_iUnion₂] at hj'
    obtain ⟨s', ⟨hs', hsub⟩, hxs'⟩ := hj'
    have hss' : s ⊆ s' := face_subset_of_mem_openSimplex_of_mem_convexHull R hs hs' hx hxs'
    have hhull : convexHull ℝ (s : Set ℂ) ⊆ famC_FIX2 j :=
      (convexHull_mono (Finset.coe_subset.mpr hss')).trans hsub
    rcases j with u | p
    · have hcard := card_le_of_hull_subset_FIX2 (R.indep hs) hhull
      have h3 : u.1.card ≤ 3 := triComplex_dim_le_FIX u.1 u.2
      exact ⟨u.1, u.2, by omega, hhull⟩
    · exfalso
      have hcl : famC_FIX2 (Sum.inr p) =
          convexHull ℝ (((levelC_FIX2 p.2 • p.1.1 : Finset ℂ)) : Set ℂ) := by
        simp only [famC_FIX2]
        rw [Finset.coe_smul_finset, convexHull_smul]
      rw [hcl] at hhull
      have hcard := card_le_of_hull_subset_FIX2 (R.indep hs) hhull
      have h1 : (levelC_FIX2 p.2 • p.1.1 : Finset ℂ).card ≤ p.1.1.card := by
        rw [Finset.smul_finset_def]
        exact Finset.card_image_le
      have h2 : p.1.1.card < 3 := by
        have hsub := p.1.2.1
        have hne := p.1.2.2.2
        have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
        rw [triVerts_card_FIX] at this
        exact this
      omega
  · apply Subset.antisymm
    · exact iUnion₂_subset fun s hs => hs.2
    · intro z hz
      have hb : ∃ b : Bool, triGauge_FIX z = levelC_FIX2 b := by
        rcases hz with h | h
        · exact ⟨false, by simp [levelC_FIX2, h]⟩
        · exact ⟨true, by simp [levelC_FIX2, h]⟩
      obtain ⟨b, hzb⟩ := hb
      have hcpos := levelC_pos_FIX2 b
      have hin : (levelC_FIX2 b)⁻¹ • z ∈ triBoundary_FIX.space := by
        rw [triBoundary_space_eq_FIX2, mem_ofPred_eq, triGauge_smul_FIX (inv_nonneg.mpr hcpos.le),
          hzb, inv_mul_cancel₀ hcpos.ne']
      obtain ⟨σ, hσ, hzσ⟩ := triBoundary_FIX.mem_space_iff.mp hin
      have hzf : z ∈ famC_FIX2 (Sum.inr (⟨σ, hσ⟩, b)) :=
        ⟨_, hzσ, by simp only; rw [smul_inv_smul₀ hcpos.ne']⟩
      have hzf' := hzf
      rw [hcover (Sum.inr (⟨σ, hσ⟩, b)), mem_iUnion₂] at hzf'
      obtain ⟨s, ⟨hs, hsub⟩, hzs⟩ := hzf'
      refine mem_iUnion₂.mpr ⟨s, ⟨hs, hsub.trans fun x hx => ?_⟩, hzs⟩
      have := famC_inr_subset_FIX2 ⟨σ, hσ⟩ b hx
      rw [mem_ofPred_eq] at this
      change triGauge_FIX x = 1 / 2 ∨ triGauge_FIX x = 3 / 4
      cases b
      · left; simpa [levelC_FIX2] using this
      · right; simpa [levelC_FIX2] using this
  · intro b
    have hV1 : ({triV1_FIX} : Finset ℂ) ∈ triBoundary_FIX.faces := by
      refine ⟨?_, Finset.singleton_nonempty _, ?_⟩
      · intro v hv
        rw [Finset.mem_singleton] at hv
        simp [triVerts_FIX, hv]
      · intro h
        have := congrArg Finset.card h
        rw [triVerts_card_FIX] at this
        simp at this
    have hmem : levelC_FIX2 b • triV1_FIX ∈ famC_FIX2 (Sum.inr (⟨{triV1_FIX}, hV1⟩, b)) := by
      simp only [famC_FIX2, Finset.coe_singleton, convexHull_singleton]
      exact ⟨triV1_FIX, rfl, rfl⟩
    have hmem' := hmem
    rw [hcover (Sum.inr (⟨{triV1_FIX}, hV1⟩, b)), mem_iUnion₂] at hmem'
    obtain ⟨s, ⟨hs, hsub⟩, hxs⟩ := hmem'
    have hss : (s : Set ℂ) ⊆ {levelC_FIX2 b • triV1_FIX} := by
      refine (subset_convexHull ℝ _).trans (hsub.trans ?_)
      simp only [famC_FIX2, Finset.coe_singleton, convexHull_singleton]
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_singleton_iff.mp hy]
      rfl
    have hsne : s.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h] at hxs
      simp at hxs
    have hseq : s = {levelC_FIX2 b • triV1_FIX} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      obtain ⟨y, hy⟩ := hsne
      have hy' := hss (Finset.mem_coe.mpr hy)
      rw [mem_singleton_iff] at hy'
      refine ⟨hy' ▸ hy, fun x hx => ?_⟩
      have := hss (Finset.mem_coe.mpr hx)
      rwa [mem_singleton_iff] at this
    rw [_root_.Geometry.SimplicialComplex.mem_vertices, ← hseq]
    exact hs

/-- 扇区里的子单形：`0 ∈ conv s` ⇒ `0 ∈ s`（`ℓ ≤ g`，`g = ℓ` 在 `t` 的凸包上，`g` 正定）。 -/
theorem zero_mem_of_mem_hull_FIX2 {s t : Finset ℂ} {ℓ : ℂ →L[ℝ] ℝ}
    (hle : ∀ z, ℓ z ≤ triGauge_FIX z) (hv : ∀ v ∈ t, triGauge_FIX v = ℓ v)
    (hsub : convexHull ℝ (s : Set ℂ) ⊆ convexHull ℝ (t : Set ℂ))
    (h0 : (0 : ℂ) ∈ convexHull ℝ (s : Set ℂ)) : (0 : ℂ) ∈ s := by
  obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp h0
  have hℓ : ∀ y ∈ s, ℓ y = triGauge_FIX y := fun y hy =>
    (triGauge_eq_on_hull_FIX hle hv y (hsub (subset_convexHull ℝ _ hy))).symm
  have hsum : ∑ y ∈ s, w y * ℓ y = 0 := by
    have := congrArg ℓ hwx
    rw [map_sum, map_zero] at this
    simpa only [map_smul, smul_eq_mul] using this
  have hnn : ∀ y ∈ s, 0 ≤ w y * ℓ y := fun y hy =>
    mul_nonneg (hw0 y hy) (by rw [hℓ y hy]; exact triGauge_nonneg_FIX y)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum
  by_contra h0s
  have : ∑ y ∈ s, w y = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    have hy0 : y ≠ 0 := fun h => h0s (h ▸ hy)
    have := hz y hy
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso
      have := triGauge_pos_FIX hy0
      rw [← hℓ y hy] at this
      linarith
  rw [hw1] at this
  exact one_ne_zero this

theorem uniqueDiffOn_hull_R_FIX2 {R : _root_.Geometry.SimplicialComplex ℝ ℂ} {s : Finset ℂ}
    (hs : s ∈ R.faces) (hc : s.card = 3) : UniqueDiffOn ℝ (convexHull ℝ (s : Set ℂ)) := by
  refine uniqueDiffOn_convex (convex_convexHull ℝ _) ?_
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  have h := (R.indep hs).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
    (by rw [Fintype.card_coe, hc, Complex.finrank_real_complex])
  simpa using h

theorem subdiv_smooth_FIX2 {R : _root_.Geometry.SimplicialComplex ℝ ℂ}
    (hRs : ∀ s ∈ R.faces, s.card = 3 → ∃ t ∈ triComplex_FIX.faces, t.card = 3 ∧
      convexHull ℝ (s : Set ℂ) ⊆ convexHull ℝ (t : Set ℂ)) :
    ∀ s ∈ R.faces, s.card = 3 →
      ContDiffOn ℝ ∞ radialGrid_FIX (convexHull ℝ (s : Set ℂ) \ (s : Set ℂ)) := by
  intro s hs hc
  obtain ⟨t, ht, htc, hsub⟩ := hRs s hs hc
  obtain ⟨-, ℓ, hle, hv⟩ := face_sector_data_FIX ht htc
  refine ((contDiffOn_sectorMap_FIX ℓ).mono ?_).congr ?_
  · rintro z ⟨hzc, hzs⟩ hz0
    rw [hz0] at hzc hzs
    exact hzs (Finset.mem_coe.mpr (zero_mem_of_mem_hull_FIX2 hle hv hsub hzc))
  · intro z hz
    exact radialGrid_eqOn_sector_FIX hle hv (hsub hz.1)

theorem subdiv_rank_FIX2 {R : _root_.Geometry.SimplicialComplex ℝ ℂ}
    (hRs : ∀ s ∈ R.faces, s.card = 3 → ∃ t ∈ triComplex_FIX.faces, t.card = 3 ∧
      convexHull ℝ (s : Set ℂ) ⊆ convexHull ℝ (t : Set ℂ)) :
    ∀ s ∈ R.faces, s.card = 3 → ∀ z ∈ convexHull ℝ (s : Set ℂ) \ (s : Set ℂ),
      Function.Injective (fderivWithin ℝ radialGrid_FIX (convexHull ℝ (s : Set ℂ)) z) := by
  intro s hs hc z hz
  obtain ⟨t, ht, htc, hsub⟩ := hRs s hs hc
  obtain ⟨-, ℓ, hle, hv⟩ := face_sector_data_FIX ht htc
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz.2 (Finset.mem_coe.mpr (zero_mem_of_mem_hull_FIX2 hle hv hsub hz.1))
  have hℓz : 0 < ℓ z := (triGauge_eq_on_hull_FIX hle hv z (hsub hz.1)) ▸ triGauge_pos_FIX hz0
  have heq : EqOn radialGrid_FIX (sectorMap_FIX ℓ) (convexHull ℝ (s : Set ℂ)) :=
    fun x hx => radialGrid_eqOn_sector_FIX hle hv (hsub hx)
  rw [fderivWithin_congr heq (heq hz.1),
    DifferentiableAt.fderivWithin ((contDiffAt_sectorMap_FIX ℓ hz0).differentiableAt (by simp))
      (uniqueDiffOn_hull_R_FIX2 hs hc z hz.1)]
  exact injective_fderiv_sectorMap_FIX ℓ hℓz

theorem subdiv_dim_le_FIX2 (R : _root_.Geometry.SimplicialComplex ℝ ℂ) :
    ∀ s ∈ R.faces, s.card ≤ 3 := by
  intro s hs
  have h := (R.indep hs).card_le_finrank_succ
  have h2 := (Submodule.finrank_le (vectorSpan ℝ (range ((↑) : s → ℂ)))).trans_eq
    Complex.finrank_real_complex
  rw [Fintype.card_coe] at h
  omega

end DifferentialGeometry.Geometry
