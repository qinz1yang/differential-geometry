import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusDiskLocalization
import DifferentialGeometry.Topology.PiecewiseLinear.PrismLateralCircleSides

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem disk_chart_boundary_eq {D : Set E} {p q : (Fin 3 → ℝ) → E}
    (hp : IsPLHomeomorphOn p (stdSimplex ℝ (Fin 3)) D)
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) D) :
    p '' stdSimplexBoundary 2 = q '' stdSimplexBoundary 2 := by
  classical
  obtain ⟨K, hKfin, hKspace⟩ := (IsPLBall.isPolyhedron ⟨p, hp⟩).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  rw [hp.image_stdSimplexBoundary_eq_boundaryComplex K hKspace,
    hq.image_stdSimplexBoundary_eq_boundaryComplex K hKspace]

theorem exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks
    {S D₀ D₁ J₀ J₁ : Set E} (hS : IsPLSphere 2 S)
    {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hb₀ : r₀ '' stdSimplexBoundary 2 = J₀)
    (hb₁ : r₁ '' stdSimplexBoundary 2 = J₁)
    (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ S ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J₀ ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = J₁ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₀ = J₀ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₁ = J₁ ∧
      S ⊆ D₀ ∪ D₁ ∪ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  let Δ := stdSimplex ℝ (Fin 3)
  let A := stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1
  let P := Δ ×ˢ ({0, 1} : Set ℝ) ∪ A
  have hΔ : IsPolyhedron Δ := (isPLBall_stdSimplex 2).isPolyhedron
  have hι₀ := hΔ.isPLHomeomorphOn_prod_const (0 : ℝ)
  have hι₁ := hΔ.isPLHomeomorphOn_prod_const (1 : ℝ)
  have hE₀P : Δ ×ˢ ({0} : Set ℝ) ⊆ P := fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩
  have hE₁P : Δ ×ˢ ({1} : Set ℝ) ⊆ P := fun _ hx => Or.inl ⟨hx.1, Or.inr hx.2⟩
  have hEdis : Disjoint (Δ ×ˢ ({0} : Set ℝ)) (Δ ×ˢ ({1} : Set ℝ)) := by
    refine disjoint_left.mpr fun x hx hy => ?_
    exact zero_ne_one ((show x.2 = 0 from hx.2).symm.trans hy.2)
  obtain ⟨φ, hφ, hφ₀, hφ₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk
    isPLSphere_stdSimplex_prism_boundary hS
    ((isPLBall_stdSimplex 2).of_isPLHomeomorphOn hι₀) hE₀P
    ((isPLBall_stdSimplex 2).of_isPLHomeomorphOn hι₁) hE₁P hEdis
    ⟨r₁, hr₁⟩ hD₁S hdis (hι₀.symm.trans hr₀) hD₀S
  have hφD₀ : φ '' (Δ ×ˢ ({0} : Set ℝ)) = D₀ :=
    hφ₀.image_eq.trans (hι₀.symm.trans hr₀).image_eq
  have hφD₁ : φ '' (Δ ×ˢ ({1} : Set ℝ)) = D₁ := hφ₁
  have hApoly : IsPolyhedron A := by
    have hbd := (isPLSphere_simplexBoundary_std 1).isPolyhedron
    rw [simplexBoundary_stdVertices_space] at hbd
    exact hbd.prod isHPolytope_Icc.isPolyhedron
  have hAP : A ⊆ P := subset_union_right
  have h₀ : φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J₀ := by
    have hmap := hφ.restrict
      ((isPLBall_stdSimplex 2).of_isPLHomeomorphOn hι₀).isPolyhedron hE₀P
    rw [hφD₀] at hmap
    have h := disk_chart_boundary_eq (hι₀.trans hmap) hr₀
    simpa only [image_comp, prod_singleton, hb₀] using h
  have h₁ : φ '' (stdSimplexBoundary 2 ×ˢ {1}) = J₁ := by
    have hmap := hφ.restrict
      ((isPLBall_stdSimplex 2).of_isPLHomeomorphOn hι₁).isPolyhedron hE₁P
    rw [hφD₁] at hmap
    have h := disk_chart_boundary_eq (hι₁.trans hmap) hr₁
    simpa only [image_comp, prod_singleton, hb₁] using h
  refine ⟨φ, hφ.restrict hApoly hAP, (image_mono hAP).trans hφ.image_eq.subset,
    h₀, h₁, ?_, ?_, ?_⟩
  · rw [← hφD₀, ← hφ.bijOn.injOn.image_inter hAP hE₀P, ← h₀]
    congr 1
    ext x
    change (x.1 ∈ stdSimplexBoundary 2 ∧ x.2 ∈ Icc (0 : ℝ) 1) ∧
      (x.1 ∈ Δ ∧ x.2 = 0) ↔ x.1 ∈ stdSimplexBoundary 2 ∧ x.2 = 0
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2.2⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, by simp only [hxt, mem_Icc]; exact ⟨le_rfl, zero_le_one⟩⟩, hx.1, hxt⟩
  · rw [← hφD₁, ← hφ.bijOn.injOn.image_inter hAP hE₁P, ← h₁]
    congr 1
    ext x
    change (x.1 ∈ stdSimplexBoundary 2 ∧ x.2 ∈ Icc (0 : ℝ) 1) ∧
      (x.1 ∈ Δ ∧ x.2 = 1) ↔ x.1 ∈ stdSimplexBoundary 2 ∧ x.2 = 1
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2.2⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨hx, by simp only [hxt, mem_Icc]; exact ⟨zero_le_one, le_rfl⟩⟩, hx.1, hxt⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hφ.image_eq.symm ▸ hx
    rcases hy with ⟨hyΔ, hy₀ | hy₁⟩ | hyA
    · exact Or.inl (Or.inl (hφD₀ ▸ mem_image_of_mem φ ⟨hyΔ, hy₀⟩))
    · exact Or.inl (Or.inr (hφD₁ ▸ mem_image_of_mem φ ⟨hyΔ, hy₁⟩))
    · exact Or.inr (mem_image_of_mem φ hyA)

theorem exists_isPLHomeomorphOn_lateral_annulus_of_disjoint_disks
    {S D₀ D₁ J₀ J₁ : Set E} (hS : IsPLSphere 2 S)
    {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hb₀ : r₀ '' stdSimplexBoundary 2 = J₀)
    (hb₁ : r₁ '' stdSimplexBoundary 2 = J₁)
    (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ S ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J₀ ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = J₁ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₀ = J₀ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₁ = J₁ := by
  obtain ⟨φ, hφ, hφS, hφ₀, hφ₁, hB₀, hB₁, -⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks
      hS hr₀ hr₁ hb₀ hb₁ hD₀S hD₁S hdis
  exact ⟨φ, hφ, hφS, hφ₀, hφ₁, hB₀, hB₁⟩


omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem disjoint_outer_disks {S D D' R R' J L : Set E}
    (hDU : D ∪ D' = S) (hDI : D ∩ D' = J)
    (hRU : R ∪ R' = S) (hRI : R ∩ R' = L)
    (hD : IsPreconnected D) (hR : IsClosed R) (hR' : IsClosed R')
    (hLD' : L ⊆ D') (hJL : Disjoint J L)
    (hanchor : ((D ∩ R) ∩ Lᶜ).Nonempty) : Disjoint D R' := by
  have hDL : Disjoint D L := disjoint_left.mpr fun x hxD hxL =>
    disjoint_left.mp hJL (hDI ▸ ⟨hxD, hLD' hxL⟩) hxL
  have hDS : D ⊆ S := hDU ▸ subset_union_left
  have hDR : D ⊆ R := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hD R R' hR hR'
        (hRU ▸ hDS) (hRI ▸ hDL.inter_eq) with h | h
    · exact h
    · obtain ⟨x, ⟨hxD, hxR⟩, hxL⟩ := hanchor
      exact (hxL (hRI ▸ ⟨hxR, h hxD⟩)).elim
  exact disjoint_left.mpr fun x hxD hxR' =>
    disjoint_left.mp hDL hxD (hRI ▸ ⟨hDR hxD, hxR'⟩)

private theorem exists_annular_band_cover_of_end_disks
    {S A A₀ A₁ D₀ D₁ J₀ J₁ : Set E} (hS : IsPLSphere 2 S)
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S)
    {r₀ r₁ : (Fin 3 → ℝ) → E}
    (hr₀ : IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀)
    (hr₁ : IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁)
    (hb₀ : r₀ '' stdSimplexBoundary 2 = J₀)
    (hb₁ : r₁ '' stdSimplexBoundary 2 = J₁)
    (hD₀S : D₀ ⊆ S) (hD₁S : D₁ ⊆ S) (hdis : Disjoint D₀ D₁)
    (hJ₀A : J₀ ⊆ A) (hJ₀end : Disjoint J₀ (A₀ ∪ A₁))
    (hJ₁end : Disjoint J₁ (A₀ ∪ A₁)) (hends : A₀ ∪ A₁ ⊆ D₀ ∪ D₁) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J₀ ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = J₁ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₀ = J₀ ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₁ = J₁ ∧
      S ⊆ D₀ ∪ D₁ ∪ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨φ, hφ, hφS, hφ₀, hφ₁, hB₀, hB₁, hcover⟩ :=
    exists_isPLHomeomorphOn_lateral_annulus_cover_of_disjoint_disks hS hr₀ hr₁ hb₀ hb₁
      hD₀S hD₁S hdis
  refine ⟨φ, hφ, ?_, hφ₀, hφ₁, hB₀, hB₁, hcover⟩
  have hconn := ((isConnected_stdSimplexBoundary 0).prod
    (isConnected_Icc (zero_le_one : (0 : ℝ) ≤ 1))).image φ
      hφ.isPiecewiseAffineOn.continuousOn
  apply hS.subset_annulus_of_isPreconnected_of_disjoint_boundary hA hAS hφS
    hconn.isPreconnected
  · obtain ⟨x, hx⟩ := (hb₀ ▸ hr₀.isPLSphere_image_stdSimplexBoundary).nonempty
    refine ⟨x, ?_, hJ₀A hx⟩
    rw [← hφ₀] at hx
    exact image_mono (prod_mono_right (by simp)) hx
  · refine disjoint_left.mpr fun x hxB hxend => ?_
    rcases hends hxend with hxD | hxD
    · exact disjoint_left.mp hJ₀end (hB₀ ▸ ⟨hxB, hxD⟩) hxend
    · exact disjoint_left.mp hJ₁end (hB₁ ▸ ⟨hxB, hxD⟩) hxend

theorem IsPLSphere.exists_annular_band_with_end_caps
    {S A A₀ A₁ J L : Set E} (hS : IsPLSphere 2 S)
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S)
    (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L)
    (hJA : J ⊆ A) (hLA : L ⊆ A) (hJL : Disjoint J L)
    (hJend : Disjoint J (A₀ ∪ A₁)) (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J)
    (hLess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = L) :
    ∃ (D₀ D₁ : Set E) (r₀ r₁ : (Fin 3 → ℝ) → E) (φ : (Fin 3 → ℝ) × ℝ → E),
      IsPLHomeomorphOn r₀ (stdSimplex ℝ (Fin 3)) D₀ ∧
      IsPLHomeomorphOn r₁ (stdSimplex ℝ (Fin 3)) D₁ ∧
      r₀ '' stdSimplexBoundary 2 = J ∧ r₁ '' stdSimplexBoundary 2 = L ∧
      D₀ ⊆ S ∧ D₁ ⊆ S ∧ Disjoint D₀ D₁ ∧
      ((A₀ ⊆ D₀ ∧ A₁ ⊆ D₁) ∨ (A₁ ⊆ D₀ ∧ A₀ ⊆ D₁)) ∧
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = L ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₀ = J ∧
      (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∩ D₁ = L ∧
      S ⊆ D₀ ∪ D₁ ∪ φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) := by
  obtain ⟨D₀, D₁, r₀, r₁, hDU, hDI, hr₀, hr₁, hb₀, hb₁, hA₀D, hA₁D⟩ :=
    (hS.exists_disk_in_annulus_or_separating_ends hA hAS hJ hJA hJend).resolve_left hJess
  obtain ⟨R₀, R₁, q₀, q₁, hRU, hRI, hq₀, hq₁, hc₀, hc₁, hA₀R, hA₁R⟩ :=
    (hS.exists_disk_in_annulus_or_separating_ends hA hAS hL hLA hLend).resolve_left hLess
  have hD₀S : D₀ ⊆ S := hDU ▸ subset_union_left
  have hD₁S : D₁ ⊆ S := hDU ▸ subset_union_right
  have hR₀S : R₀ ⊆ S := hRU ▸ subset_union_left
  have hR₁S : R₁ ⊆ S := hRU ▸ subset_union_right
  have hAne : A₀.Nonempty ∧ A₁.Nonempty := by
    obtain ⟨ψ, rfl, rfl⟩ := hA
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    constructor
    · exact ⟨ψ (⟨x, hx⟩, ⟨0, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩
    · exact ⟨ψ (⟨x, hx⟩, ⟨1, by norm_num⟩), ⟨_, ⟨_, rfl, rfl⟩, rfl⟩⟩
  have hLside : L ⊆ D₀ ∨ L ⊆ D₁ :=
    isPreconnected_iff_subset_of_disjoint_closed.mp hL.isConnected.isPreconnected D₀ D₁
      (IsPLBall.isPolyhedron ⟨r₀, hr₀⟩).isClosed
      (IsPLBall.isPolyhedron ⟨r₁, hr₁⟩).isClosed
      (hDU ▸ hLA.trans hAS) (hDI ▸ hJL.symm.inter_eq)
  rcases hLside with hLD₀ | hLD₁
  · have hdis : Disjoint D₁ R₀ := by
      apply disjoint_outer_disks (by rwa [union_comm] : D₁ ∪ D₀ = S)
        (by rwa [inter_comm] : D₁ ∩ D₀ = J)
        (by rwa [union_comm] : R₁ ∪ R₀ = S)
        (by rwa [inter_comm] : R₁ ∩ R₀ = L)
        (IsPLBall.isConnected ⟨r₁, hr₁⟩).isPreconnected
        (IsPLBall.isPolyhedron ⟨q₁, hq₁⟩).isClosed
        (IsPLBall.isPolyhedron ⟨q₀, hq₀⟩).isClosed hLD₀ hJL
      obtain ⟨x, hx⟩ := hAne.2
      exact ⟨x, ⟨hA₁D hx, hA₁R hx⟩,
        fun hxL => disjoint_left.mp hLend hxL (Or.inr hx)⟩
    obtain ⟨φ, hφ, hφA, hzero, hone, hB₀, hB₁, hcover⟩ :=
      exists_annular_band_cover_of_end_disks hS hA hAS hr₁ hq₀ hb₁ hc₀
        hD₁S hR₀S hdis hJA hJend hLend
        (union_subset (hA₀R.trans subset_union_right) (hA₁D.trans subset_union_left))
    exact ⟨D₁, R₀, r₁, q₀, φ, hr₁, hq₀, hb₁, hc₀, hD₁S, hR₀S, hdis,
      Or.inr ⟨hA₁D, hA₀R⟩, hφ, hφA, hzero, hone, hB₀, hB₁, hcover⟩
  · have hdis : Disjoint D₀ R₁ := by
      apply disjoint_outer_disks hDU hDI hRU hRI
        (IsPLBall.isConnected ⟨r₀, hr₀⟩).isPreconnected
        (IsPLBall.isPolyhedron ⟨q₀, hq₀⟩).isClosed
        (IsPLBall.isPolyhedron ⟨q₁, hq₁⟩).isClosed hLD₁ hJL
      obtain ⟨x, hx⟩ := hAne.1
      exact ⟨x, ⟨hA₀D hx, hA₀R hx⟩,
        fun hxL => disjoint_left.mp hLend hxL (Or.inl hx)⟩
    obtain ⟨φ, hφ, hφA, hzero, hone, hB₀, hB₁, hcover⟩ :=
      exists_annular_band_cover_of_end_disks hS hA hAS hr₀ hq₁ hb₀ hc₁
        hD₀S hR₁S hdis hJA hJend hLend
        (union_subset (hA₀D.trans subset_union_left) (hA₁R.trans subset_union_right))
    exact ⟨D₀, R₁, r₀, q₁, φ, hr₀, hq₁, hb₀, hc₁, hD₀S, hR₁S, hdis,
      Or.inl ⟨hA₀D, hA₁R⟩, hφ, hφA, hzero, hone, hB₀, hB₁, hcover⟩

theorem IsPLSphere.exists_annular_band_of_essential_pair
    {S A A₀ A₁ J L : Set E} (hS : IsPLSphere 2 S)
    (hA : IsAnnulusOn A A₀ A₁) (hAS : A ⊆ S)
    (hJ : IsPLSphere 1 J) (hL : IsPLSphere 1 L)
    (hJA : J ⊆ A) (hLA : L ⊆ A) (hJL : Disjoint J L)
    (hJend : Disjoint J (A₀ ∪ A₁)) (hLend : Disjoint L (A₀ ∪ A₁))
    (hJess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = J)
    (hLess : ¬ ∃ (D : Set E) (r : (Fin 3 → ℝ) → E),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) D ∧ D ⊆ A ∧
        r '' stdSimplexBoundary 2 = L) :
    ∃ φ : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn φ (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)
        (φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1)) ∧
      φ '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) ⊆ A ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {0}) = J ∧
      φ '' (stdSimplexBoundary 2 ×ˢ {1}) = L := by
  obtain ⟨-, -, -, -, φ, -, -, -, -, -, -, -, -, hφ, hφA, hzero, hone, -⟩ :=
    hS.exists_annular_band_with_end_caps hA hAS hJ hL hJA hLA hJL hJend hLend hJess hLess
  exact ⟨φ, hφ, hφA, hzero, hone⟩

end DifferentialGeometry.Topology.PiecewiseLinear
