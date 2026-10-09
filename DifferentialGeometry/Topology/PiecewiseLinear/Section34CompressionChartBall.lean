/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutsideUpdate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section ChartBall

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂} {f₁ : M₁ → M₂}

theorem exists_section34Compression_of_chartBall
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {c : OpenPartialHomeomorph M₂ E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂) (hfsc : fbl s ⊆ c.source)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    (hTcomp : IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s))
    {O₀ : Set M₂} (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ O₀ =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ O₀)
    {G Oc Sel : Set E3} (hG : IsPLBall 3 G) (hGt : G ⊆ c.target) (hGO₀ : c.symm '' G ⊆ O₀)
    (hrim : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior G) {Z : Set M₂}
    (hGZ : c.symm '' G ⊆ fbl s ∪ Z)
    (hZV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 →
      Disjoint Z (section34VertexBallImage src f₁ w))
    (hZs : ∀ s', s' ≠ s → Z ∩ fbl s' ⊆ interior (⋃ w, section34VertexBallImage src f₁ w))
    (hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t)
        (H t.1 \ (section34TetraObstacle (section34VertexBallImage src f₁) fbl t ∪ Z)) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' w.1, r y = y)
    (hOc : IsOpen Oc) (hfrO : frontier G ∩ Oc = frontier (c '' fbl s) ∩ Oc)
    (hk2 : frontier G ∩ frontier (c '' section34FaceTorus (section34VertexBallImage src f₁) s) ⊆
      Oc)
    (hk4 : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      frontier G ∩ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) ⊆ Oc)
    (hk3 : frontier G ∩ frontier (c '' section34FaceTorus (section34VertexBallImage src f₁) s) =
      frontier (c '' fbl s) ∩ frontier (c '' section34FaceTorus (section34VertexBallImage src f₁) s)
        ∩ Sel)
    (hSel : IsCompact Sel) (hSelt : Sel ⊆ c.target) {y₀ : M₂}
    (hy₀ : y₀ ∈ fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))
    (hy₀S : c y₀ ∉ Sel)
    (h7 : CarriesFirstHomologyOnto (c.symm '' (frontier G ∩
      frontier (c '' section34FaceTorus (section34VertexBallImage src f₁) s)))
      (section34FaceTorus (section34VertexBallImage src f₁) s)) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, -, -, -, -, -, -, -, -⟩ := id hinv
  set T := section34FaceTorus (section34VertexBallImage src f₁) s with hTdef
  set Sg := frontier (⋃ w', section34VertexBallImage src f₁ w') with hSgdef
  have hfbs : fblBd s ⊆ fbl s := (hfcell s).boundary_subset
  set Θ := frontier (c '' T) with hΘdef
  have hΘeq : c '' frontier T = Θ := c.image_frontier_of_isCompact hTcomp hTc
  have hfrTc : frontier T ⊆ c.source := hTcomp.isClosed.frontier_subset.trans hTc
  have hmemT : ∀ y ∈ c.source, (y ∈ frontier T ↔ c y ∈ Θ) := by
    intro y hy
    rw [← hΘeq]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfrTc hy') hy hyy]
  obtain ⟨-, hPfr⟩ := (hfcell s).isPLBall_image_chart hc hfsc
  have hmemP : ∀ y ∈ c.source, (y ∈ fblBd s ↔ c y ∈ frontier (c '' fbl s)) := by
    intro y hy
    rw [← hPfr]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfsc (hfbs hy')) hy hyy]
  have hGpoly : IsPolyhedron G := hG.isPolyhedron
  have hGc : IsClosed G := hGpoly.isClosed
  have hfrGG : frontier G ⊆ G := hGc.frontier_subset
  obtain ⟨r, hr'⟩ := id hG
  have hfr : r '' stdSimplexBoundary 3 = frontier G :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr'
  have hFcell : IsPLCellOn 3 (c.symm '' G) (c.symm '' frontier G) :=
    ⟨G, r, c.symm, hr', isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hGpoly hGt, rfl,
      by rw [hfr]⟩
  have hFc : c.symm '' G ⊆ c.source := by
    rintro _ ⟨x, hx, rfl⟩
    exact c.map_target (hGt hx)
  have hFbF : c.symm '' frontier G ⊆ c.symm '' G := image_mono hfrGG
  have hmemFb : ∀ y ∈ c.source, (y ∈ c.symm '' frontier G ↔ c y ∈ frontier G) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [c.right_inv (hGt (hfrGG hx))]
      exact hx
    · exact fun hy' => ⟨c y, hy', c.left_inv hy⟩
  have hrimc : h '' simplexRim 𝒦 s.1 ⊆ c.source := (hfrim s).trans (interior_subset.trans hfsc)
  have hFrim : h '' simplexRim 𝒦 s.1 ⊆ interior (c.symm '' G) := by
    intro y hy
    refine interior_maximal (image_mono interior_subset)
      (c.isOpen_image_symm_of_subset_target isOpen_interior (interior_subset.trans hGt)) ?_
    exact ⟨c y, hrim (mem_image_of_mem c hy), c.left_inv (hrimc hy)⟩
  have hOM : IsOpen (c.source ∩ c ⁻¹' Oc) := c.isOpen_inter_preimage hOc
  have hFbO : c.symm '' frontier G ∩ (c.source ∩ c ⁻¹' Oc) =
      fblBd s ∩ (c.source ∩ c ⁻¹' Oc) := by
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      refine ⟨(hmemP y hyO.1).mpr ?_, hyO⟩
      have h1 : c y ∈ frontier G ∩ Oc := ⟨(hmemFb y hyO.1).mp hy, hyO.2⟩
      rw [hfrO] at h1
      exact h1.1
    · rintro ⟨hy, hyO⟩
      refine ⟨(hmemFb y hyO.1).mpr ?_, hyO⟩
      have h1 : c y ∈ frontier (c '' fbl s) ∩ Oc := ⟨(hmemP y hyO.1).mp hy, hyO.2⟩
      rw [← hfrO] at h1
      exact h1.1
  have hSgF : ∀ y ∈ c.symm '' G, (y ∈ Sg ↔ y ∈ frontier T) := by
    intro y hy
    have hyO := hGO₀ hy
    constructor
    · intro h1
      have h2 : y ∈ Sg ∩ O₀ := ⟨h1, hyO⟩
      rw [hSgO₀] at h2
      exact h2.1
    · intro h1
      have h2 : y ∈ frontier T ∩ O₀ := ⟨h1, hyO⟩
      rw [← hSgO₀] at h2
      exact h2.1
  have hZO : c.symm '' frontier G ∩ Sg ⊆ c.source ∩ c ⁻¹' Oc := by
    rintro y ⟨hy, hySg⟩
    have hyc := hFc (hFbF hy)
    exact ⟨hyc, hk2 ⟨(hmemFb y hyc).mp hy, (hmemT y hyc).mp ((hSgF y (hFbF hy)).mp hySg)⟩⟩
  have hEO : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      c.symm '' frontier G ∩ section34SplitDiskImage srcBd f₁ e ⊆ c.source ∩ c ⁻¹' Oc := by
    rintro e y ⟨hy, hye⟩
    have hyc := hFc (hFbF hy)
    exact ⟨hyc, hk4 e ⟨(hmemFb y hyc).mp hy, y, ⟨hye, hyc⟩, rfl⟩⟩
  have hSelc : IsClosed (c.symm '' Sel) :=
    (hSel.image_of_continuousOn (c.continuousOn_symm.mono hSelt)).isClosed
  have hmemSel : ∀ y ∈ c.source, (y ∈ c.symm '' Sel ↔ c y ∈ Sel) := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [c.right_inv (hSelt hx)]
      exact hx
    · exact fun hy' => ⟨c y, hy', c.left_inv hy⟩
  have hZF : c.symm '' frontier G ∩ Sg = fblBd s ∩ Sg ∩ c.symm '' Sel := by
    ext y
    constructor
    · rintro ⟨hy, hySg⟩
      have hyc := hFc (hFbF hy)
      have hx : c y ∈ frontier G ∩ Θ :=
        ⟨(hmemFb y hyc).mp hy, (hmemT y hyc).mp ((hSgF y (hFbF hy)).mp hySg)⟩
      rw [hk3] at hx
      exact ⟨⟨(hmemP y hyc).mpr hx.1.1, hySg⟩, (hmemSel y hyc).mpr hx.2⟩
    · rintro ⟨⟨hy, hySg⟩, hyS⟩
      have hyc := hfsc (hfbs hy)
      have hyT : y ∈ frontier T := by
        have h2 : y ∈ Sg ∩ O₀ := ⟨hySg, hfO₀ (hfbs hy)⟩
        rw [hSgO₀] at h2
        exact h2.1
      have hx : c y ∈ frontier (c '' fbl s) ∩ Θ ∩ Sel :=
        ⟨⟨(hmemP y hyc).mp hy, (hmemT y hyc).mp hyT⟩, (hmemSel y hyc).mp hyS⟩
      rw [← hk3] at hx
      exact ⟨(hmemFb y hyc).mpr hx.1, hySg⟩
  have hy₀F : y₀ ∉ c.symm '' Sel := fun h => hy₀S ((hmemSel y₀ (hfsc (hfbs hy₀.1))).mp h)
  obtain ⟨h5, h6, h8, h9, hcount, hpcount⟩ := section34FaceBall_fields_of_inter_eq hinv hOM
    hSelc hFbO hZO hEO hZF hy₀ hy₀F
  have h7' : CarriesFirstHomologyOnto (c.symm '' frontier G ∩ frontier T) T := by
    convert h7 using 1
    ext y
    constructor
    · rintro ⟨hy, hyT⟩
      have hyc := hFc (hFbF hy)
      exact ⟨c y, ⟨(hmemFb y hyc).mp hy, (hmemT y hyc).mp hyT⟩, c.left_inv hyc⟩
    · rintro ⟨x, ⟨hx, hxΘ⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      have hxt : x ∈ c.target := hGt (hfrGG hx)
      rw [hmemT _ (c.map_target hxt), c.right_inv hxt]
      exact hxΘ
  refine ⟨Function.update fbl s (c.symm '' G), Function.update fblBd s (c.symm '' frontier G),
    section34FaceBallInvariants_update_of_overlap hinv hFcell hFrim hGZ hZV hZs hZH hr h5 h6 h7'
      h8 h9,
    fun s' hs' => ⟨Function.update_of_ne hs' _ _, Function.update_of_ne hs' _ _⟩, ?_, ?_⟩
  · simp only [section34TraceCount, section34TraceComponents, Function.update_self]
    exact hcount
  · simp only [section34CrossingCount, Function.update_self]
    exact hpcount

end ChartBall

end DifferentialGeometry.Topology.PiecewiseLinear
