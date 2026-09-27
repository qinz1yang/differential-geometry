/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartConjugate
import DifferentialGeometry.Topology.PiecewiseLinear.HalfSpaceGeneralPosition
import Mathlib.Topology.Homotopy.Basic

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable local instance euclideanDecidableEq :
    DecidableEq (EuclideanSpace ℝ (Fin 3)) := Classical.decEq _

open Classical in
theorem exists_small_isPL_homeomorph_generalPosition_homotopy_in_boundary_chart
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (C Bd : Set X) (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x))
    (hBd : ∀ x ∈ e.source, x ∈ Bd ↔ ℓ (e x) = 0)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set X} (hU : IsOpen U) (hKU : K.space ⊆ e '' (e.source ∩ U))
    (hLU : L.space ⊆ e '' (e.source ∩ U)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : X ≃ₜ X) (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPL 3 3 h ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      MapsTo h e.source e.source ∧ (∀ x, h x ∈ C ↔ x ∈ C) ∧
      (∀ x, h x ∈ Bd ↔ x ∈ Bd) ∧
      IsPLHomeomorphOn (e ∘ h ∘ e.symm) K.space ((e ∘ h ∘ e.symm) '' K.space) ∧
      G.faces.Finite ∧ G.space = (e ∘ h ∘ e.symm) '' K.space ∩ L.space ∧
      IsCombinatorialManifoldWithBoundary 1 G ∧
      (∀ z ∈ G.space,
        (z ∈ e '' (e.source ∩ Bd) ∧
          HasPLBoundaryCrossingAt (e '' (e.source ∩ C))
            ((e ∘ h ∘ e.symm) '' K.space) L.space z) ∨
        (z ∉ e '' (e.source ∩ Bd) ∧
          HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z)) ∧
      ∃ H : ContinuousMap.Homotopy (ContinuousMap.id X) (h : ContinuousMap X X),
        (∀ t x, dist (H (t, x)) x < ε) ∧
        ∀ t, EqOn (fun x => H (t, x)) id Uᶜ ∧
          MapsTo (fun x => H (t, x)) U U ∧
          MapsTo (fun x => H (t, x)) e.source e.source ∧
          (∀ x, H (t, x) ∈ C ↔ x ∈ C) ∧ (∀ x, H (t, x) ∈ Bd ↔ x ∈ Bd) := by
  let V := e '' (e.source ∩ U)
  have hV : IsOpen V := e.isOpen_image_source_inter hU
  have hVt : V ⊆ e.target := by
    rintro z ⟨x, hx, rfl⟩
    exact e.map_source hx.1
  have hcompact : IsCompact (K.space ∪ L.space) :=
    (isPolyhedron_space K).isCompact.union (isPolyhedron_space L).isCompact
  obtain ⟨r, hr, hrV⟩ := hcompact.exists_cthickening_subset_open hV (union_subset hKU hLU)
  let T := cthickening r (K.space ∪ L.space)
  let O := thickening r (K.space ∪ L.space)
  have hT : IsCompact T := isCompact_of_isClosed_isBounded isClosed_cthickening
    hcompact.isBounded.cthickening
  have hTt : T ⊆ e.target := hrV.trans hVt
  have hOT : O ⊆ T := thickening_subset_cthickening r (K.space ∪ L.space)
  obtain ⟨ρ, hρ, hρV⟩ := hT.exists_cthickening_subset_open hV hrV
  obtain ⟨δ, hδ, hδbound⟩ := e.exists_uniform_conjugateMap_radius hT hTt hε
  obtain ⟨k, G, hk, hkclose, hkfix, hkheight, hGfinite, hGspace, hGman, hGcross⟩ :=
    exists_small_homeomorph_generalPosition_in_halfSpace K L hK hL (by simp) ℓ hℓ
      hKℓ hLℓ hKboundary hLboundary (U := O) isOpen_thickening
      (subset_union_left.trans (self_subset_thickening hr _))
      (subset_union_right.trans (self_subset_thickening hr _)) (lt_min hδ hρ)
  let k₀ : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := k
      invFun := Function.invFunOn k univ
      left_inv := fun z => hk.bijOn.invOn_invFunOn.1 (mem_univ z)
      right_inv := fun z => hk.bijOn.invOn_invFunOn.2 (mem_univ z)
      continuous_toFun := continuousOn_univ.mp hk.isPiecewiseAffineOn.continuousOn
      continuous_invFun := continuousOn_univ.mp hk.isPiecewiseAffineOn_invFunOn.continuousOn }
  have hkT : EqOn k₀ id Tᶜ := fun z hz => hkfix (fun hzO => hz (hOT hzO))
  obtain ⟨hkmap, hclose⟩ :=
    hδbound k₀ (fun z _ => (hkclose z).trans_le (min_le_left δ ρ)) hkT
  let h := e.conjugateHomeomorph k₀ hT hTt hkT
  have hmap : MapsTo h e.source e.source := by
    intro x hx
    rw [show h x = e.conjugateMap k₀ x from rfl, e.conjugateMap_of_mem k₀ hx]
    exact e.map_target (hkmap (e.map_source hx))
  have hchart (x : X) (hx : x ∈ e.source) : e (h x) = k (e x) := by
    change e (e.conjugateMap k₀ x) = k (e x)
    rw [e.conjugateMap_of_mem k₀ hx, e.right_inv (hkmap (e.map_source hx))]
    rfl
  have hcoord : EqOn (e ∘ h ∘ e.symm) k K.space := by
    intro z hz
    have hzt := hVt (hKU hz)
    change e (h (e.symm z)) = k z
    rw [hchart _ (e.map_target hzt), e.right_inv hzt]
  have himage : (e ∘ h ∘ e.symm) '' K.space = k '' K.space := hcoord.image_eq
  have hCimage : e '' (e.source ∩ C) = e.target ∩ {z | 0 ≤ ℓ z} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.map_source hx.1, (hC x hx.1).mp hx.2⟩
    · rintro ⟨hz, hnonneg⟩
      refine ⟨e.symm z, ⟨e.map_target hz, (hC _ (e.map_target hz)).mpr ?_⟩, e.right_inv hz⟩
      rwa [e.right_inv hz]
  have hBdimage : e '' (e.source ∩ Bd) = e.target ∩ {z | ℓ z = 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨e.map_source hx.1, (hBd x hx.1).mp hx.2⟩
    · rintro ⟨hz, hzero⟩
      refine ⟨e.symm z, ⟨e.map_target hz, (hBd _ (e.map_target hz)).mpr ?_⟩, e.right_inv hz⟩
      rwa [e.right_inv hz]
  refine ⟨h, G, isPL_conjugateHomeomorph e he k₀ hk.isPiecewiseAffineOn hT hTt hkT,
    hclose, ?_, hmap, ?_, ?_, ?_, hGfinite, hGspace.trans ?_, hGman, ?_, ?_⟩
  · intro x hx
    apply e.conjugateMap_eqOn_compl hkT
    rintro ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwz⟩ := hrV hz
    have heq : e.symm z = w := by rw [← hwz, e.left_inv hw.1]
    exact hx (heq.symm ▸ hw.2)
  · intro x
    by_cases hx : x ∈ e.source
    · rw [hC _ (hmap hx), hC _ hx, hchart x hx]
      exact (hkheight (e x)).2
    · have heq : h x = x := e.conjugateMap_of_notMem k₀ hx
      rw [heq]
  · intro x
    by_cases hx : x ∈ e.source
    · rw [hBd _ (hmap hx), hBd _ hx, hchart x hx]
      exact (hkheight (e x)).1
    · have heq : h x = x := e.conjugateMap_of_notMem k₀ hx
      rw [heq]
  · rw [himage]
    exact (hk.restrict (isPolyhedron_space K) (subset_univ _)).congr hcoord
  · rw [himage]
  · intro z hz
    have hzt : z ∈ e.target := hVt (hLU (hGspace.subset hz).2)
    rw [himage]
    rcases hGcross z hz with ⟨hzero, hcross⟩ | ⟨hpos, hcross⟩
    · refine Or.inl ⟨hBdimage.symm ▸ ⟨hzt, hzero⟩, ?_⟩
      apply hcross.congr ?_ (Filter.Eventually.of_forall fun _ => Iff.rfl)
        (Filter.Eventually.of_forall fun _ => Iff.rfl)
      filter_upwards [e.open_target.mem_nhds hzt] with w hw
      rw [hCimage]
      exact (and_iff_right hw).symm
    · refine Or.inr ⟨?_, hcross⟩
      rw [hBdimage]
      exact fun hw => hpos.ne' hw.2
  · let J : ContinuousMap.Homotopy
        (ContinuousMap.id (EuclideanSpace ℝ (Fin 3)))
        (k₀ : ContinuousMap (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3))) :=
      { toFun := fun z => z.2 + (z.1 : ℝ) • (k₀ z.2 - z.2)
        continuous_toFun := continuous_snd.add
          ((continuous_subtype_val.comp continuous_fst).smul
            ((k₀.continuous.comp continuous_snd).sub continuous_snd))
        map_zero_left := fun z => by simp
        map_one_left := fun z => by simp }
    have hJclose (t : unitInterval) (z : EuclideanSpace ℝ (Fin 3)) :
        dist (J (t, z)) z < min δ ρ := by
      calc
        dist (J (t, z)) z = (t : ℝ) * dist (k z) z := by
          change dist (z + (t : ℝ) • (k z - z)) z = _
          simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1]
        _ ≤ dist (k z) z := by nlinarith [show 0 ≤ dist (k z) z from dist_nonneg, t.property.2]
        _ < min δ ρ := hkclose z
    have hJfix (t : unitInterval) : EqOn (fun z => J (t, z)) id Tᶜ := by
      intro z hz
      change z + (t : ℝ) • (k₀ z - z) = z
      rw [hkT hz, id_eq]
      simp
    have hJbound (t : unitInterval) := hδbound (fun z => J (t, z))
      (fun z _ => (hJclose t z).trans_le (min_le_left δ ρ)) (hJfix t)
    have hJheight (t : unitInterval) (z : EuclideanSpace ℝ (Fin 3)) :
        (ℓ (J (t, z)) = 0 ↔ ℓ z = 0) ∧ (0 ≤ ℓ (J (t, z)) ↔ 0 ≤ ℓ z) := by
      change (ℓ (z + (t : ℝ) • (k z - z)) = 0 ↔ ℓ z = 0) ∧
        (0 ≤ ℓ (z + (t : ℝ) • (k z - z)) ↔ 0 ≤ ℓ z)
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
      by_cases hz : ℓ z = 0
      · have hkz : ℓ (k z) = 0 := (hkheight z).1.mpr hz
        simp only [hz, hkz, sub_self, mul_zero, add_zero, le_refl, and_self]
      · by_cases hpos : 0 < ℓ z
        · have hkpos : 0 < ℓ (k z) := lt_of_le_of_ne ((hkheight z).2.mpr hpos.le)
            (fun hzero => hz ((hkheight z).1.mp hzero.symm))
          have hposJ : 0 < ℓ z + (t : ℝ) * (ℓ (k z) - ℓ z) :=
            (convex_Ioi (0 : ℝ)).add_smul_sub_mem hpos hkpos t.property
          exact ⟨iff_of_false hposJ.ne' hz, iff_of_true hposJ.le hpos.le⟩
        · have hneg : ℓ z < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hz
          have hkneg : ℓ (k z) < 0 := lt_of_not_ge
            (fun hnonneg => hneg.not_ge ((hkheight z).2.mp hnonneg))
          have hnegJ : ℓ z + (t : ℝ) * (ℓ (k z) - ℓ z) < 0 :=
            (convex_Iio (0 : ℝ)).add_smul_sub_mem hneg hkneg t.property
          exact ⟨iff_of_false hnegJ.ne hz, iff_of_false hnegJ.not_ge hneg.not_ge⟩
    have hHcontinuous : Continuous (fun z : unitInterval × X =>
        e.conjugateMap (fun y => J (z.1, y)) z.2) := by
      let E := (OpenPartialHomeomorph.refl unitInterval).prod e
      let F : unitInterval × EuclideanSpace ℝ (Fin 3) →
          unitInterval × EuclideanSpace ℝ (Fin 3) := fun z => (z.1, J z)
      have hF : Continuous F := continuous_fst.prodMk J.continuous_toFun
      have hFmap : MapsTo F E.target E.target := fun z hz =>
        ⟨mem_univ _, (hJbound z.1).1 hz.2⟩
      have hFfix : EqOn F id (univ ×ˢ T)ᶜ := by
        intro z hz
        have hzT : z.2 ∉ T := fun hzT => hz ⟨mem_univ _, hzT⟩
        change (z.1, J z) = z
        rw [show J z = z.2 from hJfix z.1 hzT]
      have hc := continuous_snd.comp
        (E.continuous_conjugateMap hF.continuousOn hFmap (isCompact_univ.prod hT)
          (fun z hz => ⟨mem_univ _, hTt hz.2⟩) hFfix)
      apply hc.congr
      intro z
      change (E.conjugateMap F z).2 = _
      by_cases hz : z.2 ∈ e.source
      · rw [E.conjugateMap_of_mem F ⟨mem_univ _, hz⟩, e.conjugateMap_of_mem _ hz]
        rfl
      · rw [E.conjugateMap_of_notMem F (fun hw => hz hw.2), e.conjugateMap_of_notMem _ hz]
    let H : ContinuousMap.Homotopy (ContinuousMap.id X) (h : ContinuousMap X X) :=
      { toFun := fun z => e.conjugateMap (fun y => J (z.1, y)) z.2
        continuous_toFun := hHcontinuous
        map_zero_left := fun x => by
          change e.conjugateMap (fun y => J (0, y)) x = x
          by_cases hx : x ∈ e.source
          · rw [e.conjugateMap_of_mem _ hx, J.apply_zero, ContinuousMap.id_apply, e.left_inv hx]
          · exact e.conjugateMap_of_notMem _ hx
        map_one_left := fun x => by
          change e.conjugateMap (fun y => J (1, y)) x = e.conjugateMap k₀ x
          congr 1
          funext y
          exact J.apply_one y }
    refine ⟨H, fun t x => (hJbound t).2 x, fun t => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x hx
      apply e.conjugateMap_eqOn_compl (hJfix t)
      rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := hrV hz
      have heq : e.symm z = w := by rw [← hwz, e.left_inv hw.1]
      exact hx (heq.symm ▸ hw.2)
    · intro x hx
      change e.conjugateMap (fun y => J (t, y)) x ∈ U
      by_cases hxs : x ∈ e.source
      · rw [e.conjugateMap_of_mem _ hxs]
        by_cases hxT : e x ∈ T
        · have hzV : J (t, e x) ∈ V := hρV
            (mem_cthickening_of_dist_le _ _ ρ T hxT
              ((hJclose t (e x)).trans_le (min_le_right δ ρ)).le)
          obtain ⟨w, hw, hwz⟩ := hzV
          rw [← hwz, e.left_inv hw.1]
          exact hw.2
        · have heq : J (t, e x) = e x := hJfix t hxT
          rw [heq, e.left_inv hxs]
          exact hx
      · rw [e.conjugateMap_of_notMem _ hxs]
        exact hx
    · intro x hx
      change e.conjugateMap (fun y => J (t, y)) x ∈ e.source
      rw [e.conjugateMap_of_mem _ hx]
      exact e.map_target ((hJbound t).1 (e.map_source hx))
    · intro x
      exact e.conjugateMap_mem_iff (B := {z | 0 ≤ ℓ z})
        (hJbound t).1 hC (fun z _ => (hJheight t z).2) x
    · intro x
      exact e.conjugateMap_mem_iff (B := {z | ℓ z = 0})
        (hJbound t).1 hBd (fun z _ => (hJheight t z).1) x

open Classical in
theorem exists_small_isPL_homeomorph_generalPosition_in_boundary_chart
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (C Bd : Set X) (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x))
    (hBd : ∀ x ∈ e.source, x ∈ Bd ↔ ℓ (e x) = 0)
    (K L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hKℓ : ∀ v ∈ K.vertices, 0 ≤ ℓ v) (hLℓ : ∀ v ∈ L.vertices, 0 ≤ ℓ v)
    (hKboundary : ∀ x ∈ K.space, ℓ x = 0 → x ∈ (boundaryComplex 2 K).space)
    (hLboundary : ∀ x ∈ L.space, ℓ x = 0 → x ∈ (boundaryComplex 2 L).space)
    {U : Set X} (hU : IsOpen U) (hKU : K.space ⊆ e '' (e.source ∩ U))
    (hLU : L.space ⊆ e '' (e.source ∩ U)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : X ≃ₜ X) (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
      IsPL 3 3 h ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      MapsTo h e.source e.source ∧ (∀ x, h x ∈ C ↔ x ∈ C) ∧
      (∀ x, h x ∈ Bd ↔ x ∈ Bd) ∧
      IsPLHomeomorphOn (e ∘ h ∘ e.symm) K.space ((e ∘ h ∘ e.symm) '' K.space) ∧
      G.faces.Finite ∧ G.space = (e ∘ h ∘ e.symm) '' K.space ∩ L.space ∧
      IsCombinatorialManifoldWithBoundary 1 G ∧
      ∀ z ∈ G.space,
        (z ∈ e '' (e.source ∩ Bd) ∧
          HasPLBoundaryCrossingAt (e '' (e.source ∩ C))
            ((e ∘ h ∘ e.symm) '' K.space) L.space z) ∨
        (z ∉ e '' (e.source ∩ Bd) ∧
          HasPLCrossingAt ((e ∘ h ∘ e.symm) '' K.space) L.space z) := by
  obtain ⟨h, G, hh, hclose, hfix, hmap, hCpres, hBpres, hPL, hGfinite, hGspace,
    hGman, hcross, -⟩ :=
    exists_small_isPL_homeomorph_generalPosition_homotopy_in_boundary_chart e he C Bd ℓ hℓ
      hC hBd K L hK hL hKℓ hLℓ hKboundary hLboundary hU hKU hLU hε
  exact ⟨h, G, hh, hclose, hfix, hmap, hCpres, hBpres, hPL, hGfinite, hGspace, hGman, hcross⟩

end DifferentialGeometry.Topology.PiecewiseLinear
