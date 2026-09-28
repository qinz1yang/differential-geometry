/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryMonotonicity
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedBoundaryPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.SingularCell
import DifferentialGeometry.Topology.PiecewiseLinear.SingularLocal

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

private noncomputable local instance euclideanDecidableEq {n : ℕ} :
    DecidableEq (EuclideanSpace ℝ (Fin n)) := Classical.decEq _

open Classical in
theorem exists_isOpen_forall_exists_small_isPLOn_boundary_crossing_in_chart
    {d : ℕ} {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (f : EuclideanSpace ℝ (Fin d) → X)
    (hf : IsPLOn d 3 f K.space) (hloc : IsLocallyInjective (K.space.domRestrict f))
    (hcard : ∀ z, (K.space ∩ f ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (C Bd : Set X) (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x))
    (hBd : ∀ x ∈ e.source, x ∈ Bd ↔ ℓ (e x) = 0)
    (hfC : MapsTo f K.space C)
    (hfBd : K.space ∩ f ⁻¹' Bd = (boundaryComplex 2 K).space)
    {y : X} (hy : y ∈ doublePointSet f K.space) (hye : y ∈ e.source)
    {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧ W ⊆ e.source ∧
      ∀ ε : ℝ, 0 < ε → ∃ (g : EuclideanSpace ℝ (Fin d) → X)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        IsPLOn d 3 g K.space ∧ (∀ x, dist (g x) (f x) < ε) ∧
        IsLocallyInjective (K.space.domRestrict g) ∧
        (∀ z, (K.space ∩ g ⁻¹' {z}).encard ≤ 2) ∧
        (∀ z ∉ V, g ⁻¹' {z} = f ⁻¹' {z}) ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet g K.space ↔ e z ∈ G.space) ∧
        (∀ z ∈ W ∩ doublePointSet g K.space,
          (z ∈ Bd ∧ HasPLBoundaryDoubleCrossingAt (e ∘ g)
            (K.space ∩ g ⁻¹' e.source) (e '' (e.source ∩ C)) (e z)) ∨
          (z ∉ Bd ∧ HasPLDoubleCrossingAt (e ∘ g) (K.space ∩ g ⁻¹' e.source) (e z))) ∧
        MapsTo g K.space C ∧ K.space ∩ g ⁻¹' Bd = (boundaryComplex 2 K).space ∧
        ∃ H : ContinuousMap (unitInterval × K.space) X,
          (∀ x, H (0, x) = f x) ∧ (∀ x, H (1, x) = g x) ∧
          ∀ t x, dist (H (t, x)) (f x) < ε ∧
            (H (t, x) ∈ C ↔ f x ∈ C) ∧ (H (t, x) ∈ Bd ↔ f x ∈ Bd) ∧
            (H (t, x) ∈ V ↔ f x ∈ V) ∧ (f x ∉ V → H (t, x) = f x) := by
  have hfc : ContinuousOn f K.space := fun x hx => (hf x hx).continuousWithinAt
  obtain ⟨a, ha, b, hb, hab, hfa, hfb⟩ := hy
  obtain ⟨P, Q, B₀, U, hPQ, hP, hQ, _, hB₀Q, hPB₀, hinjP, _, hU, hyU, hUV, hseam, hinjQ,
    _, houter, _, _, _, _, hPa, hB₀b⟩ := exists_isPLBall_patches_at_fiber_pair K hK f hfc hloc hcard
      ha hb hab hfa hfb (A₀ := univ) (B₀ := univ) Filter.univ_mem Filter.univ_mem
      (Filter.inter_mem hV (e.open_source.mem_nhds hye))
  obtain ⟨A, Q₁, B, U₁, _, hA, _, hB, _, hAB, hinjA, hinjB, hU₁, hyU₁, hU₁U, _, _,
    hinner, hmapsU, hAP, hBB₀, _, _, _, _⟩ := exists_isPLBall_patches_at_fiber_pair K hK f hfc
      hloc hcard ha hb hab hfa hfb hPa hB₀b (hU.mem_nhds hyU)
  have hPK : P ⊆ K.space := hPQ ▸ subset_union_left
  have hQK : Q ⊆ K.space := hPQ ▸ subset_union_right
  have hAK : A ⊆ K.space := hAP.trans hPK
  have hBQ : B ⊆ Q := hBB₀.trans hB₀Q
  have hBK : B ⊆ K.space := hBQ.trans hQK
  have hPe : MapsTo f P e.source := fun x hx => (houter (Or.inl hx)).2
  have hAe : MapsTo f A e.source := fun x hx => hPe (hAP hx)
  have hBe : MapsTo f B e.source := fun x hx => (houter (Or.inr (hBB₀ hx))).2
  obtain ⟨M, hMfinite, _, hfA, _⟩ :=
    (hf.mono_of_isPolyhedron hA.isPolyhedron hAK).exists_isPLHomeomorphOn_chart_image
      hA.isPolyhedron hinjA e he hAe
  obtain ⟨N, hNfinite, _, hfB, _⟩ :=
    (hf.mono_of_isPolyhedron hB.isPolyhedron hBK).exists_isPLHomeomorphOn_chart_image
      hB.isPolyhedron hinjB e he hBe
  have : Finite M.faces := hMfinite.to_subtype
  have : Finite N.faces := hNfinite.to_subtype
  have hMman : IsCombinatorialManifoldWithBoundary 2 M :=
    (hA.of_isPLHomeomorphOn hfA).isCombinatorialManifoldWithBoundary
  have hNman : IsCombinatorialManifoldWithBoundary 2 N :=
    (hB.of_isPLHomeomorphOn hfB).isCombinatorialManifoldWithBoundary
  have hMU : M.space ⊆ e '' (e.source ∩ U) := by
    rw [← hfA.image_eq]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨hAe hx, hmapsU (Or.inl hx)⟩, rfl⟩
  have hNU : N.space ⊆ e '' (e.source ∩ U) := by
    rw [← hfB.image_eq]
    rintro z ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨hBe hx, hmapsU (Or.inr hx)⟩, rfl⟩
  have hheight (T : Set (EuclideanSpace ℝ (Fin d))) (hTK : T ⊆ K.space)
      (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (hfJ : IsPLHomeomorphOn (e ∘ f) T J.space) (hTe : MapsTo f T e.source) :
      ∀ z ∈ J.space, 0 ≤ ℓ z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hfJ.bijOn.surjOn hz
    exact (hC _ (hTe hx)).mp (hfC (hTK hx))
  have hboundary (T : Set (EuclideanSpace ℝ (Fin d))) (hT : IsPLBall 2 T)
      (hTK : T ⊆ K.space) (J : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
      (hJfinite : J.faces.Finite) (hfJ : IsPLHomeomorphOn (e ∘ f) T J.space)
      (hTe : MapsTo f T e.source) :
      ∀ z ∈ J.space, ℓ z = 0 → z ∈ (boundaryComplex 2 J).space := by
    let _ : Finite J.faces := hJfinite.to_subtype
    obtain ⟨R, hRfinite, hRT⟩ := hT.isPolyhedron.exists_simplicialComplex
    let _ : Finite R.faces := hRfinite.to_subtype
    have hR : IsCombinatorialManifoldWithBoundary 2 R :=
      (hRT.symm ▸ hT).isCombinatorialManifoldWithBoundary
    have hRK : R.space ⊆ K.space := hRT ▸ hTK
    have hfR : IsPLHomeomorphOn (e ∘ f) R.space J.space := hRT.symm ▸ hfJ
    intro z hz hzero
    obtain ⟨x, hx, rfl⟩ := hfJ.bijOn.surjOn hz
    have hxR : x ∈ R.space := hRT.symm ▸ hx
    have hxBd : x ∈ (boundaryComplex 2 K).space :=
      hfBd.subset ⟨hTK hx, (hBd _ (hTe hx)).mpr hzero⟩
    exact (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn R J hR hfR hxR).mpr
      (inter_boundaryComplex_space_subset_of_subset K R hK hR hRK ⟨hxR, hxBd⟩)
  obtain ⟨η, hη, hηU⟩ := Metric.mem_nhds_iff.mp (hU₁.mem_nhds hyU₁)
  let W := Metric.ball y (η / 2)
  have hW : IsOpen W := isOpen_ball
  have hyW : y ∈ W := mem_ball_self (half_pos hη)
  have hclWU₁ : closure W ⊆ U₁ := by
    intro z hz
    exact hηU ((mem_closedBall.mp (closure_ball_subset_closedBall hz)).trans_lt (half_lt_self hη))
  have hWU₁ : W ⊆ U₁ := subset_closure.trans hclWU₁
  have hWe : W ⊆ e.source := fun z hz =>
    (hUV (subset_closure (hU₁U (subset_closure (hWU₁ hz))))).2
  refine ⟨W, hW, hyW, ?_, hWe, fun ε hε => ?_⟩
  · exact fun z hz => (hUV (subset_closure (hU₁U (subset_closure (hclWU₁ hz))))).1
  obtain ⟨h, G, hh, hclose, hfix, hmap, hCpres, hBpres, hcoord, hGfinite, hGspace,
    hGman, hcross, J, hJclose, hJ⟩ :=
    exists_small_isPL_homeomorph_generalPosition_homotopy_in_boundary_chart e he C Bd ℓ hℓ
      hC hBd M N hMman hNman
      (fun v hv => hheight A hAK M hfA hAe v (M.vertices_subset_space hv))
      (fun v hv => hheight B hBK N hfB hBe v (N.vertices_subset_space hv))
      (hboundary A hA hAK M hMfinite hfA hAe)
      (hboundary B hB hBK N hNfinite hfB hBe) hU hMU hNU (lt_min hε (half_pos hη))
  have hfPQ : IsPLOn d 3 f (P ∪ Q) := by rwa [hPQ]
  have hlocPQ : IsLocallyInjective ((P ∪ Q).domRestrict f) := by rwa [hPQ]
  have hcardPQ : ∀ z, ((P ∪ Q) ∩ f ⁻¹' {z}).encard ≤ 2 := by rwa [hPQ]
  obtain ⟨g, hg, hgloc, hgcard, hgP, hgQ, hgOffP, hgfiber⟩ :=
    exists_isPLOn_postcomp_on_polyhedron_of_locallyInjective hfPQ hP.isPolyhedron hQ
      hlocPQ hcardPQ hinjP hh h.injective hfix hseam hinjQ
  rw [hPQ] at hg hgloc hgcard
  have hgAe : MapsTo g A e.source := by
    intro x hx
    rw [hgP (hAP hx)]
    exact hmap (hAe hx)
  have hgBe : MapsTo g B e.source := by
    intro x hx
    rw [hgQ (hBQ hx)]
    exact hBe hx
  have hgA : IsPLHomeomorphOn (e ∘ g) A ((e ∘ h ∘ e.symm) '' M.space) := by
    apply (hfA.trans hcoord).congr
    intro x hx
    change e (g x) = e (h (e.symm (e (f x))))
    rw [hgP (hAP hx), e.left_inv (hAe hx)]
    rfl
  have hgB : IsPLHomeomorphOn (e ∘ g) B N.space := by
    apply hfB.congr
    intro x hx
    exact congrArg e (hgQ (hBQ hx))
  have hpre : ∀ z ∈ W, h.symm z ∈ U₁ := by
    intro z hz
    apply hηU
    have hsmall : dist (h.symm z) z < η / 2 := by
      simpa only [h.apply_symm_apply, dist_comm] using
        (hclose (h.symm z)).trans_le (min_le_right _ _)
    have hdist := (dist_triangle (h.symm z) z y).trans_lt (add_lt_add hsmall hz)
    rwa [add_halves] at hdist
  have hcover : ∀ z ∈ W, K.space ∩ g ⁻¹' {z} ⊆ A ∪ B := by
    intro z hz x hx
    by_cases hxP : x ∈ P
    · have hfx : f x = h.symm z := by
        apply h.injective
        rw [h.apply_symm_apply]
        exact (hgP hxP).symm.trans hx.2
      have hxAB := hinner (h.symm z) (subset_closure (hpre z hz)) ⟨hx.1, hfx⟩
      rcases hxAB with hxA | hxB
      · exact Or.inl hxA
      · exact False.elim (Set.disjoint_left.mp hPB₀ hxP (hBB₀ hxB))
    · have hfx : f x = z := (hgOffP hxP).symm.trans hx.2
      exact Or.inr ((hinner z (subset_closure (hWU₁ hz)) ⟨hx.1, hfx⟩).resolve_left
        (fun hxA => hxP (hAP hxA)))
  let S := K.space ∩ g ⁻¹' e.source
  have hAS : A ⊆ S := fun x hx => ⟨hAK hx, hgAe hx⟩
  have hBS : B ⊆ S := fun x hx => ⟨hBK hx, hgBe hx⟩
  have hdouble (z : X) (hz : z ∈ e.source) :
      e z ∈ doublePointSet (e ∘ g) S ↔ z ∈ doublePointSet g K.space := by
    constructor
    · rintro ⟨a, ha, b, hb, hab, hga, hgb⟩
      exact ⟨a, ha.1, b, hb.1, hab, e.injOn ha.2 hz hga, e.injOn hb.2 hz hgb⟩
    · rintro ⟨a, ha, b, hb, hab, hga, hgb⟩
      exact ⟨a, ⟨ha, show g a ∈ e.source from hga.symm ▸ hz⟩,
        b, ⟨hb, show g b ∈ e.source from hgb.symm ▸ hz⟩, hab,
        congrArg e hga, congrArg e hgb⟩
  have hcovercoord (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ e.target) (hzW : e.symm z ∈ W) :
      S ∩ (e ∘ g) ⁻¹' {z} ⊆ A ∪ B := by
    rintro x ⟨hx, hxe⟩
    apply hcover (e.symm z) hzW
    exact ⟨hx.1, e.injOn hx.2 (e.map_target hz) (hxe.trans (e.right_inv hz).symm)⟩
  have hGdouble : ∀ z ∈ W, z ∈ doublePointSet g K.space ↔ e z ∈ G.space := by
    intro z hz
    rw [← hdouble z (hWe hz), hGspace, ← hgA.image_eq, ← hgB.image_eq]
    apply mem_doublePointSet_iff_mem_image_inter_of_injOn (e ∘ g) hAS hBS hAB
      hgA.bijOn.injOn hgB.bijOn.injOn
    exact hcovercoord (e z) (e.map_source (hWe hz)) (by rwa [e.left_inv (hWe hz)])
  have hgC (x : EuclideanSpace ℝ (Fin d)) : g x ∈ C ↔ f x ∈ C := by
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact hCpres (f x)
    · rw [hgOffP hxP]
  have hgBd (x : EuclideanSpace ℝ (Fin d)) : g x ∈ Bd ↔ f x ∈ Bd := by
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact hBpres (f x)
    · rw [hgOffP hxP]
  refine ⟨g, G, hg, ?_, hgloc, hgcard, ?_, hGfinite, hGman, hGdouble, ?_,
    fun x hx => (hgC x).mpr (hfC hx), ?_, ?_⟩
  · intro x
    by_cases hxP : x ∈ P
    · rw [hgP hxP]
      exact (hclose (f x)).trans_le (min_le_left _ _)
    · rw [hgOffP hxP, dist_self]
      exact hε
  · intro z hz
    exact hgfiber z (fun hzU => hz (hUV (subset_closure hzU)).1)
  · intro z hz
    have hgcont : ContinuousOn (e ∘ g) S := e.continuousOn.comp
      (fun x hx => (hg x hx.1).continuousWithinAt.mono inter_subset_left) (fun _ hx => hx.2)
    have hcrossz := hcross (e z) ((hGdouble z hz.1).mp hz.2)
    rw [← hgA.image_eq, ← hgB.image_eq] at hcrossz
    have hcoverNear : ∀ᶠ w in 𝓝 (e z), S ∩ (e ∘ g) ⁻¹' {w} ⊆ A ∪ B := by
      have hsym : ContinuousAt e.symm (e z) := e.continuousAt_symm (e.map_source (hWe hz.1))
      have hWneigh : W ∈ 𝓝 (e.symm (e z)) := by
        rw [e.left_inv (hWe hz.1)]
        exact hW.mem_nhds hz.1
      filter_upwards [hsym.preimage_mem_nhds hWneigh,
        e.open_target.mem_nhds (e.map_source (hWe hz.1))] with w hw hwt
      exact hcovercoord w hwt hw
    have hzBd : e z ∈ e '' (e.source ∩ Bd) ↔ z ∈ Bd := by
      constructor
      · rintro ⟨w, hw, heq⟩
        exact e.injOn hw.1 (hWe hz.1) heq ▸ hw.2
      · intro hzb
        exact ⟨z, ⟨hWe hz.1, hzb⟩, rfl⟩
    rcases hcrossz with ⟨hzb, hcrossz⟩ | ⟨hzb, hcrossz⟩
    · refine Or.inl ⟨hzBd.mp hzb, ?_⟩
      exact hasPLBoundaryDoubleCrossingAt_of_crossing_and_eventually_fiber_subset hgcont
        hAS hBS hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hAB
        (by rwa [hgA.image_eq]) (by rwa [hgB.image_eq])
        ((hdouble z (hWe hz.1)).mpr hz.2) hcrossz hcoverNear
    · refine Or.inr ⟨fun hz0 => hzb (hzBd.mpr hz0), ?_⟩
      exact hasPLDoubleCrossingAt_of_crossing_and_eventually_fiber_subset hgcont
        hAS hBS hA.isPolyhedron.isClosed hB.isPolyhedron.isClosed hAB
        (by rwa [hgA.image_eq]) (by rwa [hgB.image_eq])
        ((hdouble z (hWe hz.1)).mpr hz.2) hcrossz hcoverNear
  · rw [← hfBd]
    ext x
    exact and_congr_right (fun _ => hgBd x)
  · let T : Set (unitInterval × K.space) := {z | (z.2 : EuclideanSpace ℝ (Fin d)) ∈ P}
    let T' : Set (unitInterval × K.space) := {z | (z.2 : EuclideanSpace ℝ (Fin d)) ∈ Q}
    have hT : IsClosed T := hP.isPolyhedron.isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)
    have hT' : IsClosed T' := hQ.isClosed.preimage
      (continuous_subtype_val.comp continuous_snd)
    have hc : Continuous (fun z : unitInterval × K.space => f z.2) :=
      hfc.domRestrict.comp continuous_snd
    have hcomp : Continuous (fun z : unitInterval × K.space => J (z.1, f z.2)) :=
      J.continuous_toFun.comp (continuous_fst.prodMk hc)
    have hseamJ : ∀ z ∈ frontier T, J (z.1, f z.2) = f z.2 := by
      intro z hz
      have hzP : (z.2 : EuclideanSpace ℝ (Fin d)) ∈ P := hT.frontier_subset hz
      have hcompl : Tᶜ ⊆ T' := by
        intro w hw
        have hwPQ : (w.2 : EuclideanSpace ℝ (Fin d)) ∈ P ∪ Q := hPQ.symm.subset w.2.property
        exact hwPQ.resolve_left hw
      have hzcl : z ∈ closure Tᶜ := by
        rw [frontier_eq_closure_inter_closure] at hz
        exact hz.2
      have hzQ : (z.2 : EuclideanSpace ℝ (Fin d)) ∈ Q :=
        closure_minimal hcompl hT' hzcl
      exact (hJ z.1).1 (fun hfxU => hseam z.2 ⟨hzP, hzQ⟩ (subset_closure hfxU))
    let H : ContinuousMap (unitInterval × K.space) X :=
      ⟨T.piecewise (fun z => J (z.1, f z.2)) (fun z => f z.2),
        Continuous.piecewise hseamJ hcomp hc⟩
    have hHP (t : unitInterval) (x : K.space) (hx : (x : EuclideanSpace ℝ (Fin d)) ∈ P) :
        H (t, x) = J (t, f x) := by
      change (if (x : EuclideanSpace ℝ (Fin d)) ∈ P then J (t, f x) else f x) = _
      exact ite_eq_left hx
    have hHOffP (t : unitInterval) (x : K.space)
        (hx : (x : EuclideanSpace ℝ (Fin d)) ∉ P) : H (t, x) = f x := by
      change (if (x : EuclideanSpace ℝ (Fin d)) ∈ P then J (t, f x) else f x) = _
      exact ite_eq_right hx
    refine ⟨H, ?_, ?_, ?_⟩
    · intro x
      by_cases hx : (x : EuclideanSpace ℝ (Fin d)) ∈ P
      · rw [hHP 0 x hx, J.apply_zero, ContinuousMap.id_apply]
      · exact hHOffP 0 x hx
    · intro x
      by_cases hx : (x : EuclideanSpace ℝ (Fin d)) ∈ P
      · rw [hHP 1 x hx, J.apply_one, hgP hx]
        rfl
      · exact (hHOffP 1 x hx).trans (hgOffP hx).symm
    · intro t x
      by_cases hx : (x : EuclideanSpace ℝ (Fin d)) ∈ P
      · rw [hHP t x hx]
        refine ⟨(hJclose t (f x)).trans_le (min_le_left _ _),
          (hJ t).2.2.2.1 (f x), (hJ t).2.2.2.2 (f x), ?_,
          fun hxV => (hJ t).1 (fun hxU => hxV (hUV (subset_closure hxU)).1)⟩
        by_cases hfx : f x ∈ U
        · exact iff_of_true (hUV (subset_closure ((hJ t).2.1 hfx))).1
            (hUV (subset_closure hfx)).1
        · have heq : J (t, f x) = f x := (hJ t).1 hfx
          rw [heq]
      · rw [hHOffP t x hx, dist_self]
        exact ⟨hε, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩

open Classical in
theorem SingularTwoCell.exists_small_boundary_doubleCrossing_in_chart
    {X : Type*} [MetricSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    (D : SingularTwoCell X) {C : Set X}
    (hmap : MapsTo D D.domain C)
    (hproper : D.domain ∩ D ⁻¹' frontier C = frontier D.domain)
    (hloc : IsLocallyInjective (D.domain.domRestrict D))
    (hcard : ∀ z, (D.domain ∩ D ⁻¹' {z}).encard ≤ 2)
    (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin 3)))
    (he : e ∈ (plGroupoid 3).maximalAtlas X)
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hC : ∀ x ∈ e.source, x ∈ C ↔ 0 ≤ ℓ (e x))
    (hBd : ∀ x ∈ e.source, x ∈ frontier C ↔ ℓ (e x) = 0)
    {y : X} (hy : y ∈ doublePointSet D D.domain) (hye : y ∈ e.source)
    {V : Set X} (hV : V ∈ 𝓝 y) :
    ∃ W : Set X, IsOpen W ∧ y ∈ W ∧ closure W ⊆ V ∧ W ⊆ e.source ∧
      ∀ ε : ℝ, 0 < ε → ∃ (A : SingularTwoCell X)
        (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))),
        A.domain = D.domain ∧ (∀ x, dist (A x) (D x) < ε) ∧
        MapsTo A A.domain C ∧ A.domain ∩ A ⁻¹' frontier C = frontier A.domain ∧
        A '' A.domain ∩ frontier C = range A.boundary ∧
        (∀ z ∉ V, A ⁻¹' {z} = D ⁻¹' {z}) ∧
        IsLocallyInjective (A.domain.domRestrict A) ∧
        (∀ z, (A.domain ∩ A ⁻¹' {z}).encard ≤ 2) ∧
        G.faces.Finite ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
        (∀ z ∈ W, z ∈ doublePointSet A A.domain ↔ e z ∈ G.space) ∧
        (∀ z ∈ W ∩ doublePointSet A A.domain,
          (z ∈ frontier C ∧ HasPLBoundaryDoubleCrossingAt (e ∘ A)
            (A.domain ∩ A ⁻¹' e.source) (e '' (e.source ∩ C)) (e z)) ∨
          (z ∉ frontier C ∧ HasPLDoubleCrossingAt (e ∘ A)
            (A.domain ∩ A ⁻¹' e.source) (e z))) ∧
        ∃ H : ContinuousMap (unitInterval × frontier D.domain) X,
          (∀ x, H (0, x) = D x) ∧ (∀ x, H (1, x) = A x) ∧
          ∀ t x, dist (H (t, x)) (D x) < ε ∧ H (t, x) ∈ frontier C ∧
            (H (t, x) ∈ V ↔ D x ∈ V) ∧ (D x ∉ V → H (t, x) = D x) := by
  obtain ⟨K, hKfin, hKP⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hK : IsCombinatorialManifoldWithBoundary 2 K :=
    (hKP.symm ▸ D.isPLBall_domain).isCombinatorialManifoldWithBoundary
  have hKboundary : (boundaryComplex 2 K).space = frontier D.domain := by
    rw [← frontier_space_eq_boundaryComplex_space hK, hKP]
  have hproperK : K.space ∩ D ⁻¹' frontier C = (boundaryComplex 2 K).space := by
    rw [hKP, hKboundary]
    exact hproper
  obtain ⟨W, hW, hyW, hWV, hWe, hsmall⟩ :=
    exists_isOpen_forall_exists_small_isPLOn_boundary_crossing_in_chart K hK D
      (hKP.symm ▸ D.isPLOn) (hKP.symm ▸ hloc) (hKP.symm ▸ hcard) e he C (frontier C) ℓ hℓ
      hC hBd (hKP.symm ▸ hmap) hproperK (hKP.symm ▸ hy) hye hV
  refine ⟨W, hW, hyW, hWV, hWe, fun ε hε => ?_⟩
  obtain ⟨g, G, hg, hclose, hgloc, hgcard, hfiber, hGfin, hGman, hGspace, hcross,
    hgmap, hgpre, H, hHzero, hHone, hH⟩ := hsmall ε hε
  rw [hKboundary, hKP] at hgpre
  rw [hKP] at hg hgloc hgcard hgmap hGspace hcross
  let A : SingularTwoCell X :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := g
      isPLOn := hg }
  have hinter : A '' A.domain ∩ frontier C = range A.boundary := by
    rw [← image_inter_preimage]
    change g '' (D.domain ∩ g ⁻¹' frontier C) = range A.boundary
    rw [hgpre]
    ext z
    exact ⟨fun ⟨x, hx, hxz⟩ => ⟨⟨x, hx⟩, hxz⟩,
      fun ⟨x, hxz⟩ => ⟨x, x.2, hxz⟩⟩
  let ι : ContinuousMap (frontier D.domain) K.space :=
    ⟨fun x => ⟨x, hKP.symm.subset (D.frontier_subset_domain x.property)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let H' : ContinuousMap (unitInterval × frontier D.domain) X :=
    H.comp ((ContinuousMap.id unitInterval).prodMap ι)
  refine ⟨A, G, rfl, hclose, hgmap, hgpre, hinter, hfiber, hgloc, hgcard,
    hGfin, hGman, hGspace, hcross, H', fun x => hHzero (ι x), fun x => hHone (ι x), ?_⟩
  intro t x
  have hb : D x ∈ frontier C := (hproper.superset x.property).2
  exact ⟨(hH t (ι x)).1, (hH t (ι x)).2.2.1.mpr hb,
    (hH t (ι x)).2.2.2.1, (hH t (ι x)).2.2.2.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
