/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.Schoenflies.ArcComplementPrep
import DifferentialGeometry.External.Schoenflies.Graph.Redrawing
import DifferentialGeometry.External.Schoenflies.Graph.VertexSquares
import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric
import DifferentialGeometry.Topology.PiecewiseLinear.CellGluingSphere
import DifferentialGeometry.Topology.PiecewiseLinear.ComplementComponents
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceChart
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellLocalSides
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellSubdisk
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSideChaining
import DifferentialGeometry.Topology.PiecewiseLinear.TubeFrontierConnected
import DifferentialGeometry.Topology.PiecewiseLinear.TwoComponentsOfPseudoCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Cells

theorem IsTopologicalCellWithInterior.subset {X : Type*} [TopologicalSpace X] {n : ℕ}
    {C I : Set X} (hC : IsTopologicalCellWithInterior n C I) : I ⊆ C := by
  obtain ⟨φ, rfl⟩ := hC
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem IsTopologicalCellWithInterior.isCompact {X : Type*} [TopologicalSpace X] {n : ℕ}
    {C I : Set X} (hC : IsTopologicalCellWithInterior n C I) : IsCompact C := by
  obtain ⟨φ, -⟩ := hC
  have : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  have h1 := isCompact_univ.image (continuous_subtype_val.comp φ.continuous)
  rwa [image_univ, range_comp, φ.surjective.range_eq, image_univ, Subtype.range_coe] at h1

theorem IsPseudoCell.isPreconnected {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) : IsPreconnected Ec := by
  obtain ⟨Ψ, Φ, -, hΦc, hΨb, hΦb, hΦΨ, -, -⟩ := hpc.isOpenCell.exists_planarChart
  have hEimg : Eint = Φ '' Metric.ball 0 1 := by
    ext y
    constructor
    · intro hy
      exact ⟨Ψ y, hΨb hy, hΦΨ y hy⟩
    · rintro ⟨p, hp, rfl⟩
      exact hΦb hp
  rw [hpc.carrierEq, ← hpc.closureEq, hEimg]
  exact ((convex_ball (0 : Schoenflies.Plane) 1).isPreconnected.image Φ hΦc).closure

end Cells

section Arms

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.rim_subset_frontier_inter_frontier (ht : IsTube K N C D Dbd h N') {f : Finset E3}
    (hf : f ∈ K.faces) (hfc : f.card = 2) {a : E3} (ha : a ∈ K.vertices) (haf : a ∈ f) :
    Dbd f ⊆ frontier (C a) ∩ frontier N := by
  intro x hx
  rw [← ht.splitProper f hf hfc] at hx
  exact ⟨ht.splitDisk_subset_frontier ha hf hfc haf hx.1, hx.2⟩

theorem IsTube.isConnected_frontier_inter_frontier (ht : IsTube K N C D Dbd h N') {v : E3}
    (hv : v ∈ K.vertices) : IsConnected (frontier (C v) ∩ frontier N) :=
  (ht.freeFaceConnected v hv).subset_closure sdiff_subset
    (ht.frontier_inter_frontier_subset_closure_freeFace hv)

theorem exists_edge_ne_of_ncard_neighborSet_ne_one (K : Geometry.SimplicialComplex ℝ E3)
    (hfin : K.faces.Finite)
    (hend : ∀ v : K.vertices, ((SimplicialComplex.edgeGraph K).neighborSet v).ncard ≠ 1)
    {v : E3} (hv : v ∈ K.vertices) {e : Finset E3} (he : e ∈ K.faces) (hcard : e.card = 2)
    (hve : v ∈ e) : ∃ f ∈ K.faces, f.card = 2 ∧ v ∈ f ∧ f ≠ e := by
  obtain ⟨u, hue, huv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
  have hu : u ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  have hpair : ({v, u} : Finset E3) = e := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hve (Finset.singleton_subset_iff.mpr hue))
    (by rw [hcard, Finset.card_pair huv.symm])
  let vv : K.vertices := ⟨v, hv⟩
  let uu : K.vertices := ⟨u, hu⟩
  have hadj : (SimplicialComplex.edgeGraph K).Adj vv uu := by
    refine ⟨fun h => huv (congrArg Subtype.val h).symm, ?_⟩
    rw [classical_insert_singleton_eq_pair, hpair]
    exact he
  have hvf : K.vertices.Finite := hfin.preimage Finset.singleton_injective.injOn
  have : Finite K.vertices := hvf.to_subtype
  have hpos : 0 < ((SimplicialComplex.edgeGraph K).neighborSet vv).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨uu, hadj⟩
  have h1 : 1 < ((SimplicialComplex.edgeGraph K).neighborSet vv).ncard := by
    have := hend vv
    omega
  obtain ⟨a, b, ha, hb, hab⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h1
  obtain ⟨ww, hww, hwu⟩ : ∃ ww : K.vertices, (SimplicialComplex.edgeGraph K).Adj vv ww ∧
      ww ≠ uu := by
    by_cases hau : a = uu
    · exact ⟨b, hb, fun hbu => hab (hau.trans hbu.symm)⟩
    · exact ⟨a, ha, hau⟩
  obtain ⟨hne, hmem⟩ := hww
  rw [classical_insert_singleton_eq_pair] at hmem
  have hwv : (ww : E3) ≠ v := fun h => hne (Subtype.ext h.symm)
  refine ⟨{v, (ww : E3)}, hmem, Finset.card_pair hwv.symm, Finset.mem_insert_self _ _, ?_⟩
  intro heq
  have hw : (ww : E3) ∈ e := by
    rw [← heq]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [← hpair, Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with hw | hw
  · exact hwv hw
  · exact hwu (Subtype.ext hw)

end Arms

section HandleArms

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}

theorem IsHandleDecompositionOfTube.exists_arm
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {v₁ : E3}
    (hv₁ : v₁ ∈ K.vertices) {e₁ e₂ : Finset E3} (he₁ : e₁ ∈ K.faces) (hcard₁ : e₁.card = 2)
    (hv₁e₁ : v₁ ∈ e₁) (he₂ : e₂ ∈ K.faces) (hcard₂ : e₂.card = 2) (hv₁e₂ : v₁ ∈ e₂)
    (hne : e₂ ≠ e₁) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (a : E3) (Γ : Set E3), IsCompact Γ ∧ IsPreconnected Γ ∧ a ∈ Γ ∧
      h (e₂.centroid ℝ id) ∈ Γ ∧ Γ ⊆ h '' K.space ∧ h (e₁.centroid ℝ id) ∉ Γ ∧
        dist a (h (e₁.centroid ℝ id)) < ρ ∧ a ∈ connectedComponentIn
          (N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) (h v₁) := by
  have ht := hd.tube
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hhc : ContinuousOn h N := ht.continuousOn
  have hhi : InjOn h N := ht.injOn
  have hK'N' : h '' K.space ⊆ N' := by
    rw [ht.imageEq]
    exact image_mono hKN
  set c₁ := e₁.centroid ℝ id with hc₁def
  set c₂ := e₂.centroid ℝ id with hc₂def
  have hc₁K : c₁ ∈ convexHull ℝ (e₁ : Set E3) := e₁.centroid_mem_convexHull ⟨v₁, hv₁e₁⟩
  have hv₁K : v₁ ∈ convexHull ℝ (e₁ : Set E3) := subset_convexHull ℝ _ hv₁e₁
  have hc₂K : c₂ ∈ convexHull ℝ (e₂ : Set E3) := e₂.centroid_mem_convexHull ⟨v₁, hv₁e₂⟩
  have hv₁K₂ : v₁ ∈ convexHull ℝ (e₂ : Set E3) := subset_convexHull ℝ _ hv₁e₂
  have hcnot : ∀ e ∈ K.faces, ∀ f ∈ K.faces, ¬ e ⊆ f →
      e.centroid ℝ id ∉ convexHull ℝ (f : Set E3) := fun e he f hf hef hc =>
    hef (face_subset_of_mem_openSimplex_of_mem_convexHull K he hf
      (centroid_mem_openSimplex_of_mem_faces K e he) hc)
  have hc₁v₁ : c₁ ≠ v₁ := by
    intro heq
    refine hcnot e₁ he₁ {v₁} hv₁ (fun hsub => ?_) ?_
    · have := Finset.card_le_card hsub
      rw [hcard₁, Finset.card_singleton] at this
      omega
    · rw [← hc₁def, heq, Finset.coe_singleton, convexHull_singleton]
      exact mem_singleton v₁
  have hc₁N : c₁ ∈ N := hKN (K.convexHull_subset_space he₁ hc₁K)
  obtain ⟨η, hη, hηh⟩ := Metric.continuousWithinAt_iff.mp (hhc c₁ hc₁N) ρ hρ
  set t₀ : ℝ := min (1 / 2) (η / (‖v₁ - c₁‖ + 1)) with ht₀def
  have ht₀pos : 0 < t₀ := lt_min (by norm_num) (div_pos hη (by positivity))
  have ht₀1 : t₀ ≤ 1 / 2 := min_le_left _ _
  set a₀ := c₁ + t₀ • (v₁ - c₁) with ha₀def
  have ha₀seg : a₀ ∈ segment ℝ c₁ v₁ :=
    ⟨1 - t₀, t₀, by linarith only [ht₀1], ht₀pos.le, by ring, by rw [ha₀def]; module⟩
  have ha₀c : dist a₀ c₁ < η := by
    rw [dist_eq_norm, ha₀def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht₀pos]
    calc t₀ * ‖v₁ - c₁‖ ≤ η / (‖v₁ - c₁‖ + 1) * ‖v₁ - c₁‖ := by
          gcongr
          exact min_le_right _ _
      _ < η := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith only [norm_nonneg (v₁ - c₁), hη]
  have hseg₁ : segment ℝ a₀ v₁ ⊆ convexHull ℝ (e₁ : Set E3) :=
    (convex_convexHull ℝ _).segment_subset
      ((convex_convexHull ℝ _).segment_subset hc₁K hv₁K ha₀seg) hv₁K
  have hseg₂ : segment ℝ v₁ c₂ ⊆ convexHull ℝ (e₂ : Set E3) :=
    (convex_convexHull ℝ _).segment_subset hv₁K₂ hc₂K
  have hseg₁K : segment ℝ a₀ v₁ ⊆ K.space := hseg₁.trans (K.convexHull_subset_space he₁)
  have hseg₂K : segment ℝ v₁ c₂ ⊆ K.space := hseg₂.trans (K.convexHull_subset_space he₂)
  have hseg₁N : segment ℝ a₀ v₁ ⊆ N := hseg₁K.trans hKN
  have hseg₂N : segment ℝ v₁ c₂ ⊆ N := hseg₂K.trans hKN
  have ha₀N : a₀ ∈ N := hseg₁N (left_mem_segment ℝ a₀ v₁)
  have hc₁seg₁ : c₁ ∉ segment ℝ a₀ v₁ := by
    rintro ⟨a, b, ha, hb, hab, heq⟩
    have hb' : b = 1 - a := by linarith only [hab]
    subst hb'
    have key : (a * t₀ + (1 - a)) • (v₁ - c₁) = 0 := by
      rw [← sub_eq_zero] at heq
      rw [← heq, ha₀def]
      module
    rcases smul_eq_zero.mp key with h0 | h0
    · nlinarith only [mul_nonneg hb (by linarith only [ht₀1] : (0 : ℝ) ≤ 1 - t₀), h0, ht₀pos]
    · exact hc₁v₁ (sub_eq_zero.mp h0).symm
  have he₁₂sub : ¬ e₁ ⊆ e₂ := fun hs =>
    hne (Finset.eq_of_subset_of_card_le hs (by rw [hcard₁, hcard₂])).symm
  have hc₁seg₂ : c₁ ∉ segment ℝ v₁ c₂ := fun hc => hcnot e₁ he₁ e₂ he₂ he₁₂sub (hseg₂ hc)
  have hsegc : ∀ x y : E3, IsCompact (segment ℝ x y) := fun x y => by
    rw [← convexHull_pair]
    exact (Set.toFinite _).isCompact_convexHull ℝ
  refine ⟨h a₀, h '' segment ℝ a₀ v₁ ∪ h '' segment ℝ v₁ c₂,
    ((hsegc a₀ v₁).image_of_continuousOn (hhc.mono hseg₁N)).union
      ((hsegc v₁ c₂).image_of_continuousOn (hhc.mono hseg₂N)),
    IsPreconnected.union (h v₁) ⟨v₁, right_mem_segment ℝ a₀ v₁, rfl⟩
      ⟨v₁, left_mem_segment ℝ v₁ c₂, rfl⟩
      ((convex_segment a₀ v₁).isPreconnected.image _ (hhc.mono hseg₁N))
      ((convex_segment v₁ c₂).isPreconnected.image _ (hhc.mono hseg₂N)),
    Or.inl ⟨a₀, left_mem_segment ℝ a₀ v₁, rfl⟩, Or.inr ⟨c₂, right_mem_segment ℝ v₁ c₂, rfl⟩,
    union_subset (image_mono hseg₁K) (image_mono hseg₂K), ?_, hηh ha₀N ha₀c, ?_⟩
  · rintro (⟨y, hy, hyc⟩ | ⟨y, hy, hyc⟩)
    · exact hc₁seg₁ (hhi (hseg₁N hy) hc₁N hyc ▸ hy)
    · exact hc₁seg₂ (hhi (hseg₂N hy) hc₁N hyc ▸ hy)
  have hΓ₁O : h '' segment ℝ a₀ v₁ ⊆
      N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hK'N' ⟨x, hseg₁K hx, rfl⟩, fun hxU => ?_⟩
    obtain ⟨e, ⟨he, hec⟩, hxe⟩ := mem_iUnion₂.mp hxU
    have hm : h x ∈ Ec e ∩ h '' K.space := ⟨hxe, x, hseg₁K hx, rfl⟩
    rw [hd.meetsGraph e he hec] at hm
    have hceN : e.centroid ℝ id ∈ N := hKN (K.convexHull_subset_space he
      (e.centroid_mem_convexHull (K.nonempty_of_mem_faces he)))
    have hxc : x = e.centroid ℝ id := hhi (hseg₁N hx) hceN (mem_singleton_iff.mp hm)
    by_cases hee : e = e₁
    · rw [hee] at hxc
      rw [hxc] at hx
      exact hc₁seg₁ hx
    · refine hcnot e he e₁ he₁ (fun hs => hee (Finset.eq_of_subset_of_card_le hs
        (by rw [hcard₁, hec]))) ?_
      rw [← hxc]
      exact hseg₁ hx
  exact ((convex_segment a₀ v₁).isPreconnected.image _
    (hhc.mono hseg₁N)).subset_connectedComponentIn ⟨v₁, right_mem_segment ℝ a₀ v₁, rfl⟩ hΓ₁O
    ⟨a₀, left_mem_segment ℝ a₀ v₁, rfl⟩

end HandleArms

section Replacement

theorem IsPseudoCell.exists_replacementDisk (h324 : Moise324) {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {DJ DJint : Set E3}
    (hDJ : IsTopologicalCellWithInterior 2 DJ DJint) (hDJE : DJ ⊆ Ec)
    (hJ : IsPLSphere 1 (DJ \ DJint)) (hJE : DJ \ DJint ⊆ Eint) (hPDJ : P ∈ DJint)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (δ : ℝ) (Δ₁ : Set E3) (r₁ : (Fin 3 → ℝ) → E3) (DJ₁ DJint₁ G : Set E3),
      0 < δ ∧ δ ≤ δ₀ ∧ IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁ ∧
        Δ₁ ⊆ Metric.ball P δ ∧ Δ₁ ∩ Ec = r₁ '' stdSimplexBoundary 2 ∧
          IsTopologicalCellWithInterior 2 DJ₁ DJint₁ ∧ DJ₁ ⊆ Ec ∧
            DJ₁ \ DJint₁ = r₁ '' stdSimplexBoundary 2 ∧ P ∈ DJint₁ ∧ DJ₁ ⊆ DJint ∧
              DJ₁ ⊆ Metric.ball P δ₀ ∧ IsPreconnected G ∧ G ⊆ Eint ∧
                (∀ y ∈ G, δ < dist y P) ∧ ∀ y ∈ Eint, δ₀ ≤ dist y P → y ∈ G := by
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hpc.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ Eint := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hPE : P ∈ Eint := hpc.centerMem
  have hbdc : IsClosed Ebd := by
    obtain ⟨φ⟩ := hpc.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hEintE : Eint ⊆ Ec := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hEc : ∀ y ∈ Ec, y ∉ Ebd → y ∈ Eint := fun y hy hyb => by
    rw [hpc.carrierEq] at hy
    exact hy.resolve_right hyb
  have hEint : ∀ y ∈ Eint, y ∉ Ebd := fun y hy hyb =>
    Set.disjoint_left.mp hpc.disjointRim hy hyb
  obtain ⟨hDJsub, hDJimg⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hDJ hDJE hJ
    hJE hPDJ hPE
  have hDJint : DJint ⊆ DJ := hDJ.subset
  have hγ : Schoenflies.IsJordanCurve (Ψ '' (DJ \ DJint)) :=
    isJordanCurve_image_of_isPLSphere_one hJ hJE hΨc hΨi
  have hsep := Schoenflies.jordan_curve_theorem hγ
  have hDJmem : ∀ y ∈ Eint, y ∈ DJint ↔ Ψ y ∈ Schoenflies.inside (Ψ '' (DJ \ DJint)) := by
    intro y hy
    rw [← hDJimg]
    constructor
    · exact fun h' => ⟨y, h', rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rwa [← hΨi (hDJsub (hDJint hz)) hy hzy]
  set c := Ψ P with hcdef
  have hcb : c ∈ Metric.ball (0 : Schoenflies.Plane) 1 := hΨb hPE
  obtain ⟨ε₃, hε₃, hball₃⟩ := Metric.isOpen_iff.mp hsep.isOpen_inside c ((hDJmem P hPE).mp hPDJ)
  obtain ⟨ε₄, hε₄, hball₄⟩ :=
    Metric.continuousAt_iff.mp (hΦc.continuousAt (Metric.isOpen_ball.mem_nhds hcb)) δ₀ hδ₀
  have hΦc₁ : Φ c = P := hΦΨ _ hPE
  set rs := min ε₃ ε₄ / 2 with hrsdef
  have hrs : 0 < rs := half_pos (lt_min hε₃ hε₄)
  have hsqball : Schoenflies.Plane.closedSquare c rs ⊆ Metric.ball c (min ε₃ ε₄) :=
    Schoenflies.Plane.closedSquare_subset_ball (lt_min hε₃ hε₄)
  have hoc : Schoenflies.Plane.openSquare c rs ⊆ Schoenflies.Plane.closedSquare c rs :=
    Schoenflies.Plane.openSquare_subset_closedSquare c rs
  have hsqin : Schoenflies.Plane.closedSquare c rs ⊆ Schoenflies.inside (Ψ '' (DJ \ DJint)) :=
    hsqball.trans ((Metric.ball_subset_ball (min_le_left _ _)).trans hball₃)
  have hsqb : Schoenflies.Plane.closedSquare c rs ⊆ Metric.ball 0 1 :=
    hsqin.trans (subset_closure.trans (closure_inside_subset_ball hγ
      (image_subset_iff.mpr fun x hx => hΨb (hJE hx))))
  have hsqΦ : ∀ p ∈ Schoenflies.Plane.closedSquare c rs, dist (Φ p) P < δ₀ := fun p hp => by
    rw [← hΦc₁]
    exact hball₄ (lt_of_lt_of_le (Metric.mem_ball.mp (hsqball hp)) (min_le_right _ _))
  obtain ⟨W₂, hW₂, hW₂eq⟩ :=
    continuousOn_iff'.mp hΨc _ (Schoenflies.Plane.isOpen_openSquare c rs)
  have hPW₂ : P ∈ W₂ := by
    have hm : P ∈ Ψ ⁻¹' Schoenflies.Plane.openSquare c rs ∩ Eint :=
      ⟨Schoenflies.Plane.mem_openSquare_self hrs, hPE⟩
    rw [hW₂eq] at hm
    exact hm.1
  obtain ⟨ε₅, hε₅, hball₅⟩ :=
    Metric.isOpen_iff.mp (hW₂.inter hbdc.isOpen_compl) _ ⟨hPW₂, hEint _ hPE⟩
  set δ := min (ε₅ / 2) δ₀ with hδdef
  have hδpos : 0 < δ := lt_min (half_pos hε₅) hδ₀
  have hδδ₀ : δ ≤ δ₀ := min_le_right _ _
  have hE₁δ : ∀ y ∈ Ec, dist y P ≤ δ → y ∈ Eint ∧ Ψ y ∈ Schoenflies.Plane.openSquare c rs := by
    intro y hy hyd
    have hyW := hball₅ (Metric.mem_ball.mpr (lt_of_le_of_lt hyd
      (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε₅))))
    have hyE := hEc y hy hyW.2
    have hm : y ∈ W₂ ∩ Eint := ⟨hyW.1, hyE⟩
    rw [← hW₂eq] at hm
    exact ⟨hyE, hm.1⟩
  obtain ⟨Δ₁, Δbd₁, r₁, hr₁, hΔbd₁, hΔ₁ball, hΔbd₁E, DJ₁, DJint₁, hDJ₁cell, hDJ₁E, hDJ₁J,
    hPDJ₁⟩ := h324 Ec Eint Ebd P hpc δ hδpos
  have hJ₁pl : IsPLSphere 1 Δbd₁ := hΔbd₁ ▸ hr₁.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hJ₁sq : ∀ y ∈ Δbd₁, y ∈ Eint ∧ Ψ y ∈ Schoenflies.Plane.openSquare c rs := by
    intro y hy
    rw [hΔbd₁E] at hy
    exact hE₁δ y hy.2 (le_of_lt (Metric.mem_ball.mp (hΔ₁ball hy.1)))
  have hJ₁E : Δbd₁ ⊆ Eint := fun y hy => (hJ₁sq y hy).1
  have hDJ₁int : DJint₁ ⊆ DJ₁ := hDJ₁cell.subset
  obtain ⟨hDJ₁sub, hDJ₁img⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ
    hDJ₁cell hDJ₁E (hDJ₁J ▸ hJ₁pl) (hDJ₁J ▸ hJ₁E) hPDJ₁ hPE
  rw [hDJ₁J] at hDJ₁img
  have hγ₁ : Schoenflies.IsJordanCurve (Ψ '' Δbd₁) :=
    isJordanCurve_image_of_isPLSphere_one hJ₁pl hJ₁E hΨc hΨi
  have hsqJ := Schoenflies.isJordanCurve_frontier_closedSquare c hrs
  have hγ₁sq : Ψ '' Δbd₁ ⊆ Schoenflies.inside (frontier (Schoenflies.Plane.closedSquare c rs)) := by
    rw [Schoenflies.inside_frontier_closedSquare]
    rintro _ ⟨y, hy, rfl⟩
    exact (hJ₁sq y hy).2
  have hcl₁ : closure (Schoenflies.inside (Ψ '' Δbd₁)) ⊆ Schoenflies.Plane.openSquare c rs := by
    rw [← Schoenflies.inside_frontier_closedSquare]
    exact closure_inside_subset_inside_of_subset_inside hsqJ hγ₁ hγ₁sq
  have hDJ₁sq : ∀ y ∈ DJ₁, Ψ y ∈ Schoenflies.Plane.openSquare c rs := by
    intro y hy
    by_cases hyi : y ∈ DJint₁
    · have h1 : Ψ y ∈ Ψ '' DJint₁ := ⟨y, hyi, rfl⟩
      rw [hDJ₁img] at h1
      exact hcl₁ (subset_closure h1)
    · have h1 : y ∈ DJ₁ \ DJint₁ := ⟨hy, hyi⟩
      rw [hDJ₁J] at h1
      exact (hJ₁sq y h1).2
  have hclsq : closure (Schoenflies.inside (frontier (Schoenflies.Plane.closedSquare c rs))) ⊆
      Schoenflies.Plane.closedSquare c rs := by
    rw [closure_inside_eq_union hsqJ, Schoenflies.inside_frontier_closedSquare]
    exact union_subset hoc (frontier_subset_closure.trans
      (Schoenflies.Plane.isClosed_closedSquare c rs).closure_subset)
  set Gp := Metric.ball (0 : Schoenflies.Plane) 1 \
    closure (Schoenflies.inside (frontier (Schoenflies.Plane.closedSquare c rs))) with hGpdef
  have hGpre : IsPreconnected (Φ '' Gp) := by
    have h1 := isPreconnected_compl_union_iUnion_closure_inside
      {frontier (Schoenflies.Plane.closedSquare c rs)}
      (fun γ' hγ' => by rw [Finset.mem_singleton.mp hγ']; exact hsqJ)
      (fun a ha b hb hab =>
        (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim)
      (F₀ := (Metric.ball (0 : Schoenflies.Plane) 1)ᶜ) Metric.isOpen_ball.isClosed_compl
      (by rw [compl_compl]; exact (convex_ball (0 : Schoenflies.Plane) 1).isPreconnected)
      (fun γ' hγ' => by
        rw [Finset.mem_singleton.mp hγ']
        exact disjoint_compl_left_iff_subset.mpr (hclsq.trans hsqb))
    have heq : ((Metric.ball (0 : Schoenflies.Plane) 1)ᶜ ∪ ⋃ γ' ∈
        ({frontier (Schoenflies.Plane.closedSquare c rs)} : Finset (Set Schoenflies.Plane)),
          closure (Schoenflies.inside γ'))ᶜ = Gp := by
      rw [Finset.set_biUnion_singleton, compl_union, compl_compl]
      rfl
    rw [heq] at h1
    exact h1.image Φ (hΦc.mono fun p hp => hp.1)
  refine ⟨δ, Δ₁, r₁, DJ₁, DJint₁, Φ '' Gp, hδpos, hδδ₀, hr₁, hΔ₁ball, ?_, hDJ₁cell, hDJ₁E,
    hDJ₁J.trans hΔbd₁, hPDJ₁, fun y hy => (hDJmem y (hDJ₁sub hy)).mpr (hsqin (hoc (hDJ₁sq y hy))),
    fun y hy => ?_, hGpre, ?_, ?_, ?_⟩
  · rw [← hΔbd₁, hΔbd₁E]
  · rw [Metric.mem_ball, ← hΦΨ y (hDJ₁sub hy)]
    exact hsqΦ _ (hoc (hDJ₁sq y hy))
  · rintro _ ⟨p, hp, rfl⟩
    exact hΦb hp.1
  · rintro _ ⟨p, hp, rfl⟩
    refine not_le.mp fun hle => hp.2 ?_
    have h1 := (hE₁δ _ (hEintE (hΦb hp.1)) hle).2
    rw [hΨΦ p hp.1] at h1
    rw [Schoenflies.inside_frontier_closedSquare]
    exact subset_closure h1
  · intro y hy hyd
    refine ⟨Ψ y, ⟨hΨb hy, fun h' => ?_⟩, hΦΨ y hy⟩
    have h1 := hsqΦ _ (hclsq h')
    rw [hΦΨ y hy] at h1
    linarith only [h1, hyd]

theorem IsPseudoCell.isPolyhedron_sdiff_of_subdisk {Ec Eint Ebd : Set E3} {P : E3}
    (hpc : IsPseudoCell Ec Eint Ebd P) {DJ DJint DJ₁ DJint₁ : Set E3}
    (hDJ : IsTopologicalCellWithInterior 2 DJ DJint) (hDJE : DJ ⊆ Ec)
    (hJ : IsPLSphere 1 (DJ \ DJint)) (hJE : DJ \ DJint ⊆ Eint)
    (hDJ₁ : IsTopologicalCellWithInterior 2 DJ₁ DJint₁) (hDJ₁E : DJ₁ ⊆ Ec)
    (hJ₁ : IsPLSphere 1 (DJ₁ \ DJint₁)) (hJ₁E : DJ₁ \ DJint₁ ⊆ Eint) (hP : P ∈ DJint₁)
    (hsub : DJ₁ ⊆ DJint) :
    IsPolyhedron (DJ \ DJint₁) ∧ ∃ W : Set E3, IsOpen W ∧ DJint₁ = W ∩ DJ := by
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hpc.isOpenCell.exists_planarChart
  have hΨi : InjOn Ψ Eint := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  have hPE : P ∈ Eint := hpc.centerMem
  have hDJint : DJint ⊆ DJ := hDJ.subset
  have hDJ₁int : DJint₁ ⊆ DJ₁ := hDJ₁.subset
  obtain ⟨hDJsub, hDJimg⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hDJ hDJE hJ
    hJE (hsub (hDJ₁int hP)) hPE
  obtain ⟨hDJ₁sub, hDJ₁img⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hDJ₁
    hDJ₁E hJ₁ hJ₁E hP hPE
  set γ := Ψ '' (DJ \ DJint) with hγdef
  set γ₁ := Ψ '' (DJ₁ \ DJint₁) with hγ₁def
  have hγ : Schoenflies.IsJordanCurve γ := isJordanCurve_image_of_isPLSphere_one hJ hJE hΨc hΨi
  have hγ₁ : Schoenflies.IsJordanCurve γ₁ :=
    isJordanCurve_image_of_isPLSphere_one hJ₁ hJ₁E hΨc hΨi
  have hsep := Schoenflies.jordan_curve_theorem hγ
  have hsep₁ := Schoenflies.jordan_curve_theorem hγ₁
  have hclb := closure_inside_subset_ball hγ (image_subset_iff.mpr fun x hx => hΨb (hJE hx))
  have hDJmem : ∀ y ∈ Eint, y ∈ DJint ↔ Ψ y ∈ Schoenflies.inside γ := by
    intro y hy
    rw [← hDJimg]
    constructor
    · exact fun h' => ⟨y, h', rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rwa [← hΨi (hDJsub (hDJint hz)) hy hzy]
  have hDJ₁mem : ∀ y ∈ Eint, y ∈ DJint₁ ↔ Ψ y ∈ Schoenflies.inside γ₁ := by
    intro y hy
    rw [← hDJ₁img]
    constructor
    · exact fun h' => ⟨y, h', rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rwa [← hΨi (hDJ₁sub (hDJ₁int hz)) hy hzy]
  have hDJ₁cl : ∀ y ∈ Eint, y ∈ DJ₁ ↔ Ψ y ∈ closure (Schoenflies.inside γ₁) := by
    intro y hy
    rw [closure_inside_eq_union hγ₁]
    constructor
    · intro hyD
      by_cases hyi : y ∈ DJint₁
      · exact Or.inl ((hDJ₁mem y hy).mp hyi)
      · exact Or.inr ⟨y, ⟨hyD, hyi⟩, rfl⟩
    · rintro (h' | ⟨z, hz, hzy⟩)
      · exact hDJ₁int ((hDJ₁mem y hy).mpr h')
      · rw [← hΨi (hJ₁E hz) hy hzy]
        exact hz.1
  have hcl₁in : closure (Schoenflies.inside γ₁) ⊆ Schoenflies.inside γ := by
    intro p hp
    have hpb : p ∈ Metric.ball (0 : Schoenflies.Plane) 1 :=
      closure_inside_subset_ball hγ₁ (image_subset_iff.mpr fun x hx => hΨb (hJ₁E hx)) hp
    have hyE := hΦb hpb
    have h1 : Φ p ∈ DJ₁ := (hDJ₁cl _ hyE).mpr (by rw [hΨΦ p hpb]; exact hp)
    have h2 := (hDJmem _ hyE).mp (hsub h1)
    rwa [hΨΦ p hpb] at h2
  obtain ⟨W₃, hW₃, hW₃eq⟩ := continuousOn_iff'.mp hΨc _ hsep₁.isOpen_inside
  have hW₃DJ : DJint₁ = W₃ ∩ DJ := by
    ext y
    constructor
    · intro hy
      have hyE := hDJ₁sub (hDJ₁int hy)
      have hm : y ∈ Ψ ⁻¹' Schoenflies.inside γ₁ ∩ Eint := ⟨(hDJ₁mem y hyE).mp hy, hyE⟩
      rw [hW₃eq] at hm
      exact ⟨hm.1, hDJint (hsub (hDJ₁int hy))⟩
    · rintro ⟨hyW, hyD⟩
      have hyE := hDJsub hyD
      have hm : y ∈ W₃ ∩ Eint := ⟨hyW, hyE⟩
      rw [← hW₃eq] at hm
      exact (hDJ₁mem y hyE).mpr hm.1
  refine ⟨?_, W₃, hW₃, hW₃DJ⟩
  have hUeq : DJint \ DJ₁ = Φ '' (Schoenflies.inside γ \ closure (Schoenflies.inside γ₁)) := by
    ext y
    constructor
    · rintro ⟨hy, hy1⟩
      have hyE := hDJsub (hDJint hy)
      exact ⟨Ψ y, ⟨(hDJmem y hyE).mp hy, fun h' => hy1 ((hDJ₁cl y hyE).mpr h')⟩,
        hΦΨ y hyE⟩
    · rintro ⟨p, ⟨hp, hp1⟩, rfl⟩
      have hpb : p ∈ Metric.ball (0 : Schoenflies.Plane) 1 := hclb (subset_closure hp)
      have hyE := hΦb hpb
      refine ⟨(hDJmem _ hyE).mpr (by rw [hΨΦ p hpb]; exact hp), fun h' => hp1 ?_⟩
      have h2 := (hDJ₁cl _ hyE).mp h'
      rwa [hΨΦ p hpb] at h2
  have hUpre : IsPreconnected (DJint \ DJ₁) := by
    have h1 := isPreconnected_compl_union_iUnion_closure_inside {γ₁}
      (fun γ' hγ' => by rw [Finset.mem_singleton.mp hγ']; exact hγ₁)
      (fun a ha b hb hab =>
        (hab ((Finset.mem_singleton.mp ha).trans (Finset.mem_singleton.mp hb).symm)).elim)
      (F₀ := (Schoenflies.inside γ)ᶜ) hsep.isOpen_inside.isClosed_compl
      (by rw [compl_compl]; exact hsep.isConnected_inside.isPreconnected)
      (fun γ' hγ' => by
        rw [Finset.mem_singleton.mp hγ']
        exact disjoint_compl_left_iff_subset.mpr hcl₁in)
    have heq : ((Schoenflies.inside γ)ᶜ ∪ ⋃ γ' ∈ ({γ₁} : Finset (Set Schoenflies.Plane)),
        closure (Schoenflies.inside γ'))ᶜ =
          Schoenflies.inside γ \ closure (Schoenflies.inside γ₁) := by
      rw [Finset.set_biUnion_singleton, compl_union, compl_compl]
      rfl
    rw [heq] at h1
    rw [hUeq]
    exact h1.image Φ (hΦc.mono fun p hp => hclb (subset_closure hp.1))
  have hDJc : IsCompact DJ := hDJ.isCompact
  have hAnneq' : DJ \ DJint₁ = DJ ∩ W₃ᶜ := by
    rw [hW₃DJ]
    ext y
    simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
    tauto
  have hAnnc : IsCompact (DJ \ DJint₁) := by
    rw [hAnneq']
    exact hDJc.inter_right hW₃.isClosed_compl
  have hAnnE : DJ \ DJint₁ ⊆ Eint \ {P} := fun y hy =>
    ⟨hDJsub hy.1, fun h1 => hy.2 (by rw [mem_singleton_iff.mp h1]; exact hP)⟩
  obtain ⟨QA, hQA, hAnnQ, hQAE, -⟩ :=
    hpc.regular.exists_isPolyhedron_neighborhood_of_isCompact hAnnc hAnnE
  have hJann : DJ \ DJint ⊆ DJ \ DJint₁ := fun y hy =>
    ⟨hy.1, fun h1 => hy.2 (hsub (hDJ₁int h1))⟩
  have hJ₁ann : DJ₁ \ DJint₁ ⊆ DJ \ DJint₁ := fun y hy => ⟨hDJint (hsub hy.1), hy.2⟩
  have hUpoly : IsPolyhedron (closure (DJint \ DJ₁)) := by
    by_cases hUne : (DJint \ DJ₁).Nonempty
    swap
    · rw [not_nonempty_iff_eq_empty.mp hUne, closure_empty]
      exact IsPolyhedron.empty
    obtain ⟨p₀, hp₀⟩ := hUne
    obtain ⟨TQ, hTQfin, hTQ⟩ := hQA.exists_simplicialComplex
    obtain ⟨TL, hTLfin, hTL⟩ := (hJ.isPolyhedron.union hJ₁.isPolyhedron).exists_simplicialComplex
    have : Finite TQ.faces := hTQfin.to_subtype
    have : Finite TL.faces := hTLfin.to_subtype
    have hLQ : TL.space ⊆ TQ.space := by
      rw [hTL, hTQ]
      exact union_subset (hJann.trans hAnnQ) (hJ₁ann.trans hAnnQ)
    have hUsub : DJint \ DJ₁ ⊆ TQ.space \ TL.space := by
      rintro y ⟨hy, hy1⟩
      rw [hTQ, hTL]
      refine ⟨hAnnQ ⟨hDJint hy, fun h1 => hy1 (hDJ₁int h1)⟩, ?_⟩
      rintro (hyJ | hyJ)
      · exact hyJ.2 hy
      · exact hy1 hyJ.1
    have hApl : IsOpen (Schoenflies.inside γ \ closure (Schoenflies.inside γ₁)) :=
      hsep.isOpen_inside.sdiff isClosed_closure
    have hBpl : IsOpen (Schoenflies.outside γ ∪ Schoenflies.inside γ₁) :=
      hsep.isOpen_outside.union hsep₁.isOpen_inside
    obtain ⟨Wa, hWa, hWaeq⟩ := continuousOn_iff'.mp hΨc _ hApl
    obtain ⟨Wb, hWb, hWbeq⟩ := continuousOn_iff'.mp hΨc _ hBpl
    have hmemW : ∀ {S : Set Schoenflies.Plane} {W : Set E3}, Ψ ⁻¹' S ∩ Eint = W ∩ Eint →
        ∀ y ∈ Eint, (y ∈ W ↔ Ψ y ∈ S) := by
      intro S W hSW y hy
      constructor
      · intro h'
        have hm : y ∈ W ∩ Eint := ⟨h', hy⟩
        rw [← hSW] at hm
        exact hm.1
      · intro h'
        have hm : y ∈ Ψ ⁻¹' S ∩ Eint := ⟨h', hy⟩
        rw [hSW] at hm
        exact hm.1
    set cc := connectedComponentIn (TQ.space \ TL.space) p₀ with hccdef
    have hccE : cc ⊆ Eint := fun y hy => by
      have hy' := connectedComponentIn_subset _ _ hy
      rw [hTQ] at hy'
      exact (hQAE hy'.1).1
    have hcover : cc ⊆ Wa ∪ Wb := by
      intro y hy
      have hyE := hccE hy
      have hy' := connectedComponentIn_subset _ _ hy
      rw [hTL] at hy'
      have hyγ : Ψ y ∉ γ := fun h' => hy'.2 (Or.inl (by
        obtain ⟨z, hz, hzy⟩ := h'
        rwa [← hΨi (hJE hz) hyE hzy]))
      have hyγ₁ : Ψ y ∉ γ₁ := fun h' => hy'.2 (Or.inr (by
        obtain ⟨z, hz, hzy⟩ := h'
        rwa [← hΨi (hJ₁E hz) hyE hzy]))
      by_cases hin : Ψ y ∈ Schoenflies.inside γ
      · by_cases hcl : Ψ y ∈ closure (Schoenflies.inside γ₁)
        · rw [closure_inside_eq_union hγ₁] at hcl
          exact Or.inr ((hmemW hWbeq y hyE).mpr (Or.inr (hcl.resolve_right hyγ₁)))
        · exact Or.inl ((hmemW hWaeq y hyE).mpr ⟨hin, hcl⟩)
      · have hout : Ψ y ∈ Schoenflies.outside γ := by
          have h1 : Ψ y ∈ γᶜ := hyγ
          rw [← Schoenflies.inside_union_outside] at h1
          exact h1.resolve_left hin
        exact Or.inr ((hmemW hWbeq y hyE).mpr (Or.inl hout))
    have hdisj : cc ∩ (Wa ∩ Wb) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y ⟨hy, hya, hyb⟩ => ?_
      have hyE := hccE hy
      have ha := (hmemW hWaeq y hyE).mp hya
      rcases (hmemW hWbeq y hyE).mp hyb with hb | hb
      · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside ha.1 hb
      · exact ha.2 (subset_closure hb)
    have hp₀E := hDJsub (hDJint hp₀.1)
    have hp₀a : p₀ ∈ Wa := (hmemW hWaeq p₀ hp₀E).mpr ⟨(hDJmem p₀ hp₀E).mp hp₀.1,
      fun h' => hp₀.2 ((hDJ₁cl p₀ hp₀E).mpr h')⟩
    have hp₀cc : p₀ ∈ cc := mem_connectedComponentIn (hUsub hp₀)
    have hcc : DJint \ DJ₁ = cc := by
      refine (hUpre.subset_connectedComponentIn hp₀ hUsub).antisymm ?_
      rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn Wa Wb
        hWa hWb hcover hdisj with hsub' | hsub'
      · intro y hy
        have hyE := hccE hy
        have ha := (hmemW hWaeq y hyE).mp (hsub' hy)
        exact ⟨(hDJmem y hyE).mpr ha.1, fun h' => ha.2 ((hDJ₁cl y hyE).mp h')⟩
      · exfalso
        have hm : p₀ ∈ cc ∩ (Wa ∩ Wb) := ⟨hp₀cc, hp₀a, hsub' hp₀cc⟩
        rw [hdisj] at hm
        exact hm
    rw [hcc]
    exact isPolyhedron_closure_connectedComponentIn_sdiff_of_subset TQ TL hLQ p₀
  have hAnneq : DJ \ DJint₁ = closure (DJint \ DJ₁) ∪ ((DJ \ DJint) ∪ (DJ₁ \ DJint₁)) := by
    apply Subset.antisymm
    · rintro y ⟨hy, hy1⟩
      by_cases hyi : y ∈ DJint
      · by_cases hy2 : y ∈ DJ₁
        · exact Or.inr (Or.inr ⟨hy2, hy1⟩)
        · exact Or.inl (subset_closure ⟨hyi, hy2⟩)
      · exact Or.inr (Or.inl ⟨hy, hyi⟩)
    · refine union_subset ?_ (union_subset hJann hJ₁ann)
      refine closure_minimal (fun y hy => ⟨hDJint hy.1, fun h1 => hy.2 (hDJ₁int h1)⟩) ?_
      rw [hAnneq']
      exact hDJc.isClosed.inter hW₃.isClosed_compl
  rw [hAnneq]
  exact hUpoly.union (hJ.isPolyhedron.union hJ₁.isPolyhedron)

theorem exists_isCombinatorialManifold_sdiff_union {Δ Δ₁ DJ DJint DJ₁ DJint₁ : Set E3}
    {r r₁ : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ₁)
    (hDJ : IsTopologicalCellWithInterior 2 DJ DJint)
    (hDJ₁ : IsTopologicalCellWithInterior 2 DJ₁ DJint₁)
    (hDJJ : DJ \ DJint = r '' stdSimplexBoundary 2)
    (hDJ₁J : DJ₁ \ DJint₁ = r₁ '' stdSimplexBoundary 2) (hsub : DJ₁ ⊆ DJint)
    (hopen : ∃ W : Set E3, IsOpen W ∧ DJint₁ = W ∩ DJ)
    (hΔDJ : Δ ∩ DJ = r '' stdSimplexBoundary 2) (hΔ₁DJ : Δ₁ ∩ DJ = r₁ '' stdSimplexBoundary 2)
    (hΔΔ₁ : Disjoint Δ Δ₁) (hann : IsPolyhedron (DJ \ DJint₁)) :
    ∃ L : Geometry.SimplicialComplex ℝ E3, L.faces.Finite ∧
      L.space = Δ ∪ ((DJ \ DJint₁) ∪ Δ₁) ∧ IsCombinatorialManifold 2 L ∧
        IsConnected L.space := by
  have hDJint : DJint ⊆ DJ := hDJ.subset
  have hDJ₁int : DJint₁ ⊆ DJ₁ := hDJ₁.subset
  have hJΔ : r '' stdSimplexBoundary 2 ⊆ Δ := by
    rw [← hΔDJ]
    exact inter_subset_left
  have hJ₁Δ₁ : r₁ '' stdSimplexBoundary 2 ⊆ Δ₁ := by
    rw [← hΔ₁DJ]
    exact inter_subset_left
  have hΔcell := hr.isTopologicalCellWithInterior
  have hΔ₁cell := hr₁.isTopologicalCellWithInterior
  have hBD : Δ₁ ∩ DJ = DJ₁ \ DJint₁ := by rw [hΔ₁DJ, hDJ₁J]
  have hBb : Δ₁ \ (Δ₁ \ r₁ '' stdSimplexBoundary 2) = DJ₁ \ DJint₁ := by
    rw [hDJ₁J, Set.sdiff_sdiff_cancel_left hJ₁Δ₁]
  obtain ⟨hD'cell, hD'bd⟩ := IsTopologicalCellWithInterior.sdiff_union_of_subcell hDJ
    hDJ₁ hΔ₁cell hsub hopen hBD hBb
  have hAB : Δ ∩ ((DJ \ DJint₁) ∪ Δ₁) = Δ \ (Δ \ r '' stdSimplexBoundary 2) := by
    rw [Set.sdiff_sdiff_cancel_left hJΔ]
    ext y
    constructor
    · rintro ⟨hyΔ, hy | hy⟩
      · rw [← hΔDJ]
        exact ⟨hyΔ, hy.1⟩
      · exact (Set.disjoint_left.mp hΔΔ₁ hyΔ hy).elim
    · intro hy
      have hyD : y ∈ DJ \ DJint := by
        rw [hDJJ]
        exact hy
      exact ⟨hJΔ hy, Or.inl ⟨hyD.1, fun h1 => hyD.2 (hsub (hDJ₁int h1))⟩⟩
  have hBA : ((DJ \ DJint₁) ∪ Δ₁) \ ((DJint \ DJ₁) ∪ Δ₁) =
      Δ \ (Δ \ r '' stdSimplexBoundary 2) := by
    rw [Set.sdiff_sdiff_cancel_left hJΔ, hD'bd, hDJJ]
  have hsphere := IsTopologicalCellWithInterior.isTopologicalSphere_union hΔcell hD'cell hAB hBA
  have hΔpoly : IsPolyhedron Δ := IsPLBall.isPolyhedron ⟨r, hr⟩
  have hΔ₁poly : IsPolyhedron Δ₁ := IsPLBall.isPolyhedron ⟨r₁, hr₁⟩
  obtain ⟨L, hLfin, hLS⟩ := (hΔpoly.union (hann.union hΔ₁poly)).exists_simplicialComplex
  have : Finite L.faces := hLfin.to_subtype
  have hsphL : IsTopologicalSphere 2 L.space := by
    rw [hLS]
    exact hsphere
  exact ⟨L, hLfin, hLS, IsTopologicalSphere.isCombinatorialManifold L hsphL, hsphL.isConnected⟩

end Replacement

section Sides

theorem false_of_sides_joined {S E O Vv Vu Q G : Set E3} (L : Geometry.SimplicialComplex ℝ E3)
    [Finite L.faces] (hL : IsCombinatorialManifold 2 L) (hconn : IsConnected L.space)
    (hLS : L.space = S) (hSc : IsClosed S) {x₁ : E3} (hx₁S : x₁ ∈ S) (hx₁E : x₁ ∈ E)
    {C A' B' : Set E3} (hC : C ∈ 𝓝 x₁) (hA' : IsConnected A') (hB' : IsConnected B')
    (hAB' : A' ∪ B' = C \ E) (hcA' : C ∩ E ⊆ closure A') (hcB' : C ∩ E ⊆ closure B')
    (hCS : C \ S = C \ E) (hCO : C \ E ⊆ O) {a : E3} (haQ : a ∈ Q) (hQ : IsPreconnected Q)
    (hQS : Disjoint Q S) (hQE : Disjoint Q E) (hQV : Q ⊆ Vv) (hx₁Q : x₁ ∈ closure Q)
    (hsatv : ∀ Z : Set E3, IsPreconnected Z → Z ⊆ O → (Z ∩ Vv).Nonempty → Z ⊆ Vv)
    (hsatu : ∀ Z : Set E3, IsPreconnected Z → Z ⊆ O → (Z ∩ Vu).Nonempty → Z ⊆ Vu)
    (hVdisj : Disjoint Vv Vu) (hVuE : Disjoint Vu E) (hEVu : E ⊆ closure Vu)
    (hG : IsPreconnected G) (hGE : G ⊆ E) (hx₁G : x₁ ∈ G)
    (hsides : ∀ x ∈ G, ∀ U ∈ 𝓝 x, ∃ C ∈ 𝓝 x, C ⊆ U ∧ ∃ A B : Set E3, IsConnected A ∧
      IsConnected B ∧ A ∪ B = C \ E ∧ C ∩ E ⊆ closure A ∧ C ∩ E ⊆ closure B)
    (hloc : ∀ x ∈ G, ∃ U ∈ 𝓝 x, U \ E ⊆ O ∧ Disjoint (U ∩ Vu) S) {z₀ : E3}
    (hz₀S : z₀ ∉ S) (hz₀G : z₀ ∈ closure G) (hz₀a : z₀ ∈ connectedComponentIn Sᶜ a) :
    False := by
  have hCS' : C \ E ⊆ Sᶜ := fun y hy => by
    rw [← hCS] at hy
    exact hy.2
  have hQ𝒞 : Q ⊆ connectedComponentIn Sᶜ a :=
    hQ.subset_connectedComponentIn haQ fun y hy hyS => Set.disjoint_left.mp hQS hy hyS
  have key : ∀ A B : Set E3, IsConnected A → IsConnected B → A ∪ B = C \ E →
      C ∩ E ⊆ closure B → (Q ∩ A).Nonempty → False := by
    intro A B hA hB hAB hcB hQA
    have hAsub : A ⊆ C \ E := by
      rw [← hAB]
      exact subset_union_left
    have hBsub : B ⊆ C \ E := by
      rw [← hAB]
      exact subset_union_right
    obtain ⟨q, hqQ, hqA⟩ := hQA
    have hA𝒞 : A ⊆ connectedComponentIn Sᶜ a := by
      have h1 := hA.isPreconnected.subset_connectedComponentIn hqA (hAsub.trans hCS')
      rwa [← connectedComponentIn_eq (hQ𝒞 hqQ)] at h1
    have hAV : A ⊆ Vv := hsatv A hA.isPreconnected (hAsub.trans hCO) ⟨q, hqA, hQV hqQ⟩
    obtain ⟨y, hyC, hyV⟩ := mem_closure_iff_nhds.mp (hEVu hx₁E) C hC
    have hyAB : y ∈ A ∪ B := by
      rw [hAB]
      exact ⟨hyC, Set.disjoint_left.mp hVuE hyV⟩
    have hyB : y ∈ B := hyAB.resolve_left fun hyA => Set.disjoint_left.mp hVdisj (hAV hyA) hyV
    have hBV : B ⊆ Vu := hsatu B hB.isPreconnected (hBsub.trans hCO) ⟨y, hyB, hyV⟩
    have hB𝒞 : B ⊆ connectedComponentIn Sᶜ y :=
      hB.isPreconnected.subset_connectedComponentIn hyB (hBsub.trans hCS')
    have hBT : B ⊆ Vu ∩ connectedComponentIn Sᶜ y := fun w hw => ⟨hBV hw, hB𝒞 hw⟩
    have hlocT : ∀ x ∈ G, ∃ U ∈ 𝓝 x, ∀ Z : Set E3, IsPreconnected Z → Z ⊆ U \ E →
        (Z ∩ (Vu ∩ connectedComponentIn Sᶜ y)).Nonempty →
          Z ⊆ Vu ∩ connectedComponentIn Sᶜ y := by
      intro x hx
      obtain ⟨U, hU, hUO, hUS⟩ := hloc x hx
      refine ⟨U, hU, fun Z hZ hZU hZT => ?_⟩
      obtain ⟨z, hzZ, hzV, hz𝒞⟩ := hZT
      have hZV := hsatu Z hZ (hZU.trans hUO) ⟨z, hzZ, hzV⟩
      have hZS : Z ⊆ Sᶜ := fun w hw hwS =>
        Set.disjoint_left.mp hUS ⟨(hZU hw).1, hZV hw⟩ hwS
      have hZ𝒞 : Z ⊆ connectedComponentIn Sᶜ y := by
        have h1 := hZ.subset_connectedComponentIn hzZ hZS
        rwa [← connectedComponentIn_eq hz𝒞] at h1
      exact fun w hw => ⟨hZV hw, hZ𝒞 hw⟩
    have hTE : Disjoint (Vu ∩ connectedComponentIn Sᶜ y) E :=
      Set.disjoint_left.mpr fun w hw hwE => Set.disjoint_left.mp hVuE hw.1 hwE
    have hGT := IsPreconnected.subset_closure_of_forall_sides hG hGE hTE hsides hlocT
      ⟨x₁, hx₁G, closure_mono hBT (hcB ⟨mem_of_mem_nhds hC, hx₁E⟩)⟩
    obtain ⟨dz, hdz, hballz⟩ := Metric.isOpen_iff.mp hSc.isOpen_compl z₀ hz₀S
    have hz₀T : z₀ ∈ closure (Vu ∩ connectedComponentIn Sᶜ y) :=
      closure_minimal hGT isClosed_closure hz₀G
    obtain ⟨y', hy'T, hy'd⟩ := Metric.mem_closure_iff.mp hz₀T dz hdz
    have hballz𝒞 : Metric.ball z₀ dz ⊆ connectedComponentIn Sᶜ a := by
      have h1 := (convex_ball z₀ dz).isPreconnected.subset_connectedComponentIn
        (Metric.mem_ball_self hdz) hballz
      rwa [← connectedComponentIn_eq hz₀a] at h1
    have hy'𝒞 := hballz𝒞 (by rw [Metric.mem_ball, dist_comm]; exact hy'd)
    have hB𝒞₀ : B ⊆ connectedComponentIn Sᶜ a := by
      have h1 : connectedComponentIn Sᶜ y = connectedComponentIn Sᶜ a := by
        rw [connectedComponentIn_eq hy'T.2, ← connectedComponentIn_eq hy'𝒞]
      rw [← h1]
      exact hB𝒞
    refine IsCombinatorialManifold.false_of_sdiff_subset_connectedComponentIn L hL (by simp)
      hconn (by rw [hLS]; exact hx₁S) hC (y := a) ?_
    rw [hLS, hCS, ← hAB]
    exact union_subset hA𝒞 hB𝒞₀
  obtain ⟨q, hqC, hqQ⟩ := mem_closure_iff_nhds.mp hx₁Q C hC
  have hqAB : q ∈ A' ∪ B' := by
    rw [hAB']
    exact ⟨hqC, Set.disjoint_left.mp hQE hqQ⟩
  rcases hqAB with hqA | hqB
  · exact key A' B' hA' hB' hAB' hcB' ⟨q, hqQ, hqA⟩
  · exact key B' A' hB' hA' (by rw [union_comm]; exact hAB') hcA' ⟨q, hqQ, hqB⟩

end Sides

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem section33_disk_meets_graph (h324 : Moise324)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (hend : ∀ v : K.vertices, ((SimplicialComplex.edgeGraph K).neighborSet v).ncard ≠ 1)
    {v₁ : EuclideanSpace ℝ (Fin 3)} (hv₁ : v₁ ∈ K.vertices)
    {e₁ : Finset (EuclideanSpace ℝ (Fin 3))} (he₁ : e₁ ∈ K.faces) (hcard : e₁.card = 2)
    {Δ : Set (EuclideanSpace ℝ (Fin 3))} {r : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔ : Δ ⊆ Cpp v₁ ∩ interior N')
    (hbd : Δ ∩ Ec e₁ = r '' stdSimplexBoundary 2)
    (hcenter : ∃ DJ DJint : Set (EuclideanSpace ℝ (Fin 3)),
      IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec e₁ ∧
        DJ \ DJint = r '' stdSimplexBoundary 2 ∧ h (e₁.centroid ℝ id) ∈ DJint)
    (hmiss : ∀ e ∈ K.faces, e.card = 2 → e ≠ e₁ → Disjoint Δ (Ec e)) :
    (Δ ∩ h '' K.space).Nonempty := by
  by_contra hK'
  have hΔK : Δ ∩ h '' K.space = ∅ := not_nonempty_iff_eq_empty.mp hK'
  obtain ⟨DJ, DJint, hDJcell, hDJE, hDJJ, hPDJ⟩ := hcenter
  have ht := hd.tube
  have hpc₁ := hd.pseudoCell e₁ he₁ hcard
  have hE₁c : IsClosed (Ec e₁) := hpc₁.isClosed
  have hbdc : IsClosed (Ebd e₁) := by
    obtain ⟨φ⟩ := hpc₁.isSphere
    exact (isCompact_iff_compactSpace.mpr φ.symm.compactSpace).isClosed
  have hEintE : Eint e₁ ⊆ Ec e₁ := by
    rw [hpc₁.carrierEq]
    exact subset_union_left
  have hbdE : Ebd e₁ ⊆ Ec e₁ := by
    rw [hpc₁.carrierEq]
    exact subset_union_right
  have hEc : ∀ y ∈ Ec e₁, y ∉ Ebd e₁ → y ∈ Eint e₁ := fun y hy hyb => by
    rw [hpc₁.carrierEq] at hy
    exact hy.resolve_right hyb
  have hEint : ∀ y ∈ Eint e₁, y ∉ Ebd e₁ := fun y hy hyb =>
    Set.disjoint_left.mp hpc₁.disjointRim hy hyb
  have hbdfr : Ebd e₁ ⊆ frontier N' := by
    rw [← hd.rimFrontier e₁ he₁ hcard]
    exact inter_subset_right
  have hPE : h (e₁.centroid ℝ id) ∈ Eint e₁ := hpc₁.centerMem
  have hJΔ : r '' stdSimplexBoundary 2 ⊆ Δ := by
    rw [← hbd]
    exact inter_subset_left
  have hJE₁ : r '' stdSimplexBoundary 2 ⊆ Ec e₁ := by
    rw [← hbd]
    exact inter_subset_right
  have hJpl : IsPLSphere 1 (r '' stdSimplexBoundary 2) :=
    hr.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hJE : r '' stdSimplexBoundary 2 ⊆ Eint e₁ := fun y hy =>
    hEc y (hJE₁ hy) fun hyb => (hbdfr hyb).2 (hΔ (hJΔ hy)).2
  have hv₁e : v₁ ∈ e₁ := by
    by_contra hn
    have h0 := hd.handlePiece_inter_pseudoCell_eq_empty hv₁ he₁ hcard hn
    obtain ⟨p, hp⟩ := (isConnected_stdSimplexBoundary 0).nonempty
    have hy' : r p ∈ Cpp v₁ ∩ Ec e₁ := ⟨(hΔ (hJΔ ⟨p, hp, rfl⟩)).1, hJE₁ ⟨p, hp, rfl⟩⟩
    rw [h0] at hy'
    exact hy'
  obtain ⟨u, hue, hu₁⟩ := Finset.exists_mem_ne (by omega : 1 < e₁.card) v₁
  have hu : u ∈ K.vertices :=
    K.down_closed he₁ (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  have hCvu : Cpp v₁ ∩ Cpp u = Ec e₁ :=
    hd.handlePiece_inter_eq_pseudoCell he₁ hcard hv₁e hue hu₁.symm
  obtain ⟨e₂, he₂, he₂c, hv₁e₂, he₂ne⟩ :=
    exists_edge_ne_of_ncard_neighborSet_ne_one K ht.facesFinite hend hv₁ he₁ hcard hv₁e
  have hpc₂ := hd.pseudoCell e₂ he₂ he₂c
  have hE₁₂ : Disjoint (Ec e₁) (Ec e₂) :=
    hd.pseudoCellDisjoint e₁ he₁ hcard e₂ he₂ he₂c he₂ne.symm
  have hP₂E₂ : h (e₂.centroid ℝ id) ∈ Ec e₂ := by
    have hmem : h (e₂.centroid ℝ id) ∈ Ec e₂ ∩ h '' K.space := by
      rw [hd.meetsGraph e₂ he₂ he₂c]
      exact mem_singleton _
    exact hmem.1
  obtain ⟨O₀, hO₀def⟩ : ∃ O₀ : Set E3,
      O₀ = N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := ⟨_, rfl⟩
  have hO₀E : ∀ z ∈ O₀, ∀ e ∈ K.faces, e.card = 2 → z ∉ Ec e := fun z hz e he hec hze => by
    rw [hO₀def] at hz
    exact hz.2 (mem_iUnion₂.mpr ⟨e, ⟨he, hec⟩, hze⟩)
  have hsatV : ∀ w : E3, ∀ Z : Set E3, IsPreconnected Z → Z ⊆ O₀ →
      (Z ∩ connectedComponentIn O₀ (h w)).Nonempty → Z ⊆ connectedComponentIn O₀ (h w) := by
    rintro w Z hZ hZO ⟨z, hzZ, hzV⟩
    rw [connectedComponentIn_eq hzV]
    exact hZ.subset_connectedComponentIn hzZ hZO
  have hVO : ∀ w : E3, connectedComponentIn O₀ (h w) ⊆ O₀ := fun w =>
    connectedComponentIn_subset _ _
  have hVC : ∀ w ∈ K.vertices, connectedComponentIn O₀ (h w) ⊆ Cpp w := fun w hw => by
    rw [hd.componentClosure w hw, ← hO₀def]
    exact subset_closure
  have hVv₁u : Disjoint (connectedComponentIn O₀ (h v₁)) (connectedComponentIn O₀ (h u)) := by
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    have hz : z ∈ Cpp v₁ ∩ Cpp u := ⟨hVC v₁ hv₁ hz₁, hVC u hu hz₂⟩
    rw [hCvu] at hz
    exact hO₀E z (hVO _ hz₁) e₁ he₁ hcard hz
  have hVuΔ : Disjoint (connectedComponentIn O₀ (h u)) Δ := by
    refine Set.disjoint_left.mpr fun z hz hzΔ => ?_
    have hz' : z ∈ Cpp v₁ ∩ Cpp u := ⟨(hΔ hzΔ).1, hVC u hu hz⟩
    rw [hCvu] at hz'
    exact hO₀E z (hVO _ hz) e₁ he₁ hcard hz'
  have hE₁Cu : Ec e₁ ⊆ closure (connectedComponentIn O₀ (h u)) := by
    rw [hO₀def, ← hd.componentClosure u hu, ← hCvu]
    exact inter_subset_right
  have hN'int : ∀ y ∈ N', y ∉ frontier N' → y ∈ interior N' := fun y hy hyf => by
    by_contra hyi
    exact hyf ⟨subset_closure hy, hyi⟩
  have hE₁N' : Ec e₁ ⊆ N' := by
    rw [hd.coversTube]
    exact (hd.pseudoCell_subset_handlePiece he₁ hcard hv₁e).trans
      (subset_biUnion_of_mem (u := Cpp) hv₁)
  have hEintN' : Eint e₁ ⊆ interior N' := fun y hy =>
    hN'int y (hE₁N' (hEintE hy)) fun hyf => by
      have hyb : y ∈ Ec e₁ ∩ frontier N' := ⟨hEintE hy, hyf⟩
      rw [hd.rimFrontier e₁ he₁ hcard] at hyb
      exact hEint y hy hyb
  have hDJint : DJint ⊆ DJ := hDJcell.subset
  obtain ⟨Ψ, Φ, hΨc, hΦc, hΨb, hΦb, hΦΨ, hΨΦ, -⟩ := hpc₁.isOpenCell.exists_planarChart
  obtain ⟨hDJsub, hDJimg⟩ := hpc₁.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hDJcell
    hDJE (hDJJ ▸ hJpl) (hDJJ ▸ hJE) hPDJ hPE
  have hΨi : InjOn Ψ (Eint e₁) := fun x hx y hy hxy => by
    rw [← hΦΨ x hx, ← hΦΨ y hy, hxy]
  obtain ⟨W₁, hW₁, hW₁eq⟩ := continuousOn_iff'.mp hΨc _
    (Schoenflies.jordan_curve_theorem (isJordanCurve_image_of_isPLSphere_one (hDJJ ▸ hJpl)
      (hDJJ ▸ hJE) hΨc hΨi)).isOpen_inside
  have hDJW : ∀ y ∈ Eint e₁, (y ∈ DJint ↔ y ∈ W₁) := by
    intro y hy
    constructor
    · intro h'
      have hm : y ∈ Ψ ⁻¹' Schoenflies.inside (Ψ '' (DJ \ DJint)) ∩ Eint e₁ := by
        rw [← hDJimg]
        exact ⟨⟨y, h', rfl⟩, hy⟩
      rw [hW₁eq] at hm
      exact hm.1
    · intro h'
      have hm : y ∈ W₁ ∩ Eint e₁ := ⟨h', hy⟩
      rw [← hW₁eq, ← hDJimg] at hm
      obtain ⟨z, hz, hzy⟩ := hm.1
      rwa [← hΨi (hDJsub (hDJint hz)) hy hzy]
  obtain ⟨Uo, hUodef⟩ : ∃ Uo : Set E3,
      Uo = ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ e ≠ e₁}, Ec e := ⟨_, rfl⟩
  have hUoc : IsClosed Uo := by
    rw [hUodef]
    exact (ht.facesFinite.subset fun e he => he.1).isClosed_biUnion fun e he =>
      (hd.pseudoCell e he.1 he.2.1).isClosed
  have hE₁Uo : Disjoint (Ec e₁) Uo := by
    refine Set.disjoint_left.mpr fun z hz hzU => ?_
    rw [hUodef] at hzU
    obtain ⟨e, ⟨he, hec, hne⟩, hze⟩ := mem_iUnion₂.mp hzU
    exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e₁ he₁ hcard e he hec hne.symm) hz hze
  have hO₀mem : ∀ z ∈ N', z ∉ Ec e₁ → z ∉ Uo → z ∈ O₀ := by
    intro z hzN hz1 hzU
    rw [hO₀def]
    refine ⟨hzN, fun hz => ?_⟩
    obtain ⟨e, ⟨he, hec⟩, hze⟩ := mem_iUnion₂.mp hz
    by_cases hee : e = e₁
    · rw [hee] at hze
      exact hz1 hze
    · rw [hUodef] at hzU
      exact hzU (mem_iUnion₂.mpr ⟨e, ⟨he, hec, hee⟩, hze⟩)
  have hPΔ : h (e₁.centroid ℝ id) ∉ Δ := by
    intro hP
    have hPJ : h (e₁.centroid ℝ id) ∈ r '' stdSimplexBoundary 2 := by
      rw [← hbd]
      exact ⟨hP, hEintE hPE⟩
    rw [← hDJJ] at hPJ
    exact hPJ.2 hPDJ
  have hΔc : IsCompact Δ := (IsPLBall.isPolyhedron ⟨r, hr⟩).isCompact
  obtain ⟨O₁, hO₁def⟩ : ∃ O₁ : Set E3, O₁ = interior N' ∩ Δᶜ ∩ Uoᶜ ∩ W₁ ∩ (Ebd e₁)ᶜ :=
    ⟨_, rfl⟩
  have hO₁ : IsOpen O₁ := by
    rw [hO₁def]
    exact (((isOpen_interior.inter hΔc.isClosed.isOpen_compl).inter
      hUoc.isOpen_compl).inter hW₁).inter hbdc.isOpen_compl
  have hPO₁ : h (e₁.centroid ℝ id) ∈ O₁ := by
    rw [hO₁def]
    exact ⟨⟨⟨⟨hEintN' hPE, hPΔ⟩, fun hU => Set.disjoint_left.mp hE₁Uo (hEintE hPE) hU⟩,
      (hDJW _ hPE).mp hPDJ⟩, hEint _ hPE⟩
  have hO₁mem : ∀ y ∈ O₁, y ∈ interior N' ∧ y ∉ Δ ∧ y ∉ Uo ∧ y ∈ W₁ ∧ y ∉ Ebd e₁ :=
    fun y hy => by
      rw [hO₁def] at hy
      exact ⟨hy.1.1.1.1, hy.1.1.1.2, hy.1.1.2, hy.1.2, hy.2⟩
  obtain ⟨ε₀, hε₀, hball₀⟩ := Metric.isOpen_iff.mp hO₁ _ hPO₁
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = ε₀ / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact half_pos hε₀
  have hballO₁ : ∀ y, dist y (h (e₁.centroid ℝ id)) ≤ ρ → y ∈ O₁ := fun y hy =>
    hball₀ (lt_of_le_of_lt hy (by rw [hρdef]; exact half_lt_self hε₀))
  obtain ⟨a, Γ, hΓc, hΓconn, haΓ, hP₂Γ, hΓK, hPΓ, haρ, haV⟩ :=
    hd.exists_arm hv₁ he₁ hcard hv₁e he₂ he₂c hv₁e₂ he₂ne hρ
  rw [← hO₀def] at haV
  have hΓΔ : Disjoint Γ Δ := Set.disjoint_left.mpr fun y hy hyΔ => by
    have hm : y ∈ Δ ∩ h '' K.space := ⟨hyΔ, hΓK hy⟩
    rw [hΔK] at hm
    exact hm
  have hΓE₁ : Disjoint Γ (Ec e₁) := Set.disjoint_left.mpr fun y hy hyE => by
    have hm : y ∈ Ec e₁ ∩ h '' K.space := ⟨hyE, hΓK hy⟩
    rw [hd.meetsGraph e₁ he₁ hcard] at hm
    exact hPΓ (mem_singleton_iff.mp hm ▸ hy)
  have haP : a ≠ h (e₁.centroid ℝ id) := fun heq => hPΓ (heq ▸ haΓ)
  have hPO₂ : h (e₁.centroid ℝ id) ∈ (Γ ∪ Ec e₂)ᶜ := fun hP =>
    hP.elim hPΓ fun h2 => Set.disjoint_left.mp hE₁₂ (hEintE hPE) h2
  obtain ⟨ε₂, hε₂, hball₂⟩ :=
    Metric.isOpen_iff.mp (hΓc.isClosed.union hpc₂.isClosed).isOpen_compl _ hPO₂
  have hda : 0 < dist a (h (e₁.centroid ℝ id)) := dist_pos.mpr haP
  obtain ⟨δ₀, hδ₀def⟩ : ∃ δ₀ : ℝ, δ₀ = min (min ε₂ (dist a (h (e₁.centroid ℝ id)))) ρ / 2 :=
    ⟨_, rfl⟩
  have hmin : 0 < min (min ε₂ (dist a (h (e₁.centroid ℝ id)))) ρ :=
    lt_min (lt_min hε₂ hda) hρ
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    exact half_pos hmin
  have hδ₀lt : δ₀ < min (min ε₂ (dist a (h (e₁.centroid ℝ id)))) ρ := by
    rw [hδ₀def]
    exact half_lt_self hmin
  have hδ₀a : δ₀ < dist a (h (e₁.centroid ℝ id)) :=
    lt_of_lt_of_le hδ₀lt ((min_le_left _ _).trans (min_le_right _ _))
  have hδ₀ρ : δ₀ < ρ := lt_of_lt_of_le hδ₀lt (min_le_right _ _)
  have hδ₀O₂ : ∀ y, dist y (h (e₁.centroid ℝ id)) < δ₀ → y ∉ Γ ∧ y ∉ Ec e₂ := fun y hy => by
    have hyO := hball₂ (Metric.mem_ball.mpr (lt_of_lt_of_le hy
      ((le_of_lt hδ₀lt).trans ((min_le_left _ _).trans (min_le_left _ _)))))
    exact ⟨fun h' => hyO (Or.inl h'), fun h' => hyO (Or.inr h')⟩
  obtain ⟨δ, Δ₁, r₁, DJ₁, DJint₁, G, hδpos, hδδ₀, hr₁, hΔ₁ball, hΔ₁E, hDJ₁cell, hDJ₁E, hDJ₁J,
    hPDJ₁, hDJ₁DJ, hDJ₁ball, hGpre, hGE, hGδ, hGfar⟩ :=
    hpc₁.exists_replacementDisk h324 hDJcell hDJE (hDJJ ▸ hJpl) (hDJJ ▸ hJE) hPDJ hδ₀pos
  have hΔ₁P : ∀ y ∈ Δ₁, dist y (h (e₁.centroid ℝ id)) < δ₀ := fun y hy =>
    lt_of_lt_of_le (Metric.mem_ball.mp (hΔ₁ball hy)) hδδ₀
  have hDJ₁int : DJint₁ ⊆ DJ₁ := hDJ₁cell.subset
  have hJ₁pl : IsPLSphere 1 (r₁ '' stdSimplexBoundary 2) :=
    hr₁.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hJ₁E : DJ₁ \ DJint₁ ⊆ Eint e₁ := fun y hy => hDJsub (hDJint (hDJ₁DJ hy.1))
  obtain ⟨hAnnpoly, hopen⟩ := hpc₁.isPolyhedron_sdiff_of_subdisk hDJcell hDJE (hDJJ ▸ hJpl)
    (hDJJ ▸ hJE) hDJ₁cell hDJ₁E (hDJ₁J ▸ hJ₁pl) hJ₁E hPDJ₁ hDJ₁DJ
  have hΔΔ₁ : Disjoint Δ Δ₁ := Set.disjoint_right.mpr fun y hy hyΔ =>
    (hO₁mem y (hballO₁ y ((hΔ₁P y hy).le.trans hδ₀ρ.le))).2.1 hyΔ
  have hΔDJ : Δ ∩ DJ = r '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyΔ, hyD⟩
      rw [← hbd]
      exact ⟨hyΔ, hDJE hyD⟩
    · intro y hy
      have hyD : y ∈ DJ \ DJint := by
        rw [hDJJ]
        exact hy
      exact ⟨hJΔ hy, hyD.1⟩
  have hΔ₁DJ : Δ₁ ∩ DJ = r₁ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hy1, hyD⟩
      rw [← hΔ₁E]
      exact ⟨hy1, hDJE hyD⟩
    · intro y hy
      have hyD : y ∈ DJ₁ \ DJint₁ := by
        rw [hDJ₁J]
        exact hy
      rw [← hΔ₁E] at hy
      exact ⟨hy.1, hDJint (hDJ₁DJ hyD.1)⟩
  obtain ⟨L, hLfin, hLS, hLman, hLconn⟩ := exists_isCombinatorialManifold_sdiff_union hr hr₁
    hDJcell hDJ₁cell hDJJ hDJ₁J hDJ₁DJ hopen hΔDJ hΔ₁DJ hΔΔ₁ hAnnpoly
  have : Finite L.faces := hLfin.to_subtype
  obtain ⟨S, hSdef⟩ : ∃ S : Set E3, S = Δ ∪ ((DJ \ DJint₁) ∪ Δ₁) := ⟨_, rfl⟩
  rw [← hSdef] at hLS
  have hSmem : ∀ y ∈ S, y ∈ Δ ∨ y ∈ DJ ∨ y ∈ Δ₁ := fun y hy => by
    rw [hSdef] at hy
    rcases hy with hy | ⟨hy, -⟩ | hy
    · exact Or.inl hy
    · exact Or.inr (Or.inl hy)
    · exact Or.inr (Or.inr hy)
  have hSc : IsClosed S := by
    rw [← hLS]
    exact (isPolyhedron_space L).isClosed
  have hSint : S ⊆ interior N' := fun y hy => by
    rcases hSmem y hy with hy | hy | hy
    · exact (hΔ hy).2
    · exact hEintN' (hDJsub hy)
    · exact (hO₁mem y (hballO₁ y ((hΔ₁P y hy).le.trans hδ₀ρ.le))).1
  have hSfr : Disjoint S (frontier N') :=
    Set.disjoint_left.mpr fun y hy hyf => hyf.2 (hSint hy)
  have hSΓ : Disjoint S Γ := Set.disjoint_left.mpr fun y hy hyΓ => by
    rcases hSmem y hy with hy | hy | hy
    · exact Set.disjoint_left.mp hΓΔ hyΓ hy
    · exact Set.disjoint_left.mp hΓE₁ hyΓ (hDJE hy)
    · exact (hδ₀O₂ y (hΔ₁P y hy)).1 hyΓ
  have hSE₂ : Disjoint S (Ec e₂) := Set.disjoint_left.mpr fun y hy hyE => by
    rcases hSmem y hy with hy | hy | hy
    · exact Set.disjoint_left.mp (hmiss e₂ he₂ he₂c he₂ne) hy hyE
    · exact Set.disjoint_left.mp hE₁₂ (hDJE hy) hyE
    · exact (hδ₀O₂ y (hΔ₁P y hy)).2 hyE
  obtain ⟨z₀, hz₀⟩ : (Ebd e₁).Nonempty := by
    obtain ⟨φ⟩ := hpc₁.isSphere
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (r := 1)).mpr zero_le_one
    exact ⟨φ.symm ⟨v, hv⟩, (φ.symm ⟨v, hv⟩).2⟩
  have hfarbd : ∀ z ∈ Ebd e₁, ρ < dist z (h (e₁.centroid ℝ id)) := fun z hz => by
    by_contra hle
    exact (hbdfr hz).2 (hO₁mem z (hballO₁ z (not_lt.mp hle))).1
  have hrank : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank]
    simp
  have hashell : a ∈ Metric.ball (h (e₁.centroid ℝ id)) ρ \
      Metric.closedBall (h (e₁.centroid ℝ id)) δ₀ :=
    ⟨haρ, fun h' => (not_le.mpr hδ₀a) (Metric.mem_closedBall.mp h')⟩
  have haE : a ∉ Ec e₁ := fun h' => Set.disjoint_left.mp hΓE₁ haΓ h'
  obtain ⟨x₁, hx₁E, hx₁O, hx₁Q⟩ := exists_mem_closure_connectedComponentIn_ball_sdiff_closedBall
    hrank hpc₁.isPreconnected hE₁c (hEintE hPE) hδ₀pos hδ₀ρ
    ⟨z₀, hbdE hz₀, (hfarbd z₀ hz₀).le⟩ hashell haE
  obtain ⟨Q, hQdef⟩ : ∃ Q : Set E3, Q = connectedComponentIn ((Metric.ball
      (h (e₁.centroid ℝ id)) ρ \ Metric.closedBall (h (e₁.centroid ℝ id)) δ₀) \ Ec e₁) a :=
    ⟨_, rfl⟩
  rw [← hQdef] at hx₁Q
  have haQ : a ∈ Q := by
    rw [hQdef]
    exact mem_connectedComponentIn ⟨hashell, haE⟩
  have hQsub : ∀ y ∈ Q, dist y (h (e₁.centroid ℝ id)) < ρ ∧
      δ₀ < dist y (h (e₁.centroid ℝ id)) ∧ y ∉ Ec e₁ := fun y hy => by
    rw [hQdef] at hy
    have hy' := connectedComponentIn_subset _ _ hy
    exact ⟨hy'.1.1, not_le.mp fun h' => hy'.1.2 (Metric.mem_closedBall.mpr h'), hy'.2⟩
  have hQS : Disjoint Q S := by
    refine Set.disjoint_left.mpr fun y hyQ hyS => ?_
    have hy := hQsub y hyQ
    rcases hSmem y hyS with hyΔ | hyD | hy1
    · exact (hO₁mem y (hballO₁ y hy.1.le)).2.1 hyΔ
    · exact hy.2.2 (hDJE hyD)
    · exact lt_asymm (hΔ₁P y hy1) hy.2.1
  have hQO₀ : Q ⊆ O₀ := fun y hyQ => by
    have hy := hQsub y hyQ
    have hyO := hO₁mem y (hballO₁ y hy.1.le)
    exact hO₀mem y (interior_subset hyO.1) hy.2.2 hyO.2.2.1
  have hQpre : IsPreconnected Q := by
    rw [hQdef]
    exact isPreconnected_connectedComponentIn
  have hQV : Q ⊆ connectedComponentIn O₀ (h v₁) :=
    hsatV v₁ Q hQpre hQO₀ ⟨a, haQ, haV⟩
  have hx₁ρ : dist x₁ (h (e₁.centroid ℝ id)) < ρ := hx₁O.1
  have hx₁δ₀ : δ₀ < dist x₁ (h (e₁.centroid ℝ id)) :=
    not_le.mp fun h' => hx₁O.2 (Metric.mem_closedBall.mpr h')
  have hx₁O₁ := hO₁mem x₁ (hballO₁ x₁ hx₁ρ.le)
  have hx₁int : x₁ ∈ Eint e₁ := hEc x₁ hx₁E hx₁O₁.2.2.2.2
  have hx₁DJ₁ : x₁ ∉ DJ₁ := fun h' => lt_asymm (Metric.mem_ball.mp (hDJ₁ball h')) hx₁δ₀
  obtain ⟨O₄, hO₄def⟩ : ∃ O₄ : Set E3, O₄ = Metric.ball (h (e₁.centroid ℝ id)) ρ ∩
      (Metric.closedBall (h (e₁.centroid ℝ id)) δ₀)ᶜ ∩ W₁ ∩ (Ebd e₁)ᶜ ∩ DJ₁ᶜ := ⟨_, rfl⟩
  have hO₄ : IsOpen O₄ := by
    rw [hO₄def]
    exact ((((Metric.isOpen_ball.inter Metric.isClosed_closedBall.isOpen_compl).inter
      hW₁).inter hbdc.isOpen_compl).inter hDJ₁cell.isCompact.isClosed.isOpen_compl)
  have hx₁O₄ : x₁ ∈ O₄ := by
    rw [hO₄def]
    exact ⟨⟨⟨⟨hx₁ρ, hx₁O.2⟩, hx₁O₁.2.2.2.1⟩, hEint x₁ hx₁int⟩, hx₁DJ₁⟩
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.isOpen_iff.mp hO₄ x₁ hx₁O₄
  have hO₄mem : ∀ y ∈ Metric.ball x₁ ε₁, dist y (h (e₁.centroid ℝ id)) < ρ ∧
      δ₀ < dist y (h (e₁.centroid ℝ id)) ∧ y ∈ W₁ ∧ y ∉ Ebd e₁ ∧ y ∉ DJ₁ := by
    intro y hy
    have hyO := hball₁ hy
    rw [hO₄def] at hyO
    exact ⟨hyO.1.1.1.1, not_le.mp fun h' => hyO.1.1.1.2 (Metric.mem_closedBall.mpr h'),
      hyO.1.1.2, hyO.1.2, hyO.2⟩
  have hSloc : ∀ y ∈ Metric.ball x₁ ε₁, (y ∈ S ↔ y ∈ Ec e₁) := by
    intro y hy
    have hyO := hO₄mem y hy
    constructor
    · intro hyS
      rcases hSmem y hyS with hyΔ | hyD | hy1
      · exact ((hO₁mem y (hballO₁ y hyO.1.le)).2.1 hyΔ).elim
      · exact hDJE hyD
      · exact (lt_asymm (hΔ₁P y hy1) hyO.2.1).elim
    · intro hyE
      have hyint := hEc y hyE hyO.2.2.2.1
      have hyDJ := (hDJW y hyint).mpr hyO.2.2.1
      rw [hSdef]
      exact Or.inr (Or.inl ⟨hDJint hyDJ, fun h' => hyO.2.2.2.2 (hDJ₁int h')⟩)
  obtain ⟨C₁, hC₁, hC₁U, A', B', hA', hB', hAB', hcA', hcB'⟩ :=
    hpc₁.exists_connected_neighborhood_pair_sdiff hx₁int
      (fun h' => by rw [h', dist_self] at hx₁δ₀; exact (lt_irrefl _ (hδ₀pos.trans hx₁δ₀)))
      (Metric.ball_mem_nhds x₁ hε₁)
  have hC₁S : C₁ \ S = C₁ \ Ec e₁ := by
    ext y
    constructor
    · rintro ⟨hyC, hyS⟩
      exact ⟨hyC, fun hyE => hyS ((hSloc y (hC₁U hyC)).mpr hyE)⟩
    · rintro ⟨hyC, hyE⟩
      exact ⟨hyC, fun hyS => hyE ((hSloc y (hC₁U hyC)).mp hyS)⟩
  have hC₁O₀ : C₁ \ Ec e₁ ⊆ O₀ := fun y hy => by
    have hyO₁ := hO₁mem y (hballO₁ y (hO₄mem y (hC₁U hy.1)).1.le)
    exact hO₀mem y (interior_subset hyO₁.1) hy.2 hyO₁.2.2.1
  have hx₁S : x₁ ∈ S := (hSloc x₁ (Metric.mem_ball_self hε₁)).mpr hx₁E
  have hΓS : Γ ⊆ Sᶜ := fun y hy hyS => Set.disjoint_left.mp hSΓ hyS hy
  have hΓ𝒞 : Γ ⊆ connectedComponentIn Sᶜ a := hΓconn.subset_connectedComponentIn haΓ hΓS
  have hE₂𝒞 : Ec e₂ ⊆ connectedComponentIn Sᶜ a := by
    have hsubS : Ec e₂ ⊆ Sᶜ := fun y hy hyS => Set.disjoint_left.mp hSE₂ hyS hy
    have h1 := hpc₂.isPreconnected.subset_connectedComponentIn hP₂E₂ hsubS
    rwa [← connectedComponentIn_eq (hΓ𝒞 hP₂Γ)] at h1
  have hFrconn : IsPreconnected (h '' (frontier (C v₁) ∩ frontier N)) :=
    (ht.isConnected_frontier_inter_frontier hv₁).isPreconnected.image h
      (ht.continuousOn.mono fun y hy => ht.isClosed.frontier_subset hy.2)
  have hFrfr : h '' (frontier (C v₁) ∩ frontier N) ⊆ frontier N' := by
    rw [ht.frontier_eq_image_frontier]
    exact image_mono inter_subset_right
  have hrimFr : ∀ f ∈ K.faces, f.card = 2 → v₁ ∈ f →
      Ebd f ⊆ h '' (frontier (C v₁) ∩ frontier N) := fun f hf hfc hvf => by
    rw [hd.rimEq f hf hfc]
    exact image_mono (ht.rim_subset_frontier_inter_frontier hf hfc hv₁ hvf)
  obtain ⟨w₂, hw₂⟩ : (Ebd e₂).Nonempty := by
    obtain ⟨φ⟩ := hpc₂.isSphere
    obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 2)))
      (r := 1)).mpr zero_le_one
    exact ⟨φ.symm ⟨v, hv⟩, (φ.symm ⟨v, hv⟩).2⟩
  have hw₂E : w₂ ∈ Ec e₂ := by
    rw [hpc₂.carrierEq]
    exact Or.inr hw₂
  have hFr𝒞 : h '' (frontier (C v₁) ∩ frontier N) ⊆ connectedComponentIn Sᶜ a := by
    have hsubS : h '' (frontier (C v₁) ∩ frontier N) ⊆ Sᶜ := fun y hy hyS =>
      Set.disjoint_left.mp hSfr hyS (hFrfr hy)
    have h1 := hFrconn.subset_connectedComponentIn (hrimFr e₂ he₂ he₂c hv₁e₂ hw₂) hsubS
    rwa [← connectedComponentIn_eq (hE₂𝒞 hw₂E)] at h1
  have hz₀a : z₀ ∈ connectedComponentIn Sᶜ a := hFr𝒞 (hrimFr e₁ he₁ hcard hv₁e hz₀)
  have hz₀G : z₀ ∈ closure G := by
    refine mem_closure_iff_nhds.mpr fun t ht' => ?_
    have hz₀cl : z₀ ∈ closure (Eint e₁) := by
      rw [hpc₁.closureEq]
      exact Or.inr hz₀
    have hfar : (Metric.closedBall (h (e₁.centroid ℝ id)) δ₀)ᶜ ∈ 𝓝 z₀ :=
      Metric.isClosed_closedBall.isOpen_compl.mem_nhds fun h' =>
        (not_le.mpr (hδ₀ρ.trans (hfarbd z₀ hz₀))) (Metric.mem_closedBall.mp h')
    obtain ⟨g, ⟨hgt, hgfar⟩, hgE⟩ := mem_closure_iff_nhds.mp hz₀cl _ (Filter.inter_mem ht' hfar)
    exact ⟨g, hgt, hGfar g hgE (not_lt.mp fun h' => hgfar (Metric.mem_closedBall.mpr h'.le))⟩
  have hloc : ∀ x ∈ G, ∃ U ∈ 𝓝 x, U \ Ec e₁ ⊆ O₀ ∧
      Disjoint (U ∩ connectedComponentIn O₀ (h u)) S := by
    intro x hx
    have hxE := hGE hx
    have hxδ := hGδ x hx
    obtain ⟨U, hUdef⟩ : ∃ U : Set E3, U = interior N' ∩ Uoᶜ ∩
        (Metric.closedBall (h (e₁.centroid ℝ id)) δ)ᶜ := ⟨_, rfl⟩
    have hU : IsOpen U := by
      rw [hUdef]
      exact (isOpen_interior.inter hUoc.isOpen_compl).inter
        Metric.isClosed_closedBall.isOpen_compl
    have hxU : x ∈ U := by
      rw [hUdef]
      exact ⟨⟨hEintN' hxE, fun h' => Set.disjoint_left.mp hE₁Uo (hEintE hxE) h'⟩,
        fun h' => (not_le.mpr hxδ) (Metric.mem_closedBall.mp h')⟩
    refine ⟨U, hU.mem_nhds hxU, fun z hz => ?_, Set.disjoint_left.mpr fun w hw hwS => ?_⟩
    · have hzU := hz.1
      rw [hUdef] at hzU
      exact hO₀mem z (interior_subset hzU.1.1) hz.2 hzU.1.2
    · have hwU := hw.1
      rw [hUdef] at hwU
      rcases hSmem w hwS with hwΔ | hwD | hw1
      · exact Set.disjoint_left.mp hVuΔ hw.2 hwΔ
      · exact hO₀E w (hVO u hw.2) e₁ he₁ hcard (hDJE hwD)
      · exact hwU.2 (Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hΔ₁ball hw1)).le)
  exact false_of_sides_joined L hLman hLconn hLS hSc hx₁S hx₁E hC₁ hA' hB' hAB' hcA' hcB' hC₁S
    hC₁O₀ haQ hQpre hQS (Set.disjoint_left.mpr fun y hy hyE => (hQsub y hy).2.2 hyE) hQV hx₁Q
    (hsatV v₁) (hsatV u) hVv₁u
    (Set.disjoint_left.mpr fun w hw hwE => hO₀E w (hVO u hw) e₁ he₁ hcard hwE) hE₁Cu hGpre
    (hGE.trans hEintE) (hGfar x₁ hx₁int hx₁δ₀.le)
    (fun x hx U hU => hpc₁.exists_connected_neighborhood_pair_sdiff (hGE hx)
      (fun h' => by
        have h2 := hGδ x hx
        rw [h', dist_self] at h2
        exact lt_irrefl _ (hδpos.trans h2)) hU)
    hloc (fun h' => Set.disjoint_left.mp hSfr h' (hbdfr hz₀)) hz₀G hz₀a

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
