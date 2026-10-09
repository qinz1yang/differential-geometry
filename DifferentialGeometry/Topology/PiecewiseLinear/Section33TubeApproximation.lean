/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section33Approximation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
def Moise331OnTube : Prop :=
  ∀ (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3)))
    (N N' : Set (EuclideanSpace ℝ (Fin 3)))
    (C : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)))
    (D Dbd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3)))
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)),
    IsTube K N C D Dbd h N' → IsConnected K.space →
    (∀ v : K.vertices, ((SimplicialComplex.edgeGraph K).neighborSet v).ncard ≠ 1) →
    ∀ W : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3)),
      (∀ v ∈ K.vertices, W v ∈ nhdsSet (h '' C v)) →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ nhdsSet (h '' K.space) ∧
          ∀ v ∈ K.vertices, f '' C v ⊆ W v

section Extension

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_section33Extension_image_dualCell_subset (h324 : Moise324)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (frontier N) (frontier XK.space))
    (hgA : ∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ frontier XK.space)
    (hgD : ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ frontier XK.space) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ nhdsSet (h '' K.space) ∧
      ∀ v ∈ K.vertices, f '' C v ⊆
        Cpp v ∪ ⋃ e ∈ edgesAt K v, Metric.ball (h (e.centroid ℝ id)) δ := by
  classical
  have ht := hd.tube
  have hXfin := h2.facesFinite
  let _ : Finite XK.faces := hXfin.to_subtype
  have hXclosed : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have hKX : h '' K.space ⊆ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood
  obtain ⟨e₁, he₁, he₁c⟩ := ht.hasEdge
  obtain ⟨v₀, hv₀e⟩ := Finset.card_pos.mp (by omega : 0 < e₁.card)
  have hv₀ : v₀ ∈ K.vertices :=
    K.down_closed he₁ (Finset.singleton_subset_iff.mpr hv₀e) (Finset.singleton_nonempty v₀)
  have hint : (interior XK.space).Nonempty := ⟨h v₀, hKX (mem_image_of_mem h
    (K.convexHull_subset_space hv₀ (subset_convexHull ℝ _ (Finset.mem_singleton_self v₀))))⟩
  obtain ⟨hXint, hXc, hXfr⟩ := isConnected_interior_space_and_compl hXfin h2.isManifold h56.2.1 hint
  have hN'c : IsCompact N' := by
    rw [ht.imageEq]
    exact ht.isCompact.image_of_continuousOn ht.continuousOn
  have hsmall : ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v,
      dist x y < 4 * (Metric.diam N' + 1) / 4 := by
    intro v hv x hx y hy
    have hsub : Cpp v ⊆ N' := by
      rw [hd.coversTube]
      exact subset_biUnion_of_mem (u := Cpp) hv
    have hle := Metric.dist_le_diam_of_mem hN'c.isBounded (hsub hx) (hsub hy)
    linarith
  obtain ⟨δ₀, hδ₀, hball, hsep, hbEc, -, -⟩ := hd.exists_small_radius hKX hsmall
  set ρ := min δ₀ δ / 2 with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact half_pos (lt_min hδ₀ hδ)
  have hρδ₀ : 2 * ρ ≤ δ₀ := by
    rw [hρdef]
    linarith [min_le_left δ₀ δ]
  have hρδ : ρ < δ := by
    rw [hρdef]
    linarith [min_le_right δ₀ δ]
  obtain ⟨F, hF⟩ := hd.exists_plDisks h324 h2 h34 hρ
  have hPEc : ∀ e ∈ K.faces, e.card = 2 → h (e.centroid ℝ id) ∈ Ec e := fun e he hc => by
    have hpc := hd.pseudoCell e he hc
    rw [hpc.carrierEq]
    exact Or.inl hpc.centerMem
  have hball' : ∀ e ∈ K.faces, e.card = 2 →
      Metric.ball (h (e.centroid ℝ id)) (2 * ρ) ⊆ interior XK.space := fun e he hc =>
    (Metric.ball_subset_ball (by linarith)).trans (hball e he hc)
  have hsep' : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      3 * ρ ≤ dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)) :=
    fun e he hc e' he' hc' hne => by linarith [hsep e he hc e' he' hc' hne]
  have hballX : ∀ e ∈ K.faces, e.card = 2 →
      Metric.ball (h (e.centroid ℝ id)) ρ ⊆ interior XK.space := fun e he hc =>
    (Metric.ball_subset_ball (by linarith)).trans (hball' e he hc)
  have hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space := fun e he hc x hx => by
    rcases (hF e he hc).2.1 hx with h' | h'
    · exact h'.2
    · exact interior_subset (hballX e he hc h')
  have hFbd : ∀ e ∈ K.faces, e.card = 2 →
      F e ∩ frontier XK.space = Ec e ∩ frontier XK.space := by
    intro e he hc
    apply Subset.antisymm
    · rintro x ⟨hxF, hxb⟩
      rcases (hF e he hc).2.1 hxF with h' | h'
      · exact ⟨h'.1, hxb⟩
      · exact absurd (hballX e he hc h') hxb.2
    · rintro x ⟨hxE, hxb⟩
      exact ⟨(hF e he hc).2.2 ⟨⟨hxE, hXclosed.frontier_subset hxb⟩,
        fun hxball => hxb.2 (hballX e he hc hxball)⟩, hxb⟩
  have hFpl : ∀ e ∈ K.faces, e.card = 2 → IsPLBall 2 (F e) := fun e he hc => by
    obtain ⟨r, hr, -⟩ := (hF e he hc).1
    exact ⟨r, hr⟩
  have hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e) := fun e he hc =>
    (hFpl e he hc).isConnected.isPreconnected
  have hFcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (F e) := fun e he hc =>
    (hFpl e he hc).isPolyhedron.isClosed
  have hbEc' : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (Metric.ball (h (e.centroid ℝ id)) (2 * ρ)) (Ec e') :=
    fun e he hc e' he' hc' hne =>
      (hbEc e he hc e' he' hc' hne).mono_left (Metric.ball_subset_ball hρδ₀)
  have hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e') := by
    intro e he hc e' he' hc' hne
    rw [disjoint_left]
    intro x hx hx'
    rcases (hF e he hc).2.1 hx with h1 | h1 <;> rcases (hF e' he' hc').2.1 hx' with h2' | h2'
    · exact disjoint_left.mp (hd.pseudoCellDisjoint e he hc e' he' hc' hne) h1.1 h2'.1
    · exact disjoint_left.mp (hbEc' e' he' hc' e he hc (Ne.symm hne))
        (Metric.ball_subset_ball (by linarith) h2') h1.1
    · exact disjoint_left.mp (hbEc' e he hc e' he' hc' hne)
        (Metric.ball_subset_ball (by linarith) h1) h2'.1
    · have h3 := hsep' e he hc e' he' hc' hne
      have h4 := Metric.mem_ball.mp h1
      have h5 := Metric.mem_ball.mp h2'
      have h6 := dist_triangle (h (e.centroid ℝ id)) x (h (e'.centroid ℝ id))
      rw [dist_comm (h (e.centroid ℝ id)) x] at h6
      linarith
  have hFsub : ∀ e ∈ K.faces, e.card = 2 →
      F e ⊆ Ec e ∪ Metric.ball (h (e.centroid ℝ id)) ρ := fun e he hc x hx => by
    rcases (hF e he hc).2.1 hx with h' | h'
    · exact Or.inl h'.1
    · exact Or.inr h'
  have hApoly : ∀ v ∈ K.vertices, IsPolyhedron (Cpp v ∩ frontier XK.space) := fun v hv => by
    obtain ⟨hfin, hsp, -⟩ := h56.2.2 v hv
    let _ : Finite (AK v).faces := hfin.to_subtype
    rw [← hsp]
    exact isPolyhedron_space (AK v)
  obtain ⟨ψ, hψg, hψD, hψS⟩ := hd.exists_sphere_maps hg hgA hgD hApoly
    (fun e he hc => (hF e he hc).1) hFbd hFdisj
  have hBex : ∀ v : EuclideanSpace ℝ (Fin 3), ∃ Bv : Set (EuclideanSpace ℝ (Fin 3)),
      v ∈ K.vertices → IsPLBall 3 Bv ∧
        frontier Bv = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hS : IsPLSphere 2 ((Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e) :=
        (ht.dualBall v hv).isPLSphere_frontier.of_isPLHomeomorphOn (hψS v hv)
      obtain ⟨Bv, hBv, hfr, -⟩ := hS.exists_isPLBall_complement_components
      exact ⟨Bv, fun _ => ⟨hBv, hfr⟩⟩
    · exact ⟨∅, fun h' => absurd h' hv⟩
  choose B hB using hBex
  have hBpl : ∀ v ∈ K.vertices, IsPLBall 3 (B v) := fun v hv => (hB v hv).1
  have hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e :=
    fun v hv => (hB v hv).2
  have hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e :=
    fun v hv => hd.exists_freeFace_image_notMem_pseudoCell hg hgA hgD hv
  have hfvex : ∀ v : EuclideanSpace ℝ (Fin 3),
      ∃ G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3), v ∈ K.vertices →
        IsPLHomeomorphOn G (C v) (B v) ∧ EqOn G ψ (frontier (C v)) := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hψ' : IsPLHomeomorphOn ψ (frontier (C v)) (frontier (B v)) := by
        rw [hBfr v hv]
        exact hψS v hv
      obtain ⟨G, hG, hGe⟩ :=
        exists_isPLHomeomorphOn_of_frontier (ht.dualBall v hv) (hBpl v hv) hψ'
      exact ⟨G, fun _ => ⟨hG, hGe⟩⟩
    · exact ⟨id, fun h' => absurd h' hv⟩
  choose fv hfv using hfvex
  have hmeet : ∀ u ∈ K.vertices, ∀ v ∈ K.vertices, u ≠ v → B u ∩ B v ⊆ ψ '' (C u ∩ C v) := by
    intro u hu v hv huv y hy
    obtain ⟨e, he, hc, hue, hve, hyF⟩ := hd.exists_edge_of_mem_ball_inter_ball h34 hXfin hXc hFX
      hFbd hFc hFdisj hBpl hBfr hpt hu hv huv hy
    rw [← (hψD e he hc).image_eq] at hyF
    obtain ⟨x, hx, rfl⟩ := hyF
    exact ⟨x, ⟨(ht.dualBall u hu).isPolyhedron.isClosed.frontier_subset
      (ht.splitDisk_subset_frontier hu he hc hue hx),
      (ht.dualBall v hv).isPolyhedron.isClosed.frontier_subset
      (ht.splitDisk_subset_frontier hv he hc hve hx)⟩, rfl⟩
  obtain ⟨f, hf, hfC⟩ := ht.exists_isPLHomeomorphOn_glue (fun v hv => (hfv v hv).1)
    (fun v hv => (hfv v hv).2) hmeet
  have hcover := hd.iUnion_balls_eq h2 h34 hXc hXint hFX hFbd hFc hFcl hFdisj hBpl hBfr hpt
  rw [hcover] at hf
  have hfN : f '' N = XK.space := hf.image_eq
  refine ⟨f, by rw [hfN]; exact hf, by rw [hfN]; exact h2.isNeighborhood, fun v hv => ?_⟩
  have himg : f '' C v = B v := by
    rw [image_congr (hfC v hv)]
    exact (hfv v hv).1.image_eq
  rw [himg]
  have hA := hd.ball_subset_and_disjoint_interior h34 hXfin hXc hFX hFbd hFc hFdisj hv
    (hBpl v hv) (hBfr v hv)
  intro y hy
  by_cases hyi : y ∈ interior (B v)
  · by_cases hnear : ∃ e ∈ K.faces, e.card = 2 ∧ dist y (h (e.centroid ℝ id)) ≤ ρ
    · obtain ⟨e, he, hc, hye⟩ := hnear
      by_cases hve : v ∈ e
      · exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hc, hve⟩,
          Metric.mem_ball.mpr (hye.trans_lt hρδ)⟩)
      · exfalso
        set P := h (e.centroid ℝ id)
        have hQfr : Disjoint (Metric.ball P (2 * ρ)) (frontier (B v)) := by
          rw [hBfr v hv, disjoint_union_right]
          refine ⟨disjoint_left.mpr fun z hzQ hzA => hzA.2.2 (hball' e he hc hzQ), ?_⟩
          rw [disjoint_iUnion₂_right]
          intro e' he'
          have hne : e ≠ e' := fun heq => hve (heq ▸ he'.2.2)
          rw [disjoint_left]
          intro z hzQ hzF
          rcases hFsub e' he'.1 he'.2.1 hzF with h' | h'
          · exact disjoint_left.mp (hbEc' e he hc e' he'.1 he'.2.1 hne) hzQ h'
          · have h3 := hsep' e he hc e' he'.1 he'.2.1 hne
            have h4 := Metric.mem_ball.mp hzQ
            have h5 := Metric.mem_ball.mp h'
            have h6 := dist_triangle P z (h (e'.centroid ℝ id))
            rw [dist_comm P z] at h6
            linarith
        have hQsub : Metric.ball P (2 * ρ) ⊆ interior (B v) := by
          refine (convex_ball P (2 * ρ)).isPreconnected.subset_left_of_subset_union
            isOpen_interior isClosed_closure.isOpen_compl
            (disjoint_compl_right.mono_left interior_subset_closure) ?_
            ⟨y, Metric.mem_ball.mpr (by linarith), hyi⟩
          intro z hzQ
          by_cases hzi : z ∈ interior (B v)
          · exact Or.inl hzi
          · refine Or.inr fun hzc => disjoint_left.mp hQfr hzQ ⟨hzc, hzi⟩
        have hpc := hd.pseudoCell e he hc
        obtain ⟨φ⟩ := hpc.isSphere
        obtain ⟨r, hr⟩ : (Ebd e).Nonempty := by
          have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1).Nonempty :=
            NormedSpace.sphere_nonempty.mpr zero_le_one
          obtain ⟨p, hp⟩ := hne
          exact ⟨(φ.symm ⟨p, hp⟩ : EuclideanSpace ℝ (Fin 3)), (φ.symm ⟨p, hp⟩).2⟩
        have hrE : r ∈ Ec e := by
          rw [hpc.carrierEq]
          exact Or.inr hr
        have hrfar : 2 * ρ ≤ dist r P := by
          by_contra hlt
          push Not at hlt
          have hrfr : r ∈ Ec e ∩ frontier N' := by
            rw [hd.rimFrontier e he hc]
            exact hr
          exact hrfr.2.2 (h2.subsetInterior
            (interior_subset (hball' e he hc (Metric.mem_ball.mpr hlt))))
        have hcont : ContinuousOn (fun z => dist z P) (Ec e) :=
          (continuous_id.dist continuous_const).continuousOn
        obtain ⟨z, hzE, hz'⟩ := hpc.isPreconnected.intermediate_value (hPEc e he hc) hrE hcont
          (show 3 * ρ / 2 ∈ Icc (dist P P) (dist r P) by
            rw [dist_self]
            constructor <;> linarith)
        have hz : dist z P = 3 * ρ / 2 := hz'
        have hzQ : z ∈ Metric.ball P (2 * ρ) := by
          rw [Metric.mem_ball, hz]
          linarith
        have hzF : z ∈ F e := (hF e he hc).2.2 ⟨⟨hzE, interior_subset (hball' e he hc hzQ)⟩,
          fun hzb => by
            rw [Metric.mem_ball, hz] at hzb
            linarith⟩
        exact disjoint_left.mp (hA.2.2 e he hc) (hQsub hzQ) hzF
    · push Not at hnear
      by_cases hyE : ∃ e ∈ K.faces, e.card = 2 ∧ y ∈ Ec e
      · obtain ⟨e, he, hc, hyEe⟩ := hyE
        by_cases hve : v ∈ e
        · exact Or.inl (hd.pseudoCell_subset_handlePiece he hc hve hyEe)
        · exfalso
          have hyF : y ∈ F e := (hF e he hc).2.2 ⟨⟨hyEe, hA.1 (interior_subset hyi)⟩,
            fun hyb => by
              rw [Metric.mem_ball] at hyb
              linarith [hnear e he hc]⟩
          exact disjoint_left.mp (hA.2.2 e he hc) hyi hyF
      · push Not at hyE
        exact Or.inl (hd.mem_handlePiece_of_mem_interior_ball h2 h34 hXc hXint hXfr hFX hFbd hFc
          hFcl hFdisj hBpl hBfr hpt hρ hFsub (fun e he hc => (hF e he hc).2.2) hball' hsep'
          (interior_mono hA.1 hyi) hnear hyE hv hyi)
  · have hyfr : y ∈ frontier (B v) := ⟨subset_closure hy, hyi⟩
    rw [hBfr v hv] at hyfr
    rcases hyfr with hyA | hyF
    · exact Or.inl hyA.1
    · obtain ⟨e, he, hyFe⟩ := mem_iUnion₂.mp hyF
      rcases hFsub e he.1 he.2.1 hyFe with h' | h'
      · exact Or.inl (hd.pseudoCell_subset_handlePiece he.1 he.2.1 he.2.2 h')
      · exact Or.inr (mem_iUnion₂.mpr ⟨e, he, Metric.ball_subset_ball hρδ.le h'⟩)

end Extension

theorem moise331OnTube_of_moise323_of_moise324_of_moise264Orientable (h323 : Moise323)
    (h324 : Moise324) (h264 : Moise264Orientable) : Moise331OnTube := by
  intro K N N' C D Dbd h ht hconn hend W hW
  have hr : ∀ v : EuclideanSpace ℝ (Fin 3), ∃ r : ℝ, v ∈ K.vertices →
      0 < r ∧ Metric.thickening (2 * r) (h '' C v) ⊆ W v := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hCN : C v ⊆ N := by
        rw [ht.unionEq]
        exact subset_biUnion_of_mem (u := C) hv
      have hc : IsCompact (h '' C v) :=
        (ht.dualBall v hv).isPolyhedron.isCompact.image_of_continuousOn (ht.continuousOn.mono hCN)
      obtain ⟨r, hr, hrW⟩ := hc.exists_thickening_subset_open isOpen_interior
        (subset_interior_iff_mem_nhdsSet.mpr (hW v hv))
      exact ⟨r / 2, fun _ => ⟨half_pos hr, by
        rw [mul_div_cancel₀ r two_ne_zero]
        exact hrW.trans interior_subset⟩⟩
    · exact ⟨1, fun h' => absurd h' hv⟩
  choose r hr using hr
  obtain ⟨Ec, Eint, Ebd, Cpp, hd, hsub⟩ := h323 K N C D Dbd h N' ht
    (fun v => Metric.thickening (r v) (h '' C v)) fun v hv =>
      Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening (hr v hv).1 _)
  obtain ⟨XK₀, h2₀⟩ := exists_isPolyhedralTubeNeighborhood hd
  obtain ⟨XK₁, h2₁, h34₁⟩ := exists_hasSinglePolygonTraces hd h2₀
  obtain ⟨XK₂, AK₂, h2₂, h34₂, h56₂⟩ := exists_hasConnectedHandlePieces hd hconn h2₁ h34₁
  obtain ⟨XK, AK, h2, h34, h56, h7⟩ := exists_hasNoHandleLoopTheoremDisk hd h2₂ h34₂ h56₂
  have h9 := section33_not_isLoopTheoremDisk hd h2 h34 h7
    fun _ hv₁ _ he₁ hcard _ _ hr' hΔ hbd hcenter hmiss =>
      section33_disk_meets_graph h324 hd hend hv₁ he₁ hcard hr' hΔ hbd hcenter hmiss
  have h10 := section33_fundamentalGroup_map_bijective_of_isTube h264 ht h2 h56.2.1 h9
  have h12 := section33_faceEulerChar_handlePiece hd h2 h34 h56 h10
  obtain ⟨g, hg, hgA, hgD⟩ := exists_section33BoundaryMatch hd hconn h2 h34 h56 h12
  obtain ⟨e₁, he₁, he₁c⟩ := ht.hasEdge
  obtain ⟨v₀, hv₀e⟩ := Finset.card_pos.mp (by omega : 0 < e₁.card)
  have hv₀ : v₀ ∈ K.vertices :=
    K.down_closed he₁ (Finset.singleton_subset_iff.mpr hv₀e) (Finset.singleton_nonempty v₀)
  obtain ⟨w₀, hw₀, hmin⟩ := ht.finite_vertices.toFinset.exists_min_image r
    ⟨v₀, ht.finite_vertices.mem_toFinset.mpr hv₀⟩
  have hδ : 0 < r w₀ := (hr w₀ (ht.finite_vertices.mem_toFinset.mp hw₀)).1
  have hle : ∀ v ∈ K.vertices, r w₀ ≤ r v :=
    fun v hv => hmin v (ht.finite_vertices.mem_toFinset.mpr hv)
  obtain ⟨f, hf, hfN, hfC⟩ :=
    exists_section33Extension_image_dualCell_subset h324 hd h2 h34 h56 hg hgA hgD hδ
  refine ⟨f, hf, hfN, fun v hv => (hfC v hv).trans (union_subset ?_ ?_)⟩
  · exact (hsub v hv).trans ((Metric.thickening_mono (by linarith [(hr v hv).1]) _).trans
      (hr v hv).2)
  · refine iUnion₂_subset fun e he => ?_
    intro y hy
    have hPC : h (e.centroid ℝ id) ∈ Metric.thickening (r v) (h '' C v) := by
      refine hsub v hv (hd.pseudoCell_subset_handlePiece he.1 he.2.1 he.2.2 ?_)
      have hpc := hd.pseudoCell e he.1 he.2.1
      rw [hpc.carrierEq]
      exact Or.inl hpc.centerMem
    obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hPC
    refine (hr v hv).2 (Metric.mem_thickening_iff.mpr ⟨z, hz, ?_⟩)
    have h1 := Metric.mem_ball.mp hy
    have h2' := dist_triangle y (h (e.centroid ℝ id)) z
    linarith [hle v hv]

open Classical in
theorem Moise331OnTube.moise331 (h331 : Moise331OnTube) : Moise331 := by
  intro L hfin hdim hedge hconn hend U hU hLU h hh ε hε
  obtain ⟨T, L', C, D, Dbd, hTfin, hsub, hLT, hT, hDN, hNU, hend', ht, -, hCsmall⟩ :=
    exists_section33TubeFrame L hdim hedge hend hU hLU hh hε
  have hconn' : IsConnected L'.space := by
    rw [hsub.space_eq]
    exact hconn
  obtain ⟨f, hf, hfN, hfC⟩ := h331 L' _ _ C D Dbd h ht hconn' hend'
    (fun v => Metric.thickening (ε / 4) (h '' C v)) fun v _ =>
      Metric.isOpen_thickening.mem_nhdsSet.mpr (Metric.self_subset_thickening (by linarith) _)
  refine ⟨T, L', hTfin, hsub, hLT, hT, ?_, hDN, ?_, hNU, f, hf, ?_, fun x hx => ?_⟩
  · rw [← hsub.space_eq]
    exact Filter.mem_of_superset ht.isNeighborhood (derivedNeighborhood_space_subset T L')
  · rw [← hsub.space_eq]
    exact ht.isNeighborhood
  · rw [← hsub.space_eq]
    exact hfN
  · have hx' : x ∈ ⋃ v ∈ L'.vertices, C v := by
      rw [← ht.unionEq]
      exact hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hx'
    obtain ⟨z, ⟨y, hy, rfl⟩, hdz⟩ := Metric.mem_thickening_iff.mp (hfC v hv ⟨x, hxv, rfl⟩)
    have h1 := hCsmall v hv y hy x hxv
    have h2 := dist_triangle (f x) (h y) (h x)
    linarith

end DifferentialGeometry.Topology.PiecewiseLinear
