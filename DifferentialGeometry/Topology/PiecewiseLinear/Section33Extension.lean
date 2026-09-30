/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellDiskReplacement
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionSphereMaps
import DifferentialGeometry.Topology.PiecewiseLinear.SphereComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsHandleDecompositionOfTube.exists_small_radius
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
    {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {X : Set E3}
    (hX : h '' K.space ⊆ interior X) {ε : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < ε / 4) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      (∀ e ∈ K.faces, e.card = 2 → Metric.ball (h (e.centroid ℝ id)) (2 * δ₀) ⊆ interior X) ∧
      (∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
        3 * δ₀ ≤ dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id))) ∧
      (∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
        Disjoint (Metric.ball (h (e.centroid ℝ id)) δ₀) (Ec e')) ∧
      (∀ v ∈ K.vertices, ∀ e ∈ K.faces, e.card = 2 → δ₀ < dist (h v) (h (e.centroid ℝ id))) ∧
      ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y + 3 * δ₀ ≤ ε / 4 := by
  have ht := hd.tube
  have hEfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    ht.facesFinite.subset fun e he => he.1
  have hEcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (Ec e) := fun e he hc => by
    have hpc := hd.pseudoCell e he hc
    rw [hpc.carrierEq, ← hpc.closureEq]
    exact isClosed_closure
  have hPE : ∀ e ∈ K.faces, e.card = 2 → h (e.centroid ℝ id) ∈ Ec e ∩ h '' K.space :=
    fun e he hc => by
      rw [hd.meetsGraph e he hc]
      exact mem_singleton _
  have hev : ∀ {p : ℝ → Prop} {r : ℝ}, 0 < r → (∀ δ, 0 < δ → δ < r → p δ) →
      ∀ᶠ δ in 𝓝[>] (0 : ℝ), p δ := fun hr hp =>
    Filter.mem_of_superset (Ioo_mem_nhdsGT hr) fun δ hδ => hp δ hδ.1 hδ.2
  have h0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2},
      Metric.ball (h (e.centroid ℝ id)) (2 * δ) ⊆ interior X := by
    refine (Filter.eventually_all_finite hEfin).mpr fun e he => ?_
    obtain ⟨r, hr, hrX⟩ := Metric.isOpen_iff.mp isOpen_interior _ (hX (hPE e he.1 he.2).2)
    exact hev (half_pos hr) fun δ _ hδr => (Metric.ball_subset_ball (by linarith)).trans hrX
  have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2},
      ∀ e' ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, e ≠ e' →
        3 * δ ≤ dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)) := by
    refine (Filter.eventually_all_finite hEfin).mpr fun e he =>
      (Filter.eventually_all_finite hEfin).mpr fun e' he' => ?_
    by_cases hne : e = e'
    · exact Filter.Eventually.of_forall fun δ h' => absurd hne h'
    · have hpos : 0 < dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)) := by
        refine dist_pos.mpr fun heq => ?_
        have h3 := (hPE e' he'.1 he'.2).1
        rw [← heq] at h3
        exact disjoint_left.mp (hd.pseudoCellDisjoint e he.1 he.2 e' he'.1 he'.2 hne)
          (hPE e he.1 he.2).1 h3
      exact hev (by positivity : 0 < dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)) / 3)
        fun δ _ hδr _ => by linarith
  have h3 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2},
      ∀ e' ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, e ≠ e' →
        Disjoint (Metric.ball (h (e.centroid ℝ id)) δ) (Ec e') := by
    refine (Filter.eventually_all_finite hEfin).mpr fun e he =>
      (Filter.eventually_all_finite hEfin).mpr fun e' he' => ?_
    by_cases hne : e = e'
    · exact Filter.Eventually.of_forall fun δ h' => absurd hne h'
    · have hPn : h (e.centroid ℝ id) ∈ (Ec e')ᶜ := fun h' =>
        disjoint_left.mp (hd.pseudoCellDisjoint e he.1 he.2 e' he'.1 he'.2 hne)
          (hPE e he.1 he.2).1 h'
      obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp (hEcl e' he'.1 he'.2).isOpen_compl _ hPn
      exact hev hr fun δ _ hδr _ =>
        disjoint_compl_left.mono_left ((Metric.ball_subset_ball hδr.le).trans hrE)
  have h4 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ v ∈ K.vertices,
      ∀ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, δ < dist (h v) (h (e.centroid ℝ id)) := by
    refine (Filter.eventually_all_finite ht.finite_vertices).mpr fun v hv =>
      (Filter.eventually_all_finite hEfin).mpr fun e he => ?_
    have hpos : 0 < dist (h v) (h (e.centroid ℝ id)) := by
      refine dist_pos.mpr fun heq => ?_
      exact hd.vertex_image_notMem_pseudoCell hv he.1 he.2 (heq ▸ (hPE e he.1 he.2).1)
    exact hev hpos fun δ _ hδr => hδr
  have h5 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v,
      dist x y + 3 * δ ≤ ε / 4 := by
    refine (Filter.eventually_all_finite ht.finite_vertices).mpr fun v hv => ?_
    have hN'c : IsCompact N' := by
      rw [ht.imageEq]
      exact ht.isCompact.image_of_continuousOn ht.continuousOn
    have hCc : IsCompact (Cpp v) := by
      refine hN'c.of_isClosed_subset ?_ ?_
      · rw [hd.componentClosure v hv]
        exact isClosed_closure
      · rw [hd.coversTube]
        exact subset_biUnion_of_mem (u := Cpp) hv
    by_cases hne : (Cpp v).Nonempty
    · obtain ⟨p, hp, hmax⟩ := (hCc.prod hCc).exists_isMaxOn (hne.prod hne)
        (continuous_dist.continuousOn (s := Cpp v ×ˢ Cpp v))
      have hlt := hsmall v hv p.1 hp.1 p.2 hp.2
      refine hev (by linarith : 0 < (ε / 4 - dist p.1 p.2) / 3) fun δ _ hδr x hx y hy => ?_
      have hxy : dist x y ≤ dist p.1 p.2 := isMaxOn_iff.mp hmax (x, y) ⟨hx, hy⟩
      linarith
    · exact Filter.Eventually.of_forall fun δ x hx => absurd ⟨x, hx⟩ hne
  obtain ⟨δ₀, hδ0, hb, hs, hd3, hv4, h5'⟩ := (h0.and (h1.and (h2.and (h3.and (h4.and h5))))).exists
  exact ⟨δ₀, hδ0, fun e he hc => hb e ⟨he, hc⟩,
    fun e he hc e' he' hc' hne => hs e ⟨he, hc⟩ e' ⟨he', hc'⟩ hne,
    fun e he hc e' he' hc' hne => hd3 e ⟨he, hc⟩ e' ⟨he', hc'⟩ hne,
    fun v hv e he hc => hv4 v hv e ⟨he, hc⟩, h5'⟩

theorem IsHandleDecompositionOfTube.exists_plDisks (h324 : Moise324)
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
    {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
    {XK : Geometry.SimplicialComplex ℝ E3}
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ F : Finset E3 → Set E3, ∀ e ∈ K.faces, e.card = 2 →
      (∃ r : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (F e) ∧
        r '' stdSimplexBoundary 2 = Ec e ∩ frontier XK.space) ∧
      F e ⊆ (Ec e ∩ XK.space) ∪ Metric.ball (h (e.centroid ℝ id)) δ₀ ∧
      (Ec e ∩ XK.space) \ Metric.ball (h (e.centroid ℝ id)) δ₀ ⊆ F e := by
  have hex : ∀ e : Finset E3, ∃ Fe : Set E3, e ∈ K.faces → e.card = 2 →
      (∃ r : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Fe ∧
        r '' stdSimplexBoundary 2 = Ec e ∩ frontier XK.space) ∧
      Fe ⊆ (Ec e ∩ XK.space) ∪ Metric.ball (h (e.centroid ℝ id)) δ₀ ∧
      (Ec e ∩ XK.space) \ Metric.ball (h (e.centroid ℝ id)) δ₀ ⊆ Fe := by
    intro e
    by_cases he : e ∈ K.faces ∧ e.card = 2
    · obtain ⟨hJ, DJint, hDJ, hDJbd, hPDJ⟩ := h34 e he.1 he.2
      have hpc := hd.pseudoCell e he.1 he.2
      have hDJE : Ec e ∩ XK.space ⊆ Eint e := by
        rintro x ⟨hxE, hxX⟩
        rw [hpc.carrierEq] at hxE
        exact hxE.resolve_right fun hb => disjoint_left.mp (h2.rimDisjoint e he.1 he.2) hb hxX
      obtain ⟨Fe, r, hr, hrb, hsub, hsup⟩ :=
        hpc.exists_plDisk_agreeing_off_ball h324 hDJ hDJE (hDJbd ▸ hJ) hPDJ hδ₀
      exact ⟨Fe, fun _ _ => ⟨⟨r, hr, hrb.trans hDJbd⟩, hsub, hsup⟩⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ he⟩
  choose F hF using hex
  exact ⟨F, hF⟩

section Leaves

variable {K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {N N' : Set (EuclideanSpace ℝ (Fin 3))}
  {C Cpp : EuclideanSpace ℝ (Fin 3) → Set (EuclideanSpace ℝ (Fin 3))}
  {D Dbd Ec Eint Ebd : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {XK : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {AK : EuclideanSpace ℝ (Fin 3) → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}

theorem exists_section33Extension (h324 : Moise324)
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space)
    (h56 : HasConnectedHandlePieces K Ec Cpp XK.space AK)
    {g : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
    (hg : IsPLHomeomorphOn g (frontier N) (frontier XK.space))
    (hgA : ∀ v ∈ K.vertices, g '' (frontier (C v) ∩ frontier N) = Cpp v ∩ frontier XK.space)
    (hgD : ∀ e ∈ K.faces, e.card = 2 → g '' Dbd e = Ec e ∩ frontier XK.space) {ε : ℝ}
    (hsmall : ∀ v ∈ K.vertices, ∀ x ∈ Cpp v, ∀ y ∈ Cpp v, dist x y < ε / 4) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f N (f '' N) ∧ f '' N ∈ nhdsSet (h '' K.space) ∧
      EqOn f g (frontier N) ∧ (∀ v ∈ K.vertices, h v ∈ f '' C v) ∧
      ∀ v ∈ K.vertices, ∀ x ∈ C v, ∀ y ∈ C v, dist (f x) (f y) < ε / 4 := by
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
  obtain ⟨δ₀, hδ₀, hball, hsep, hbEc, hvert, hslack⟩ := hd.exists_small_radius hKX hsmall
  obtain ⟨F, hF⟩ := hd.exists_plDisks h324 h2 h34 hδ₀
  have hPEc : ∀ e ∈ K.faces, e.card = 2 → h (e.centroid ℝ id) ∈ Ec e := fun e he hc => by
    have hpc := hd.pseudoCell e he hc
    rw [hpc.carrierEq]
    exact Or.inl hpc.centerMem
  have hballX : ∀ e ∈ K.faces, e.card = 2 →
      Metric.ball (h (e.centroid ℝ id)) δ₀ ⊆ interior XK.space := fun e he hc =>
    (Metric.ball_subset_ball (by linarith)).trans (hball e he hc)
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
  have hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e') := by
    intro e he hc e' he' hc' hne
    rw [disjoint_left]
    intro x hx hx'
    rcases (hF e he hc).2.1 hx with h1 | h1 <;> rcases (hF e' he' hc').2.1 hx' with h2' | h2'
    · exact disjoint_left.mp (hd.pseudoCellDisjoint e he hc e' he' hc' hne) h1.1 h2'.1
    · exact disjoint_left.mp (hbEc e' he' hc' e he hc (Ne.symm hne)) h2' h1.1
    · exact disjoint_left.mp (hbEc e he hc e' he' hc' hne) h1 h2'.1
    · have h3 := hsep e he hc e' he' hc' hne
      have h4 := Metric.mem_ball.mp h1
      have h5 := Metric.mem_ball.mp h2'
      have h6 := dist_triangle (h (e.centroid ℝ id)) x (h (e'.centroid ℝ id))
      rw [dist_comm (h (e.centroid ℝ id)) x] at h6
      linarith
  have hFsub : ∀ e ∈ K.faces, e.card = 2 →
      F e ⊆ Ec e ∪ Metric.ball (h (e.centroid ℝ id)) δ₀ := fun e he hc x hx => by
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
  have hBex : ∀ v : E3, ∃ Bv : Set E3, v ∈ K.vertices → IsPLBall 3 Bv ∧
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
  have hfvex : ∀ v : E3, ∃ G : E3 → E3, v ∈ K.vertices →
      IsPLHomeomorphOn G (C v) (B v) ∧ EqOn G ψ (frontier (C v)) := by
    intro v
    by_cases hv : v ∈ K.vertices
    · have hψ' : IsPLHomeomorphOn ψ (frontier (C v)) (frontier (B v)) := by
        rw [hBfr v hv]
        exact hψS v hv
      obtain ⟨G, hG, hGe⟩ := exists_isPLHomeomorphOn_of_frontier (ht.dualBall v hv) (hBpl v hv) hψ'
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
  refine ⟨f, by rw [hfN]; exact hf, by rw [hfN]; exact h2.isNeighborhood, ?_, ?_, ?_⟩
  · intro x hx
    have hxN : x ∈ N := ht.isClosed.frontier_subset hx
    rw [ht.unionEq] at hxN
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxN
    have hxfr : x ∈ frontier (C v) :=
      ⟨subset_closure hxv, fun hi => hx.2 (interior_mono (ht.dualCell_subset hv) hi)⟩
    rw [hfC v hv hxv, (hfv v hv).2 hxfr, hψg hx]
  · intro v hv
    have himg : f '' C v = B v := by
      rw [image_congr (hfC v hv)]
      exact (hfv v hv).1.image_eq
    rw [himg]
    exact interior_subset (hd.mem_interior_ball_of_vertex h2 h34 hXc hXint hXfr hFX hFbd hFc
      hFcl hFdisj hBpl hBfr hpt hδ₀ hFsub (fun e he hc => (hF e he hc).2.2) hball hsep hvert hv)
  · intro v hv x hx y hy
    have hfx : f x ∈ B v := by
      rw [hfC v hv hx]
      exact (hfv v hv).1.bijOn.mapsTo hx
    have hfy : f y ∈ B v := by
      rw [hfC v hv hy]
      exact (hfv v hv).1.bijOn.mapsTo hy
    obtain ⟨z, hz, z', hz', hle⟩ :=
      IsCompact.exists_mem_frontier_pair_dist_le (hBpl v hv).isPolyhedron.isCompact hfx hfy
    rw [hBfr v hv] at hz hz'
    have hnear : ∀ w ∈ (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e,
        ∃ c ∈ Cpp v, dist w c ≤ δ₀ := by
      rintro w (hw | hw)
      · exact ⟨w, hw.1, by rw [dist_self]; exact hδ₀.le⟩
      · obtain ⟨e, he, hwe⟩ := mem_iUnion₂.mp hw
        rcases (hF e he.1 he.2.1).2.1 hwe with h' | h'
        · exact ⟨w, hd.pseudoCell_subset_handlePiece he.1 he.2.1 he.2.2 h'.1,
            by rw [dist_self]; exact hδ₀.le⟩
        · exact ⟨h (e.centroid ℝ id),
            hd.pseudoCell_subset_handlePiece he.1 he.2.1 he.2.2 (hPEc e he.1 he.2.1),
            (Metric.mem_ball.mp h').le⟩
    obtain ⟨c, hc, hzc⟩ := hnear z hz
    obtain ⟨c', hc', hzc'⟩ := hnear z' hz'
    have h1 := hslack v hv c hc c' hc'
    have h3 := dist_triangle4 z c c' z'
    rw [dist_comm c' z'] at h3
    linarith

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
