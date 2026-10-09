/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section33ExtensionBalls
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellLocalSides
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskMeetsPseudoCells
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskArcSide

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C Cpp : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3}
  {XK : Geometry.SimplicialComplex ℝ E3} {F : Finset E3 → Set E3} {B : E3 → Set E3}

theorem eq_empty_of_isPreconnected_of_closure_cover {X : Type*} [TopologicalSpace X]
    {S G Bd : Set X} (hS : IsPreconnected S) (hGS : G ⊆ S) (hBS : Bd ⊆ S) (hGne : G.Nonempty)
    (hcov : S ⊆ closure G ∪ closure Bd) (hdis : ∀ y ∈ S, y ∈ closure G → y ∉ closure Bd) :
    Bd = ∅ := by
  have hint : S ∩ (closure G ∩ closure Bd) = ∅ := by
    apply eq_empty_of_forall_notMem
    rintro y ⟨hyS, hyG, hyB⟩
    exact hdis y hyS hyG hyB
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS _ _ isClosed_closure isClosed_closure
    hcov hint with h' | h'
  · apply eq_empty_of_forall_notMem
    intro b hb
    exact hdis b (hBS hb) (h' (hBS hb)) (subset_closure hb)
  · obtain ⟨g, hg⟩ := hGne
    exact absurd (h' (hGS hg)) (hdis g (hGS hg) (subset_closure hg))

theorem IsHandleDecompositionOfTube.mem_handlePiece_of_mem_interior_ball
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXc : IsConnected XK.spaceᶜ)
    (hXint : IsConnected (interior XK.space))
    (hXcl : frontier XK.space ⊆ closure (interior XK.space))
    (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hFsub : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ Ec e ∪ Metric.ball (h (e.centroid ℝ id)) δ₀)
    (hFsup : ∀ e ∈ K.faces, e.card = 2 →
      (Ec e ∩ XK.space) \ Metric.ball (h (e.centroid ℝ id)) δ₀ ⊆ F e)
    (hball : ∀ e ∈ K.faces, e.card = 2 →
      Metric.ball (h (e.centroid ℝ id)) (2 * δ₀) ⊆ interior XK.space)
    (hsep : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      3 * δ₀ ≤ dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)))
    {y : E3} (hyX : y ∈ interior XK.space)
    (hyb : ∀ e ∈ K.faces, e.card = 2 → δ₀ < dist y (h (e.centroid ℝ id)))
    (hyE : ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e) {x : E3} (hx : x ∈ K.vertices)
    (hyx : y ∈ interior (B x)) : y ∈ Cpp x := by
  have hXfin := h2.facesFinite
  have hEfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun e he => he.1
  have hEcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (Ec e) := fun e he hc => by
    have hpc := hd.pseudoCell e he hc
    rw [hpc.carrierEq, ← hpc.closureEq]
    exact isClosed_closure
  have hEUc : IsClosed (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :=
    hEfin.isClosed_biUnion fun e he => hEcl e he.1 he.2
  have hCppc : ∀ w ∈ K.vertices, IsClosed (Cpp w) := fun w hw => by
    rw [hd.componentClosure w hw]
    exact isClosed_closure
  have hA := fun w (hw : w ∈ K.vertices) =>
    hd.ball_subset_and_disjoint_interior h34 hXfin hXc hFX hFbd hFc hFdisj hw (hB w hw)
      (hBfr w hw)
  have hdisj : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices, a ≠ b →
      Disjoint (interior (B a)) (interior (B b)) := fun a ha b hb hab =>
    hd.disjoint_interior_balls h34 hXfin hXc hFX hFbd hFc hFdisj hB hBfr hpt ha hb hab
  have hcover := hd.iUnion_balls_eq h2 h34 hXc hXint hFX hFbd hFc hFcl hFdisj hB hBfr hpt
  obtain ⟨Ω, hΩdef⟩ : ∃ Ω : Set E3, Ω = interior XK.space \
      ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2},
        Metric.closedBall (h (e.centroid ℝ id)) δ₀ := ⟨_, rfl⟩
  have hΩ : ∀ z, z ∈ Ω ↔ z ∈ interior XK.space ∧
      ∀ e ∈ K.faces, e.card = 2 → δ₀ < dist z (h (e.centroid ℝ id)) := by
    intro z
    rw [hΩdef, mem_sdiff, mem_iUnion₂]
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hz, fun e he hc => not_le.mp fun hle =>
        hn ⟨e, ⟨he, hc⟩, Metric.mem_closedBall.mpr hle⟩⟩
    · rintro ⟨hz, hd'⟩
      refine ⟨hz, ?_⟩
      rintro ⟨e, he, hze⟩
      exact (not_le.mpr (hd' e he.1 he.2)) (Metric.mem_closedBall.mp hze)
  have hΩc : IsConnected Ω := by
    rw [hΩdef]
    exact isConnected_sdiff_biUnion_closedBall hEfin hXint isOpen_interior
      (fun e => h (e.centroid ℝ id)) hδ₀ (fun e he => hball e he.1 he.2)
      (fun e he e' he' hne => hsep e he.1 he.2 e' he'.1 he'.2 hne)
  have hΩo : IsOpen Ω := by
    rw [hΩdef]
    exact isOpen_interior.sdiff (hEfin.isClosed_biUnion fun e _ => Metric.isClosed_closedBall)
  have hFΩ : ∀ e ∈ K.faces, e.card = 2 → ∀ z ∈ Ω, (z ∈ F e ↔ z ∈ Ec e) := by
    intro e he hc z hz
    obtain ⟨hzX, hzd⟩ := (hΩ z).mp hz
    have hzb : z ∉ Metric.ball (h (e.centroid ℝ id)) δ₀ := fun hb =>
      lt_asymm (Metric.mem_ball.mp hb) (hzd e he hc)
    constructor
    · intro hzF
      rcases hFsub e he hc hzF with h' | h'
      · exact h'
      · exact absurd h' hzb
    · intro hzE
      exact hFsup e he hc ⟨⟨hzE, interior_subset hzX⟩, hzb⟩
  have hCuniq : ∀ q : E3, (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) →
      ∀ w ∈ K.vertices, ∀ w' ∈ K.vertices, q ∈ Cpp w → q ∈ Cpp w' → w = w' := by
    intro q hq w hw w' hw' h1 h2'
    by_contra hne
    obtain ⟨e, he, hqe⟩ :=
      mem_iUnion₂.mp (hd.handlePiece_inter_subset_pseudoCells hw hw' hne ⟨h1, h2'⟩)
    exact hq e he.1 he.2 hqe
  have hlab : ∀ Z : Set E3, IsPreconnected Z → Z.Nonempty → Z ⊆ Ω →
      (∀ z ∈ Z, ∀ e ∈ K.faces, e.card = 2 → z ∉ Ec e) →
      ∃ a ∈ K.vertices, Z ⊆ interior (B a) ∧ ∃ w ∈ K.vertices, Z ⊆ Cpp w := by
    intro Z hZ hZne hZΩ hZE
    obtain ⟨z, hz⟩ := hZne
    have hzX := ((hΩ z).mp (hZΩ hz)).1
    have hzY : z ∈ ⋃ v ∈ K.vertices, B v := by
      rw [hcover]
      exact interior_subset hzX
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hzY
    have hZfr : Disjoint Z (frontier (B a)) := by
      rw [hBfr a ha, disjoint_union_right]
      refine ⟨disjoint_left.mpr fun q hq hq' => ?_,
        disjoint_iUnion₂_right.mpr fun e he => disjoint_left.mpr fun q hq hqF => ?_⟩
      · exact hq'.2.2 ((hΩ q).mp (hZΩ hq)).1
      · exact hZE q hq e he.1 he.2.1 ((hFΩ e he.1 he.2.1 q (hZΩ hq)).mp hqF)
    have hzI : z ∈ interior (B a) := by
      by_contra hn
      exact disjoint_left.mp hZfr hz ⟨subset_closure hza, hn⟩
    refine ⟨a, ha, subset_interior_of_isPreconnected_of_disjoint_frontier hZ hZfr ⟨z, hz, hzI⟩, ?_⟩
    have hZN : Z ⊆ interior N' := fun q hq =>
      h2.subsetInterior (interior_subset ((hΩ q).mp (hZΩ hq)).1)
    have hZEU : Disjoint Z (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :=
      disjoint_left.mpr fun q hq hqE => by
        obtain ⟨e, he, hqe⟩ := mem_iUnion₂.mp hqE
        exact hZE q hq e he.1 he.2 hqe
    exact hd.exists_subset_handlePiece hZ ⟨z, hz⟩ hZN hZEU
  obtain ⟨G, hG⟩ : ∃ G : Set E3, ∀ q, q ∈ G ↔ q ∈ Ω ∧
      (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) ∧
      ∃ w ∈ K.vertices, q ∈ interior (B w) ∧ q ∈ Cpp w := ⟨_, fun q => Iff.rfl⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd : Set E3, ∀ q, q ∈ Bd ↔ q ∈ Ω ∧
      (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) ∧
      ∃ w ∈ K.vertices, ∃ w' ∈ K.vertices, w ≠ w' ∧ q ∈ interior (B w) ∧ q ∈ Cpp w' :=
    ⟨_, fun q => Iff.rfl⟩
  have hGB : ∀ Z : Set E3, IsPreconnected Z → Z.Nonempty → Z ⊆ Ω →
      (∀ z ∈ Z, ∀ e ∈ K.faces, e.card = 2 → z ∉ Ec e) → Z ⊆ G ∨ Z ⊆ Bd := by
    intro Z hZ hZne hZΩ hZE
    obtain ⟨a, ha, hZa, w, hw, hZw⟩ := hlab Z hZ hZne hZΩ hZE
    by_cases haw : a = w
    · left
      intro q hq
      exact (hG q).mpr ⟨hZΩ hq, hZE q hq, a, ha, hZa hq, haw ▸ hZw hq⟩
    · right
      intro q hq
      exact (hBd q).mpr ⟨hZΩ hq, hZE q hq, a, ha, w, hw, haw, hZa hq, hZw hq⟩
  have hGBdisj : Disjoint G Bd := by
    rw [disjoint_left]
    intro q hqG hqB
    obtain ⟨-, hqE, w, hw, hqw, hqCw⟩ := (hG q).mp hqG
    obtain ⟨-, -, a, ha, a', ha', haa', hqa, hqCa'⟩ := (hBd q).mp hqB
    have hwa : w = a := by
      by_contra hne
      exact disjoint_left.mp (hdisj w hw a ha hne) hqw hqa
    exact haa' (hwa.symm.trans (hCuniq q hqE w hw a' ha' hqCw hqCa'))
  have hGsub : ∀ q ∈ G, (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) := fun q hq => ((hG q).mp hq).2.1
  have hBsub : ∀ q ∈ Bd, (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) :=
    fun q hq => ((hBd q).mp hq).2.1
  have hopen : ∀ q ∈ Ω, (∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e) →
      ∃ W ∈ 𝓝 q, W ⊆ G ∨ W ⊆ Bd := by
    intro q hqΩ hqE
    have hO : IsOpen (Ω \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :=
      hΩo.sdiff hEUc
    have hqO : q ∈ Ω \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
      refine ⟨hqΩ, fun h' => ?_⟩
      obtain ⟨e, he, hqe⟩ := mem_iUnion₂.mp h'
      exact hqE e he.1 he.2 hqe
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO q hqO
    refine ⟨Metric.ball q r, Metric.ball_mem_nhds q hr, hGB _ (convex_ball q r).isPreconnected
      ⟨q, Metric.mem_ball_self hr⟩ (fun z hz => (hrO hz).1) fun z hz e he hc hze => ?_⟩
    exact (hrO hz).2 (mem_iUnion₂.mpr ⟨e, ⟨he, hc⟩, hze⟩)
  have hsides : ∀ q ∈ Ω, ∀ e ∈ K.faces, e.card = 2 → q ∈ Ec e →
      ∃ Cn ∈ 𝓝 q, Cn ⊆ Ω ∧ ∃ A₀ B₀ : Set E3, IsConnected A₀ ∧ IsConnected B₀ ∧
        A₀ ∪ B₀ = Cn \ Ec e ∧ q ∈ closure A₀ ∧ q ∈ closure B₀ ∧
        (A₀ ⊆ G ∨ A₀ ⊆ Bd) ∧ (B₀ ⊆ G ∨ B₀ ⊆ Bd) := by
    intro q hq e he hc hqe
    have hpc := hd.pseudoCell e he hc
    obtain ⟨hqX, hqd⟩ := (hΩ q).mp hq
    have hqI : q ∈ Eint e := by
      have hq' := hqe
      rw [hpc.carrierEq] at hq'
      rcases hq' with h' | h'
      · exact h'
      · exact absurd (interior_subset hqX) (disjoint_left.mp (h2.rimDisjoint e he hc) h')
    have hqP : q ≠ h (e.centroid ℝ id) := by
      intro hqP
      have := hqd e he hc
      rw [hqP, dist_self] at this
      linarith
    have hOthc : IsClosed
        (⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, Ec e') :=
      (hEfin.subset fun e' h' => ⟨h'.1, h'.2.1⟩).isClosed_biUnion
        fun e' h' => hEcl e' h'.1 h'.2.1
    have hqOth : q ∉ ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, Ec e' := by
      intro h'
      obtain ⟨e', he', hqe'⟩ := mem_iUnion₂.mp h'
      exact disjoint_left.mp (hd.pseudoCellDisjoint e he hc e' he'.1 he'.2.1 (Ne.symm he'.2.2))
        hqe hqe'
    have hU : Ω \ ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, Ec e' ∈ 𝓝 q :=
      (hΩo.sdiff hOthc).mem_nhds ⟨hq, hqOth⟩
    obtain ⟨Cn, hCn, hCU, A₀, B₀, hA₀, hB₀, hAB, hcA, hcB⟩ :=
      hpc.exists_connected_neighborhood_pair_sdiff hqI hqP hU
    have hside : ∀ Z : Set E3, IsConnected Z → Z ⊆ A₀ ∪ B₀ → Z ⊆ G ∨ Z ⊆ Bd := by
      intro Z hZ hZs
      rw [hAB] at hZs
      refine hGB Z hZ.isPreconnected hZ.nonempty (fun z hz => (hCU (hZs hz).1).1) ?_
      intro z hz e' he' hc' hze'
      by_cases hee : e' = e
      · exact (hZs hz).2 (hee ▸ hze')
      · exact (hCU (hZs hz).1).2 (mem_iUnion₂.mpr ⟨e', ⟨he', hc', hee⟩, hze'⟩)
    exact ⟨Cn, hCn, fun z hz => (hCU hz).1, A₀, B₀, hA₀, hB₀, hAB,
      hcA ⟨mem_of_mem_nhds hCn, hqe⟩, hcB ⟨mem_of_mem_nhds hCn, hqe⟩,
      hside A₀ hA₀ subset_union_left, hside B₀ hB₀ subset_union_right⟩
  have hcov : Ω ⊆ closure G ∪ closure Bd := by
    intro q hq
    by_cases hqE : ∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e
    · obtain ⟨W, hW, hW'⟩ := hopen q hq hqE
      rcases hW' with h' | h'
      · exact Or.inl (subset_closure (h' (mem_of_mem_nhds hW)))
      · exact Or.inr (subset_closure (h' (mem_of_mem_nhds hW)))
    · push Not at hqE
      obtain ⟨e, he, hc, hqe⟩ := hqE
      obtain ⟨Cn, -, -, A₀, -, -, -, -, hqA, -, hAGB, -⟩ := hsides q hq e he hc hqe
      rcases hAGB with h' | h'
      · exact Or.inl (closure_mono h' hqA)
      · exact Or.inr (closure_mono h' hqA)
  have hcontra : ∀ q ∈ Ω, ∀ e ∈ K.faces, e.card = 2 → q ∈ Ec e → ∀ Cn ∈ 𝓝 q, Cn ⊆ Ω →
      ∀ Z₁ Z₂ : Set E3, Z₁ ∪ Z₂ = Cn \ Ec e → IsConnected Z₁ → IsConnected Z₂ → Z₁ ⊆ G →
      Z₂ ⊆ Bd → q ∈ closure Z₁ → q ∈ closure Z₂ → False := by
    intro q hq e he hc hqe Cn hCn hCnΩ Z₁ Z₂ hZ hZ₁ hZ₂ hZ₁G hZ₂B hq₁ hq₂
    obtain ⟨z₁, hz₁⟩ := hZ₁.nonempty
    obtain ⟨-, hz₁E, x₁, hx₁, hz₁x, hz₁C⟩ := (hG z₁).mp (hZ₁G hz₁)
    obtain ⟨z₂, hz₂⟩ := hZ₂.nonempty
    obtain ⟨-, hz₂E, x₂, hx₂, w₂, hw₂, hxw₂, hz₂x, hz₂C⟩ := (hBd z₂).mp (hZ₂B hz₂)
    obtain ⟨a₁, ha₁, hZa₁, c₁, hc₁, hZc₁⟩ := hlab Z₁ hZ₁.isPreconnected hZ₁.nonempty
      (fun z hz => ((hG z).mp (hZ₁G hz)).1) (fun z hz => hGsub z (hZ₁G hz))
    obtain ⟨a₂, ha₂, hZa₂, c₂, hc₂, hZc₂⟩ := hlab Z₂ hZ₂.isPreconnected hZ₂.nonempty
      (fun z hz => ((hBd z).mp (hZ₂B hz)).1) (fun z hz => hBsub z (hZ₂B hz))
    have ha₁x : a₁ = x₁ := by
      by_contra hne
      exact disjoint_left.mp (hdisj a₁ ha₁ x₁ hx₁ hne) (hZa₁ hz₁) hz₁x
    have hc₁x : c₁ = x₁ := hCuniq z₁ hz₁E c₁ hc₁ x₁ hx₁ (hZc₁ hz₁) hz₁C
    have ha₂x : a₂ = x₂ := by
      by_contra hne
      exact disjoint_left.mp (hdisj a₂ ha₂ x₂ hx₂ hne) (hZa₂ hz₂) hz₂x
    have hc₂w : c₂ = w₂ := hCuniq z₂ hz₂E c₂ hc₂ w₂ hw₂ (hZc₂ hz₂) hz₂C
    rw [ha₁x] at hZa₁
    rw [hc₁x] at hZc₁
    rw [ha₂x] at hZa₂
    rw [hc₂w] at hZc₂
    have hqF : q ∈ F e := (hFΩ e he hc q hq).mpr hqe
    have hmemE : ∀ w ∈ K.vertices, q ∈ Cpp w → w ∈ e := by
      intro w hw hqw
      by_contra hwe
      have hqwe : q ∈ Cpp w ∩ Ec e := ⟨hqw, hqe⟩
      rw [hd.handlePiece_inter_pseudoCell_eq_empty hw he hc hwe] at hqwe
      exact hqwe
    have hx₁e : x₁ ∈ e := hmemE x₁ hx₁ ((hCppc x₁ hx₁).closure_subset (closure_mono hZc₁ hq₁))
    have hw₂e : w₂ ∈ e := hmemE w₂ hw₂ ((hCppc w₂ hw₂).closure_subset (closure_mono hZc₂ hq₂))
    have hx₂e : x₂ ∈ e := by
      have hqB : q ∈ B x₂ := (hB x₂ hx₂).isPolyhedron.isClosed.closure_subset
        (closure_mono (hZa₂.trans interior_subset) hq₂)
      have hqni : q ∉ interior (B x₂) := fun hi =>
        disjoint_left.mp ((hA x₂ hx₂).2.2 e he hc) hi hqF
      have hqfr : q ∈ frontier (B x₂) := ⟨subset_closure hqB, hqni⟩
      rw [hBfr x₂ hx₂] at hqfr
      rcases hqfr with h' | h'
      · exact absurd ((hΩ q).mp hq).1 h'.2.2
      · obtain ⟨e', he', hqe'⟩ := mem_iUnion₂.mp h'
        by_cases hee : e' = e
        · exact hee ▸ he'.2.2
        · exact absurd hqe' (disjoint_left.mp (hFdisj e he hc e' he'.1 he'.2.1 (Ne.symm hee)) hqF)
    have hx₁₂ : x₁ ≠ x₂ := by
      intro heq
      obtain ⟨t, hte, htx⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) x₁
      have ht : t ∈ K.vertices :=
        K.down_closed he (Finset.singleton_subset_iff.mpr hte) (Finset.singleton_nonempty t)
      have hqt : q ∈ closure (interior (B t)) := by
        rw [(hB t ht).closure_interior]
        have hqtf : q ∈ frontier (B t) := by
          rw [hBfr t ht]
          exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hc, hte⟩, hqF⟩)
        exact (hB t ht).isPolyhedron.isClosed.frontier_subset hqtf
      obtain ⟨p, hpC, hpt'⟩ := mem_closure_iff_nhds.mp hqt Cn hCn
      have hpE : p ∉ Ec e := fun hpe =>
        disjoint_left.mp ((hA t ht).2.2 e he hc) hpt' ((hFΩ e he hc p (hCnΩ hpC)).mpr hpe)
      have hpZ : p ∈ Z₁ ∪ Z₂ := by
        rw [hZ]
        exact ⟨hpC, hpE⟩
      have hpx : p ∈ interior (B x₁) := by
        rcases hpZ with hp | hp
        · exact hZa₁ hp
        · rw [heq]
          exact hZa₂ hp
      exact disjoint_left.mp (hdisj t ht x₁ hx₁ htx) hpt' hpx
    have hw₂x₁ : w₂ = x₁ := by
      rcases mem_or_mem_of_card_eq_two hc hx₁e hx₂e hx₁₂ hw₂e with h' | h'
      · exact h'
      · exact absurd h'.symm hxw₂
    have hqCx₂ : q ∈ Cpp x₂ := hd.pseudoCell_subset_handlePiece he hc hx₂e hqe
    rw [hd.componentClosure x₂ hx₂] at hqCx₂
    obtain ⟨p, hpC, hpG⟩ := mem_closure_iff_nhds.mp hqCx₂ Cn hCn
    have hpNE := connectedComponentIn_subset _ _ hpG
    have hpE' : ∀ e' ∈ K.faces, e'.card = 2 → p ∉ Ec e' := fun e' he' hc' hpe' =>
      hpNE.2 (mem_iUnion₂.mpr ⟨e', ⟨he', hc'⟩, hpe'⟩)
    have hpZ : p ∈ Z₁ ∪ Z₂ := by
      rw [hZ]
      exact ⟨hpC, hpE' e he hc⟩
    have hpx₁ : p ∈ Cpp x₁ := by
      rcases hpZ with hp | hp
      · exact hZc₁ hp
      · rw [← hw₂x₁]
        exact hZc₂ hp
    have hpx₂ : p ∈ Cpp x₂ := by
      rw [hd.componentClosure x₂ hx₂]
      exact subset_closure hpG
    exact hx₁₂ (hCuniq p hpE' x₁ hx₁ x₂ hx₂ hpx₁ hpx₂)
  have hdis : ∀ q ∈ Ω, q ∈ closure G → q ∉ closure Bd := by
    intro q hq hqG hqB
    by_cases hqE : ∀ e ∈ K.faces, e.card = 2 → q ∉ Ec e
    · obtain ⟨W, hW, hW'⟩ := hopen q hq hqE
      rcases hW' with h' | h'
      · obtain ⟨z, hzW, hzB⟩ := mem_closure_iff_nhds.mp hqB W hW
        exact disjoint_left.mp hGBdisj (h' hzW) hzB
      · obtain ⟨z, hzW, hzG⟩ := mem_closure_iff_nhds.mp hqG W hW
        exact disjoint_left.mp hGBdisj hzG (h' hzW)
    · push Not at hqE
      obtain ⟨e, he, hc, hqe⟩ := hqE
      obtain ⟨Cn, hCn, hCnΩ, A₀, B₀, hA₀, hB₀, hAB, hqA, hqB', hAGB, hBGB⟩ :=
        hsides q hq e he hc hqe
      have hmeetG : (A₀ ∩ G).Nonempty ∨ (B₀ ∩ G).Nonempty := by
        obtain ⟨z, hzC, hzS⟩ := mem_closure_iff_nhds.mp hqG Cn hCn
        have hz : z ∈ A₀ ∪ B₀ := by
          rw [hAB]
          exact ⟨hzC, hGsub z hzS e he hc⟩
        rcases hz with h' | h'
        · exact Or.inl ⟨z, h', hzS⟩
        · exact Or.inr ⟨z, h', hzS⟩
      have hmeetB : (A₀ ∩ Bd).Nonempty ∨ (B₀ ∩ Bd).Nonempty := by
        obtain ⟨z, hzC, hzS⟩ := mem_closure_iff_nhds.mp hqB Cn hCn
        have hz : z ∈ A₀ ∪ B₀ := by
          rw [hAB]
          exact ⟨hzC, hBsub z hzS e he hc⟩
        rcases hz with h' | h'
        · exact Or.inl ⟨z, h', hzS⟩
        · exact Or.inr ⟨z, h', hzS⟩
      have hresG : ∀ Z : Set E3, (Z ⊆ G ∨ Z ⊆ Bd) → (Z ∩ G).Nonempty → Z ⊆ G :=
        fun Z hZ hne => hZ.resolve_right fun hZB => by
          obtain ⟨z, hzZ, hzG⟩ := hne
          exact disjoint_left.mp hGBdisj hzG (hZB hzZ)
      have hresB : ∀ Z : Set E3, (Z ⊆ G ∨ Z ⊆ Bd) → (Z ∩ Bd).Nonempty → Z ⊆ Bd :=
        fun Z hZ hne => hZ.resolve_left fun hZG => by
          obtain ⟨z, hzZ, hzB⟩ := hne
          exact disjoint_left.mp hGBdisj (hZG hzZ) hzB
      rcases hmeetG with hAG | hBG
      · have hAG' := hresG A₀ hAGB hAG
        rcases hmeetB with hABd | hBBd
        · obtain ⟨z, hzA, hzB⟩ := hABd
          exact disjoint_left.mp hGBdisj (hAG' hzA) hzB
        · exact hcontra q hq e he hc hqe Cn hCn hCnΩ A₀ B₀ hAB hA₀ hB₀ hAG'
            (hresB B₀ hBGB hBBd) hqA hqB'
      · have hBG' := hresG B₀ hBGB hBG
        rcases hmeetB with hABd | hBBd
        · exact hcontra q hq e he hc hqe Cn hCn hCnΩ B₀ A₀ (by rw [union_comm]; exact hAB) hB₀
            hA₀ hBG' (hresB A₀ hAGB hABd) hqB' hqA
        · obtain ⟨z, hzB, hzBd⟩ := hBBd
          exact disjoint_left.mp hGBdisj (hBG' hzB) hzBd
  have hGne : G.Nonempty := by
    let _ : Finite XK.faces := hXfin.to_subtype
    obtain ⟨e₁, he₁, he₁c⟩ := hd.tube.hasEdge
    obtain ⟨v₀, hv₀e⟩ := Finset.card_pos.mp (by omega : 0 < e₁.card)
    have hv₀ : v₀ ∈ K.vertices :=
      K.down_closed he₁ (Finset.singleton_subset_iff.mpr hv₀e) (Finset.singleton_nonempty v₀)
    obtain ⟨y₀, ⟨hy₀C, hy₀X⟩, hy₀E⟩ := hpt v₀ hv₀
    have hXcl' : IsClosed XK.space := (isPolyhedron_space XK).isClosed
    have hFUc : IsClosed (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, F e) :=
      hEfin.isClosed_biUnion fun e he => hFcl e he.1 he.2
    have hy₀F : y₀ ∉ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, F e := by
      intro h'
      obtain ⟨e, he, hy₀e⟩ := mem_iUnion₂.mp h'
      have hy₀e' : y₀ ∈ F e ∩ frontier XK.space := ⟨hy₀e, hy₀X⟩
      rw [hFbd e he.1 he.2] at hy₀e'
      exact hy₀E e he.1 he.2 hy₀e'.1
    have hy₀EU : y₀ ∉ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
      intro h'
      obtain ⟨e, he, hy₀e⟩ := mem_iUnion₂.mp h'
      exact hy₀E e he.1 he.2 hy₀e
    have hy₀N : y₀ ∈ interior N' := h2.subsetInterior (hXcl'.frontier_subset hy₀X)
    have hU₀ : Metric.ball y₀ (δ₀ / 2) ∩ interior N' ∩
        (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)ᶜ ∩
        (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, F e)ᶜ ∈ 𝓝 y₀ :=
      Filter.inter_mem (Filter.inter_mem (Filter.inter_mem
        (Metric.ball_mem_nhds y₀ (by linarith)) (isOpen_interior.mem_nhds hy₀N))
        (hEUc.isOpen_compl.mem_nhds hy₀EU)) (hFUc.isOpen_compl.mem_nhds hy₀F)
    obtain ⟨Cn, hCn, hCU, A₀, B₀, hA₀, hB₀, hAB, hcA, hcB⟩ :=
      exists_connected_neighborhood_pair_sdiff_frontier_space hXfin h2.isManifold hy₀X hU₀
    obtain ⟨p, hpC, hpI⟩ := mem_closure_iff_nhds.mp (hXcl hy₀X) Cn hCn
    have hfar : ∀ e ∈ K.faces, e.card = 2 → 2 * δ₀ ≤ dist y₀ (h (e.centroid ℝ id)) := by
      intro e he hc
      by_contra hlt
      push Not at hlt
      exact hy₀X.2 (hball e he hc (Metric.mem_ball.mpr hlt))
    have hZG : ∀ Z : Set E3, IsConnected Z → Z ⊆ A₀ ∪ B₀ → y₀ ∈ closure Z → p ∈ Z →
        G.Nonempty := by
      intro Z hZ hZs hy₀Z hpZ
      rw [hAB] at hZs
      have hZX : Z ⊆ interior XK.space := by
        have hcomp := compl_frontier_eq_interior_union_compl hXcl'
        rcases hZ.isPreconnected.subset_or_subset isOpen_interior hXcl'.isOpen_compl
          (disjoint_compl_right.mono_left interior_subset)
          (by rw [← hcomp]; exact fun z hz => (hZs hz).2) with h' | h'
        · exact h'
        · exact absurd (interior_subset hpI) (h' hpZ)
      have hZΩ : Z ⊆ Ω := by
        intro z hz
        refine (hΩ z).mpr ⟨hZX hz, fun e he hc => ?_⟩
        have h1 := hfar e he hc
        have h2' : dist z y₀ < δ₀ / 2 := Metric.mem_ball.mp (hCU (hZs hz).1).1.1.1
        have h3 := dist_triangle y₀ z (h (e.centroid ℝ id))
        rw [dist_comm y₀ z] at h3
        linarith
      have hZE : ∀ z ∈ Z, ∀ e ∈ K.faces, e.card = 2 → z ∉ Ec e := fun z hz e he hc hze =>
        (hCU (hZs hz).1).1.2 (mem_iUnion₂.mpr ⟨e, ⟨he, hc⟩, hze⟩)
      obtain ⟨a, ha, hZa, w, hw, hZw⟩ := hlab Z hZ.isPreconnected hZ.nonempty hZΩ hZE
      have hy₀w : y₀ ∈ Cpp w := (hCppc w hw).closure_subset (closure_mono hZw hy₀Z)
      have hwv : w = v₀ := hCuniq y₀ hy₀E w hw v₀ hv₀ hy₀w hy₀C
      have hy₀a : y₀ ∈ Cpp a := by
        have hy₀B : y₀ ∈ B a := (hB a ha).isPolyhedron.isClosed.closure_subset
          (closure_mono (hZa.trans interior_subset) hy₀Z)
        have hni : y₀ ∉ interior (B a) := fun hi => disjoint_left.mp (hA a ha).2.1 hi hy₀X
        have hfr : y₀ ∈ frontier (B a) := ⟨subset_closure hy₀B, hni⟩
        rw [hBfr a ha] at hfr
        rcases hfr with h' | h'
        · exact h'.1
        · obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp h'
          exact absurd (mem_iUnion₂.mpr ⟨e, ⟨he.1, he.2.1⟩, hye⟩) hy₀F
      have hav : a = v₀ := hCuniq y₀ hy₀E a ha v₀ hv₀ hy₀a hy₀C
      refine ⟨p, (hG p).mpr ⟨hZΩ hpZ, hZE p hpZ, a, ha, hZa hpZ, ?_⟩⟩
      rw [hav, ← hwv]
      exact hZw hpZ
    have hpAB : p ∈ A₀ ∪ B₀ := by
      rw [hAB]
      exact ⟨hpC, fun hpf => hpf.2 hpI⟩
    rcases hpAB with hpA | hpB
    · exact hZG A₀ hA₀ subset_union_left (hcA ⟨mem_of_mem_nhds hCn, hy₀X⟩) hpA
    · exact hZG B₀ hB₀ subset_union_right (hcB ⟨mem_of_mem_nhds hCn, hy₀X⟩) hpB
  have hBd0 : Bd = ∅ := eq_empty_of_isPreconnected_of_closure_cover hΩc.isPreconnected
    (fun q hq => ((hG q).mp hq).1) (fun q hq => ((hBd q).mp hq).1) hGne hcov hdis
  have hyΩ : y ∈ Ω := (hΩ y).mpr ⟨hyX, hyb⟩
  have hyN : y ∈ N' := interior_subset (h2.subsetInterior (interior_subset hyX))
  rw [hd.coversTube] at hyN
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyN
  by_cases hxw : x = w
  · rw [hxw]
    exact hyw
  · have hyB : y ∈ Bd := (hBd y).mpr ⟨hyΩ, hyE, x, hx, w, hw, hxw, hyx, hyw⟩
    rw [hBd0] at hyB
    exact absurd hyB (notMem_empty y)

theorem IsHandleDecompositionOfTube.mem_interior_ball_of_vertex
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) (hXc : IsConnected XK.spaceᶜ)
    (hXint : IsConnected (interior XK.space))
    (hXcl : frontier XK.space ⊆ closure (interior XK.space))
    (hFX : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ XK.space)
    (hFbd : ∀ e ∈ K.faces, e.card = 2 → F e ∩ frontier XK.space = Ec e ∩ frontier XK.space)
    (hFc : ∀ e ∈ K.faces, e.card = 2 → IsPreconnected (F e))
    (hFcl : ∀ e ∈ K.faces, e.card = 2 → IsClosed (F e))
    (hFdisj : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      Disjoint (F e) (F e'))
    (hB : ∀ v ∈ K.vertices, IsPLBall 3 (B v))
    (hBfr : ∀ v ∈ K.vertices,
      frontier (B v) = (Cpp v ∩ frontier XK.space) ∪ ⋃ e ∈ edgesAt K v, F e)
    (hpt : ∀ v ∈ K.vertices,
      ∃ y ∈ Cpp v ∩ frontier XK.space, ∀ e ∈ K.faces, e.card = 2 → y ∉ Ec e)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hFsub : ∀ e ∈ K.faces, e.card = 2 → F e ⊆ Ec e ∪ Metric.ball (h (e.centroid ℝ id)) δ₀)
    (hFsup : ∀ e ∈ K.faces, e.card = 2 →
      (Ec e ∩ XK.space) \ Metric.ball (h (e.centroid ℝ id)) δ₀ ⊆ F e)
    (hball : ∀ e ∈ K.faces, e.card = 2 →
      Metric.ball (h (e.centroid ℝ id)) (2 * δ₀) ⊆ interior XK.space)
    (hsep : ∀ e ∈ K.faces, e.card = 2 → ∀ e' ∈ K.faces, e'.card = 2 → e ≠ e' →
      3 * δ₀ ≤ dist (h (e.centroid ℝ id)) (h (e'.centroid ℝ id)))
    (hvert : ∀ v ∈ K.vertices, ∀ e ∈ K.faces, e.card = 2 →
      δ₀ < dist (h v) (h (e.centroid ℝ id)))
    {v : E3} (hv : v ∈ K.vertices) : h v ∈ interior (B v) := by
  have hXfin := h2.facesFinite
  have ht := hd.tube
  have hKN : K.space ⊆ N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood).trans interior_subset
  have hvK : ∀ w ∈ K.vertices, w ∈ K.space := fun w hw =>
    K.convexHull_subset_space hw (subset_convexHull ℝ _ (Finset.mem_singleton_self w))
  have hvX : h v ∈ interior XK.space :=
    subset_interior_iff_mem_nhdsSet.mpr h2.isNeighborhood (mem_image_of_mem h (hvK v hv))
  have hhv : ∀ w ∈ K.vertices, h w ∈ Cpp w := fun w hw => by
    have hw' : h w ∈ Cpp w ∩ h '' K.vertices := by
      rw [hd.oneVertex w hw]
      exact mem_singleton _
    exact hw'.1
  have hvE : ∀ e ∈ K.faces, e.card = 2 → h v ∉ Ec e := by
    intro e he hc hve
    obtain ⟨a, hae, b, hbe, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < e.card)
    have ha : a ∈ K.vertices :=
      K.down_closed he (Finset.singleton_subset_iff.mpr hae) (Finset.singleton_nonempty a)
    have hb : b ∈ K.vertices :=
      K.down_closed he (Finset.singleton_subset_iff.mpr hbe) (Finset.singleton_nonempty b)
    have hva : h v = h a := by
      have hva' : h v ∈ Cpp a ∩ h '' K.vertices :=
        ⟨hd.pseudoCell_subset_handlePiece he hc hae hve, mem_image_of_mem h hv⟩
      rw [hd.oneVertex a ha] at hva'
      exact hva'
    have hvb : h v = h b := by
      have hvb' : h v ∈ Cpp b ∩ h '' K.vertices :=
        ⟨hd.pseudoCell_subset_handlePiece he hc hbe hve, mem_image_of_mem h hv⟩
      rw [hd.oneVertex b hb] at hvb'
      exact hvb'
    exact hab (ht.injOn (hKN (hvK a ha)) (hKN (hvK b hb)) (hva.symm.trans hvb))
  have hcover := hd.iUnion_balls_eq h2 h34 hXc hXint hFX hFbd hFc hFcl hFdisj hB hBfr hpt
  have hvY : h v ∈ ⋃ w ∈ K.vertices, B w := by
    rw [hcover]
    exact interior_subset hvX
  obtain ⟨x, hx, hvx⟩ := mem_iUnion₂.mp hvY
  have hvF : ∀ e ∈ K.faces, e.card = 2 → h v ∉ F e := fun e he hc hvF => by
    rcases hFsub e he hc hvF with h' | h'
    · exact hvE e he hc h'
    · exact lt_asymm (Metric.mem_ball.mp h') (hvert v hv e he hc)
  have hvxi : h v ∈ interior (B x) := by
    by_contra hn
    have hfr : h v ∈ frontier (B x) := ⟨subset_closure hvx, hn⟩
    rw [hBfr x hx] at hfr
    rcases hfr with h' | h'
    · exact h'.2.2 hvX
    · obtain ⟨e, he, hve⟩ := mem_iUnion₂.mp h'
      exact hvF e he.1 he.2.1 hve
  have hvCx := hd.mem_handlePiece_of_mem_interior_ball h2 h34 hXc hXint hXcl hFX hFbd hFc hFcl
    hFdisj hB hBfr hpt hδ₀ hFsub hFsup hball hsep hvX (hvert v hv) hvE hx hvxi
  have hxv : x = v := by
    by_contra hne
    obtain ⟨e, he, hye⟩ :=
      mem_iUnion₂.mp (hd.handlePiece_inter_subset_pseudoCells hx hv hne ⟨hvCx, hhv v hv⟩)
    exact hvE e he.1 he.2 hye
  rw [hxv] at hvxi
  exact hvxi

end DifferentialGeometry.Topology.PiecewiseLinear
