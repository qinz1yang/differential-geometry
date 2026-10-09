/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallSphereLink
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceEulerChar
import DifferentialGeometry.Topology.PiecewiseLinear.LinkHalfSpace
import DifferentialGeometry.Topology.PiecewiseLinear.PiecewiseAffineSimplicial
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeSinglePolygonTraces
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionTransport

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section HandlePieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsHandleDecompositionOfTube.subset_interior_handlePiece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {v : E3}
    (hv : v ∈ K.vertices) :
    (interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) ∩ Cpp v ⊆
      interior (Cpp v) := by
  have hfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun e he => he.1
  have hO : IsOpen (interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :=
    isOpen_interior.sdiff (hfin.isClosed_biUnion fun e he => (hd.pseudoCell e he.1 he.2).isClosed)
  rintro y ⟨hyO, hyC⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO y hyO
  have hsub : Metric.ball y r ⊆ N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e :=
    fun z hz => ⟨interior_subset (hball hz).1, (hball hz).2⟩
  rw [hd.componentClosure v hv] at hyC
  obtain ⟨z, hzB, hzc⟩ := mem_closure_iff_nhds.mp hyC _ (Metric.ball_mem_nhds y hr)
  have hBc := (convex_ball y r).isPreconnected.subset_connectedComponentIn hzB hsub
  rw [← connectedComponentIn_eq hzc] at hBc
  refine mem_interior.mpr ⟨Metric.ball y r, fun w hw => ?_, Metric.isOpen_ball,
    Metric.mem_ball_self hr⟩
  rw [hd.componentClosure v hv]
  exact subset_closure (hBc hw)

theorem IsHandleDecompositionOfTube.subset_handlePiece_of_isPreconnected
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {v : E3}
    (hv : v ∈ K.vertices) {P : Set E3} (hP : IsPreconnected P)
    (hPO : P ⊆ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)
    (hne : (P ∩ Cpp v).Nonempty) : P ⊆ Cpp v := by
  have hCc : IsClosed (Cpp v) := by
    rw [hd.componentClosure v hv]
    exact isClosed_closure
  obtain ⟨z, hzP, hzC⟩ := hne
  have hsub := hP.subset_left_of_subset_union isOpen_interior hCc.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset)
    (fun y hy => by
      by_cases hyC : y ∈ Cpp v
      · exact Or.inl (hd.subset_interior_handlePiece hv ⟨hPO hy, hyC⟩)
      · exact Or.inr hyC)
    ⟨z, hzP, hd.subset_interior_handlePiece hv ⟨hPO hzP, hzC⟩⟩
  exact hsub.trans interior_subset

theorem IsHandleDecompositionOfTube.pseudoCell_subset_handlePiece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {f : Finset E3}
    (hf : f ∈ K.faces) (hfc : f.card = 2) {v : E3} (hvf : v ∈ f) : Ec f ⊆ Cpp v := by
  obtain ⟨w, hwf, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < f.card) v
  have hv : v ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr hvf) (Finset.singleton_nonempty v)
  have hw : w ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr hwf) (Finset.singleton_nonempty w)
  have hpair : ({v, w} : Finset E3) = f := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hvf (Finset.singleton_subset_iff.mpr hwf))
    (by rw [hfc, Finset.card_pair hwv.symm])
  have heq := hd.handleEdge v hv w hw hwv.symm (by rw [hpair]; exact hf)
  rw [hpair] at heq
  rw [← heq]
  exact inter_subset_left

theorem IsHandleDecompositionOfTube.handlePiece_inter_eq_pseudoCell
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {f : Finset E3}
    (hf : f ∈ K.faces) (hfc : f.card = 2) {v w : E3} (hvf : v ∈ f) (hwf : w ∈ f) (hvw : v ≠ w) :
    Cpp v ∩ Cpp w = Ec f := by
  have hv : v ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr hvf) (Finset.singleton_nonempty v)
  have hw : w ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr hwf) (Finset.singleton_nonempty w)
  have hpair : ({v, w} : Finset E3) = f := Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hvf (Finset.singleton_subset_iff.mpr hwf))
    (by rw [hfc, Finset.card_pair hvw])
  have heq := hd.handleEdge v hv w hw hvw (by rw [hpair]; exact hf)
  rwa [hpair] at heq

theorem IsHandleDecompositionOfTube.handlePiece_inter_pseudoCell_eq_empty
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {v : E3}
    (hv : v ∈ K.vertices) {f : Finset E3} (hf : f ∈ K.faces) (hfc : f.card = 2) (hvf : v ∉ f) :
    Cpp v ∩ Ec f = ∅ := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hfc
  have ha : a ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a {b}))
      (Finset.singleton_nonempty a)
  have hb : b ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))) (Finset.singleton_nonempty b)
  have hva : v ≠ a := fun hva => hvf (by rw [hva]; exact Finset.mem_insert_self a {b})
  have hvb : v ≠ b := fun hvb => hvf (by
    rw [hvb]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self b))
  rw [← hd.handleEdge a ha b hb hab hf, ← inter_assoc]
  exact hd.inter_inter_eq_empty hv ha hb hva hvb hab

theorem IsPolyhedralTubeNeighborhood.isPLBall_geometricLink_handlePiece [DecidableEq E3]
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {v : E3} (hv : v ∈ K.vertices)
    {f : Finset E3} (hf : f ∈ K.faces) (hfc : f.card = 2) (hvf : v ∈ f)
    (R : Geometry.SimplicialComplex ℝ E3) [Finite R.faces]
    (hR : R.space = Cpp v ∩ frontier XK.space) {x : E3} (hx : {x} ∈ R.faces)
    (hxJ : x ∈ Ec f ∩ frontier XK.space) :
    IsPLBall 1 (SimplicialComplex.geometricLink R {x}).space := by
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hpc := hd.pseudoCell f hf hfc
  obtain ⟨w, hwf, hwv⟩ := Finset.exists_mem_ne (by omega : 1 < f.card) v
  have hw : w ∈ K.vertices :=
    K.down_closed hf (Finset.singleton_subset_iff.mpr hwf) (Finset.singleton_nonempty w)
  have hfv : Ec f ⊆ Cpp v := hd.pseudoCell_subset_handlePiece hf hfc hvf
  have hfw : Ec f ⊆ Cpp w := hd.pseudoCell_subset_handlePiece hf hfc hwf
  have hvw : Cpp v ∩ Cpp w = Ec f :=
    hd.handlePiece_inter_eq_pseudoCell hf hfc hvf hwf hwv.symm
  have hEEc : Eint f ⊆ Ec f := by
    rw [hpc.carrierEq]
    exact subset_union_left
  have hfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun e he => he.1
  have hEbdc : IsClosed (Ebd f) := by
    rw [← hd.rimFrontier f hf hfc]
    exact hpc.isClosed.inter isClosed_frontier
  let W : Set E3 := interior N' \
    (Ebd f ∪ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2} \ {f}, Ec e)
  have hWo : IsOpen W := isOpen_interior.sdiff (hEbdc.union
    ((hfin.subset sdiff_subset).isClosed_biUnion fun e he =>
      (hd.pseudoCell e he.1.1 he.1.2).isClosed))
  have hxE : x ∈ Eint f := (h2.trace_subset hd hf hfc hxJ).1
  have hxW : x ∈ W := by
    refine ⟨hd.interior_pseudoCell_subset_interior hf hfc hxE, ?_⟩
    rintro (hxB | hxU)
    · exact Set.disjoint_left.mp hpc.disjointRim hxE hxB
    · obtain ⟨e, ⟨he, hef⟩, hxe⟩ := mem_iUnion₂.mp hxU
      exact Set.disjoint_left.mp (hd.pseudoCellDisjoint f hf hfc e he.1 he.2 (Ne.symm hef))
        hxJ.1 hxe
  obtain ⟨U, φ, ρ, hU, hxU, hρ, hφ, hφx, hφU⟩ := h2.exists_sideChart hd hf hfc hxJ
  let g := Function.invFunOn φ U
  have hgc : ContinuousOn g (Metric.ball 0 ρ) := hφ.isPiecewiseAffineOn_invFunOn.continuousOn
  have hgU : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ρ, g z ∈ U ∧ φ (g z) = z := fun z hz =>
    ⟨hφ.bijOn.surjOn.mapsTo_invFunOn hz, hφ.bijOn.invOn_invFunOn.2 hz⟩
  have hgφ : ∀ y ∈ U, g (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hg0 : g 0 = x := by
    rw [← hφx]
    exact hgφ x hxU
  have h0ρ : (0 : ℝ × ℝ × ℝ) ∈ Metric.ball 0 ρ := Metric.mem_ball_self hρ
  obtain ⟨r₀, hr₀, hr₀W⟩ := Metric.mem_nhds_iff.mp
    ((hgc.continuousAt (Metric.isOpen_ball.mem_nhds h0ρ)).preimage_mem_nhds
      (by rw [hg0]; exact hWo.mem_nhds hxW))
  have hr : 0 < min r₀ ρ := lt_min hr₀ hρ
  have hrρ : Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ) ⊆ Metric.ball 0 ρ :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hgW : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), g z ∈ W := fun z hz =>
    hr₀W (Metric.ball_subset_ball (min_le_left _ _) hz)
  have hgO : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), z.2.2 ≠ 0 →
      g z ∈ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
    intro z hz hz2
    have hzW := hgW z hz
    obtain ⟨hzU, hφz⟩ := hgU z (hrρ hz)
    refine ⟨hzW.1, fun hU' => ?_⟩
    obtain ⟨e, he, hze⟩ := mem_iUnion₂.mp hU'
    by_cases hef : e = f
    · rw [hef, hpc.carrierEq] at hze
      rcases hze with hzE | hzB
      · have h0 := (hφU _ hzU).1.mp hzE
        rw [hφz] at h0
        exact hz2 h0
      · exact hzW.2 (Or.inl hzB)
    · exact hzW.2 (Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hef⟩, hze⟩))
  have hgE : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), z.2.2 = 0 → g z ∈ Ec f := by
    intro z hz hz2
    obtain ⟨hzU, hφz⟩ := hgU z (hrρ hz)
    refine hEEc ((hφU _ hzU).1.mpr ?_)
    rw [hφz]
    exact hz2
  have hlin2 : IsLinearMap ℝ fun z : ℝ × ℝ × ℝ => z.2.2 :=
    ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))).isLinear
  let Hp : Set (ℝ × ℝ × ℝ) := Metric.ball 0 (min r₀ ρ) ∩ {z | 0 < z.2.2}
  let Hm : Set (ℝ × ℝ × ℝ) := Metric.ball 0 (min r₀ ρ) ∩ {z | z.2.2 < 0}
  have hHp : IsPreconnected (g '' Hp) :=
    ((convex_ball 0 _).inter (convex_halfSpace_gt hlin2 0)).isPreconnected.image g
      (hgc.mono (inter_subset_left.trans hrρ))
  have hHm : IsPreconnected (g '' Hm) :=
    ((convex_ball 0 _).inter (convex_halfSpace_lt hlin2 0)).isPreconnected.image g
      (hgc.mono (inter_subset_left.trans hrρ))
  have hHpO : g '' Hp ⊆ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgO z hz.1 hz.2.ne'
  have hHmO : g '' Hm ⊆ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
    rintro _ ⟨z, hz, rfl⟩
    exact hgO z hz.1 hz.2.ne
  have hopen : IsOpen (U ∩ φ ⁻¹' Metric.ball 0 (min r₀ ρ)) :=
    hφ.isPiecewiseAffineOn.continuousOn.isOpen_inter_preimage hU Metric.isOpen_ball
  have hxopen : x ∈ U ∩ φ ⁻¹' Metric.ball 0 (min r₀ ρ) := by
    refine ⟨hxU, ?_⟩
    rw [mem_preimage, hφx]
    exact Metric.mem_ball_self hr
  have hnear : ∀ a ∈ K.vertices, a ∈ f → ∃ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ),
      z.2.2 ≠ 0 ∧ g z ∈ Cpp a := by
    intro a ha haf
    have hxa : x ∈ closure (connectedComponentIn (N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧
        e.card = 2}, Ec e) (h a)) := by
      rw [← hd.componentClosure a ha]
      exact hd.pseudoCell_subset_handlePiece hf hfc haf hxJ.1
    obtain ⟨y, ⟨hyU, hyb⟩, hyc⟩ := mem_closure_iff_nhds.mp hxa _ (hopen.mem_nhds hxopen)
    have hyN := connectedComponentIn_subset _ _ hyc
    refine ⟨φ y, hyb, fun h0 => hyN.2 (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, ?_⟩), ?_⟩
    · have := hgE (φ y) hyb h0
      rwa [hgφ y hyU] at this
    · rw [hgφ y hyU, hd.componentClosure a ha]
      exact subset_closure hyc
  have hside : ∀ H₁ H₂ : Set (ℝ × ℝ × ℝ), IsPreconnected (g '' H₁) →
      IsPreconnected (g '' H₂) →
      g '' H₁ ⊆ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e →
      g '' H₂ ⊆ interior N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e →
      (∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), z.2.2 ≠ 0 → z ∈ H₁ ∨ z ∈ H₂) →
      (g '' H₁ ∩ Cpp v).Nonempty → g '' H₁ ⊆ Cpp v ∧ Disjoint (g '' H₂) (Cpp v) := by
    intro H₁ H₂ hH₁ hH₂ hH₁O hH₂O hcov hne
    have h₁ := hd.subset_handlePiece_of_isPreconnected hv hH₁ hH₁O hne
    refine ⟨h₁, ?_⟩
    obtain ⟨z, hz, hz2, hzw⟩ := hnear w hw hwf
    have hnotEc : ∀ y ∈ g '' H₁ ∪ g '' H₂, y ∉ Ec f := by
      rintro y (hy | hy) hyE
      · exact (hH₁O hy).2 (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, hyE⟩)
      · exact (hH₂O hy).2 (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, hyE⟩)
    rcases hcov z hz hz2 with hz1 | hz2'
    · exact (hnotEc (g z) (Or.inl ⟨z, hz1, rfl⟩) (hvw ▸ ⟨h₁ ⟨z, hz1, rfl⟩, hzw⟩)).elim
    · have h₂ := hd.subset_handlePiece_of_isPreconnected hw hH₂ hH₂O ⟨g z, ⟨z, hz2', rfl⟩, hzw⟩
      exact Set.disjoint_left.mpr fun y hy hyv =>
        hnotEc y (Or.inr hy) (hvw ▸ ⟨hyv, h₂ hy⟩)
  obtain ⟨σ, hσσ, hσp, hσm⟩ : ∃ σ : ℝ, σ * σ = 1 ∧
      (∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), 0 < σ * z.2.2 → g z ∈ Cpp v) ∧
      (∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ), σ * z.2.2 < 0 → g z ∉ Cpp v) := by
    obtain ⟨z₀, hz₀, hz₀2, hz₀v⟩ := hnear v hv hvf
    rcases lt_or_gt_of_ne hz₀2 with hneg | hpos
    · obtain ⟨h₁, h₂⟩ := hside Hm Hp hHm hHp hHmO hHpO
        (fun z hz hz2 => (lt_or_gt_of_ne hz2).imp (fun h => ⟨hz, h⟩) fun h => ⟨hz, h⟩)
        ⟨g z₀, ⟨z₀, ⟨hz₀, hneg⟩, rfl⟩, hz₀v⟩
      refine ⟨-1, by norm_num, fun z hz hpos' => h₁ ⟨z, ⟨hz, show z.2.2 < 0 by linarith⟩, rfl⟩,
        fun z hz hneg' hzv =>
          Set.disjoint_left.mp h₂ ⟨z, ⟨hz, show 0 < z.2.2 by linarith⟩, rfl⟩ hzv⟩
    · obtain ⟨h₁, h₂⟩ := hside Hp Hm hHp hHm hHpO hHmO
        (fun z hz hz2 => (lt_or_gt_of_ne hz2).symm.imp (fun h => ⟨hz, h⟩) fun h => ⟨hz, h⟩)
        ⟨g z₀, ⟨z₀, ⟨hz₀, hpos⟩, rfl⟩, hz₀v⟩
      refine ⟨1, by norm_num, fun z hz hpos' => h₁ ⟨z, ⟨hz, show 0 < z.2.2 by linarith⟩, rfl⟩,
        fun z hz hneg' hzv =>
          Set.disjoint_left.mp h₂ ⟨z, ⟨hz, show z.2.2 < 0 by linarith⟩, rfl⟩ hzv⟩
  have hσne : σ ≠ 0 := fun h0 => by rw [h0, zero_mul] at hσσ; exact zero_ne_one hσσ
  have hchar : ∀ z ∈ Metric.ball (0 : ℝ × ℝ × ℝ) (min r₀ ρ),
      g z ∈ Cpp v ∩ frontier XK.space ↔ z.2.1 = 0 ∧ 0 ≤ σ * z.2.2 := by
    intro z hz
    obtain ⟨hzU, hφz⟩ := hgU z (hrρ hz)
    have hfrz : g z ∈ frontier XK.space ↔ z.2.1 = 0 := by
      rw [(hφU _ hzU).2.1, hφz]
    constructor
    · rintro ⟨hzC, hzfr⟩
      exact ⟨hfrz.mp hzfr, not_lt.mp fun hneg => hσm z hz hneg hzC⟩
    · rintro ⟨hz1, hz2⟩
      refine ⟨?_, hfrz.mpr hz1⟩
      rcases hz2.lt_or_eq with hpos | hzero
      · exact hσp z hz hpos
      · have hz2' : z.2.2 = 0 := by
          rcases mul_eq_zero.mp hzero.symm with h0 | h0
          · exact (hσne h0).elim
          · exact h0
        exact hfv (hgE z hz hz2')
  let M : (ℝ × ℝ × ℝ) →ₗ[ℝ] ℝ × ℝ := (LinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (σ • ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))))
  have hM : ∀ z : ℝ × ℝ × ℝ, M z = (z.1, σ * z.2.2) := fun z => rfl
  let ψ : E3 → ℝ × ℝ := M.toAffineMap ∘ φ
  have hψ : ∀ y, ψ y = ((φ y).1, σ * (φ y).2.2) := fun y => hM (φ y)
  have hψU : IsPiecewiseAffineOn ψ U := hφ.isPiecewiseAffineOn.affine_comp M.toAffineMap
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hopen x hxopen
  obtain ⟨Nc, hNc⟩ := ((Set.toFinite R.faces).image (fun s : Finset E3 => s.card)).bddAbove
  have hcardR : ∀ s ∈ R.faces, s.card ≤ Nc + 1 :=
    fun s hs => (hNc (mem_image_of_mem _ hs)).trans (Nat.le_succ Nc)
  obtain ⟨R', hR', hR'fin, -, hdiam⟩ := exists_isSubdivision_diam_lt R hcardR hε
  have : Finite R'.faces := hR'fin.to_subtype
  have hxR' : {x} ∈ R'.faces := hR'.singleton_mem hx
  rw [← isPLBall_geometricLink_iff_of_isSubdivision hR' hx,
    ← geometricLink_starComplex R' x]
  have : Finite (starComplex R' x).faces := (starComplex_faces_finite R' x).to_subtype
  have hStsp : (starComplex R' x).space = closedStar R' x := starComplex_space R' x hxR'
  have hStA : (starComplex R' x).space ⊆ Cpp v ∩ frontier XK.space := by
    rw [hStsp, ← hR, ← hR'.space_eq]
    exact closedStar_subset_space R' x
  have hStU : (starComplex R' x).space ⊆ U ∩ φ ⁻¹' Metric.ball 0 (min r₀ ρ) := by
    rw [hStsp]
    intro y hy
    obtain ⟨s, ⟨hs, hxs⟩, hys⟩ := mem_iUnion₂.mp hy
    refine hεU (Metric.mem_ball.mpr ((Metric.dist_le_diam_of_mem
      (s.finite_toSet.isCompact_convexHull ℝ).isBounded hys hxs).trans_lt (hdiam s hs)))
  have hψSt : IsPiecewiseAffineOn ψ (starComplex R' x).space :=
    hψU.mono_of_isPolyhedron (isPolyhedron_space _) (hStU.trans inter_subset_left)
  have hmemA : ∀ y ∈ (starComplex R' x).space, (φ y).2.1 = 0 ∧ 0 ≤ σ * (φ y).2.2 := by
    intro y hy
    have hyU := hStU hy
    have h := (hchar (φ y) hyU.2).mp (by rw [hgφ y hyU.1]; exact hStA hy)
    exact h
  have hinjSt : InjOn ψ (starComplex R' x).space := by
    intro y₁ hy₁ y₂ hy₂ heq
    rw [hψ, hψ] at heq
    obtain ⟨h1, h2'⟩ := Prod.mk.inj heq
    have h22 : (φ y₁).2.2 = (φ y₂).2.2 := mul_left_cancel₀ hσne h2'
    have h21 : (φ y₁).2.1 = (φ y₂).2.1 := ((hmemA y₁ hy₁).1).trans ((hmemA y₂ hy₂).1).symm
    exact hφ.bijOn.injOn (hStU hy₁).1 (hStU hy₂).1 (Prod.ext h1 (Prod.ext h21 h22))
  obtain ⟨St', hSt', hSt'fin, hAff⟩ := hψSt.exists_isSubdivision_affineOn_faces _
  have : Finite St'.faces := hSt'fin.to_subtype
  have hsimp : EqOn (simplicialMap St' ψ) ψ St'.space :=
    simplicialMap_eq_of_forall_affineOn St' _ hAff
  have hinjSt' : InjOn ψ St'.space := by
    rw [hSt'.space_eq]
    exact hinjSt
  have hinj' : InjOn (simplicialMap St' ψ) St'.space :=
    fun a ha b hb hab => hinjSt' ha hb (by rw [← hsimp ha, ← hsimp hb]; exact hab)
  have hind : ∀ s ∈ St'.faces, AffineIndependent ℝ
      ((↑) : {u // u ∈ s.image ψ} → ℝ × ℝ) := fun s hs => by
    obtain ⟨Af, hAf⟩ := hAff s hs
    have himgs : s.image ψ = s.image Af :=
      Finset.image_congr fun u hu => hAf (subset_convexHull ℝ _ hu)
    rw [himgs]
    refine affineIndependent_image_of_injOn_convexHull Af (St'.indep hs) fun a ha b hb hab =>
      hinjSt' (St'.convexHull_subset_space hs ha) (St'.convexHull_subset_space hs hb) ?_
    rw [hAf ha, hAf hb]
    exact hab
  obtain ⟨φ', hφ'⟩ := exists_isGlueIso_simplicialImage St' ψ hind hinj'
  have : Finite (simplicialImage St' ψ hind hinj').faces :=
    (simplicialImage_faces_finite St' ψ hind hinj').to_subtype
  have hxSt : {x} ∈ (starComplex R' x).faces := singleton_mem_starComplex R' x hxR'
  have hxSt' : {x} ∈ St'.faces := hSt'.singleton_mem hxSt
  have hψx : ψ x = 0 := by
    rw [hψ, hφx]
    simp
  have hLsp : (simplicialImage St' ψ hind hinj').space = ψ '' (starComplex R' x).space := by
    rw [simplicialImage_space, hsimp.image_eq, hSt'.space_eq]
  obtain ⟨O₁, hO₁, hxO₁, hO₁St⟩ := mem_nhdsWithin.mp (closedStar_mem_nhdsWithin R' x)
  let κ : ℝ × ℝ → ℝ × ℝ × ℝ := fun p => (p.1, 0, σ * p.2)
  have hκc : Continuous κ := by fun_prop
  have hVo : IsOpen (κ ⁻¹' (Metric.ball 0 (min r₀ ρ) ∩ g ⁻¹' O₁)) :=
    ((hgc.mono hrρ).isOpen_inter_preimage Metric.isOpen_ball hO₁).preimage hκc
  have hκ0 : κ 0 = 0 := by
    simp [κ]
  have hψV : ψ x ∈ κ ⁻¹' (Metric.ball 0 (min r₀ ρ) ∩ g ⁻¹' O₁) := by
    rw [hψx, mem_preimage, hκ0]
    exact ⟨Metric.mem_ball_self hr, by rw [mem_preimage, hg0]; exact hxO₁⟩
  have hhalf : ∃ V ∈ 𝓝 (ψ x), (simplicialImage St' ψ hind hinj').space ∩ V =
      {p | 0 ≤ (LinearMap.snd ℝ ℝ ℝ) p} ∩ V := by
    refine ⟨_, hVo.mem_nhds hψV, ?_⟩
    rw [hLsp]
    ext p
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hpV⟩
      refine ⟨?_, hpV⟩
      change 0 ≤ (ψ y).2
      rw [hψ]
      exact (hmemA y hy).2
    · rintro ⟨hp, hpV⟩
      have hp2 : 0 ≤ p.2 := hp
      have hκb := hpV.1
      have hκO := hpV.2
      have hgmem : g (κ p) ∈ Cpp v ∩ frontier XK.space := by
        refine (hchar (κ p) hκb).mpr ⟨rfl, ?_⟩
        change 0 ≤ σ * (σ * p.2)
        rw [← mul_assoc, hσσ, one_mul]
        exact hp2
      have hgR' : g (κ p) ∈ R'.space := by
        rw [hR'.space_eq, hR]
        exact hgmem
      have hgSt : g (κ p) ∈ (starComplex R' x).space := by
        rw [hStsp]
        exact hO₁St ⟨hκO, hgR'⟩
      refine ⟨⟨g (κ p), hgSt, ?_⟩, hpV⟩
      rw [hψ, (hgU (κ p) (hrρ hκb)).2]
      change (p.1, σ * (σ * p.2)) = p
      rw [← mul_assoc, hσσ, one_mul]
  have hL := isPLBall_geometricLink_of_halfSpace (n := 1) (by simp)
    (simplicialImage St' ψ hind hinj') (hφ'.singleton_mem hxSt') (LinearMap.snd ℝ ℝ ℝ)
    (fun h0 => by
      have := LinearMap.congr_fun h0 ((0 : ℝ), (1 : ℝ))
      simp at this)
    (by rw [hψx]; rfl) hhalf
  have : Finite (SimplicialComplex.geometricLink St' {x}).faces :=
    ((Set.toFinite St'.faces).subset (SimplicialComplex.geometricLink_le St' {x})).to_subtype
  have : Finite (SimplicialComplex.geometricLink (simplicialImage St' ψ hind hinj') {ψ x}).faces :=
    ((Set.toFinite _).subset (SimplicialComplex.geometricLink_le _ {ψ x})).to_subtype
  have hSt'ball := hL.of_isPLHomeomorphOn (hφ'.geometricLink hxSt').symm.isPLHomeomorphOn
  rwa [isPLBall_geometricLink_iff_of_isSubdivision hSt' hxSt] at hSt'ball

end HandlePieces

end DifferentialGeometry.Topology.PiecewiseLinear
