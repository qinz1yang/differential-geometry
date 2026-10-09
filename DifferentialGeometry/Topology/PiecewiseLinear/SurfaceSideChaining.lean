/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsCombinatorialManifold.false_of_sdiff_subset_connectedComponentIn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces] (hL : IsCombinatorialManifold 2 L)
    (hdim : Module.finrank ℝ E = 3) (hconn : IsConnected L.space) {x : E} (hx : x ∈ L.space)
    {C : Set E} (hC : C ∈ 𝓝 x) {y : E} (hsub : C \ L.space ⊆ connectedComponentIn L.spaceᶜ y) :
    False := by
  obtain ⟨a, ha, b, hb, hdisj, hunion, -, -, hfa, hfb⟩ :=
    hL.exists_connectedComponentIn_pair_compl L hdim hconn
  have hmiss : ∀ Z : Set E, Z ⊆ L.spaceᶜ → x ∈ frontier Z → ¬ Disjoint Z (C \ L.space) := by
    intro Z hZ hxZ hZC
    obtain ⟨z, hzC, hzZ⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hxZ) C hC
    exact Set.disjoint_left.mp hZC hzZ ⟨hzC, hZ hzZ⟩
  have hA : connectedComponentIn L.spaceᶜ a ⊆ L.spaceᶜ := connectedComponentIn_subset _ _
  have hB : connectedComponentIn L.spaceᶜ b ⊆ L.spaceᶜ := connectedComponentIn_subset _ _
  by_cases hy : y ∈ L.spaceᶜ
  · have hy' : y ∈ connectedComponentIn L.spaceᶜ a ∪ connectedComponentIn L.spaceᶜ b := by
      rw [hunion]
      exact hy
    rcases hy' with hya | hyb
    · rw [← connectedComponentIn_eq hya] at hsub
      exact hmiss _ hB (hfb.symm ▸ hx) (hdisj.symm.mono_right hsub)
    · rw [← connectedComponentIn_eq hyb] at hsub
      exact hmiss _ hA (hfa.symm ▸ hx) (hdisj.mono_right hsub)
  · rw [connectedComponentIn_eq_empty hy] at hsub
    exact hmiss _ hA (hfa.symm ▸ hx) (Set.disjoint_of_subset_right hsub (Set.disjoint_empty _))

theorem IsPreconnected.subset_closure_of_forall_sides {X : Type*} [TopologicalSpace X]
    {G F T : Set X} (hG : IsPreconnected G) (hGF : G ⊆ F) (hTF : Disjoint T F)
    (hsides : ∀ x ∈ G, ∀ U ∈ 𝓝 x, ∃ C ∈ 𝓝 x, C ⊆ U ∧ ∃ A B : Set X, IsConnected A ∧
      IsConnected B ∧ A ∪ B = C \ F ∧ C ∩ F ⊆ closure A ∧ C ∩ F ⊆ closure B)
    (hloc : ∀ x ∈ G, ∃ U ∈ 𝓝 x, ∀ Z : Set X, IsPreconnected Z → Z ⊆ U \ F →
      (Z ∩ T).Nonempty → Z ⊆ T)
    (hne : (G ∩ closure T).Nonempty) : G ⊆ closure T := by
  have hstep : ∀ x ∈ G ∩ closure T, ∃ V ∈ 𝓝 x, G ∩ V ⊆ closure T := by
    rintro x ⟨hxG, hxT⟩
    obtain ⟨U, hU, hUsat⟩ := hloc x hxG
    obtain ⟨C, hC, hCU, A, B, hA, hB, hAB, hcA, hcB⟩ := hsides x hxG U hU
    obtain ⟨y, hyC, hyT⟩ := mem_closure_iff_nhds.mp hxT C hC
    have hyAB : y ∈ A ∪ B := by
      rw [hAB]
      exact ⟨hyC, Set.disjoint_left.mp hTF hyT⟩
    have hsat : ∀ Z : Set X, IsConnected Z → Z ⊆ A ∪ B → y ∈ Z → closure Z ⊆ closure T := by
      intro Z hZ hZAB hyZ
      refine closure_mono (hUsat Z hZ.isPreconnected (fun z hz => ?_) ⟨y, hyZ, hyT⟩)
      have hz' := hZAB hz
      rw [hAB] at hz'
      exact ⟨hCU hz'.1, hz'.2⟩
    refine ⟨C, hC, fun z hz => ?_⟩
    rcases hyAB with hyA | hyB
    · exact hsat A hA subset_union_left hyA (hcA ⟨hz.2, hGF hz.1⟩)
    · exact hsat B hB subset_union_right hyB (hcB ⟨hz.2, hGF hz.1⟩)
  choose! V hV hVT using hstep
  let u := ⋃ x ∈ G ∩ closure T, interior (V x)
  have hu : IsOpen u := isOpen_biUnion fun x _ => isOpen_interior
  have hGu : G ∩ u ⊆ closure T := by
    rintro z ⟨hzG, hzu⟩
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hzu
    exact hVT x hx ⟨hzG, interior_subset hzx⟩
  by_contra hnot
  obtain ⟨z, hzG, hzT⟩ := not_subset.mp hnot
  obtain ⟨x₀, hx₀⟩ := hne
  have hx₀u : x₀ ∈ u := mem_iUnion₂.mpr ⟨x₀, hx₀, mem_interior_iff_mem_nhds.mpr (hV x₀ hx₀)⟩
  obtain ⟨w, hwG, hwu, hwv⟩ := hG u (closure T)ᶜ hu isClosed_closure.isOpen_compl
    (fun y hy => by
      by_cases hyT : y ∈ closure T
      · exact Or.inl (mem_iUnion₂.mpr ⟨y, ⟨hy, hyT⟩, mem_interior_iff_mem_nhds.mpr
          (hV y ⟨hy, hyT⟩)⟩)
      · exact Or.inr hyT)
    ⟨x₀, hx₀.1, hx₀u⟩ ⟨z, hzG, hzT⟩
  exact hwv (hGu ⟨hwG, hwu⟩)

theorem isPreconnected_ball_sdiff_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) (P : E) {δ₀ ρ : ℝ} (hδ₀ : 0 ≤ δ₀) :
    IsPreconnected (Metric.ball P ρ \ Metric.closedBall P δ₀) := by
  have hS := isConnected_sphere hE (0 : E) zero_le_one
  have hprod := hS.isPreconnected.prod (isPreconnected_Ioo (a := δ₀) (b := ρ))
  have himg := hprod.image (fun z : E × ℝ => P + z.2 • z.1) (by fun_prop)
  convert himg using 1
  ext y
  constructor
  · rintro ⟨hyρ, hyδ⟩
    rw [Metric.mem_ball, dist_eq_norm] at hyρ
    rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hyδ
    have hpos : 0 < ‖y - P‖ := hδ₀.trans_lt hyδ
    refine ⟨(‖y - P‖⁻¹ • (y - P), ‖y - P‖), ⟨?_, hyδ, hyρ⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    · simp only [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
  · rintro ⟨⟨u, t⟩, ⟨hu, ht⟩, rfl⟩
    rw [mem_sphere_zero_iff_norm] at hu
    have hnorm : ‖P + t • u - P‖ = t := by
      rw [add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_eq_abs,
        abs_of_pos (hδ₀.trans_lt ht.1)]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, hnorm]
      exact ht.2
    · rw [Metric.mem_closedBall, dist_eq_norm, hnorm, not_le]
      exact ht.1

theorem exists_mem_closure_connectedComponentIn_ball_sdiff_closedBall {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (hE : 1 < Module.rank ℝ E) {F : Set E}
    (hF : IsPreconnected F) (hFc : IsClosed F) {P : E} (hP : P ∈ F) {δ₀ ρ : ℝ} (hδ₀ : 0 < δ₀)
    (hδρ : δ₀ < ρ) (hout : ∃ z ∈ F, ρ ≤ dist z P) {a : E}
    (ha : a ∈ Metric.ball P ρ \ Metric.closedBall P δ₀) (haF : a ∉ F) :
    ∃ x ∈ F, x ∈ Metric.ball P ρ \ Metric.closedBall P δ₀ ∧
      x ∈ closure (connectedComponentIn ((Metric.ball P ρ \ Metric.closedBall P δ₀) \ F) a) := by
  set O := Metric.ball P ρ \ Metric.closedBall P δ₀ with hOdef
  set Q := connectedComponentIn (O \ F) a with hQdef
  by_contra hno
  push Not at hno
  have hOo : IsOpen O := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hQo : IsOpen Q := (hOo.sdiff hFc).connectedComponentIn
  have haQ : a ∈ Q := mem_connectedComponentIn ⟨ha, haF⟩
  have hQsub : Q ⊆ O \ F := connectedComponentIn_subset _ _
  have hOQ : O ⊆ Q := by
    refine (isPreconnected_ball_sdiff_closedBall hE P hδ₀.le).subset_left_of_subset_union hQo
      isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure)
      (fun y hy => ?_) ⟨a, ha, haQ⟩
    by_cases hycl : y ∈ closure Q
    · refine Or.inl ?_
      have hyF : y ∉ F := fun hyF => hno y hyF hy hycl
      have hpre : IsPreconnected (insert y Q) :=
        isPreconnected_connectedComponentIn.subset_closure (subset_insert _ _)
          (insert_subset_iff.mpr ⟨hycl, subset_closure⟩)
      have hsub : insert y Q ⊆ O \ F := insert_subset_iff.mpr ⟨⟨hy, hyF⟩, hQsub⟩
      exact hpre.subset_connectedComponentIn (mem_insert_of_mem _ haQ) hsub (mem_insert y Q)
    · exact Or.inr hycl
  obtain ⟨z, hzF, hzρ⟩ := hout
  have hcont : ContinuousOn (fun x : E => dist x P) F :=
    (continuous_id.dist continuous_const).continuousOn
  have hivt := hF.intermediate_value hP hzF hcont
  have hmid : (δ₀ + ρ) / 2 ∈ Icc ((fun x : E => dist x P) P) ((fun x : E => dist x P) z) := by
    simp only [dist_self]
    constructor <;> linarith
  obtain ⟨x, hxF, hx⟩ := hivt hmid
  simp only at hx
  have hxO : x ∈ O := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball]
      linarith
    · rw [Metric.mem_closedBall, not_le]
      linarith
  exact (hQsub (hOQ hxO)).2 hxF

end DifferentialGeometry.Topology.PiecewiseLinear
