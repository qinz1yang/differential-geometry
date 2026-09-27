/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem mem_of_mem_closure_of_forall_subset_or_subset {X : Type*} [TopologicalSpace X]
    {A B S : Set X} (hA : IsConnected A) (hAB : Disjoint A B) (hAS : A ⊆ S)
    (hclause : ∀ V : Set X, IsPreconnected V → V ⊆ S → V ⊆ A ∨ V ⊆ B) {x : X}
    (hx : x ∈ closure A) (hxS : x ∈ S) : x ∈ A := by
  have hpre : IsPreconnected (insert x A) :=
    hA.isPreconnected.subset_closure (subset_insert x A) (insert_subset hx subset_closure)
  rcases hclause _ hpre (insert_subset hxS hAS) with h | h
  · exact h (mem_insert x A)
  · obtain ⟨a, ha⟩ := hA.nonempty
    exact absurd (h (mem_insert_of_mem x ha)) (Set.disjoint_left.mp hAB ha)

theorem exists_mem_nhds_forall_mem_iff_of_forall_subset_or_subset {X : Type*}
    [TopologicalSpace X] {A B S : Set X} (hA : IsConnected A) (hB : IsConnected B)
    (hAB : Disjoint A B) (hS : A ∪ B = S)
    (hclause : ∀ V : Set X, IsPreconnected V → V ⊆ S → V ⊆ A ∨ V ⊆ B) {x : X} (hx : x ∈ S) :
    ∃ O ∈ 𝓝 x, ∀ y ∈ O, y ∈ S → (y ∈ A ↔ x ∈ A) := by
  have hAS : A ⊆ S := subset_union_left.trans hS.subset
  have hBS : B ⊆ S := subset_union_right.trans hS.subset
  have hclause' : ∀ V : Set X, IsPreconnected V → V ⊆ S → V ⊆ B ∨ V ⊆ A :=
    fun V hV hVS => (hclause V hV hVS).symm
  rw [← hS] at hx
  rcases hx with hxA | hxB
  · refine ⟨(closure B)ᶜ, isClosed_closure.isOpen_compl.mem_nhds fun hxB => ?_,
      fun y hy hyS => ?_⟩
    · exact Set.disjoint_left.mp hAB hxA
        (mem_of_mem_closure_of_forall_subset_or_subset hB hAB.symm hBS hclause' hxB (hAS hxA))
    · rw [← hS] at hyS
      exact ⟨fun _ => hxA, fun _ => hyS.resolve_right fun hyB => hy (subset_closure hyB)⟩
  · refine ⟨(closure A)ᶜ, isClosed_closure.isOpen_compl.mem_nhds fun hxA => ?_,
      fun y hy _ => ?_⟩
    · exact Set.disjoint_left.mp hAB
        (mem_of_mem_closure_of_forall_subset_or_subset hA hAB hAS hclause hxA (hBS hxB)) hxB
    · exact ⟨fun hyA => absurd (subset_closure hyA) hy,
        fun hxA => absurd hxA (Set.disjoint_right.mp hAB hxB)⟩

theorem exists_mem_nhds_forall_mem_of_mem {X ι : Type*} [TopologicalSpace X] {I : Set ι}
    (hI : I.Finite) {P : ι → Set X} (hP : ∀ i ∈ I, IsClosed (P i)) (x : X) :
    ∃ O ∈ 𝓝 x, ∀ y ∈ O, ∀ i ∈ I, y ∈ P i → x ∈ P i := by
  refine ⟨(⋃ i ∈ {i | i ∈ I ∧ x ∉ P i}, P i)ᶜ, ((hI.subset fun _ hi => hi.1).isClosed_biUnion
    fun i hi => hP i hi.1).isOpen_compl.mem_nhds ?_, ?_⟩
  · intro hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hi.2 hxi
  · intro y hy i hi hyi
    by_contra hxi
    exact hy (mem_iUnion₂.mpr ⟨i, ⟨hi, hxi⟩, hyi⟩)

theorem eq_or_eq_of_mem_of_card_eq_two {α : Type*} {e : Finset α} (he : e.card = 2) {a b c : α}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) (hc : c ∈ e) : c = a ∨ c = b := by
  classical
  by_contra hne
  rw [not_or] at hne
  have hsub : insert c (insert a {b}) ⊆ e := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hc
    · exact ha
    · exact hb
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hne.1, hne.2]), Finset.card_pair hab, he] at hcard
  omega

section Helpers

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3}

theorem IsTube.inter_eq_of_mem_faces (ht : IsTube K N C D Dbd h N') {a b : E3}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b) {f : Finset E3}
    (hf : f ∈ K.faces) (haf : a ∈ f) (hbf : b ∈ f) : C a ∩ C b = D f := by
  have hpair : ({a, b} : Finset E3) = f := by
    refine Finset.eq_of_subset_of_card_le
      (Finset.insert_subset haf (Finset.singleton_subset_iff.mpr hbf)) ?_
    rw [Finset.card_pair hab]
    exact ht.oneDimensional f hf
  rw [← hpair]
  exact ht.interEdge ha hb hab (by rw [hpair]; exact hf)

theorem IsTube.inter_eq_empty_of_forall_notMem_faces (ht : IsTube K N C D Dbd h N') {a b : E3}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) (hab : a ≠ b)
    (hno : ∀ f ∈ K.faces, a ∈ f → b ∉ f) : C a ∩ C b = ∅ :=
  ht.interNonEdge ha hb hab fun hmem =>
    hno _ hmem (Finset.mem_insert_self a {b})
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))

end Helpers

section Leaves

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}

open Classical in
theorem handlePiece_subset_of_edgeCollars (ht : IsTube K N C D Dbd h N')
    {V : E3 → Set E3} {W : Finset E3 → Set E3} (hW : IsEdgeCollarFamily K C D Dbd h V W)
    {Ec Eint Ebd : Finset E3 → Set E3}
    (hE : ∀ e ∈ K.faces, e.card = 2 → ∃ u v : E3, u ∈ K.vertices ∧ v ∈ K.vertices ∧ u ≠ v ∧
      e = {u, v} ∧ SplitsDualCellsAlong K N C Dbd h (W e) (Ec e) (Eint e) (Ebd e) u v) :
    ∀ v ∈ K.vertices, handlePiece K N' Ec h v ⊆
      h '' C v ∪ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}, W e := by
  intro v hv
  have hinj : InjOn h N := by
    intro x hx y hy hxy
    have hxy' : N.domRestrict h ⟨x, hx⟩ = N.domRestrict h ⟨y, hy⟩ := hxy
    exact congrArg Subtype.val (ht.isEmbedding.injective hxy')
  have hcont : ContinuousOn h N :=
    continuousOn_iff_continuous_domRestrict.mpr ht.isEmbedding.continuous
  have hCN : ∀ a ∈ K.vertices, C a ⊆ N := by
    intro a ha
    rw [ht.unionEq]
    exact subset_biUnion_of_mem (u := C) ha
  have hspaceN : K.space ⊆ N := subset_of_mem_nhdsSet ht.isNeighborhood
  have hclosedP : ∀ a ∈ K.vertices, IsClosed (h '' C a) := fun a ha =>
    ((ht.dualBall a ha).isPolyhedron.isCompact.image_of_continuousOn
      (hcont.mono (hCN a ha))).isClosed
  have hmemC : ∀ a ∈ K.vertices, a ∈ C a := by
    intro a ha
    have hmem : a ∈ C a ∩ K.vertices := by
      rw [ht.dualVertex ha]
      exact mem_singleton a
    exact hmem.1
  have hVfin : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn ht.facesFinite
  have hcentroid : ∀ f ∈ K.faces, f.card = 2 → ∀ a ∈ K.vertices, a ≠ f.centroid ℝ id := by
    intro f hf hfc a ha hac
    have hx : f.centroid ℝ id ∈ convexHull ℝ (({a} : Finset E3) : Set E3) := by
      rw [← hac]
      exact subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self a))
    have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K hf ha
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces hf)) hx
    have hle := Finset.card_le_card hsub
    rw [hfc, Finset.card_singleton] at hle
    omega
  have hvertW : ∀ f ∈ K.faces, f.card = 2 → ∀ a ∈ K.vertices, h a ∉ W f := by
    intro f hf hfc a ha haW
    have hmem : h a ∈ W f ∩ h '' K.space :=
      ⟨haW, a, Geometry.SimplicialComplex.vertices_subset_space ha, rfl⟩
    rw [(hW f hf hfc).2.2.1] at hmem
    have hc : f.centroid ℝ id ∈ K.space :=
      K.convexHull_subset_space hf (f.centroid_mem_convexHull (K.nonempty_of_mem_faces hf))
    exact hcentroid f hf hfc a ha
      (hinj (hspaceN (Geometry.SimplicialComplex.vertices_subset_space ha)) (hspaceN hc) hmem)
  have hDW : ∀ f ∈ K.faces, f.card = 2 → h '' D f ⊆ W f := by
    intro f hf hfc
    obtain ⟨-, hint, hK, hpair, -, -⟩ := hW f hf hfc
    obtain ⟨a, b, hab, hfab⟩ := Finset.card_eq_two.mp hfc
    have hbd : h '' Dbd f ⊆ W f := by
      have hfr := (hpair a (by rw [hfab]; simp) b (by rw [hfab]; simp) hab).2
      rw [← hfr]
      exact inter_subset_left
    have hc : h (f.centroid ℝ id) ∈ W f := by
      have hcm : h (f.centroid ℝ id) ∈ W f ∩ h '' K.space := by
        rw [hK]
        exact mem_singleton _
      exact hcm.1
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxb : x ∈ Dbd f
    · exact hbd ⟨x, hxb, rfl⟩
    · by_cases hxc : h x = h (f.centroid ℝ id)
      · rw [hxc]
        exact hc
      · exact interior_subset (hint ⟨⟨x, ⟨hx, hxb⟩, rfl⟩, hxc⟩)
  have hEcW : ∀ f ∈ K.faces, f.card = 2 → Ec f ⊆ W f := by
    intro f hf hfc
    obtain ⟨_, _, -, -, -, -, hS⟩ := hE f hf hfc
    exact hS.2.2.1
  have hWeq : ∀ e ∈ K.faces, e.card = 2 → ∀ f ∈ K.faces, f.card = 2 → ∀ x, x ∈ W e →
      x ∈ W f → e = f := by
    intro e he hec f hf hfc x hxe hxf
    by_contra hne
    exact Set.disjoint_left.mp ((hW e he hec).2.2.2.2.2 f hf hfc hne) hxe hxf
  have hPP : ∀ a ∈ K.vertices, ∀ b ∈ K.vertices, a ≠ b → ∀ x, x ∈ h '' C a → x ∈ h '' C b →
      ∃ f ∈ K.faces, f.card = 2 ∧ a ∈ f ∧ b ∈ f ∧ x ∈ W f := by
    intro a ha b hb hab x hxa hxb
    have hx : x ∈ h '' (C a ∩ C b) := by
      rw [hinj.image_inter (hCN a ha) (hCN b hb)]
      exact ⟨hxa, hxb⟩
    by_cases hadj : ∃ f ∈ K.faces, a ∈ f ∧ b ∈ f
    · obtain ⟨f, hf, haf, hbf⟩ := hadj
      have hfc : f.card = 2 := le_antisymm (ht.oneDimensional f hf) (by
        have hle := Finset.card_le_card
          (Finset.insert_subset haf (Finset.singleton_subset_iff.mpr hbf))
        rwa [Finset.card_pair hab] at hle)
      rw [ht.inter_eq_of_mem_faces ha hb hab hf haf hbf] at hx
      exact ⟨f, hf, hfc, haf, hbf, hDW f hf hfc hx⟩
    · rw [ht.inter_eq_empty_of_forall_notMem_faces ha hb hab
        fun f hf haf hbf => hadj ⟨f, hf, haf, hbf⟩, image_empty] at hx
      exact hx.elim
  have hpiece : ∀ y ∈ N', ∃ z ∈ K.vertices, y ∈ h '' C z := by
    intro y hy
    rw [ht.imageEq] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    rw [ht.unionEq] at hp
    obtain ⟨z, hz, hpz⟩ := mem_iUnion₂.mp hp
    exact ⟨z, hz, p, hpz, rfl⟩
  have hside : ∀ e : Finset E3, ∃ w : E3, ∃ A B : Set E3, e ∈ K.faces → e.card = 2 → v ∈ e →
      w ∈ K.vertices ∧ w ∈ e ∧ w ≠ v ∧ h v ∈ A ∧ h w ∈ B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = (h '' C v ∪ h '' C w) \ Ec e ∧
      (∀ V' : Set E3, IsPreconnected V' → V' ⊆ (h '' C v ∪ h '' C w) \ Ec e →
        V' ⊆ A ∨ V' ⊆ B) ∧ Ec e ⊆ W e := by
    intro e
    by_cases he : e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e
    · obtain ⟨he₁, he₂, hve⟩ := he
      obtain ⟨a, b, ha, hb, hab, heq, hS⟩ := hE e he₁ he₂
      obtain ⟨-, -, hEcWe, -, -, U₁, U₂, hU₁, hU₂, hc₁, hc₂, hdisj, hunion, hpre, -⟩ := hS
      have hva : v = a ∨ v = b := by
        rw [heq] at hve
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hve
      rcases hva with rfl | rfl
      · exact ⟨b, U₁, U₂, fun _ _ _ => ⟨hb, by rw [heq]; simp, fun h' => hab h'.symm, hU₁, hU₂,
          hc₁, hc₂, hdisj, hunion, hpre, hEcWe⟩⟩
      · refine ⟨a, U₂, U₁, fun _ _ _ => ⟨ha, by rw [heq]; simp, hab, hU₂, hU₁, hc₂, hc₁,
          hdisj.symm, ?_, ?_, hEcWe⟩⟩
        · rw [union_comm U₂ U₁, hunion, union_comm (h '' C a) (h '' C v)]
        · intro V' hV' hV'S
          rw [union_comm (h '' C v) (h '' C a)] at hV'S
          exact (hpre V' hV' hV'S).symm
    · exact ⟨v, ∅, ∅, fun he₁ he₂ hve => absurd ⟨he₁, he₂, hve⟩ he⟩
  choose w A B hAB using hside
  have hvA : ∀ e ∈ K.faces, e.card = 2 → v ∈ e → h '' C v \ W e ⊆ A e := by
    intro e he₁ he₂ hve
    obtain ⟨-, -, -, hvA, -, -, -, hdisj, -, hpre, hEcWe⟩ := hAB e he₁ he₂ hve
    have hconn := ((hW e he₁ he₂).2.2.2.2.1 v hve).1
    have hsub : h '' C v \ W e ⊆ (h '' C v ∪ h '' C (w e)) \ Ec e :=
      fun x hx => ⟨Or.inl hx.1, fun hxE => hx.2 (hEcWe hxE)⟩
    rcases hpre _ hconn.isPreconnected hsub with h1 | h1
    · exact h1
    · have hvmem : h v ∈ h '' C v \ W e := ⟨⟨v, hmemC v hv, rfl⟩, hvertW e he₁ he₂ v hv⟩
      exact absurd (h1 hvmem) (Set.disjoint_left.mp hdisj hvA)
  have hBw : ∀ e ∈ K.faces, e.card = 2 → v ∈ e → h '' C (w e) \ W e ⊆ B e := by
    intro e he₁ he₂ hve
    obtain ⟨hw, hwe, -, -, hwB, -, -, hdisj, -, hpre, hEcWe⟩ := hAB e he₁ he₂ hve
    have hconn := ((hW e he₁ he₂).2.2.2.2.1 (w e) hwe).1
    have hsub : h '' C (w e) \ W e ⊆ (h '' C v ∪ h '' C (w e)) \ Ec e :=
      fun x hx => ⟨Or.inr hx.1, fun hxE => hx.2 (hEcWe hxE)⟩
    rcases hpre _ hconn.isPreconnected hsub with h1 | h1
    · have hwmem : h (w e) ∈ h '' C (w e) \ W e :=
        ⟨⟨w e, hmemC _ hw, rfl⟩, hvertW e he₁ he₂ _ hw⟩
      exact absurd hwB (Set.disjoint_left.mp hdisj (h1 hwmem))
    · exact h1
  have hAW : ∀ e ∈ K.faces, e.card = 2 → v ∈ e → A e ∩ h '' C (w e) ⊆ W e := by
    intro e he₁ he₂ hve x hx
    by_contra hxW
    obtain ⟨-, -, -, -, -, -, -, hdisj, -⟩ := hAB e he₁ he₂ hve
    exact Set.disjoint_left.mp hdisj hx.1 (hBw e he₁ he₂ hve ⟨hx.2, hxW⟩)
  obtain ⟨X, hX⟩ : ∃ X : Set E3,
      X = N' \ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := ⟨_, rfl⟩
  have hXmem : ∀ z, z ∈ X ↔ z ∈ N' ∧ ∀ f ∈ K.faces, f.card = 2 → z ∉ Ec f := by
    intro z
    rw [hX]
    constructor
    · rintro ⟨hzN, hzE⟩
      exact ⟨hzN, fun f hf hfc hzf => hzE (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc⟩, hzf⟩)⟩
    · rintro ⟨hzN, hzE⟩
      refine ⟨hzN, fun hz => ?_⟩
      obtain ⟨f, ⟨hf, hfc⟩, hzf⟩ := mem_iUnion₂.mp hz
      exact hzE f hf hfc hzf
  obtain ⟨R, hR⟩ : ∃ R : Set E3, R = {x | x ∈ X ∧
      (x ∈ h '' C v ∨ ∃ e ∈ K.faces, e.card = 2 ∧ v ∈ e ∧ x ∈ h '' C (w e)) ∧
      ∀ e ∈ K.faces, e.card = 2 → v ∈ e → x ∈ (h '' C v ∪ h '' C (w e)) \ Ec e → x ∈ A e} :=
    ⟨_, rfl⟩
  have hRmem : ∀ z, z ∈ R ↔ z ∈ X ∧
      (z ∈ h '' C v ∨ ∃ e ∈ K.faces, e.card = 2 ∧ v ∈ e ∧ z ∈ h '' C (w e)) ∧
      ∀ e ∈ K.faces, e.card = 2 → v ∈ e → z ∈ (h '' C v ∪ h '' C (w e)) \ Ec e → z ∈ A e := by
    intro z
    rw [hR]
    exact Iff.rfl
  have hvX : h v ∈ X := (hXmem (h v)).mpr
    ⟨by rw [ht.imageEq]; exact ⟨v, hCN v hv (hmemC v hv), rfl⟩,
      fun f hf hfc hvf => hvertW f hf hfc v hv (hEcW f hf hfc hvf)⟩
  have hvR : h v ∈ R := (hRmem _).mpr ⟨hvX, Or.inl ⟨v, hmemC v hv, rfl⟩,
    fun e he₁ he₂ hve _ => (hAB e he₁ he₂ hve).2.2.2.1⟩
  have hEdfin : {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}.Finite :=
    ht.facesFinite.subset fun _ he => he.1
  have hTcl : IsClosed (h '' C v ∪ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e},
      W e) :=
    (hclosedP v hv).union (hEdfin.isClosed_biUnion fun e he => (hW e he.1 he.2.1).1)
  have hRT : R ⊆ h '' C v ∪ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}, W e := by
    intro x hx
    obtain ⟨hxX, hx1, hx2⟩ := (hRmem x).mp hx
    rcases hx1 with hxv | ⟨e, he₁, he₂, hve, hxw⟩
    · exact Or.inl hxv
    · refine Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he₁, he₂, hve⟩, ?_⟩)
      exact hAW e he₁ he₂ hve
        ⟨hx2 e he₁ he₂ hve ⟨Or.inr hxw, ((hXmem x).mp hxX).2 e he₁ he₂⟩, hxw⟩
  have hcore : ∀ x y, x ∈ X → y ∈ X → (∀ a ∈ K.vertices, y ∈ h '' C a → x ∈ h '' C a) →
      (∀ e ∈ K.faces, e.card = 2 → v ∈ e → y ∈ (h '' C v ∪ h '' C (w e)) \ Ec e →
        x ∈ (h '' C v ∪ h '' C (w e)) \ Ec e ∧ (y ∈ A e ↔ x ∈ A e)) →
      (y ∈ R ↔ x ∈ R) := by
    intro x y hxX hyX hpc hsd
    have hxN := (hXmem x).mp hxX
    have hyN := (hXmem y).mp hyX
    rw [hRmem, hRmem]
    constructor
    · rintro ⟨-, hy1, hy2⟩
      refine ⟨hxX, ?_, ?_⟩
      · rcases hy1 with hyv | ⟨e, he₁, he₂, hve, hyw⟩
        · exact Or.inl (hpc v hv hyv)
        · exact Or.inr ⟨e, he₁, he₂, hve, hpc _ (hAB e he₁ he₂ hve).1 hyw⟩
      · intro e he₁ he₂ hve hxS
        obtain ⟨hw, hwe, hwv, -, -, -, -, -, hunion, -, -⟩ := hAB e he₁ he₂ hve
        by_contra hxA
        by_cases hyP : y ∈ h '' C v ∪ h '' C (w e)
        · have hyS : y ∈ (h '' C v ∪ h '' C (w e)) \ Ec e := ⟨hyP, hyN.2 e he₁ he₂⟩
          exact hxA ((hsd e he₁ he₂ hve hyS).2.mp (hy2 e he₁ he₂ hve hyS))
        · rcases hy1 with hyv | ⟨e', he'₁, he'₂, hve', hyw'⟩
          · exact hyP (Or.inl hyv)
          · obtain ⟨hw', hwe', hwv', -⟩ := hAB e' he'₁ he'₂ hve'
            have hww : w e' ≠ w e := fun heq => hyP (Or.inr (heq ▸ hyw'))
            have hxw' : x ∈ h '' C (w e') := hpc _ hw' hyw'
            rcases hxS.1 with hxv | hxw
            · obtain ⟨f, hf₁, hf₂, -, hw'f, hxf⟩ := hPP v hv (w e') hw' hwv'.symm x hxv hxw'
              have hxWe : x ∉ W e := by
                intro hxWe
                have hfe : f = e := hWeq f hf₁ hf₂ e he₁ he₂ x hxf hxWe
                rw [hfe] at hw'f
                rcases eq_or_eq_of_mem_of_card_eq_two he₂ hve hwe hwv.symm hw'f with h1 | h1
                · exact hwv' h1
                · exact hww h1
              exact hxA (hvA e he₁ he₂ hve ⟨hxv, hxWe⟩)
            · obtain ⟨f, hf₁, hf₂, hwf, -, hxf⟩ := hPP (w e) hw (w e') hw' hww.symm x hxw hxw'
              have hyS' : y ∈ (h '' C v ∪ h '' C (w e')) \ Ec e' :=
                ⟨Or.inr hyw', hyN.2 e' he'₁ he'₂⟩
              have hxA' : x ∈ A e' :=
                (hsd e' he'₁ he'₂ hve' hyS').2.mp (hy2 e' he'₁ he'₂ hve' hyS')
              have hxWe' : x ∈ W e' := hAW e' he'₁ he'₂ hve' ⟨hxA', hxw'⟩
              have hfe : f = e' := hWeq f hf₁ hf₂ e' he'₁ he'₂ x hxf hxWe'
              rw [hfe] at hwf
              rcases eq_or_eq_of_mem_of_card_eq_two he'₂ hve' hwe' hwv'.symm hwf with h1 | h1
              · exact hwv h1
              · exact hww h1.symm
    · rintro ⟨-, hx1, hx2⟩
      refine ⟨hyX, ?_, fun e he₁ he₂ hve hyS => ?_⟩
      · obtain ⟨z, hz, hyz⟩ := hpiece y hyN.1
        have hxz := hpc z hz hyz
        by_cases hzv : z = v
        · exact Or.inl (hzv ▸ hyz)
        · by_cases hzw : ∃ e ∈ K.faces, e.card = 2 ∧ v ∈ e ∧ w e = z
          · obtain ⟨e, he₁, he₂, hve, hwz⟩ := hzw
            exact Or.inr ⟨e, he₁, he₂, hve, hwz ▸ hyz⟩
          · exfalso
            rcases hx1 with hxv | ⟨e₀, he₀₁, he₀₂, hve₀, hxw₀⟩
            · obtain ⟨f, hf₁, hf₂, hvf, hzf, -⟩ := hPP v hv z hz (Ne.symm hzv) x hxv hxz
              obtain ⟨-, hwf, hwv, -⟩ := hAB f hf₁ hf₂ hvf
              rcases eq_or_eq_of_mem_of_card_eq_two hf₂ hvf hwf hwv.symm hzf with h1 | h1
              · exact hzv h1
              · exact hzw ⟨f, hf₁, hf₂, hvf, h1.symm⟩
            · obtain ⟨hw₀, hwe₀, hwv₀, -⟩ := hAB e₀ he₀₁ he₀₂ hve₀
              have hzw₀ : w e₀ ≠ z := fun heq => hzw ⟨e₀, he₀₁, he₀₂, hve₀, heq⟩
              obtain ⟨f, hf₁, hf₂, -, hzf, hxf⟩ := hPP (w e₀) hw₀ z hz hzw₀ x hxw₀ hxz
              have hxS₀ : x ∈ (h '' C v ∪ h '' C (w e₀)) \ Ec e₀ :=
                ⟨Or.inr hxw₀, hxN.2 e₀ he₀₁ he₀₂⟩
              have hxW₀ : x ∈ W e₀ :=
                hAW e₀ he₀₁ he₀₂ hve₀ ⟨hx2 e₀ he₀₁ he₀₂ hve₀ hxS₀, hxw₀⟩
              have hfe : f = e₀ := hWeq f hf₁ hf₂ e₀ he₀₁ he₀₂ x hxf hxW₀
              rw [hfe] at hzf
              rcases eq_or_eq_of_mem_of_card_eq_two he₀₂ hve₀ hwe₀ hwv₀.symm hzf with h1 | h1
              · exact hzv h1
              · exact hzw₀ h1.symm
      · obtain ⟨hxS, hiff⟩ := hsd e he₁ he₂ hve hyS
        exact hiff.mpr (hx2 e he₁ he₂ hve hxS)
  have hloc : ∀ x ∈ X, ∃ O ∈ 𝓝 x, ∀ y ∈ O, y ∈ X → (y ∈ R ↔ x ∈ R) := by
    intro x hxX
    obtain ⟨O₀, hO₀, hO₀p⟩ := exists_mem_nhds_forall_mem_of_mem hVfin hclosedP x
    have hOe : ∀ e : Finset E3, ∃ O ∈ 𝓝 x, e ∈ K.faces → e.card = 2 → v ∈ e → ∀ y ∈ O,
        y ∈ (h '' C v ∪ h '' C (w e)) \ Ec e →
          x ∈ (h '' C v ∪ h '' C (w e)) \ Ec e ∧ (y ∈ A e ↔ x ∈ A e) := by
      intro e
      by_cases he : e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e
      · obtain ⟨he₁, he₂, hve⟩ := he
        obtain ⟨hw, -, -, -, -, hAc, hBc, hdisj, hunion, hpre, -⟩ := hAB e he₁ he₂ hve
        by_cases hxS : x ∈ (h '' C v ∪ h '' C (w e)) \ Ec e
        · obtain ⟨O, hO, hOS⟩ := exists_mem_nhds_forall_mem_iff_of_forall_subset_or_subset
            hAc hBc hdisj hunion hpre hxS
          exact ⟨O, hO, fun _ _ _ y hy hyS => ⟨hxS, hOS y hy hyS⟩⟩
        · have hxP : x ∉ h '' C v ∪ h '' C (w e) :=
            fun hxP => hxS ⟨hxP, ((hXmem x).mp hxX).2 e he₁ he₂⟩
          exact ⟨(h '' C v ∪ h '' C (w e))ᶜ,
            ((hclosedP v hv).union (hclosedP _ hw)).isOpen_compl.mem_nhds hxP,
            fun _ _ _ y hy hyS => absurd hyS.1 hy⟩
      · exact ⟨univ, Filter.univ_mem, fun he₁ he₂ hve => absurd ⟨he₁, he₂, hve⟩ he⟩
    choose Oe hOe hOeS using hOe
    refine ⟨O₀ ∩ ⋂ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2 ∧ v ∈ e}, Oe e,
      Filter.inter_mem hO₀ ((Filter.biInter_mem hEdfin).mpr fun e _ => hOe e), ?_⟩
    rintro y ⟨hyO₀, hyO⟩ hyX
    exact hcore x y hxX hyX (fun a ha hya => hO₀p y hyO₀ a ha hya)
      (fun e he₁ he₂ hve hyS =>
        hOeS e he₁ he₂ hve y (mem_iInter₂.mp hyO e ⟨he₁, he₂, hve⟩) hyS)
  have hcomp : connectedComponentIn X (h v) ⊆ R := by
    intro y hy
    have hcont' : ContinuousOn (fun z => decide (z ∈ R)) (connectedComponentIn X (h v)) := by
      intro z hz
      obtain ⟨O, hO, hOR⟩ := hloc z (connectedComponentIn_subset X (h v) hz)
      rw [ContinuousWithinAt, nhds_discrete Bool, Filter.tendsto_pure]
      filter_upwards [mem_nhdsWithin_of_mem_nhds hO, self_mem_nhdsWithin] with y' hy'O hy'C
      exact decide_eq_decide.mpr (hOR y' hy'O (connectedComponentIn_subset X (h v) hy'C))
    have hconst := isPreconnected_connectedComponentIn.constant hcont'
      (mem_connectedComponentIn hvX) hy
    exact (decide_eq_decide.mp hconst).mp hvR
  have hhp : handlePiece K N' Ec h v = closure (connectedComponentIn X (h v)) := by
    rw [hX]
    rfl
  rw [hhp]
  exact closure_minimal (hcomp.trans hRT) hTcl

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
