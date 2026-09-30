/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ChartPush
import DifferentialGeometry.Topology.PiecewiseLinear.HandlePieceChart
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellFlatChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section PushOff

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsHandleDecompositionOfTube.exists_side_of_chart
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) {v : E3} (hve : v ∈ e) {U : Set E3}
    {V : Set (ℝ × ℝ × ℝ)} {φ : E3 → ℝ × ℝ × ℝ} (hφ : IsPLHomeomorphOn φ U V) (hU : IsOpen U)
    {x : E3} (hx : x ∈ U) (hxE : x ∈ Ec e) {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall (φ x) r ⊆ V)
    (hUN : U ⊆ N') (hUE : ∀ y ∈ U, (y ∈ Ec e ↔ (φ y).2.2 = (φ x).2.2))
    (hUo : ∀ y ∈ U, ∀ f ∈ K.faces, f.card = 2 → f ≠ e → y ∉ Ec f) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ y ∈ U, φ y ∈ Metric.ball (φ x) r →
      (y ∈ Cpp v ↔ 0 ≤ s * ((φ y).2.2 - (φ x).2.2)) := by
  classical
  obtain ⟨u, hue, huv⟩ := Finset.exists_mem_ne (by omega : 1 < e.card) v
  have hv : v ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hve) (Finset.singleton_nonempty v)
  have hu : u ∈ K.vertices :=
    K.down_closed he (Finset.singleton_subset_iff.mpr hue) (Finset.singleton_nonempty u)
  have hCvu : Cpp v ∩ Cpp u = Ec e := hd.handlePiece_inter_eq_pseudoCell he hcard hve hue huv.symm
  set O₀ := N' \ ⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}, Ec f with hO₀def
  have hO₀E : ∀ z ∈ O₀, z ∉ Ec e := fun z hz hze => hz.2 (mem_iUnion₂.mpr ⟨e, ⟨he, hcard⟩, hze⟩)
  have hsat : ∀ w : E3, ∀ Z : Set E3, IsPreconnected Z → Z ⊆ O₀ →
      (Z ∩ connectedComponentIn O₀ (h w)).Nonempty → Z ⊆ connectedComponentIn O₀ (h w) := by
    rintro w Z hZ hZO ⟨z, hzZ, hzV⟩
    rw [connectedComponentIn_eq hzV]
    exact hZ.subset_connectedComponentIn hzZ hZO
  have hVC : ∀ w ∈ K.vertices, connectedComponentIn O₀ (h w) ⊆ Cpp w := fun w hw => by
    rw [hd.componentClosure w hw]
    exact subset_closure
  have hVdisj : Disjoint (connectedComponentIn O₀ (h v)) (connectedComponentIn O₀ (h u)) := by
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    have hz : z ∈ Cpp v ∩ Cpp u := ⟨hVC v hv hz₁, hVC u hu hz₂⟩
    rw [hCvu] at hz
    exact hO₀E z (connectedComponentIn_subset _ _ hz₁) hz
  set g := Function.invFunOn φ U with hgdef
  have hg : IsPLHomeomorphOn g V U := hφ.symm
  have hgφ : ∀ y ∈ U, g (φ y) = y := fun y hy => hφ.bijOn.invOn_invFunOn.1 hy
  have hφg : ∀ w ∈ V, φ (g w) = w := fun w hw => hφ.bijOn.invOn_invFunOn.2 hw
  have hgU : ∀ w ∈ V, g w ∈ U := fun w hw => hg.bijOn.mapsTo hw
  set c₀ := (φ x).2.2 with hc₀def
  set B := Metric.ball (φ x) r with hBdef
  have hBV : B ⊆ V := Metric.ball_subset_closedBall.trans hball
  have hhalf : ∀ t : ℝ, t ≠ 0 → IsPreconnected (g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)})) ∧
      g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) ⊆ O₀ := by
    intro t ht
    have hlin : IsLinearMap ℝ fun w : ℝ × ℝ × ℝ => t * w.2.2 :=
      ⟨fun a b => by simp [mul_add], fun c a => by simp; ring⟩
    have hconv : Convex ℝ (B ∩ {w : ℝ × ℝ × ℝ | 0 < t * (w.2.2 - c₀)}) := by
      refine (convex_ball _ _).inter ?_
      have heq : {w : ℝ × ℝ × ℝ | 0 < t * (w.2.2 - c₀)} = {w | t * c₀ < t * w.2.2} := by
        ext w
        simp only [mem_ofPred_eq]
        constructor <;> intro hw <;> nlinarith
      rw [heq]
      exact convex_halfSpace_gt hlin _
    refine ⟨hconv.isPreconnected.image g
      (hg.isPiecewiseAffineOn.continuousOn.mono (inter_subset_left.trans hBV)), ?_⟩
    rintro _ ⟨w, ⟨hwB, hw⟩, rfl⟩
    have hwV := hBV hwB
    refine ⟨hUN (hgU w hwV), fun hwE => ?_⟩
    obtain ⟨f, ⟨hf, hfc⟩, hwf⟩ := mem_iUnion₂.mp hwE
    by_cases hfe : f = e
    · rw [hfe] at hwf
      have h1 := (hUE _ (hgU w hwV)).mp hwf
      rw [hφg w hwV] at h1
      simp only [mem_ofPred_eq, h1, sub_self, mul_zero, lt_self_iff_false] at hw
    · exact hUo _ (hgU w hwV) f hf hfc hfe hwf
  have hBg : U ∩ φ ⁻¹' B ∈ 𝓝 x := Filter.inter_mem (hU.mem_nhds hx)
    ((hφ.isPiecewiseAffineOn.continuousAt hU hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  have hhalfmem : ∀ z ∈ U, φ z ∈ B → ∀ t : ℝ, 0 < t * ((φ z).2.2 - c₀) →
      z ∈ g '' (B ∩ {w | 0 < t * (w.2.2 - c₀)}) := fun z hz hzB t ht =>
    ⟨φ z, ⟨hzB, ht⟩, hgφ z hz⟩
  have hnear : ∀ w ∈ K.vertices, w ∈ e → ∃ z, z ∈ connectedComponentIn O₀ (h w) ∧ z ∈ U ∧
      φ z ∈ B ∧ (φ z).2.2 ≠ c₀ := by
    intro w hw hwe
    have hxw : x ∈ closure (connectedComponentIn O₀ (h w)) := by
      rw [← hd.componentClosure w hw]
      exact hd.pseudoCell_subset_handlePiece he hcard hwe hxE
    obtain ⟨z, ⟨hzU, hzB⟩, hzV⟩ := mem_closure_iff_nhds.mp hxw _ hBg
    refine ⟨z, hzV, hzU, hzB, fun hz0 => ?_⟩
    exact hO₀E z (connectedComponentIn_subset _ _ hzV) ((hUE z hzU).mpr hz0)
  obtain ⟨y, hyV, hyU, hyB, hy0⟩ := hnear v hv hve
  obtain ⟨y', hy'V, hy'U, hy'B, hy'0⟩ := hnear u hu hue
  have hsign : ∀ a : ℝ, a ≠ 0 → ∃ t : ℝ, (t = 1 ∨ t = -1) ∧ 0 < t * a := by
    intro a ha
    rcases lt_or_gt_of_ne ha with hlt | hgt
    · exact ⟨-1, Or.inr rfl, by linarith⟩
    · exact ⟨1, Or.inl rfl, by linarith⟩
  obtain ⟨t, ht, hty⟩ := hsign _ (sub_ne_zero.mpr hy0)
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have hHv := hsat v _ (hhalf t ht0).1 (hhalf t ht0).2 ⟨y, hhalfmem y hyU hyB t hty, hyV⟩
  have hy't : ¬ 0 < t * ((φ y').2.2 - c₀) := fun h' =>
    Set.disjoint_left.mp hVdisj (hHv (hhalfmem y' hy'U hy'B t h')) hy'V
  have hy'neg : 0 < -t * ((φ y').2.2 - c₀) := by
    have hne : t * ((φ y').2.2 - c₀) ≠ 0 := mul_ne_zero ht0 (sub_ne_zero.mpr hy'0)
    have := lt_of_le_of_ne (not_lt.mp hy't) hne
    linarith
  have hnt0 : -t ≠ 0 := neg_ne_zero.mpr ht0
  have hHu := hsat u _ (hhalf (-t) hnt0).1 (hhalf (-t) hnt0).2
    ⟨y', hhalfmem y' hy'U hy'B (-t) hy'neg, hy'V⟩
  refine ⟨t, ht, fun z hz hzB => ⟨fun hzC => ?_, fun hz0 => ?_⟩⟩
  · by_contra hneg
    have hneg' : 0 < -t * ((φ z).2.2 - c₀) := by linarith [not_le.mp hneg]
    have hzV := hHu (hhalfmem z hz hzB (-t) hneg')
    have hzE : z ∈ Cpp v ∩ Cpp u := ⟨hzC, hVC u hu hzV⟩
    rw [hCvu] at hzE
    exact hO₀E z (connectedComponentIn_subset _ _ hzV) hzE
  · rcases hz0.lt_or_eq with hpos | hzero
    · exact hVC v hv (hHv (hhalfmem z hz hzB t hpos))
    · have h0 : (φ z).2.2 = c₀ := by
        have := (mul_eq_zero.mp hzero.symm).resolve_left ht0
        linarith
      exact hd.pseudoCell_subset_handlePiece he hcard hve ((hUE z hz).mpr h0)

theorem IsPolyhedralTubeNeighborhood.exists_localPush
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {v : E3} (hv : v ∈ K.vertices)
    {O : Set E3} (hO : IsOpen O) (hON : O ⊆ interior N') (hOK : Disjoint O (h '' K.space))
    {x : E3} (hxO : x ∈ O) (hxC : x ∈ Cpp v)
    (hxE : x ∈ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :
    ∃ (Ψ : E3 → E3) (W : Set E3), IsPLHomeomorphOn Ψ univ univ ∧ W ∈ 𝓝 x ∧
      (∀ y, y ∉ O → Ψ y = y) ∧ (∀ y, Ψ y ∈ XK.space ↔ y ∈ XK.space) ∧
        ∀ y ∈ Cpp v, Ψ y ∈ Cpp v ∧
          (Ψ y ∈ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e →
            y ∈ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e ∧ y ∉ W ∧ Ψ y = y) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  have ht := hd.tube
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    ht.facesFinite.subset fun f hf => hf.1
  obtain ⟨e, ⟨he, hcard⟩, hxe⟩ := mem_iUnion₂.mp hxE
  have hpc := hd.pseudoCell e he hcard
  have hve : v ∈ e := by
    by_contra hn
    have h0 := hd.handlePiece_inter_pseudoCell_eq_empty hv he hcard hn
    have hmem : x ∈ Cpp v ∩ Ec e := ⟨hxC, hxe⟩
    rw [h0] at hmem
    exact hmem
  have hnotbd : ∀ y ∈ O, y ∉ Ebd e := fun y hy hyb => by
    have hfr : y ∈ Ec e ∩ frontier N' := by
      rw [hd.rimFrontier e he hcard]
      exact hyb
    exact hfr.2.2 (hON hy)
  have hEint : ∀ y ∈ O, (y ∈ Ec e ↔ y ∈ Eint e) := by
    intro y hy
    rw [hpc.carrierEq]
    exact ⟨fun h' => h'.resolve_right (hnotbd y hy), Or.inl⟩
  have hxint : x ∈ Eint e := (hEint x hxO).mp hxe
  have hxP : x ≠ h (e.centroid ℝ id) := by
    intro hxP
    have hmem : h (e.centroid ℝ id) ∈ Ec e ∩ h '' K.space := by
      rw [hd.meetsGraph e he hcard]
      exact mem_singleton _
    exact Set.disjoint_left.mp hOK (hxP ▸ hxO) hmem.2
  set Uo := (⋃ f ∈ {f : Finset E3 | f ∈ K.faces ∧ f.card = 2 ∧ f ≠ e}, Ec f)ᶜ with hUodef
  have hUoo : IsOpen Uo := ((hfin.subset fun f hf => ⟨hf.1, hf.2.1⟩).isClosed_biUnion
    fun f hf => (hd.pseudoCell f hf.1 hf.2.1).isClosed).isOpen_compl
  have hxUo : x ∈ Uo := by
    simp only [hUodef, mem_compl_iff, mem_iUnion, not_exists]
    intro f hf hxf
    exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e he hcard f hf.1 hf.2.1 hf.2.2.symm)
      hxe hxf
  have hUo : ∀ y ∈ Uo, ∀ f ∈ K.faces, f.card = 2 → f ≠ e → y ∉ Ec f := by
    intro y hy f hf hfc hfe hyf
    exact hy (mem_iUnion₂.mpr ⟨f, ⟨hf, hfc, hfe⟩, hyf⟩)
  have hchart : ∃ (U : Set E3) (V : Set (ℝ × ℝ × ℝ)) (φ : E3 → ℝ × ℝ × ℝ), IsOpen U ∧
      IsOpen V ∧ x ∈ U ∧ U ⊆ O ∩ Uo ∧ IsPLHomeomorphOn φ U V ∧
        (∀ y ∈ U, (y ∈ Ec e ↔ (φ y).2.2 = (φ x).2.2)) ∧
        ∀ r : ℝ, Metric.ball (φ x) r ⊆ V → ∀ y ∈ U, ∀ y' ∈ U, φ y ∈ Metric.ball (φ x) r →
          φ y' ∈ Metric.ball (φ x) r → (φ y).1 = (φ y').1 → (φ y).2.1 = (φ y').2.1 →
            (y ∈ XK.space ↔ y' ∈ XK.space) := by
    by_cases hxfr : x ∈ frontier XK.space
    · obtain ⟨U₁, φ, ρ, hU₁, hxU₁, hρ, hφ, hφx, hloc⟩ := h2.exists_sideChart hd he hcard ⟨hxe, hxfr⟩
      set U := U₁ ∩ (O ∩ Uo) with hUdef
      have hU : IsOpen U := hU₁.inter (hO.inter hUoo)
      have hUsub : U ⊆ U₁ := inter_subset_left
      have hV : IsOpen (φ '' U) := hφ.isOpen_image_of_isOpen Metric.isOpen_ball hU hUsub
      refine ⟨U, φ '' U, φ, hU, hV, ⟨hxU₁, hxO, hxUo⟩, inter_subset_right,
        hφ.restrict_isOpen hU hUsub hV, fun y hy => ?_, fun r _ y hy y' hy' _ _ _ h21 => ?_⟩
      · rw [hEint y hy.2.1, hφx, (hloc y hy.1).1]
        rfl
      · rw [(hloc y hy.1).2.2, (hloc y' hy'.1).2.2, h21]
    · have hOn : O ∩ Uo ∩ (frontier XK.space)ᶜ ∈ 𝓝 x :=
        (hO.inter hUoo).inter isClosed_frontier.isOpen_compl |>.mem_nhds ⟨⟨hxO, hxUo⟩, hxfr⟩
      obtain ⟨U, V, φ, hU, hV, hxU, hUO, hφ, hE⟩ := hpc.exists_flatChart hxint hxP hOn
      refine ⟨U, V, φ, hU, hV, hxU, fun y hy => (hUO hy).1, hφ, fun y hy => ?_,
        fun r hball y hy y' hy' hyb hy'b _ _ => ?_⟩
      · rw [hE y hy, (hE x hxU).mp hxe]
      · set g := Function.invFunOn φ U with hgdef
        have hg : IsPLHomeomorphOn g V U := hφ.symm
        have hpre : IsPreconnected (g '' Metric.ball (φ x) r) :=
          (convex_ball _ _).isPreconnected.image g
            (hg.isPiecewiseAffineOn.continuousOn.mono hball)
        have hsubU : g '' Metric.ball (φ x) r ⊆ U := image_subset_iff.mpr fun w hw =>
          hg.bijOn.mapsTo (hball hw)
        have hyg : y ∈ g '' Metric.ball (φ x) r := ⟨φ y, hyb, hφ.bijOn.invOn_invFunOn.1 hy⟩
        have hy'g : y' ∈ g '' Metric.ball (φ x) r :=
          ⟨φ y', hy'b, hφ.bijOn.invOn_invFunOn.1 hy'⟩
        have hcover : g '' Metric.ball (φ x) r ⊆ interior XK.space ∪ XK.spaceᶜ := by
          intro w hw
          by_cases hwX : w ∈ XK.space
          · exact Or.inl ((mem_interior_iff_notMem_frontier hwX).mpr (hUO (hsubU hw)).2)
          · exact Or.inr hwX
        rcases hpre.subset_or_subset isOpen_interior hXc.isOpen_compl
            (disjoint_compl_right.mono_left interior_subset) hcover with h' | h'
        · exact ⟨fun _ => interior_subset (h' hy'g), fun _ => interior_subset (h' hyg)⟩
        · exact ⟨fun h'' => absurd h'' (h' hyg), fun h'' => absurd h'' (h' hy'g)⟩
  obtain ⟨U, V, φ, hU, hV, hxU, hUsub, hφ, hUE, hUX⟩ := hchart
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV (φ x) (hφ.bijOn.mapsTo hxU)
  have hr : 0 < ε / 2 := half_pos hε
  have hball : Metric.closedBall (φ x) (ε / 2) ⊆ V :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hUN : U ⊆ N' := fun y hy => interior_subset (hON (hUsub hy).1)
  have hUo' : ∀ y ∈ U, ∀ f ∈ K.faces, f.card = 2 → f ≠ e → y ∉ Ec f :=
    fun y hy => hUo y (hUsub hy).2
  obtain ⟨s, hs, hsC⟩ :=
    hd.exists_side_of_chart he hcard hve hφ hU hxU hxe hr hball hUN hUE hUo'
  have hA : ∀ y ∈ U, φ y ∈ Metric.ball (φ x) (ε / 2) →
      (y ∈ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e ↔
        (φ y).2.2 = (φ x).2.2) := by
    intro y hy _
    rw [← hUE y hy]
    constructor
    · intro hyA
      obtain ⟨f, ⟨hf, hfc⟩, hyf⟩ := mem_iUnion₂.mp hyA
      by_contra hye
      exact hUo' y hy f hf hfc (fun hfe => hye (by rw [← hfe]; exact hyf)) hyf
    · intro hye
      exact mem_iUnion₂.mpr ⟨e, ⟨he, hcard⟩, hye⟩
  have hsub : Metric.ball (φ x) (ε / 2) ⊆ V :=
    (Metric.ball_subset_ball (half_le_self hε.le)).trans hεV
  obtain ⟨Ψ, W, hΨ, hW, hΨU, hΨX, hΨC⟩ :=
    exists_isPLHomeomorphOn_push_of_chart hU hφ hxU hr hball hs hA hsC (hUX (ε / 2) hsub)
  exact ⟨Ψ, W, hΨ, hW, fun y hy => hΨU y fun hyU => hy (hUsub hyU).1, hΨX, hΨC⟩

theorem IsPolyhedralTubeNeighborhood.exists_pushOff_handlePiece
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {v : E3} (hv : v ∈ K.vertices)
    {O : Set E3} (hO : IsOpen O) (hON : O ⊆ interior N') (hOK : Disjoint O (h '' K.space))
    {Z : Set E3} (hZ : IsCompact Z) (hZO : Z ⊆ O) (hZC : Z ⊆ Cpp v) :
    ∃ Φ : E3 → E3, IsPLHomeomorphOn Φ univ univ ∧ (∀ y, y ∉ O → Φ y = y) ∧
      (∀ y, Φ y ∈ XK.space ↔ y ∈ XK.space) ∧ Φ '' Z ⊆ Cpp v ∧
        Disjoint (Φ '' Z) (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) := by
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  have hAc : IsClosed A := hfin.isClosed_biUnion fun f hf => (hd.pseudoCell f hf.1 hf.2).isClosed
  obtain ⟨Φ, hΦ, hΦO, hΦX, hΦC⟩ := exists_isPLHomeomorphOn_push_of_forall (A := A)
    (C := Cpp v) (X := XK.space) (O := O) (hZ.inter_right hAc)
    fun x hx => h2.exists_localPush hd hv hO hON hOK (hZO hx.1) (hZC hx.1) hx.2
  refine ⟨Φ, hΦ, hΦO, hΦX, ?_, Set.disjoint_left.mpr ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (hΦC y (hZC hy)).1
  · rintro _ ⟨y, hy, rfl⟩ hyA
    obtain ⟨hyZ, hΦy⟩ := (hΦC y (hZC hy)).2 hyA
    exact hyZ ⟨hy, hΦy ▸ hyA⟩

theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_disjoint_pseudoCells
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {v : E3} (hv : v ∈ K.vertices)
    {Δ : Set E3} (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ)
    (hΔC : Δ ⊆ Cpp v) :
    ∃ Δ' : Set E3, IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Δ' ⊆ Cpp v ∧
      Disjoint Δ' (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) := by
  obtain ⟨r, hr, hΔsub, hΔB, hb, hnull⟩ := hΔ
  have hKc : IsClosed (h '' K.space) := hd.tube.isCompact_image_space.isClosed
  have hO : IsOpen (interior N' \ h '' K.space) := isOpen_interior.sdiff hKc
  have hΔc : IsCompact Δ := by
    rw [← hr.image_eq]
    exact (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).image_of_continuousOn
      hr.isPiecewiseAffineOn.continuousOn
  have hΔpoly : IsPolyhedron Δ := by
    rw [← hr.image_eq]
    exact (isHPolytope_stdSimplex (Fin 3)).isPolyhedron.image_of_isPiecewiseAffineOn
      hr.isPiecewiseAffineOn hr.bijOn.injOn
  obtain ⟨Φ, hΦ, hΦO, hΦX, hΦC, hΦA⟩ := h2.exists_pushOff_handlePiece hd hv hO sdiff_subset
    disjoint_sdiff_left hΔc hΔsub hΔC
  let H := (Homeomorph.Set.univ E3).symm.trans (hΦ.homeomorph.trans (Homeomorph.Set.univ E3))
  have hpre : H ⁻¹' XK.space = XK.space := by
    ext y
    exact hΦX y
  have hfr0 := H.preimage_frontier XK.space
  rw [hpre] at hfr0
  have hfr : ∀ y, Φ y ∈ frontier XK.space ↔ y ∈ frontier XK.space := fun y =>
    Set.ext_iff.mp hfr0 y
  have hinj : ∀ y y', Φ y = Φ y' → y = y' := fun y y' hyy =>
    hΦ.bijOn.injOn (mem_univ y) (mem_univ y') hyy
  have hΦO' : ∀ y ∈ interior N' \ h '' K.space, Φ y ∈ interior N' \ h '' K.space := by
    intro y hy
    by_contra hn
    have hyy := hinj _ _ (hΦO _ hn)
    rw [hyy] at hn
    exact hn hy
  have himg : (Φ ∘ r) '' stdSimplexBoundary 2 = Φ '' Δ ∩ frontier XK.space := by
    rw [image_comp, ← hΔB]
    ext z
    constructor
    · rintro ⟨y, ⟨hyΔ, hyB⟩, rfl⟩
      exact ⟨mem_image_of_mem Φ hyΔ, (hfr y).mpr hyB⟩
    · rintro ⟨⟨y, hyΔ, rfl⟩, hyB⟩
      exact ⟨y, ⟨hyΔ, (hfr y).mp hyB⟩, rfl⟩
  have hb' : (Φ ∘ r) '' stdSimplexBoundary 2 ⊆ frontier XK.space := by
    rw [himg]
    exact inter_subset_right
  have hr' : IsPLHomeomorphOn (Φ ∘ r) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (Φ '' Δ) :=
    IsPLHomeomorphOn.trans hr (IsPLHomeomorphOn.restrict hΦ hΔpoly (subset_univ Δ))
  refine ⟨Φ '' Δ, ⟨Φ ∘ r, hr', ?_, himg.symm, hb', fun hnull' => hnull ?_⟩,
    image_subset_iff.mpr fun y hy => hΦC ⟨y, hy, rfl⟩, hΦA⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hΦO' y (hΔsub hy)
  · have hgmem : ∀ z : frontier XK.space, H.symm z ∈ frontier XK.space := fun z =>
      (hfr _).mp (by
        change H (H.symm z) ∈ frontier XK.space
        rw [H.apply_symm_apply]
        exact z.2)
    have hkmem : ∀ y : r '' stdSimplexBoundary 2, H y ∈ (Φ ∘ r) '' stdSimplexBoundary 2 :=
      fun y => by
        rw [image_comp]
        exact mem_image_of_mem Φ y.2
    let g : C(frontier XK.space, frontier XK.space) :=
      ⟨fun z => ⟨H.symm z, hgmem z⟩, (H.symm.continuous.comp continuous_subtype_val).subtype_mk
        hgmem⟩
    let k : C(r '' stdSimplexBoundary 2, (Φ ∘ r) '' stdSimplexBoundary 2) :=
      ⟨fun y => ⟨H y, hkmem y⟩, (H.continuous.comp continuous_subtype_val).subtype_mk hkmem⟩
    have hcomp := (hnull'.comp_right g).comp_left k
    convert hcomp using 1
    refine ContinuousMap.ext fun y => Subtype.ext ?_
    exact (H.symm_apply_apply (y : E3)).symm

end PushOff

end DifferentialGeometry.Topology.PiecewiseLinear
