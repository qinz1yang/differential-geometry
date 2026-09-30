/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallInterior
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssembly
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphereDisk
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSplitBallPair

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.subset_closure_interior {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {S B : Set M} (h : IsPLCellOn 3 S B) :
    S ⊆ closure (interior S) := by
  obtain ⟨P, r, u, hr, hu, rfl, -⟩ := h
  have hball : IsPLBall 3 P := ⟨r, hr⟩
  have hcl : closure (interior P) = P := hball.closure_interior
  calc u '' P = u '' closure (interior P) := by rw [hcl]
    _ ⊆ closure (u '' interior P) :=
        ContinuousOn.image_closure (by rw [hcl]; exact hu.continuousOn)
    _ = closure (interior (u '' P)) := by rw [hu.image_interior]

theorem IsPLHomeomorphInto.isPLSphere_invFunOn_image {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {m : ℕ} {P : Set (EuclideanSpace ℝ (Fin 3))}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P) {C : Set M}
    (hC : IsPolyhedralSphere (n := 3) m C) (hCP : C ⊆ u '' P) :
    IsPLSphere m (Function.invFunOn u P '' C) := by
  obtain ⟨T, hT⟩ := hC
  have hid : IsPiecewiseAffineOn (id : EuclideanSpace ℝ (Fin T.ambientDim) → _)
      T.piece.complex.space :=
    (isPiecewiseAffineOn_id isOpen_univ).mono_of_isPolyhedron T.piece.isPolyhedron_space
      (subset_univ _)
  have hmap : IsPLOn T.ambientDim 3 (T.piece.map ∘ id) T.piece.complex.space :=
    T.piece.isPLOn_comp hid (mapsTo_id _)
  have hmaps : MapsTo (T.piece.map ∘ id) T.piece.complex.space (u '' P) :=
    fun x hx => hCP (T.piece.bijOn.mapsTo hx)
  have hpa : IsPiecewiseAffineOn (Function.invFunOn u P ∘ T.piece.map ∘ id)
      T.piece.complex.space :=
    isPLOn_iff_isPiecewiseAffineOn.mp
      (IsPLOn.comp_of_mapsTo (hu.isPLOn_inverse hu.injOn.leftInvOn_invFunOn) hmap hmaps)
  have hsec : ∀ z ∈ u '' P, u (Function.invFunOn u P z) = z := fun z hz =>
    hu.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hinj : InjOn (Function.invFunOn u P ∘ T.piece.map ∘ id) T.piece.complex.space := by
    intro x hx y hy hxy
    refine T.piece.bijOn.injOn hx hy ?_
    have hx' := hsec _ (hmaps hx)
    have hy' := hsec _ (hmaps hy)
    simp only [Function.comp_apply, id] at hxy hx' hy'
    rw [← hx', ← hy', hxy]
  have himg : (Function.invFunOn u P ∘ T.piece.map ∘ id) '' T.piece.complex.space =
      Function.invFunOn u P '' C := by
    rw [image_comp, image_comp, image_id, T.piece.bijOn.image_eq]
  rw [← himg]
  exact hT.of_isPLHomeomorphOn
    (isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn T.piece.isPolyhedron_space hpa
      hinj.bijOn_image)

theorem IsPLCellOn.sdiff_interior_of_frontier_inter {M : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {X Y C : Set M} (hX : IsPLCellOn 3 X (frontier X)) (hY : IsPLCellOn 3 Y (frontier Y))
    (hC : IsPolyhedralSphere (n := 3) 1 C) (hXY : frontier X ∩ frontier Y = C)
    (hin : (frontier Y ∩ interior X).Nonempty) (hout : ¬ frontier Y ⊆ X) :
    IsPLCellOn 3 (X \ interior Y) (frontier (X \ interior Y)) ∧
      IsPLCellOn 2 (frontier Y ∩ X) C := by
  have hXc : IsClosed X := hX.isCompact.isClosed
  have hYc : IsClosed Y := hY.isCompact.isClosed
  have hYcl : Y ⊆ closure (interior Y) := hY.subset_closure_interior
  have hCX : C ⊆ frontier X := by rw [← hXY]; exact inter_subset_left
  have hCY : C ⊆ frontier Y := by rw [← hXY]; exact inter_subset_right
  have hCXsub : C ⊆ X := hCX.trans hXc.frontier_subset
  have hdich : ∀ (Z : Set M), IsClosed Z → ∀ s : Set M, IsPreconnected s →
      Disjoint s (frontier Z) → s ⊆ interior Z ∨ Disjoint s Z := by
    intro Z hZc s hs hsZ
    have hcover : s ⊆ interior Z ∪ Zᶜ := by
      intro z hz
      by_cases hzZ : z ∈ Z
      · refine Or.inl (by_contra fun hzi => disjoint_left.mp hsZ hz ?_)
        rw [hZc.frontier_eq]
        exact ⟨hzZ, hzi⟩
      · exact Or.inr hzZ
    rcases hs.subset_or_subset isOpen_interior hZc.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) hcover with h | h
    · exact Or.inl h
    · exact Or.inr (subset_compl_iff_disjoint_right.mp h)
  obtain ⟨PY, rY, uY, hrY, huY, hYeq, hYbd⟩ := hY
  have hbY : IsPLBall 3 PY := ⟨rY, hrY⟩
  have hPYc : IsClosed PY := hbY.isPolyhedron.isClosed
  have hrYb : rY '' stdSimplexBoundary 3 = frontier PY :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hrY
  rw [hrYb] at hYbd
  have hfPY : frontier PY ⊆ PY := hPYc.frontier_subset
  have hYinv : ∀ y ∈ PY, Function.invFunOn uY PY (uY y) = y := fun y hy =>
    huY.injOn.leftInvOn_invFunOn hy
  have hYsec : ∀ z ∈ uY '' PY, uY (Function.invFunOn uY PY z) = z := fun z hz =>
    huY.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hCPY : C ⊆ uY '' PY := by
    refine hCY.trans ?_
    rw [hYbd]
    exact image_mono hfPY
  obtain ⟨J, hJdef⟩ : ∃ J, J = Function.invFunOn uY PY '' C := ⟨_, rfl⟩
  have hJ : IsPLSphere 1 J := hJdef ▸ huY.isPLSphere_invFunOn_image hC hCPY
  have hJS : J ⊆ frontier PY := by
    rw [hJdef]
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ uY '' frontier PY := by rw [← hYbd]; exact hCY hz
    obtain ⟨y, hy, rfl⟩ := hz'
    rw [hYinv y (hfPY hy)]
    exact hy
  have huJ : uY '' J = C := by
    rw [hJdef, image_image]
    exact (image_congr fun z hz => hYsec z (hCPY hz)).trans (image_id' C)
  obtain ⟨D₁, D₂, hD₁₂, -, f₁, f₂, hf₁, hf₂, hf₁b, hf₂b⟩ :=
    exists_disk_decomposition_of_isPLSphere_one_subset_two
      (hbY.isPLSphere_frontier (n := 2)) hJ hJS
  have hcov : ∀ A₀ A₁ : Set (EuclideanSpace ℝ (Fin 3)), A₀ ∪ A₁ = frontier PY →
      ∀ z ∈ frontier Y, z ∈ C ∨ z ∈ uY '' (A₀ \ J) ∨ z ∈ uY '' (A₁ \ J) := by
    intro A₀ A₁ hA z hz
    rw [hYbd, ← hA] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    by_cases hyJ : y ∈ J
    · refine Or.inl ?_
      rw [← huJ]
      exact mem_image_of_mem uY hyJ
    · rcases hy with hy | hy
      · exact Or.inr (Or.inl ⟨y, ⟨hy, hyJ⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨y, ⟨hy, hyJ⟩, rfl⟩)
  have hdisk : ∀ (A₀ : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
      IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A₀ → f '' stdSimplexBoundary 2 = J →
      A₀ ⊆ frontier PY → IsPreconnected (uY '' (A₀ \ J)) ∧
        Disjoint (uY '' (A₀ \ J)) (frontier X) := by
    intro A₀ f hf hfb hA
    refine ⟨?_, ?_⟩
    · have hconn : IsConnected (A₀ \ f '' stdSimplexBoundary 2) :=
        hf.isConnected_sdiff_image_stdSimplexBoundary (n := 1)
      rw [hfb] at hconn
      exact hconn.isPreconnected.image uY
        (huY.continuousOn.mono (sdiff_subset.trans (hA.trans hfPY)))
    · rw [disjoint_left]
      rintro _ ⟨y, ⟨hyA, hyJ⟩, rfl⟩ hyX
      apply hyJ
      have hyY : uY y ∈ frontier Y := by rw [hYbd]; exact mem_image_of_mem uY (hA hyA)
      have hyC : uY y ∈ C := by rw [← hXY]; exact ⟨hyX, hyY⟩
      rw [hJdef]
      exact ⟨uY y, hyC, hYinv y (hfPY (hA hyA))⟩
  obtain ⟨p, hpY, hpX⟩ := hin
  have hpC : p ∉ C := fun hpC => (hCX hpC).2 hpX
  obtain ⟨A₀, A₁, f, hf, hfb, hA₀₁, hAin, hAout⟩ :
      ∃ (A₀ A₁ : Set (EuclideanSpace ℝ (Fin 3))) (f : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3)),
        IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A₀ ∧ f '' stdSimplexBoundary 2 = J ∧
          A₀ ∪ A₁ = frontier PY ∧ uY '' (A₀ \ J) ⊆ interior X ∧
            Disjoint (uY '' (A₁ \ J)) X := by
    have hsub₁ : D₁ ⊆ frontier PY := by rw [← hD₁₂]; exact subset_union_left
    have hsub₂ : D₂ ⊆ frontier PY := by rw [← hD₁₂]; exact subset_union_right
    obtain ⟨hc₁, hd₁⟩ := hdisk D₁ f₁ hf₁ hf₁b hsub₁
    obtain ⟨hc₂, hd₂⟩ := hdisk D₂ f₂ hf₂ hf₂b hsub₂
    rcases hdich X hXc _ hc₁ hd₁ with h₁ | h₁ <;> rcases hdich X hXc _ hc₂ hd₂ with h₂ | h₂
    · refine absurd (fun z hz => ?_) hout
      rcases hcov D₁ D₂ hD₁₂ z hz with hz | hz | hz
      · exact hCXsub hz
      · exact interior_subset (h₁ hz)
      · exact interior_subset (h₂ hz)
    · exact ⟨D₁, D₂, f₁, hf₁, hf₁b, hD₁₂, h₁, h₂⟩
    · exact ⟨D₂, D₁, f₂, hf₂, hf₂b, (union_comm _ _).trans hD₁₂, h₂, h₁⟩
    · exfalso
      rcases hcov D₁ D₂ hD₁₂ p hpY with hz | hz | hz
      · exact hpC hz
      · exact disjoint_left.mp h₁ hz (interior_subset hpX)
      · exact disjoint_left.mp h₂ hz (interior_subset hpX)
  have hA : A₀ ⊆ frontier PY := by rw [← hA₀₁]; exact subset_union_left
  have hJA : J ⊆ A₀ := by
    rw [← hfb]
    exact image_subset_iff.mpr fun x hx => hf.1.mapsTo hx.1
  have hΔ : frontier Y ∩ X = uY '' A₀ := by
    apply Subset.antisymm
    · rintro z ⟨hzY, hzX⟩
      rcases hcov A₀ A₁ hA₀₁ z hzY with hz | hz | hz
      · rw [← huJ] at hz
        exact image_mono hJA hz
      · exact image_mono sdiff_subset hz
      · exact absurd hzX (disjoint_left.mp hAout hz)
    · rintro _ ⟨y, hy, rfl⟩
      refine ⟨by rw [hYbd]; exact mem_image_of_mem uY (hA hy), ?_⟩
      by_cases hyJ : y ∈ J
      · refine hCXsub ?_
        rw [← huJ]
        exact mem_image_of_mem uY hyJ
      · exact interior_subset (hAin ⟨y, ⟨hy, hyJ⟩, rfl⟩)
  have hApoly : IsPolyhedron A₀ := IsPLBall.isPolyhedron (n := 2) ⟨f, hf⟩
  have huA : IsPLHomeomorphInto 3 uY A₀ :=
    IsPLOn.isPLHomeomorphInto (huY.isPLOn.mono_of_isPolyhedron hApoly (hA.trans hfPY))
      hApoly.isCompact (huY.injOn.mono (hA.trans hfPY))
  have hcell2 : IsPLCellOn 2 (frontier Y ∩ X) C :=
    ⟨A₀, f, uY, hf, huA, hΔ, by rw [hfb, huJ]⟩
  obtain ⟨PX, rX, uX, hrX, huX, hXeq, hXbd⟩ := hX
  have hbX : IsPLBall 3 PX := ⟨rX, hrX⟩
  have hPXc : IsClosed PX := hbX.isPolyhedron.isClosed
  have hrXb : rX '' stdSimplexBoundary 3 = frontier PX :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hrX
  rw [hrXb] at hXbd
  have hXsec : ∀ z ∈ uX '' PX, uX (Function.invFunOn uX PX z) = z := fun z hz =>
    huX.injOn.bijOn_image.invOn_invFunOn.2 hz
  have hAX : uY '' A₀ ⊆ uX '' PX := by
    rw [← hXeq, ← hΔ]
    exact inter_subset_right
  have hg : IsPLHomeomorphOn (Function.invFunOn uX PX ∘ uY) A₀
      ((Function.invFunOn uX PX ∘ uY) '' A₀) :=
    huA.isPLHomeomorphOn_invFunOn_comp hApoly huX hAX
  have hback : ∀ S ⊆ A₀, uX '' ((Function.invFunOn uX PX ∘ uY) '' S) = uY '' S := by
    intro S hS
    rw [image_image]
    exact image_congr fun y hy => hXsec _ (hAX (mem_image_of_mem uY (hS hy)))
  obtain ⟨DX, hDXdef⟩ : ∃ DX, DX = (Function.invFunOn uX PX ∘ uY) '' A₀ := ⟨_, rfl⟩
  rw [← hDXdef] at hg
  have hDXPX : DX ⊆ PX := by
    rw [hDXdef]
    rintro _ ⟨y, hy, rfl⟩
    exact huX.injOn.bijOn_image.surjOn.mapsTo_invFunOn (hAX (mem_image_of_mem uY hy))
  have huDX : uX '' DX = uY '' A₀ := by rw [hDXdef]; exact hback A₀ Subset.rfl
  have hgf : IsPLHomeomorphOn ((Function.invFunOn uX PX ∘ uY) ∘ f)
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) DX :=
    hf.trans hg
  have htrace : DX ∩ frontier PX =
      ((Function.invFunOn uX PX ∘ uY) ∘ f) '' stdSimplexBoundary 2 := by
    have hsub2 : ((Function.invFunOn uX PX ∘ uY) ∘ f) '' stdSimplexBoundary 2 ⊆ PX := by
      rw [image_comp, hfb]
      refine (image_mono hJA).trans ?_
      rw [← hDXdef]
      exact hDXPX
    refine (huX.injOn.image_eq_image_iff (inter_subset_left.trans hDXPX) hsub2).mp ?_
    have hlhs : (frontier Y ∩ X) ∩ frontier X = C := by
      rw [← hXY]
      ext z
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h3, h1⟩
      · rintro ⟨h3, h1⟩
        exact ⟨⟨h1, hXc.frontier_subset h3⟩, h3⟩
    rw [huX.injOn.image_inter hDXPX hPXc.frontier_subset, huDX, ← hXbd, ← hΔ, hlhs,
      image_comp, hfb, hback J hJA, huJ]
  obtain ⟨P₀, P₁, hb₀, hb₁, hP01, -, hD₀, hD₁⟩ :=
    hbX.exists_pair_union_eq_inter_eq_of_boundary_trace hgf hDXPX htrace
  have hsubPX : ∀ Q, IsPLBall 3 Q → Q ⊆ PX → IsPLHomeomorphInto 3 uX Q := fun Q hQ hQP =>
    IsPLOn.isPLHomeomorphInto (huX.isPLOn.mono_of_isPolyhedron hQ.isPolyhedron hQP)
      hQ.isPolyhedron.isCompact (huX.injOn.mono hQP)
  have hcellQ : ∀ Q, IsPLBall 3 Q → Q ⊆ PX →
      IsPLCellOn 3 (uX '' Q) (frontier (uX '' Q)) := by
    intro Q hQ hQP
    obtain ⟨r, hr⟩ := hQ
    have hc : IsPLCellOn 3 (uX '' Q) (uX '' (r '' stdSimplexBoundary 3)) :=
      ⟨Q, r, uX, hr, hsubPX Q ⟨r, hr⟩ hQP, rfl, rfl⟩
    rw [hc.boundary_eq_frontier] at hc
    exact hc
  have hcl : ∀ Q, IsPLBall 3 Q → Q ⊆ PX → uX '' Q ⊆ closure (interior (uX '' Q)) :=
    fun Q hQ hQP => (hcellQ Q hQ hQP).subset_closure_interior
  have hP₀ : P₀ ⊆ PX := by rw [← hP01]; exact subset_union_left
  have hP₁ : P₁ ⊆ PX := by rw [← hP01]; exact subset_union_right
  have hint : ∀ Q, IsPLBall 3 Q → Q ⊆ PX → DX ⊆ frontier Q →
      IsPreconnected (interior (uX '' Q)) ∧ Disjoint (interior (uX '' Q)) (frontier Y) := by
    intro Q hQ hQP hDQ
    rw [← (hsubPX Q hQ hQP).image_interior]
    refine ⟨(isConnected_interior_of_isPLBall hQ).isPreconnected.image uX
      (huX.continuousOn.mono (interior_subset.trans hQP)), ?_⟩
    rw [disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ haY
    have hmem : uX a ∈ frontier Y ∩ X := by
      refine ⟨haY, ?_⟩
      rw [hXeq]
      exact mem_image_of_mem uX (hQP (interior_subset ha))
    rw [hΔ, ← huDX] at hmem
    obtain ⟨b, hb, hba⟩ := hmem
    have hab : b = a := huX.injOn (hDXPX hb) (hQP (interior_subset ha)) hba
    rw [hab] at hb
    exact (hDQ hb).2 ha
  have hXU : X = uX '' P₀ ∪ uX '' P₁ := by rw [hXeq, ← image_union, hP01]
  obtain ⟨hc₀, hd₀⟩ := hint P₀ hb₀ hP₀ hD₀
  obtain ⟨hc₁, hd₁⟩ := hint P₁ hb₁ hP₁ hD₁
  have hout' : ∀ Q, IsPLBall 3 Q → Q ⊆ PX → Disjoint (interior (uX '' Q)) Y →
      uX '' Q ⊆ (interior Y)ᶜ := by
    intro Q hQ hQP hQd
    refine (hcl Q hQ hQP).trans ?_
    rw [← closure_compl]
    exact closure_mono (subset_compl_iff_disjoint_right.mpr hQd)
  have hin' : ∀ Q, IsPLBall 3 Q → Q ⊆ PX → interior (uX '' Q) ⊆ interior Y → uX '' Q ⊆ Y :=
    fun Q hQ hQP hQi =>
      (hcl Q hQ hQP).trans ((closure_mono hQi).trans (closure_minimal interior_subset hYc))
  have key : ∀ Pa Pb, IsPLBall 3 Pa → IsPLBall 3 Pb → Pa ⊆ PX → Pb ⊆ PX → Pa ∪ Pb = PX →
      DX ⊆ Pb → interior (uX '' Pa) ⊆ interior Y → Disjoint (interior (uX '' Pb)) Y →
      X \ interior Y = uX '' Pb := by
    intro Pa Pb ha hb hPa hPb hab hDb hia hib
    apply Subset.antisymm
    · rintro z ⟨hzX, hzY⟩
      rw [hXeq, ← hab, image_union] at hzX
      rcases hzX with hz | hz
      · have hzfr : z ∈ frontier Y ∩ X := by
          refine ⟨?_, ?_⟩
          · rw [hYc.frontier_eq]
            exact ⟨hin' Pa ha hPa hia hz, hzY⟩
          · rw [hXeq]
            exact image_mono hPa hz
        rw [hΔ, ← huDX] at hzfr
        exact image_mono hDb hzfr
      · exact hz
    · intro z hz
      refine ⟨?_, hout' Pb hb hPb hib hz⟩
      rw [hXeq]
      exact image_mono hPb hz
  obtain ⟨Pb, hPb, hPbX, heq⟩ :
      ∃ Pb, IsPLBall 3 Pb ∧ Pb ⊆ PX ∧ X \ interior Y = uX '' Pb := by
    rcases hdich Y hYc _ hc₀ hd₀ with h₀ | h₀ <;> rcases hdich Y hYc _ hc₁ hd₁ with h₁ | h₁
    · exfalso
      have hXY' : X ⊆ Y := by
        rw [hXU]
        exact union_subset (hin' P₀ hb₀ hP₀ h₀) (hin' P₁ hb₁ hP₁ h₁)
      exact hpY.2 (interior_mono hXY' hpX)
    · exact ⟨P₁, hb₁, hP₁, key P₀ P₁ hb₀ hb₁ hP₀ hP₁ hP01
        (hD₁.trans hb₁.isPolyhedron.isClosed.frontier_subset) h₀ h₁⟩
    · exact ⟨P₀, hb₀, hP₀, key P₁ P₀ hb₁ hb₀ hP₁ hP₀ ((union_comm _ _).trans hP01)
        (hD₀.trans hb₀.isPolyhedron.isClosed.frontier_subset) h₁ h₀⟩
    · exfalso
      have hpcl : p ∈ closure (interior Y) := hYcl (hYc.frontier_subset hpY)
      obtain ⟨z, hzX, hzY⟩ :=
        mem_closure_iff_nhds.mp hpcl (interior X) (isOpen_interior.mem_nhds hpX)
      have hzX' := interior_subset hzX
      rw [hXU] at hzX'
      rcases hzX' with hz | hz
      · exact hout' P₀ hb₀ hP₀ h₀ hz hzY
      · exact hout' P₁ hb₁ hP₁ h₁ hz hzY
  refine ⟨?_, hcell2⟩
  rw [heq]
  exact hcellQ Pb hPb hPbX

theorem IsPLCellOn.sdiff_biUnion_interior {M κ : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {X : Set M} {Y C : κ → Set M} (s : Finset κ) (hX : IsPLCellOn 3 X (frontier X))
    (hY : ∀ e ∈ s, IsPLCellOn 3 (Y e) (frontier (Y e)))
    (hC : ∀ e ∈ s, IsPolyhedralSphere (n := 3) 1 (C e))
    (hXY : ∀ e ∈ s, frontier X ∩ frontier (Y e) = C e)
    (hin : ∀ e ∈ s, (frontier (Y e) ∩ interior X).Nonempty)
    (hout : ∀ e ∈ s, ¬ frontier (Y e) ⊆ X)
    (hdisj : ∀ e ∈ s, ∀ d ∈ s, e ≠ d → Disjoint (Y e ∩ X) (Y d ∩ X)) :
    IsPLCellOn 3 (X \ ⋃ e ∈ s, interior (Y e)) (frontier (X \ ⋃ e ∈ s, interior (Y e))) := by
  classical
  have hXc : IsClosed X := hX.isCompact.isClosed
  induction s using Finset.induction_on with
  | empty => simpa using hX
  | insert e s he ih =>
    have hmem : e ∈ insert e s := Finset.mem_insert_self e s
    have hsub : ∀ d ∈ s, d ∈ insert e s := fun d hd => Finset.mem_insert_of_mem hd
    have ih' := ih (fun d hd => hY d (hsub d hd)) (fun d hd => hC d (hsub d hd))
      (fun d hd => hXY d (hsub d hd)) (fun d hd => hin d (hsub d hd))
      (fun d hd => hout d (hsub d hd))
      (fun d hd d' hd' hdd' => hdisj d (hsub d hd) d' (hsub d' hd') hdd')
    have heq : X \ ⋃ d ∈ insert e s, interior (Y d) =
        (X \ ⋃ d ∈ s, interior (Y d)) \ interior (Y e) := by
      rw [Finset.set_biUnion_insert, union_comm, ← Set.sdiff_sdiff]
    rw [heq]
    have hYe : IsClosed (Y e) := (hY e hmem).isCompact.isClosed
    have hFc : IsClosed (⋃ d ∈ s, Y d) :=
      s.finite_toSet.isClosed_biUnion fun d hd => (hY d (hsub d hd)).isCompact.isClosed
    have hsep : Disjoint (Y e ∩ X) (⋃ d ∈ s, Y d) := by
      rw [disjoint_left]
      intro z hz hzF
      obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzF
      have hed : e ≠ d := fun h => he (h ▸ hd)
      exact disjoint_left.mp (hdisj e hmem d (hsub d hd) hed) hz ⟨hzd, hz.2⟩
    have hXsX : X \ ⋃ d ∈ s, interior (Y d) ⊆ X := sdiff_subset
    have hopen : interior X \ ⋃ d ∈ s, Y d ⊆ interior (X \ ⋃ d ∈ s, interior (Y d)) := by
      refine interior_maximal ?_ (isOpen_interior.sdiff hFc)
      rintro z ⟨hzi, hzF⟩
      refine ⟨interior_subset hzi, fun hzU => hzF ?_⟩
      obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzU
      exact mem_iUnion₂.mpr ⟨d, hd, interior_subset hzd⟩
    refine (IsPLCellOn.sdiff_interior_of_frontier_inter ih' (hY e hmem) (hC e hmem) ?_ ?_
      (fun h => hout e hmem (h.trans hXsX))).1
    · rw [← hXY e hmem]
      ext z
      constructor
      · rintro ⟨hz1, hz2⟩
        have hzY : z ∈ Y e := hYe.frontier_subset hz2
        have hzX : z ∈ X := closure_minimal hXsX hXc (frontier_subset_closure hz1)
        have hzF : z ∉ ⋃ d ∈ s, Y d := disjoint_left.mp hsep ⟨hzY, hzX⟩
        refine ⟨?_, hz2⟩
        rw [hXc.frontier_eq]
        exact ⟨hzX, fun hzi => hz1.2 (hopen ⟨hzi, hzF⟩)⟩
      · rintro ⟨hz1, hz2⟩
        have hzY : z ∈ Y e := hYe.frontier_subset hz2
        have hzX : z ∈ X := hXc.frontier_subset hz1
        have hzF : z ∉ ⋃ d ∈ s, Y d := disjoint_left.mp hsep ⟨hzY, hzX⟩
        refine ⟨⟨subset_closure ⟨hzX, fun hzU => hzF ?_⟩,
          fun hzi => hz1.2 (interior_mono hXsX hzi)⟩, hz2⟩
        obtain ⟨d, hd, hzd⟩ := mem_iUnion₂.mp hzU
        exact mem_iUnion₂.mpr ⟨d, hd, interior_subset hzd⟩
    · obtain ⟨p, hp1, hp2⟩ := hin e hmem
      exact ⟨p, hp1, hopen ⟨hp2, disjoint_left.mp hsep
        ⟨hYe.frontier_subset hp1, interior_subset hp2⟩⟩⟩

theorem isPLCellOn_sdiff_iUnion_interior_of_caps {M ι κ : Type*} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [HasGroupoid M (plGroupoid 3)]
    {B : ι → Set M} {ends : κ → ι × ι} {C : κ → Set M} {Dv : ι → Set M}
    (hB : ∀ w, IsPLCellOn 3 (B w) (frontier (B w)))
    (hfin : ∀ w, {e | (ends e).2 = w}.Finite) (hne : ∀ e, (ends e).1 ≠ (ends e).2)
    (hC : ∀ e, IsPolyhedralSphere (n := 3) 1 (C e))
    (hBC : ∀ e, frontier (B (ends e).2) ∩ frontier (B (ends e).1) = C e)
    (hin : ∀ e, (frontier (B (ends e).1) ∩ interior (B (ends e).2)).Nonempty)
    (hout : ∀ e, ¬ frontier (B (ends e).1) ⊆ B (ends e).2)
    (hover : ∀ e d, e ≠ d →
      Disjoint (B (ends e).1 ∩ B (ends e).2) (B (ends d).1 ∩ B (ends d).2))
    (hDv : ∀ w, Dv w = B w \ ⋃ (e : κ) (_ : (ends e).2 = w), interior (B (ends e).1)) :
    (∀ w, IsPLCellOn 3 (Dv w) (frontier (Dv w))) ∧
      (∀ e, IsPLCellOn 2 (frontier (B (ends e).1) ∩ B (ends e).2) (C e)) ∧
      (∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = frontier (B (ends e).1) ∩ B (ends e).2) ∧
      (∀ e, frontier (B (ends e).1) ∩ B (ends e).2 ⊆
        frontier (Dv (ends e).1) ∩ frontier (Dv (ends e).2)) ∧
      (∀ w, interior (B w) \ ⋃ (e : κ) (_ : (ends e).2 = w), B (ends e).1 ⊆
        interior (Dv w)) ∧
      ∀ w, B w ⊆ ⋃ v, Dv v := by
  classical
  have hBc : ∀ w, IsClosed (B w) := fun w => (hB w).isCompact.isClosed
  have hmemDv : ∀ w z, z ∈ Dv w ↔
      z ∈ B w ∧ ∀ e, (ends e).2 = w → z ∉ interior (B (ends e).1) := by
    intro w z
    rw [hDv w]
    simp only [Set.mem_sdiff, mem_iUnion, exists_prop, not_exists, not_and]
  have hsep : ∀ e d, e ≠ d → ∀ z, z ∈ B (ends e).1 → z ∈ B (ends e).2 → z ∈ B (ends d).2 →
      z ∉ B (ends d).1 := fun e d hed z h1 h2 h3 h4 =>
    disjoint_left.mp (hover e d hed) ⟨h1, h2⟩ ⟨h4, h3⟩
  have hcell : ∀ w, IsPLCellOn 3 (Dv w) (frontier (Dv w)) := by
    intro w
    have hU : ⋃ (e : κ) (_ : (ends e).2 = w), interior (B (ends e).1) =
        ⋃ e ∈ (hfin w).toFinset, interior (B (ends e).1) := by
      ext z
      simp only [mem_iUnion, Set.Finite.mem_toFinset, mem_ofPred_eq, exists_prop]
    rw [hDv w, hU]
    refine IsPLCellOn.sdiff_biUnion_interior (hfin w).toFinset (hB w) (fun e _ => hB _)
      (fun e _ => hC e) (fun e he => ?_) (fun e he => ?_) (fun e he => ?_)
      (fun e he d hd hed => ?_)
    · have he' : (ends e).2 = w := (hfin w).mem_toFinset.mp he
      subst he'
      exact hBC e
    · have he' : (ends e).2 = w := (hfin w).mem_toFinset.mp he
      subst he'
      exact hin e
    · have he' : (ends e).2 = w := (hfin w).mem_toFinset.mp he
      subst he'
      exact hout e
    · have he' : (ends e).2 = w := (hfin w).mem_toFinset.mp he
      have hd' : (ends d).2 = w := (hfin w).mem_toFinset.mp hd
      have h := hover e d hed
      rw [he', hd'] at h
      exact h
  have hmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = frontier (B (ends e).1) ∩ B (ends e).2 := by
    intro e
    ext z
    rw [mem_inter_iff, hmemDv, hmemDv]
    constructor
    · rintro ⟨⟨hz1, -⟩, hz2, hz2'⟩
      refine ⟨?_, hz2⟩
      rw [(hBc _).frontier_eq]
      exact ⟨hz1, hz2' e rfl⟩
    · rintro ⟨hzf, hz2⟩
      have hz1 : z ∈ B (ends e).1 := (hBc _).frontier_subset hzf
      refine ⟨⟨hz1, fun d hd hzd => ?_⟩, hz2, fun d hd hzd => ?_⟩
      · have hed : e ≠ d := by
          rintro rfl
          exact hne e hd.symm
        exact hsep e d hed z hz1 hz2 (by rw [hd]; exact hz1) (interior_subset hzd)
      · by_cases hed : e = d
        · subst hed
          exact hzf.2 hzd
        · exact hsep e d hed z hz1 hz2 (by rw [hd]; exact hz2) (interior_subset hzd)
  have hbd : ∀ e, frontier (B (ends e).1) ∩ B (ends e).2 ⊆
      frontier (Dv (ends e).1) ∩ frontier (Dv (ends e).2) := by
    intro e z hz
    have hzD : z ∈ Dv (ends e).1 ∩ Dv (ends e).2 := by rw [hmeet e]; exact hz
    have hDB : Dv (ends e).1 ⊆ B (ends e).1 := fun y hy => ((hmemDv _ _).mp hy).1
    refine ⟨⟨subset_closure hzD.1, fun hzi => hz.1.2 (interior_mono hDB hzi)⟩,
      subset_closure hzD.2, fun hzi => ?_⟩
    have hzcl : z ∈ closure (interior (B (ends e).1)) :=
      (hB _).subset_closure_interior ((hBc _).frontier_subset hz.1)
    obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.mp hzcl _ (isOpen_interior.mem_nhds hzi)
    exact ((hmemDv _ _).mp (interior_subset hy1)).2 e rfl hy2
  have hmark : ∀ w, interior (B w) \ ⋃ (e : κ) (_ : (ends e).2 = w), B (ends e).1 ⊆
      interior (Dv w) := by
    intro w
    have hcl : IsClosed (⋃ (e : κ) (_ : (ends e).2 = w), B (ends e).1) :=
      (hfin w).isClosed_biUnion fun e _ => hBc (ends e).1
    refine interior_maximal ?_ (isOpen_interior.sdiff hcl)
    rintro z ⟨hzi, hzU⟩
    rw [hmemDv]
    exact ⟨interior_subset hzi, fun e he hze =>
      hzU (mem_iUnion₂.mpr ⟨e, he, interior_subset hze⟩)⟩
  have hcover : ∀ w, B w ⊆ ⋃ v, Dv v := by
    intro w z hz
    by_cases hzw : z ∈ Dv w
    · exact mem_iUnion.mpr ⟨w, hzw⟩
    · rw [hmemDv] at hzw
      push Not at hzw
      obtain ⟨e, he, hze⟩ := hzw hz
      refine mem_iUnion.mpr ⟨(ends e).1, (hmemDv _ _).mpr ⟨interior_subset hze, fun d hd hzd => ?_⟩⟩
      have hed : e ≠ d := by
        rintro rfl
        exact hne e hd.symm
      exact hsep e d hed z (interior_subset hze) (by rw [he]; exact hz)
        (by rw [hd]; exact interior_subset hze) (interior_subset hzd)
  exact ⟨hcell, fun e => (IsPLCellOn.sdiff_interior_of_frontier_inter (hB _) (hB _) (hC e)
    (hBC e) (hin e) (hout e)).2, hmeet, hbd, hmark, hcover⟩

end DifferentialGeometry.Topology.PiecewiseLinear
