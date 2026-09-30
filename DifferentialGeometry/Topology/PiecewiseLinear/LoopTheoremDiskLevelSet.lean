/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FreeFaceArc
import DifferentialGeometry.Topology.PiecewiseLinear.LevelSetComponents
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskPrism
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellLocalDisks
import DifferentialGeometry.Topology.PiecewiseLinear.StarSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.StdChart

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem mem_openSimplex_stdVertices_of_mem_sdiff {x : Fin 3 → ℝ}
    (hx : x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) :
    x ∈ openSimplex (stdVertices 1) :=
  (mem_openSimplex_stdVertices_iff 1).mpr
    ⟨fun i => lt_of_le_of_ne (hx.1.1 i) fun h => hx.2 ⟨hx.1, i, h.symm⟩, hx.1.2⟩

theorem notMem_stdSimplexBoundary_of_mem_openSimplex {x : Fin 3 → ℝ}
    (hx : x ∈ openSimplex (stdVertices 1)) : x ∉ stdSimplexBoundary 2 := by
  rintro ⟨-, i, hi⟩
  exact (((mem_openSimplex_stdVertices_iff 1).mp hx).1 i).ne' hi

theorem prism_mem_interior_image {Np : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) Np)
    {z : (Fin 3 → ℝ) × ℝ} (hz1 : z.1 ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2)
    (hz2 : z.2 ∈ Ioo (-1 : ℝ) 1) : f z ∈ interior Np := by
  let U : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := stdTarget 1 ×ˢ Ioo (-1 : ℝ) 1
  let ι : EuclideanSpace ℝ (Fin 2) × ℝ → (Fin 3 → ℝ) × ℝ := fun w => (stdLift 1 w.1, w.2)
  have hιc : Continuous ι :=
    ((stdLift 1).continuous_of_finiteDimensional.comp continuous_fst).prodMk continuous_snd
  have hιU : MapsTo ι U (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) := fun w hw =>
    ⟨openSimplex_stdVertices_subset_stdSimplex (n := 1) (stdLift_mem_openSimplex 1 hw.1),
      Ioo_subset_Icc_self hw.2⟩
  have hU : IsOpen U := (isOpen_stdTarget 1).prod isOpen_Ioo
  have hcont : ContinuousOn (f ∘ ι) U :=
    hf.isPiecewiseAffineOn.continuousOn.comp hιc.continuousOn hιU
  have hinj : InjOn (f ∘ ι) U := by
    intro w hw w' hw' hww
    have h := hf.bijOn.injOn (hιU hw) (hιU hw') hww
    have h1 : stdProj 1 (stdLift 1 w.1) = stdProj 1 (stdLift 1 w'.1) :=
      congrArg (stdProj 1) (congrArg Prod.fst h)
    rw [stdProj_stdLift, stdProj_stdLift] at h1
    have h2 := congrArg Prod.snd h
    exact Prod.ext h1 h2
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ E3 := by
    simp [Module.finrank_prod]
  have hopen := invariance_of_domain_isOpen_image_of_finrank_eq hdim hU hcont hinj
  have hsub : (f ∘ ι) '' U ⊆ Np := by
    rintro _ ⟨w, hw, rfl⟩
    exact hf.bijOn.mapsTo (hιU hw)
  have hx := mem_openSimplex_stdVertices_of_mem_sdiff hz1
  refine interior_maximal hsub hopen ⟨(stdProj 1 z.1, z.2), ⟨stdProj_mem_stdTarget 1 hx, hz2⟩, ?_⟩
  change f (stdLift 1 (stdProj 1 z.1), z.2) = f z
  rw [stdLift_stdProj_of_mem 1 hx]

theorem prism_mem_wall_iff {Np : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) Np) {B : Set E3}
    (hwall : B ∩ Np = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)) {w : (Fin 3 → ℝ) × ℝ}
    (hw : w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :
    f w ∈ B ↔ w.1 ∈ stdSimplexBoundary 2 := by
  constructor
  · intro hB
    obtain ⟨w', hw', hww⟩ := hwall.subset ⟨hB, hf.bijOn.mapsTo hw⟩
    have heq : w' = w := hf.bijOn.injOn ⟨hw'.1.1, hw'.2⟩ hw hww
    exact heq ▸ hw'.1
  · intro h1
    exact (hwall.symm.subset ⟨w, ⟨h1, hw.2⟩, rfl⟩).1

theorem prism_subset_or_subset {Np : Set E3} {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) Np) {X : Set E3}
    (hX : IsClosed X)
    (hwall : frontier X ∩ Np = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1)) :
    Np ⊆ X ∨ Np ⊆ (interior X)ᶜ := by
  have hfc := hf.isPiecewiseAffineOn.continuousOn
  let S₀ : Set ((Fin 3 → ℝ) × ℝ) := openSimplex (stdVertices 1) ×ˢ Icc (-1 : ℝ) 1
  have hS₀sub : S₀ ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 :=
    prod_mono (openSimplex_stdVertices_subset_stdSimplex (n := 1)) subset_rfl
  have hY : IsPreconnected (f '' S₀) :=
    ((convex_openSimplex _).prod (convex_Icc _ _)).isPreconnected.image f (hfc.mono hS₀sub)
  have hYB : ∀ y ∈ f '' S₀, y ∉ frontier X := by
    rintro _ ⟨w, hw, rfl⟩ hB
    exact notMem_stdSimplexBoundary_of_mem_openSimplex hw.1
      ((prism_mem_wall_iff hf hwall (hS₀sub hw)).mp hB)
  have hcl : Np ⊆ closure (f '' S₀) := by
    rw [← hf.image_eq]
    rintro _ ⟨w, hw, rfl⟩
    apply ((hfc w hw).mono hS₀sub).mem_closure_image
    rw [closure_prod_eq]
    exact ⟨stdSimplex_subset_closure_openSimplex 1 hw.1, subset_closure hw.2⟩
  have hcover : f '' S₀ ⊆ interior X ∪ (closure X)ᶜ := by
    intro y hy
    by_cases h1 : y ∈ interior X
    · exact Or.inl h1
    · exact Or.inr fun h2 => hYB y hy ⟨h2, h1⟩
  rcases hY.subset_or_subset isOpen_interior isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left (interior_subset.trans subset_closure)) hcover with h | h
  · left
    calc Np ⊆ closure (f '' S₀) := hcl
      _ ⊆ closure (interior X) := closure_mono h
      _ ⊆ X := closure_minimal interior_subset hX
  · right
    rw [hX.closure_eq] at h
    calc Np ⊆ closure (f '' S₀) := hcl
      _ ⊆ closure Xᶜ := closure_mono h
      _ = (interior X)ᶜ := closure_compl

theorem mem_restrict_faces_of_inter_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Geometry.SimplicialComplex ℝ E) {Q U : Set E} (hQ : (restrict T Q).space = Q)
    (hU : IsOpen U) (hUQ : U ∩ T.space ⊆ Q) {s : Finset E} (hs : s ∈ T.faces)
    (hsU : (convexHull ℝ (s : Set E) ∩ U).Nonempty) : s ∈ (restrict T Q).faces := by
  obtain ⟨x, hxs, hxU⟩ := hsU
  obtain ⟨p, hpU, hps⟩ : (U ∩ openSimplex s).Nonempty :=
    mem_closure_iff.mp (convexHull_subset_closure_openSimplex (T.nonempty_of_mem_faces hs) hxs)
      U hU hxU
  have hpT : p ∈ T.space := T.convexHull_subset_space hs (openSimplex_subset_convexHull s hps)
  have hpQ : p ∈ (restrict T Q).space := hQ.symm ▸ hUQ ⟨hpU, hpT⟩
  obtain ⟨t, ht, hpt⟩ := (restrict T Q).mem_space_iff.mp hpQ
  have hst : s ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull T hs ht.1 hps hpt
  exact ⟨hs, (convexHull_mono (Finset.coe_subset.mpr hst)).trans ht.2⟩

open Classical in
theorem restrict_isPLBall_cofaces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces]
    {Q U : Set E} {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q)
    (hQ : (restrict T Q).space = Q) (hU : IsOpen U) (hUQ : U ∩ T.space ⊆ Q) :
    (∀ s ∈ T.faces, (convexHull ℝ (s : Set E) ∩ U).Nonempty → s.card ≤ 3) ∧
    (∀ s ∈ T.faces, s.card = 2 → ∀ x ∈ openSimplex s, x ∈ U →
      (x ∈ q '' stdSimplexBoundary 2 → ∃ a, {w | w ∉ s ∧ insert w s ∈ T.faces} = {a}) ∧
      (x ∉ q '' stdSimplexBoundary 2 →
        ∃ a b, a ≠ b ∧ {w | w ∉ s ∧ insert w s ∈ T.faces} = {a, b})) ∧
    (∀ s ∈ T.faces, s.card = 3 → ∀ x ∈ openSimplex s, x ∈ U →
      x ∉ q '' stdSimplexBoundary 2) := by
  let R := restrict T Q
  have : Finite R.faces := (restrict_faces_finite T Q).to_subtype
  have hRball : IsPLBall (1 + 1) R.space := by
    rw [hQ]
    exact ⟨q, hq⟩
  have hR : IsCombinatorialManifoldWithBoundary (1 + 1) R :=
    IsPLBall.isCombinatorialManifoldWithBoundary hRball
  have hloc : ∀ s ∈ T.faces, (convexHull ℝ (s : Set E) ∩ U).Nonempty → s ∈ R.faces :=
    fun s hs hsU => mem_restrict_faces_of_inter_isOpen T hQ hU hUQ hs hsU
  have hbd : q '' stdSimplexBoundary 2 = (boundaryComplex 2 R).space :=
    hq.image_stdSimplexBoundary_eq_boundaryComplex (m := 1) R hQ
  have hmem : ∀ s ∈ R.faces, ∀ x ∈ openSimplex s,
      x ∈ q '' stdSimplexBoundary 2 → s ∈ (boundaryComplex 2 R).faces := by
    intro s hs x hx hxq
    rw [hbd] at hxq
    obtain ⟨t, ht, hxt⟩ := (boundaryComplex 2 R).mem_space_iff.mp hxq
    have hst : s ⊆ t := face_subset_of_mem_openSimplex_of_mem_convexHull R hs ht.1 hx hxt
    exact (boundaryComplex 2 R).down_closed ht hst (R.nonempty_of_mem_faces hs)
  refine ⟨fun s hs hsU => IsCombinatorialManifoldWithBoundary.card_le R hR (hloc s hs hsU),
    fun s hs hcard x hx hxU => ?_, fun s hs hcard x hx hxU hxq => ?_⟩
  · have hsR := hloc s hs ⟨x, openSimplex_subset_convexHull s hx, hxU⟩
    have hcof : {w | w ∉ s ∧ insert w s ∈ T.faces} = {w | w ∉ s ∧ insert w s ∈ R.faces} := by
      ext w
      refine ⟨fun hw => ⟨hw.1, hloc _ hw.2 ⟨x, ?_, hxU⟩⟩, fun hw => ⟨hw.1, hw.2.1⟩⟩
      refine convexHull_mono ?_ (openSimplex_subset_convexHull s hx)
      rw [Finset.coe_insert]
      exact subset_insert w _
    rw [hcof]
    refine ⟨fun hxq => ?_, fun hxq => ?_⟩
    · exact (IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface R hR
        (n := 1) hcard).mp (hmem s hsR x hx hxq)
    · refine IsCombinatorialManifoldWithBoundary.codimension_one_cofaces_of_notMem_boundary R hR
        hsR hcard fun hsB => hxq ?_
      rw [hbd]
      exact (boundaryComplex 2 R).convexHull_subset_space hsB (openSimplex_subset_convexHull s hx)
  · have hsR := hloc s hs ⟨x, openSimplex_subset_convexHull s hx, hxU⟩
    obtain ⟨-, t, -, hst, htc, -⟩ := hmem s hsR x hx hxq
    have := Finset.card_le_card hst
    omega

section LevelSet

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsPolyhedralTubeNeighborhood.exists_prism_localDisk
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {Np : Set E3}
    {f : (Fin 3 → ℝ) × ℝ → E3}
    (hf : IsPLHomeomorphOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) Np)
    (hNp : Np ⊆ interior N' \ h '' K.space)
    (hwall : frontier XK.space ∩ Np = f '' (stdSimplexBoundary 2 ×ˢ Icc (-1 : ℝ) 1))
    (hside : Np ⊆ XK.space ∨ Np ⊆ (interior XK.space)ᶜ) {z : (Fin 3 → ℝ) × ℝ}
    (hz : z ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1)
    (hzA : f z ∈ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)
    (hz2 : z.2 ∈ Ioo (-1 : ℝ) 1) :
    ∃ (Q U : Set ((Fin 3 → ℝ) × ℝ)) (q : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ),
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧
      Q ⊆ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∩
        f ⁻¹' (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) ∧
      IsOpen U ∧ z ∈ U ∧
      U ∩ ((Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∩
        f ⁻¹' (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e)) ⊆ Q ∧
      ∀ w ∈ U ∩ Q, (w ∈ q '' stdSimplexBoundary 2 ↔ w.1 ∈ stdSimplexBoundary 2) := by
  classical
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfc : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
    hf.isPiecewiseAffineOn.continuousOn
  have hwiff : ∀ w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1,
      f w ∈ frontier XK.space ↔ w.1 ∈ stdSimplexBoundary 2 :=
    fun w hw => prism_mem_wall_iff hf hwall hw
  obtain ⟨e, ⟨he, hcard⟩, hye⟩ := mem_iUnion₂.mp hzA
  have hpc := hd.pseudoCell e he hcard
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  set Oth := ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, Ec e' with hOthdef
  have hOthc : IsClosed Oth := (hfin.subset fun e' he' => ⟨he'.1, he'.2.1⟩).isClosed_biUnion
    fun e' he' => (hd.pseudoCell e' he'.1 he'.2.1).isClosed
  have hyOth : f z ∉ Oth := by
    intro hy
    obtain ⟨e', ⟨he', hcard', hne⟩, hye'⟩ := mem_iUnion₂.mp hy
    exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e he hcard e' he' hcard' hne.symm) hye hye'
  have hAOth : ∀ y ∈ A, y ∉ Oth → y ∈ Ec e := by
    intro y hy hyO
    obtain ⟨e', ⟨he', hcard'⟩, hye'⟩ := mem_iUnion₂.mp hy
    by_cases hee : e' = e
    · exact hee ▸ hye'
    · exact absurd (mem_iUnion₂.mpr ⟨e', ⟨he', hcard', hee⟩, hye'⟩) hyO
  have hEA : Ec e ⊆ A := fun y hy => mem_iUnion₂.mpr ⟨e, ⟨he, hcard⟩, hy⟩
  have hyN : f z ∈ Np := hf.bijOn.mapsTo hz
  have hyE : f z ∈ Eint e := by
    have hEc : f z ∈ Eint e ∪ Ebd e := hpc.carrierEq ▸ hye
    refine hEc.resolve_right fun hbd => ?_
    rw [← hd.rimFrontier e he hcard] at hbd
    exact Set.disjoint_left.mp disjoint_interior_frontier (hNp hyN).1 hbd.2
  have hyP : f z ≠ h (e.centroid ℝ id) := by
    intro heq
    have hmem : h (e.centroid ℝ id) ∈ Ec e ∩ h '' K.space := by
      rw [hd.meetsGraph e he hcard]
      rfl
    exact (hNp hyN).2 (heq ▸ hmem.2)
  set g := Function.invFunOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) with hgdef
  have hg : IsPLHomeomorphOn g Np (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) := hf.symm
  have hfg : ∀ y ∈ Np, f (g y) = y := fun y hy => hf.bijOn.invOn_invFunOn.2 hy
  have hgf : ∀ w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1, g (f w) = w :=
    fun w hw => hf.bijOn.invOn_invFunOn.1 hw
  obtain ⟨Dk, W, q₀, hq₀, hDk, hW, hyW, hWDk, hbdk⟩ : ∃ (Dk W : Set E3)
      (q₀ : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Dk ∧
      Dk ⊆ Ec e ∩ Np ∧ IsOpen W ∧ f z ∈ W ∧ W ∩ Ec e ∩ Np ⊆ Dk ∧
      ∀ d ∈ W ∩ Dk, (d ∈ q₀ '' stdSimplexBoundary 2 ↔ d ∈ frontier XK.space) := by
    by_cases hz1 : z.1 ∈ stdSimplexBoundary 2
    · have hyX : f z ∈ frontier XK.space := (hwiff z hz).mpr hz1
      obtain ⟨Sd, hSd, hNpSd⟩ : ∃ Sd : Set E3,
          (Sd = XK.space ∨ Sd = (interior XK.space)ᶜ) ∧ Np ⊆ Sd :=
        hside.elim (fun hs => ⟨_, Or.inl rfl, hs⟩) (fun hs => ⟨_, Or.inr rfl, hs⟩)
      have hprc : IsCompact (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
        (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod isCompact_Icc
      have hNpc : IsClosed Np := by
        rw [← hf.image_eq]
        exact (hprc.image_of_continuousOn hfc).isClosed
      have hTbsub : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({-1, 1} : Set ℝ) ⊆
          Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
        refine prod_mono subset_rfl ?_
        rintro t (rfl | rfl) <;> constructor <;> norm_num
      have hTbc : IsCompact (f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({-1, 1} : Set ℝ))) :=
        ((Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod (Set.toFinite _).isCompact).image_of_continuousOn
          (hfc.mono hTbsub)
      have hzTb : f z ∉ f '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({-1, 1} : Set ℝ)) := by
        rintro ⟨w, hw, hwz⟩
        have heq : w = z := hf.bijOn.injOn (hTbsub hw) hz hwz
        rcases hw.2 with h1 | h1
        · exact (heq ▸ hz2).1.ne' h1
        · exact (heq ▸ hz2).2.ne h1
      have hMint : ∀ᶠ y' in 𝓝 (f z), y' ∈ Np → y' ∉ frontier XK.space → Np ∈ 𝓝 y' := by
        filter_upwards [hTbc.isClosed.isOpen_compl.mem_nhds hzTb] with y' hy' hy'N hy'X
        rw [← hf.image_eq] at hy'N
        obtain ⟨w, hw, rfl⟩ := hy'N
        have hw1 : w.1 ∉ stdSimplexBoundary 2 := fun h1 => hy'X ((hwiff w hw).mpr h1)
        have hw2 : w.2 ∈ Ioo (-1 : ℝ) 1 := by
          refine ⟨lt_of_le_of_ne hw.2.1 fun h1 => hy' ⟨w, ⟨hw.1, Or.inl h1.symm⟩, rfl⟩,
            lt_of_le_of_ne hw.2.2 fun h1 => hy' ⟨w, ⟨hw.1, Or.inr h1⟩, rfl⟩⟩
        exact mem_interior_iff_mem_nhds.mp (prism_mem_interior_image hf ⟨hw.1, hw1⟩ hw2)
      have hMy : f z ∈ closure (Np \ frontier XK.space) := by
        let S₀ : Set ((Fin 3 → ℝ) × ℝ) := openSimplex (stdVertices 1) ×ˢ {z.2}
        have hS₀sub : S₀ ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
          rintro w ⟨hw1, hw2⟩
          exact ⟨openSimplex_stdVertices_subset_stdSimplex (n := 1) hw1,
            (mem_singleton_iff.mp hw2) ▸ hz.2⟩
        have hzS : z ∈ closure S₀ := by
          rw [closure_prod_eq]
          exact ⟨stdSimplex_subset_closure_openSimplex 1 hz.1, subset_closure rfl⟩
        refine closure_mono ?_ (((hfc z hz).mono hS₀sub).mem_closure_image hzS)
        rintro _ ⟨w, hw, rfl⟩
        exact ⟨hf.bijOn.mapsTo (hS₀sub hw), fun hX =>
          notMem_stdSimplexBoundary_of_mem_openSimplex hw.1 ((hwiff w (hS₀sub hw)).mp hX)⟩
      obtain ⟨Dk, W, q₀, hq₀, hDk, hW, hyW, hWDk, hbdk⟩ := h2.exists_sideDisk hd he hcard
        ⟨hye, hyX⟩ hSd hNpc hNpSd hMint hMy (hOthc.isOpen_compl.mem_nhds hyOth)
      exact ⟨Dk, W, q₀, hq₀, fun d hd' => ⟨(hDk hd').1.1, (hDk hd').1.2⟩, hW, hyW, hWDk, hbdk⟩
    · have hyX : f z ∉ frontier XK.space := fun hX => hz1 ((hwiff z hz).mp hX)
      have hint : f z ∈ interior Np := prism_mem_interior_image hf ⟨hz.1, hz1⟩ hz2
      have hO : interior Np ∩ (frontier XK.space)ᶜ ∈ 𝓝 (f z) :=
        (isOpen_interior.inter isClosed_frontier.isOpen_compl).mem_nhds ⟨hint, hyX⟩
      obtain ⟨Dk, W, q₀, hq₀, hDk, hW, hyW, hWDk, hWbd⟩ := hpc.exists_localDisk hyE hyP hO
      refine ⟨Dk, W, q₀, hq₀, fun d hd' => ⟨(hDk hd').1, interior_subset (hDk hd').2.1⟩, hW,
        hyW, fun d hd' => hWDk ⟨hd'.1.1, hd'.1.2⟩, fun d hd' => ?_⟩
      exact ⟨fun hq => absurd hq (Set.disjoint_left.mp hWbd hd'.1),
        fun hX => absurd hX (hDk hd'.2).2.2⟩
  have hDkN : Dk ⊆ Np := fun d hd' => (hDk hd').2
  have hDkpoly : IsPolyhedron Dk := IsPLBall.isPolyhedron (n := 2) ⟨q₀, hq₀⟩
  have hq : IsPLHomeomorphOn (g ∘ q₀) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (g '' Dk) :=
    hq₀.trans (hg.restrict hDkpoly hDkN)
  obtain ⟨U, hU, hUeq⟩ := _root_.continuousOn_iff'.mp hfc (W ∩ Othᶜ)
    (hW.inter hOthc.isOpen_compl)
  have hmemU : ∀ w ∈ U, w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 → f w ∈ W ∧ f w ∉ Oth :=
    fun w hwU hw => (hUeq.symm.subset ⟨hwU, hw⟩).1
  refine ⟨g '' Dk, U, g ∘ q₀, hq, ?_, hU, (hUeq.subset ⟨⟨hyW, hyOth⟩, hz⟩).1, ?_, ?_⟩
  · rintro _ ⟨d, hd', rfl⟩
    exact ⟨hg.bijOn.mapsTo (hDkN hd'), show f (g d) ∈ A by
      rw [hfg d (hDkN hd')]
      exact hEA (hDk hd').1⟩
  · rintro w ⟨hwU, hwpr, hwA⟩
    obtain ⟨hwW, hwO⟩ := hmemU w hwU hwpr
    have hwD : f w ∈ Dk := hWDk ⟨⟨hwW, hAOth _ hwA hwO⟩, hf.bijOn.mapsTo hwpr⟩
    exact ⟨f w, hwD, hgf w hwpr⟩
  · rintro w ⟨hwU, d, hd', rfl⟩
    have hdN := hDkN hd'
    have hgpr : g d ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := hg.bijOn.mapsTo hdN
    have hdW : d ∈ W := by
      have := (hmemU _ hwU hgpr).1
      rwa [hfg d hdN] at this
    rw [← hwiff _ hgpr, hfg d hdN, ← hbdk d ⟨hdW, hd'⟩]
    constructor
    · rintro ⟨x, hx, hxd⟩
      have hqx : q₀ x ∈ Np := hDkN (hq₀.bijOn.mapsTo hx.1)
      have := congrArg f hxd
      simp only [Function.comp_apply] at this
      rw [hfg _ hqx, hfg d hdN] at this
      exact ⟨x, hx, this⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩

open Classical in
theorem IsPolyhedralTubeNeighborhood.exists_isLoopTheoremDisk_levelSet
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK) {Δ : Set E3}
    (hΔ : IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ) :
    ∃ (Δ' : Set E3) (Cs : Set (Set E3)),
      IsLoopTheoremDisk (h '' K.space) N' (frontier XK.space) Δ' ∧ Cs.Finite ∧
      Cs.PairwiseDisjoint id ∧
      Δ' ∩ (⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) = ⋃₀ Cs ∧
      ∀ S ∈ Cs, (IsPLSphere 1 S ∧ Disjoint S (frontier XK.space)) ∨
        ∃ q : (Fin 2 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S ∧
          q '' stdSimplexBoundary 1 = S ∩ frontier XK.space := by
  have : Finite XK.faces := h2.facesFinite.to_subtype
  have hXc : IsClosed XK.space := (isPolyhedron_space XK).isClosed
  set A := ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e with hAdef
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  have hAc : IsClosed A := hfin.isClosed_biUnion fun f hf => (hd.pseudoCell f hf.1 hf.2).isClosed
  obtain ⟨r, hr, hΔsub, hΔB, hb, hnull⟩ := hΔ
  have hKc : IsClosed (h '' K.space) := hd.tube.isCompact_image_space.isClosed
  have hV : IsOpen (interior N' \ h '' K.space) := isOpen_interior.sdiff hKc
  obtain ⟨Np, f, hf, hNpV, hzero, hwall, -⟩ :=
    exists_prism_of_inter_frontier_eq XK h2.isManifold hV hr hΔsub hΔB
  have hprc : IsCompact (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).prod isCompact_Icc
  have hfc : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) :=
    hf.isPiecewiseAffineOn.continuousOn
  have hwiff : ∀ w ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1,
      f w ∈ frontier XK.space ↔ w.1 ∈ stdSimplexBoundary 2 :=
    fun w hw => prism_mem_wall_iff hf hwall hw
  have hside := prism_subset_or_subset hf hXc hwall
  set P : Set ((Fin 3 → ℝ) × ℝ) := (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1) ∩ f ⁻¹' A
    with hPdef
  have hPc : IsClosed P := hfc.preimage_isClosed_of_isClosed hprc.isClosed hAc
  set Cm : Set ((Fin 3 → ℝ) × ℝ) := P ∩ {w | w.2 ∈ Icc (-(1 / 2) : ℝ) (1 / 2)} with hCmdef
  have hCmc : IsCompact Cm := hprc.of_isClosed_subset
    (hPc.inter (isClosed_Icc.preimage continuous_snd)) fun w hw => hw.1.1
  have hloc : ∀ z ∈ Cm, ∃ (Q U : Set ((Fin 3 → ℝ) × ℝ))
      (q : (Fin 3 → ℝ) → (Fin 3 → ℝ) × ℝ), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Q ∧
      Q ⊆ P ∧ IsOpen U ∧ z ∈ U ∧ U ∩ P ⊆ Q ∧
      ∀ w ∈ U ∩ Q, (w ∈ q '' stdSimplexBoundary 2 ↔ w.1 ∈ stdSimplexBoundary 2) :=
    fun z hz => h2.exists_prism_localDisk hd hf hNpV hwall hside hz.1.1 hz.1.2
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  choose! Q U q hq hQP hU hzU hUQ hQbd using hloc
  obtain ⟨t, htCm, hcover⟩ :=
    hCmc.elim_nhds_subcover U fun z hz => (hU z hz).mem_nhds (hzU z hz)
  have hQpoly : ∀ j : t, IsPolyhedron (Q j) :=
    fun j => IsPLBall.isPolyhedron (n := 2) ⟨q j, hq j (htCm j j.2)⟩
  obtain ⟨T₀, hT₀fin, hT₀⟩ := (IsPolyhedron.iUnion hQpoly).exists_simplicialComplex
  have : Finite T₀.faces := hT₀fin.to_subtype
  obtain ⟨T, hTT₀, hTfin, hTQ, -⟩ := exists_isSubdivision_subcomplexes_closedStars_subset_openStar
    T₀ (fun j : t => Q j) hQpoly fun j => hT₀ ▸ subset_iUnion (fun j : t => Q j) j
  have : Finite T.faces := hTfin.to_subtype
  have hTspace : T.space = ⋃ j : t, Q j := hTT₀.space_eq.trans hT₀
  have hTP : T.space ⊆ P := by
    rw [hTspace]
    exact iUnion_subset fun j => hQP j (htCm j j.2)
  have hlev : ∀ x ∈ P, x.2 ∈ Icc (-(1 / 2) : ℝ) (1 / 2) →
      ∃ j : t, x ∈ U j ∧ x ∈ Q j := by
    intro x hxP hx2
    obtain ⟨z, hzt, hxz⟩ := mem_iUnion₂.mp (hcover ⟨hxP, hx2⟩)
    exact ⟨⟨z, hzt⟩, hxz, hUQ z (htCm z hzt) ⟨hxz, hxP⟩⟩
  have hvf : ((fun v : (Fin 3 → ℝ) × ℝ => v.2) '' T.vertices).Finite :=
    (hTfin.preimage Finset.singleton_injective.injOn).image _
  obtain ⟨r₀, ⟨hr₀1, hr₀2⟩, hr₀v⟩ :=
    ((Ioo_infinite (by norm_num : (-(1 / 2) : ℝ) < 1 / 2)).sdiff hvf).nonempty
  have hr₀I : r₀ ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hr₀J : r₀ ∈ Icc (-(1 / 2) : ℝ) (1 / 2) := ⟨hr₀1.le, hr₀2.le⟩
  let ℓ : (Fin 3 → ℝ) × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ (Fin 3 → ℝ) ℝ
  have hℓ : ℓ ≠ 0 := by
    intro h0
    have h1 := LinearMap.congr_fun h0 ((0 : Fin 3 → ℝ), (1 : ℝ))
    simp [ℓ] at h1
  have hdimE : Module.finrank ℝ ((Fin 3 → ℝ) × ℝ) = 3 + 1 := by simp [Module.finrank_prod]
  have hUT : ∀ j : t, U j ∩ T.space ⊆ Q j :=
    fun j x hx => hUQ j (htCm j j.2) ⟨hx.1, hTP hx.2⟩
  have hcof := fun j : t =>
    restrict_isPLBall_cofaces T (hq j (htCm j j.2)) (hTQ j) (hU j (htCm j j.2)) (hUT j)
  have hlevT : ∀ x ∈ T.space, ℓ x = r₀ → ∃ j : t, x ∈ U j ∧ x ∈ Q j := fun x hx hxr =>
    hlev x (hTP hx) (show x.2 ∈ Icc (-(1 / 2) : ℝ) (1 / 2) from (show x.2 = r₀ from hxr) ▸ hr₀J)
  obtain ⟨G, hGfin, hGspace, hGcard, hGW, hGdeg⟩ := exists_levelComplex_of_cofaces T hdimE ℓ hℓ
    (r := r₀) (fun v hv hvr => hr₀v ⟨v, hv, hvr⟩)
    (fun s hs ⟨x, hxs, hxr⟩ => by
      obtain ⟨j, hxU, -⟩ := hlevT x (T.convexHull_subset_space hs hxs) hxr
      exact (hcof j).1 s hs ⟨x, hxs, hxU⟩)
    {w | w.1 ∈ stdSimplexBoundary 2}
    (fun s hs hs2 x hx hxr => by
      obtain ⟨j, hxU, hxQ⟩ :=
        hlevT x (T.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)) hxr
      have hiff := hQbd j (htCm j j.2) x ⟨hxU, hxQ⟩
      obtain ⟨h1, h2'⟩ := (hcof j).2.1 s hs hs2 x hx hxU
      exact ⟨fun hW => h1 (hiff.mpr hW), fun hW => h2' fun hq' => hW (hiff.mp hq')⟩)
    (fun s hs hs3 x hx hxr hW => by
      obtain ⟨j, hxU, hxQ⟩ :=
        hlevT x (T.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)) hxr
      exact (hcof j).2.2 s hs hs3 x hx hxU ((hQbd j (htCm j j.2) x ⟨hxU, hxQ⟩).mpr hW))
  have : Finite G.faces := hGfin.to_subtype
  obtain ⟨CT, hCTfin, hCTdisj, hGC, hCT⟩ :=
    exists_finite_circle_arc_decomposition_of_neighbors G hGcard _ hGW hGdeg
  have hCTpr : ∀ S ∈ CT, S ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (-1 : ℝ) 1 := by
    intro S hS w hw
    have hwG : w ∈ G.space := hGC ▸ mem_sUnion_of_mem hw hS
    rw [hGspace] at hwG
    exact (hTP hwG.1).1
  have hlevel : (fun x => f (x, r₀)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ∩ A = f '' G.space := by
    rw [hGspace]
    apply Subset.antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxA⟩
      have hxP : (x, r₀) ∈ P := ⟨⟨hx, hr₀I⟩, hxA⟩
      obtain ⟨j, -, hxQ⟩ := hlev (x, r₀) hxP hr₀J
      exact ⟨(x, r₀), ⟨hTspace ▸ mem_iUnion.mpr ⟨j, hxQ⟩, rfl⟩, rfl⟩
    · rintro _ ⟨w, ⟨hwT, hwr⟩, rfl⟩
      have hwP := hTP hwT
      refine ⟨⟨w.1, hwP.1.1, ?_⟩, hwP.2⟩
      change f (w.1, r₀) = f w
      rw [show r₀ = w.2 from hwr.symm]
  have hΔ'B := prism_level_inter_eq hf hwall hr₀I
  have hbs : (fun x => f (x, r₀)) '' stdSimplexBoundary 2 ⊆ frontier XK.space := by
    rw [← hΔ'B]
    exact inter_subset_right
  refine ⟨(fun x => f (x, r₀)) '' Convexity.StdSimplex.coordinateSet ℝ (Fin 3), (fun S => f '' S) '' CT,
    ⟨fun x => f (x, r₀), isPLHomeomorphOn_prism_level hf hr₀I, ?_, hΔ'B, hbs,
      not_nullhomotopic_prism_level hf hwall hr hzero hb hnull hr₀I hbs⟩,
    hCTfin.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hNpV (hf.bijOn.mapsTo ⟨hx, hr₀I⟩)
  · rintro _ ⟨S₁, h1, rfl⟩ _ ⟨S₂, h2', rfl⟩ hne
    have hS : S₁ ≠ S₂ := fun heq => hne (heq ▸ rfl)
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb', hba⟩
    have heq : b = a := hf.bijOn.injOn (hCTpr S₂ h2' hb') (hCTpr S₁ h1 ha) hba
    exact Set.disjoint_left.mp (hCTdisj h1 h2' hS) ha (heq ▸ hb')
  · rw [hlevel, hGC, image_sUnion]
  · rintro _ ⟨S, hS, rfl⟩
    have hSpr := hCTpr S hS
    rcases hCT S hS with ⟨hsph, hdisj⟩ | ⟨qa, hqa, hqaW⟩
    · refine Or.inl ⟨hsph.of_isPLHomeomorphOn (hf.restrict hsph.isPolyhedron hSpr), ?_⟩
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨w, hw, rfl⟩ hX
      exact Set.disjoint_left.mp hdisj hw ((hwiff w (hSpr hw)).mp hX)
    · have hSpoly : IsPolyhedron S := IsPLBall.isPolyhedron (n := 1) ⟨qa, hqa⟩
      refine Or.inr ⟨f ∘ qa, hqa.trans (hf.restrict hSpoly hSpr), ?_⟩
      rw [image_comp, hqaW]
      ext y
      constructor
      · rintro ⟨w, ⟨hwS, hwW⟩, rfl⟩
        exact ⟨mem_image_of_mem f hwS, (hwiff w (hSpr hwS)).mpr hwW⟩
      · rintro ⟨⟨w, hwS, rfl⟩, hX⟩
        exact ⟨w, ⟨hwS, (hwiff w (hSpr hwS)).mp hX⟩, rfl⟩

end LevelSet

end DifferentialGeometry.Topology.PiecewiseLinear
