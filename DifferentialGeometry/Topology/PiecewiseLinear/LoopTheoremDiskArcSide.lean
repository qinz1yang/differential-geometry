/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamTubePages
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheoremDiskCircleStep

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_isPLHomeomorphOn_Icc_of_stdSimplex_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {S W : Set E} {q : (Fin 2 → ℝ) → E}
    (hq : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) S)
    (hqb : q '' stdSimplexBoundary 1 = S ∩ W) :
    ∃ g : ℝ → E, IsPLHomeomorphOn g (Icc 0 1) S ∧ ({g 0, g 1} : Set E) = S ∩ W := by
  let L : ℝ →ᵃ[ℝ] (Fin 2 → ℝ) := AffineMap.lineMap ![1, 0] ![0, 1]
  have hL0 : ∀ t : ℝ, L t 0 = 1 - t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
    ring
  have hL1 : ∀ t : ℝ, L t 1 = t := by
    intro t
    simp only [L, AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp
  have hLbij : BijOn L (Icc 0 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) := by
    refine ⟨fun t ht => ⟨fun i => ?_, ?_⟩, fun s _ t _ hst => ?_, fun x hx => ?_⟩
    · fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, hL0]
        linarith [ht.2]
      · simp only [Fin.mk_one, Fin.isValue, hL1]
        exact ht.1
    · rw [Fin.sum_univ_two, hL0, hL1]
      ring
    · have := congrFun hst 1
      rwa [hL1, hL1] at this
    · refine ⟨x 1, ⟨hx.1 1, ?_⟩, ?_⟩
      · have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
        linarith [hx.1 0]
      · funext j
        fin_cases j
        · simp only [Fin.zero_eta, Fin.isValue, hL0]
          have hsum : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx.2
          linarith
        · simp only [Fin.mk_one, Fin.isValue, hL1]
  have hLpl : IsPLHomeomorphOn L (Icc 0 1) (Convexity.StdSimplex.coordinateSet ℝ (Fin 2)) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      ((isPiecewiseAffineOn_of_affine L isOpen_univ).mono_of_isPolyhedron
        isHPolytope_Icc.isPolyhedron (subset_univ _)) hLbij
  refine ⟨q ∘ L, hLpl.trans hq, ?_⟩
  rw [← hqb, stdSimplexBoundary_one_eq_pair, image_pair]
  simp only [Function.comp_apply, L, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one]

theorem IsLoopTheoremDisk.of_isPLHomeomorphOn {Kimg N' B Δ S : Set E3}
    {r : (Fin 3 → ℝ) → E3} (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hsub : Δ ⊆ interior N' \ Kimg) (hΔB : Δ ∩ B = S) (hrS : r '' stdSimplexBoundary 2 = S)
    (hSB : S ⊆ B)
    (hnull : ¬ (⟨Set.inclusion hSB, continuous_inclusion hSB⟩ : C(S, B)).Nullhomotopic) :
    IsLoopTheoremDisk Kimg N' B Δ := by
  have key : ∀ T : Set E3, T = S →
      ∃ hT : T ⊆ B, ¬ (⟨Set.inclusion hT, continuous_inclusion hT⟩ : C(T, B)).Nullhomotopic := by
    rintro T rfl
    exact ⟨hSB, hnull⟩
  exact ⟨r, hr, hsub, hΔB.trans hrS.symm, key _ hrS⟩

section ArcSide

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}

theorem IsHandleDecompositionOfTube.handlePiece_inter_subset_pseudoCells
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {u w : E3}
    (hu : u ∈ K.vertices) (hw : w ∈ K.vertices) (huw : u ≠ w) :
    Cpp u ∩ Cpp w ⊆ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e := by
  classical
  by_cases hf : ({u, w} : Finset E3) ∈ K.faces
  · rw [hd.handleEdge u hu w hw huw hf]
    exact subset_iUnion₂ (s := fun e (_ : e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}) =>
      Ec e) {u, w} ⟨hf, Finset.card_pair huw⟩
  · rw [hd.handleNonEdge u hu w hw huw hf]
    exact empty_subset _

theorem IsHandleDecompositionOfTube.exists_handlePiece_near
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    {W : Set (EuclideanSpace ℝ (Fin 2))} (hW : IsPLBall 2 W)
    {ρ : EuclideanSpace ℝ (Fin 2) → E3} (hρ : ContinuousOn ρ W) (hρN : ρ '' W ⊆ interior N')
    {Bp W₀ : Set (EuclideanSpace ℝ (Fin 2))} (hBp : IsPreconnected Bp) (hBpne : Bp.Nonempty)
    (hBpW : Bp ⊆ W) (hW₀ : IsOpen W₀) (hBpW₀ : Bp ⊆ W₀)
    (hA : ∀ z ∈ interior W ∩ W₀,
      ρ z ∉ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) :
    ∃ v ∈ K.vertices, ∃ Wo : Set (EuclideanSpace ℝ (Fin 2)), IsOpen Wo ∧ Bp ⊆ Wo ∧
      ρ '' (W ∩ Wo) ⊆ Cpp v := by
  classical
  have hcl : closure (interior W) = W := hW.closure_interior
  have hloc : ∀ x ∈ Bp, ∃ V : Set (EuclideanSpace ℝ (Fin 2)), IsOpen V ∧ x ∈ V ∧ V ⊆ W₀ ∧
      ∃ v ∈ K.vertices, ρ '' (V ∩ interior W) ⊆ Cpp v := by
    intro x hx
    obtain ⟨V, hV, hxV, hVW₀, hVpre⟩ :=
      hW.exists_isOpen_isPreconnected_inter_interior (hBpW hx) (hW₀.mem_nhds (hBpW₀ hx))
    have hne : (V ∩ interior W).Nonempty := by
      have hxcl : x ∈ closure (interior W) := hcl.symm ▸ hBpW hx
      exact mem_closure_iff.mp hxcl V hV hxV
    obtain ⟨v, hv, hZv⟩ := hd.exists_subset_handlePiece
      (hVpre.image ρ (hρ.mono (inter_subset_right.trans interior_subset))) (hne.image ρ)
      (fun y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        exact hρN (mem_image_of_mem ρ (interior_subset hz.2)))
      (Set.disjoint_left.mpr fun y hy => by
        obtain ⟨z, hz, rfl⟩ := hy
        exact hA z ⟨hz.2, hVW₀ hz.1⟩)
    exact ⟨V, hV, hxV, hVW₀, v, hv, hZv⟩
  choose! V hV hxV hVW₀ v hv hZv using hloc
  have hsame : ∀ x ∈ Bp, ∀ y ∈ Bp, ∀ z ∈ Bp, z ∈ V x → z ∈ V y → v x = v y := by
    intro x hx y hy z hz hzx hzy
    by_contra hne
    have hzcl : z ∈ closure (interior W) := hcl.symm ▸ hBpW hz
    obtain ⟨w, ⟨hwx, hwy⟩, hwi⟩ :=
      mem_closure_iff.mp hzcl (V x ∩ V y) ((hV x hx).inter (hV y hy)) ⟨hzx, hzy⟩
    have h1 : ρ w ∈ Cpp (v x) := hZv x hx ⟨w, ⟨hwx, hwi⟩, rfl⟩
    have h2 : ρ w ∈ Cpp (v y) := hZv y hy ⟨w, ⟨hwy, hwi⟩, rfl⟩
    exact hA w ⟨hwi, hVW₀ x hx hwx⟩
      (hd.handlePiece_inter_subset_pseudoCells (hv x hx) (hv y hy) hne ⟨h1, h2⟩)
  obtain ⟨x₀, hx₀⟩ := hBpne
  set S₁ := ⋃ x ∈ {x | x ∈ Bp ∧ v x = v x₀}, V x with hS₁def
  set S₂ := ⋃ x ∈ {x | x ∈ Bp ∧ v x ≠ v x₀}, V x with hS₂def
  have hS₁o : IsOpen S₁ := isOpen_biUnion fun x hx => hV x hx.1
  have hS₂o : IsOpen S₂ := isOpen_biUnion fun x hx => hV x hx.1
  have hcov : Bp ⊆ S₁ ∪ S₂ := by
    intro z hz
    by_cases hzv : v z = v x₀
    · exact Or.inl (mem_iUnion₂.mpr ⟨z, ⟨hz, hzv⟩, hxV z hz⟩)
    · exact Or.inr (mem_iUnion₂.mpr ⟨z, ⟨hz, hzv⟩, hxV z hz⟩)
  have hdis : Bp ∩ (S₁ ∩ S₂) = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun z ⟨hz, h1, h2⟩ => ?_
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp h1
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp h2
    exact hy.2 ((hsame y hy.1 x hx.1 z hz hzy hzx).trans hx.2)
  rcases (isPreconnected_iff_subset_of_disjoint.mp hBp) S₁ S₂ hS₁o hS₂o hcov hdis with h1 | h1
  · refine ⟨v x₀, hv x₀ hx₀, S₁, hS₁o, h1, ?_⟩
    rintro _ ⟨z, ⟨hzW, hzS⟩, rfl⟩
    obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp hzS
    have hzcl : z ∈ closure (V x ∩ interior W) :=
      (hV x hx.1).inter_closure ⟨hzx, hcl.symm ▸ hzW⟩
    have hmem := ((hρ z hzW).mono (inter_subset_right.trans interior_subset)).mem_closure_image
      hzcl
    have hCc : IsClosed (Cpp (v x₀)) := by
      rw [hd.componentClosure (v x₀) (hv x₀ hx₀)]
      exact isClosed_closure
    rw [← hx.2]
    exact closure_minimal (hZv x hx.1) (hx.2 ▸ hCc) hmem
  · obtain ⟨y, hy, hx₀y⟩ := mem_iUnion₂.mp (h1 hx₀)
    exact absurd (hsame y hy.1 x₀ hx₀ x₀ hx₀ hx₀y (hxV x₀ hx₀)) hy.2

end ArcSide

end DifferentialGeometry.Topology.PiecewiseLinear
