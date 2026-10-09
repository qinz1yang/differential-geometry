/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryCrossingChart
import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem notMem_boundaryComplex_faces_of_lt_card (K : Geometry.SimplicialComplex ℝ E) {n : ℕ}
    {t : Finset E} (hcard : n < t.card) : t ∉ (boundaryComplex n K).faces := by
  rintro ⟨-, v, -, htv, hvn, -⟩
  have hle := Finset.card_le_card htv
  omega

open Classical in
theorem hasPLTwoSidedCrossingAt_of_codimension_one [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 3) {x : E} (hxs : x ∈ openSimplex s)
    (hxt : x ∈ openSimplex t) (hsB : s ∉ (boundaryComplex 2 K).faces)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    HasPLTwoSidedCrossingAt K.space L.space x := by
  let S := vectorSpan ℝ (s : Set E)
  let T := vectorSpan ℝ (t : Set E)
  have hSdim : Module.finrank ℝ S = 1 := by
    have hrank := (K.indep hs).finrank_vectorSpan (show Fintype.card s = 1 + 1 by
      simpa only [Fintype.card_coe] using hsc)
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) = 1 at hrank
    rwa [hrange] at hrank
  have hTdim : Module.finrank ℝ T = 2 := by
    have hrank := (L.indep ht).finrank_vectorSpan (show Fintype.card t = 2 + 1 by
      simpa only [Fintype.card_coe] using htc)
    have hrange : Set.range ((↑) : t → E) = (t : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) = 2 at hrank
    rwa [hrange] at hrank
  have htmax : ∀ v ∈ L.faces, t ⊆ v → v.card ≤ t.card := by
    intro v hv _
    rw [htc]
    exact hL.card_le L hv
  have hbound : ∀ v ∈ K.faces, s ⊆ v → v.card ≤ s.card + 1 := by
    intro v hv _
    have hle := hK.card_le K hv
    omega
  obtain ⟨a, b, hab, habset⟩ := hK.codimension_one_cofaces_of_notMem_boundary K hs hsc hsB
  obtain ⟨u, h, huT, hu, hh, hhx, hTiff, hfull⟩ :=
    exists_isPLHomeomorphOn_linearize_coface_pair K hs hbound hxs hab habset T hcompl
  have huS : u ∉ S := fun hmem => hu (Submodule.disjoint_def.mp hcompl.disjoint _ hmem huT)
  let P : Submodule ℝ E := S ⊔ Submodule.span ℝ {u}
  have hspan1 : Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) = 1 := finrank_span_singleton hu
  have hI0 : Module.finrank ℝ (S ⊓ Submodule.span ℝ {u} : Submodule ℝ E) = 0 :=
    Submodule.finrank_eq_zero.mpr (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem
      huS))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {u})
  have hPdim : Module.finrank ℝ P = 2 := by
    change Module.finrank ℝ P + Module.finrank ℝ (S ⊓ Submodule.span ℝ {u} : Submodule ℝ E) =
      Module.finrank ℝ S + Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) at hdim
    omega
  have hPQT : P ⊔ T = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le_sup le_sup_left le_rfl
  have hdimPT := Submodule.finrank_sup_add_finrank_inf_eq P T
  rw [hPQT] at hdimPT
  have hIdim : Module.finrank ℝ (P ⊓ T : Submodule ℝ E) = 1 := by
    have hdim' : Module.finrank ℝ E + Module.finrank ℝ (P ⊓ T : Submodule ℝ E) =
        Module.finrank ℝ P + Module.finrank ℝ T := by simpa using hdimPT
    omega
  have hLmodel : ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ h y ∈ T := by
    filter_upwards [eventually_mem_space_iff_sub_mem_vectorSpan L ht htmax hxt] with y hy
    exact hy.trans (hTiff y)
  refine ⟨univ, univ, h, P, T, isOpen_univ, isOpen_univ, mem_univ x, hh, hhx, hPdim, hTdim,
    hIdim, hPQT, ?_⟩
  filter_upwards [hfull, hLmodel] with y hyK hyL
  exact ⟨hyK, hyL⟩

open Classical in
theorem hasPLTwoSidedCrossingAt_of_codimension_one_of_isCombinatorialManifold
    [FiniteDimensional ℝ E] (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    [Finite L.faces] (hK : IsCombinatorialManifold 2 K)
    (hL : IsCombinatorialManifoldWithBoundary 2 L) (hdimE : Module.finrank ℝ E = 3)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hsc : s.card = 2) (htc : t.card = 3)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    HasPLTwoSidedCrossingAt K.space L.space x := by
  refine hasPLTwoSidedCrossingAt_of_codimension_one K L hK.isCombinatorialManifoldWithBoundary hL
    hdimE hs ht hsc htc hxs hxt ?_ hcompl
  have hempty : (boundaryComplex 2 K).faces = ∅ := hK.boundaryComplex_faces_eq_empty K
  rw [hempty]
  exact Set.notMem_empty s

end DifferentialGeometry.Topology.PiecewiseLinear
