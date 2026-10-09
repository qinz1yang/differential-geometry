/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainOpenCellCap
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.AnnularChainRimTails

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {φ : E3 → E3} {Pt : ℤ → E3}
  {Dp Dpint J A S T S'' T'' H B Jlo Jhi : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' : E3}

theorem IsAnnularChain.locallyFinite_annuli
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    LocallyFinite (fun i =>
      (Subtype.val : (⋃ j, H j ∪ B j) → E3) ⁻¹' (H i ∪ B i)) := by
  intro x
  have hxI : (x : E3) ∈ I := hch.annularChain_subset_interior htw (Or.inl x.property)
  have hxP : (x : E3) ≠ P' := by
    intro heq
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    exact hch.centerNotMem i (heq ▸ hi)
  obtain ⟨U, hU, hF⟩ := htw.locallyFinite x hxI hxP
  let F : Set ℤ := {j | ((φ '' S j) ∩ U).Nonempty}
  have hfinite (k : ℤ) : {i : ℤ | 2 * i + k ∈ F}.Finite := by
    change ((fun i : ℤ => 2 * i + k) ⁻¹' F).Finite
    apply Set.Finite.preimage (s := F) ?_ hF
    intro i _ j _ hij
    dsimp at hij
    omega
  let L : Set ℤ := {i | 2 * i ∈ F} ∪
    {i | 2 * i + 1 ∈ F} ∪ {i | 2 * i + 2 ∈ F}
  have hL : L.Finite := by
    have h₀ : {i : ℤ | 2 * i ∈ F}.Finite := by simpa using hfinite 0
    exact (h₀.union (hfinite 1)).union (hfinite 2)
  refine ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt hU, hL.subset ?_⟩
  rintro i ⟨y, hy, hyU⟩
  rcases hy with hyH | hyB
  · exact Or.inl (Or.inl ⟨y, hch.halfSubsetTorus i hyH, hyU⟩)
  · rcases hch.bridgeSubset i hyB with (h₀ | h₁) | h₂
    · exact Or.inl (Or.inl ⟨y, h₀, hyU⟩)
    · exact Or.inl (Or.inr ⟨y, h₁, hyU⟩)
    · exact Or.inr ⟨y, h₂, hyU⟩

theorem IsAnnularChain.exists_cylinder_homeomorph
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    ∃ c : (stdSimplexBoundary 2 × ℝ) ≃ₜ (⋃ i, H i ∪ B i),
      ∀ i : ℤ, (fun p => (c p : E3)) '' (univ ×ˢ Icc (i : ℝ) ((i : ℝ) + 1)) =
        H i ∪ B i := by
  classical
  have hcompact : IsCompact (stdSimplexBoundary 2) := by
    have hc : IsClosed (⋃ i : Fin 3, {x : Fin 3 → ℝ | x i = 0}) :=
      isClosed_iUnion_of_finite fun i => isClosed_eq (continuous_apply i) continuous_const
    convert (Convexity.StdSimplex.isCompact_coordinateSet ℝ (Fin 3)).inter_right hc using 1
    ext x
    simp [stdSimplexBoundary]
  let : CompactSpace (stdSimplexBoundary 2) := isCompact_iff_compactSpace.mp hcompact
  have ha (i : ℤ) : IsPLAnnulusWithEnds (H i ∪ B i) (Jhi (i - 1)) (Jhi i) :=
    (hch.half i).union (hch.bridge i) (hch.halfInterBridge i)
  choose e he₀ he₁ using fun i => (ha i).exists_homeomorph
  have hseam₀ (i : ℤ) : range (fun x => (e i (x, 1) : E3)) =
      range (fun x => (e (i + 1) (x, 0) : E3)) := by
    rw [he₁, he₀]
    congr 1
    omega
  obtain ⟨e', hseam, hrange⟩ := exists_compatible_annulus_homeomorphs e hseam₀
  have hinter (i : ℤ) : (H i ∪ B i) ∩ (H (i + 1) ∪ B (i + 1)) = Jhi i := by
    ext x
    constructor
    · rintro ⟨hH | hB, hH' | hB'⟩
      · exact False.elim (Set.disjoint_left.mp (hch.halfDisjoint i (i + 1) (by omega))
          hH hH')
      · exact False.elim (Set.disjoint_left.mp
          (hch.halfBridgeDisjoint i (i + 1) (by omega) (by omega)) hH hB')
      · exact hch.bridgeInterHalf i ▸ ⟨hB, hH'⟩
      · exact False.elim (Set.disjoint_left.mp (hch.bridgeDisjoint i (i + 1) (by omega))
          hB hB')
    · intro hx
      have hx' : x ∈ B i ∩ H (i + 1) := (hch.bridgeInterHalf i).symm ▸ hx
      exact ⟨Or.inr hx'.1, Or.inl hx'.2⟩
  have hdisj (i j : ℤ) (hij : 2 ≤ |i - j|) :
      Disjoint (H i ∪ B i) (H j ∪ B j) := by
    rw [le_abs] at hij
    apply Set.disjoint_left.mpr
    rintro x (hx | hx) (hy | hy)
    · exact Set.disjoint_left.mp (hch.halfDisjoint i j (by omega)) hx hy
    · exact Set.disjoint_left.mp (hch.halfBridgeDisjoint i j (by omega) (by omega)) hx hy
    · exact Set.disjoint_left.mp (hch.halfBridgeDisjoint j i (by omega) (by omega)) hy hx
    · exact Set.disjoint_left.mp (hch.bridgeDisjoint i j (by omega)) hx hy
  obtain ⟨c, hc⟩ := exists_annulus_chain_cylinder_homeomorph e' hseam
    (fun i => (hinter i).trans ((hrange i 1).trans (he₁ i)).symm) hdisj
    (hch.locallyFinite_annuli htw)
  refine ⟨c, fun i => ?_⟩
  ext y
  constructor
  · rintro ⟨⟨x, t⟩, ⟨_, ht⟩, rfl⟩
    let s : unitInterval := ⟨t - i, by constructor <;> linarith [ht.1, ht.2]⟩
    have ht' : t = (i : ℝ) + s := by dsimp [s]; ring
    change (c (x, t) : E3) ∈ H i ∪ B i
    rw [ht', hc]
    exact (e' i (x, s)).property
  · intro hy
    obtain ⟨⟨x, s⟩, hs⟩ := (e' i).surjective ⟨y, hy⟩
    refine ⟨(x, (i : ℝ) + s), ⟨mem_univ _, ?_⟩,
      (hc i x s).trans (congrArg Subtype.val hs)⟩
    constructor <;> linarith [s.property.1, s.property.2]

theorem IsAnnularChain.exists_lower_annuli_subset
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hI : IsCompact (closure I)) {V : Set E3} (hV : IsOpen V) (hP : P' ∈ V) :
    ∃ m : ℤ, ∀ i, i ≤ m → H i ∪ B i ⊆ V := by
  obtain ⟨n, hn⟩ := htw.exists_lower_tail_subset hI hV hP
  refine ⟨min 0 (n - 2), fun i hi x hx => ?_⟩
  have hi₀ : i ≤ 0 := hi.trans (min_le_left _ _)
  have hin : i ≤ n - 2 := hi.trans (min_le_right _ _)
  rcases hx with hx | hx
  · exact hn (2 * i) (by omega) (hch.halfSubsetTorus i hx)
  · rcases hch.bridgeSubset i hx with (h₀ | h₁) | h₂
    · exact hn (2 * i) (by omega) h₀
    · exact hn (2 * i + 1) (by omega) h₁
    · exact hn (2 * i + 2) (by omega) h₂

theorem IsAnnularChain.notMem_closure_upper_annuli
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hP : P' ∉ Dbdimg) (m : ℤ) :
    P' ∉ closure (⋃ i, ⋃ (_ : m ≤ i), H i ∪ B i) := by
  have hn : ∃ n : ℤ, P' ∉ closure (⋃ i, ⋃ (_ : n ≤ i), φ '' S i) := by
    by_contra hn
    push Not at hn
    exact hP (htw.iInter_closure_upper_eq ▸ mem_iInter.mpr hn)
  obtain ⟨n, hn⟩ := hn
  let k : ℤ := max 0 n
  let F : Set E3 := ⋃ i ∈ Icc m k, H i ∪ B i
  have hFclosed : IsClosed F := (finite_Icc m k).isClosed_biUnion fun i _ =>
    (hch.half_isPolyhedron i).isClosed.union (hch.bridge_isPolyhedron i).isClosed
  have hPF : P' ∉ F := by
    intro hp
    obtain ⟨i, _, hi⟩ := mem_iUnion₂.mp hp
    exact hch.centerNotMem i hi
  have hsub : (⋃ i, ⋃ (_ : m ≤ i), H i ∪ B i) ⊆
      F ∪ closure (⋃ i, ⋃ (_ : n ≤ i), φ '' S i) := by
    intro x hx
    obtain ⟨i, hmi, hi⟩ := mem_iUnion₂.mp hx
    by_cases hik : i ≤ k
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, ⟨hmi, hik⟩, hi⟩)
    · have hi₀ : 0 ≤ i := (le_max_left 0 n).trans (not_le.mp hik).le
      have hni : n ≤ i := (le_max_right 0 n).trans (not_le.mp hik).le
      apply Or.inr
      apply subset_closure
      rcases hi with hi | hi
      · exact mem_iUnion₂.mpr ⟨2 * i, by omega, hch.halfSubsetTorus i hi⟩
      · rcases hch.bridgeSubset i hi with (h₀ | h₁) | h₂
        · exact mem_iUnion₂.mpr ⟨2 * i, by omega, h₀⟩
        · exact mem_iUnion₂.mpr ⟨2 * i + 1, by omega, h₁⟩
        · exact mem_iUnion₂.mpr ⟨2 * i + 2, by omega, h₂⟩
  intro hp
  exact (closure_minimal hsub (hFclosed.union isClosed_closure) hp).elim hPF hn

theorem IsAnnularChain.isOpenTopologicalCell
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P')
    (hI : IsCompact (closure I)) (hP : P' ∉ Dbdimg) :
    IsOpenTopologicalCell 2 (annularChain H B P') := by
  classical
  obtain ⟨c, hc⟩ := hch.exists_cylinder_homeomorph htw
  obtain ⟨J₀, ρ, hJ₀, _, _, _⟩ := hch.half 0
  obtain ⟨a₀⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJ₀
  obtain ⟨q, hq⟩ := hJ₀
  let b : loopCircle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).trans
      (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
        change z ∈ Metric.sphere (0 : ℂ) 1 ↔
          Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
        rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
          Complex.orthonormalBasisOneI.repr.norm_map])
  let a : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ stdSimplexBoundary 2 :=
    b.symm.trans (a₀.trans hq.homeomorph.symm)
  have hPc : P' ∉ ⋃ i, H i ∪ B i := by
    intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact hch.centerNotMem i hi
  have hband (z : stdSimplexBoundary 2 × ℝ) :
      (c z : E3) ∈ H ⌊z.2⌋ ∪ B ⌊z.2⌋ := by
    apply (hc ⌊z.2⌋).subset
    exact mem_image_of_mem _ ⟨mem_univ _, Int.floor_le _, (Int.lt_floor_add_one _).le⟩
  have hlower : ∀ V : Set E3, IsOpen V → P' ∈ V →
      ∃ b : ℝ, ∀ z : stdSimplexBoundary 2 × ℝ, z.2 ≤ b → (c z : E3) ∈ V := by
    intro V hV hPV
    obtain ⟨m, hm⟩ := hch.exists_lower_annuli_subset htw hI hV hPV
    refine ⟨m, fun z hz => hm ⌊z.2⌋ ?_ (hband z)⟩
    exact_mod_cast (Int.floor_le z.2).trans hz
  have hupper : ∀ b : ℝ,
      P' ∉ closure ((fun z => (c z : E3)) '' (univ ×ˢ Ici b)) := by
    intro b hp
    apply hch.notMem_closure_upper_annuli htw hP ⌊b⌋
    apply closure_mono ?_ hp
    rintro y ⟨z, hz, rfl⟩
    exact mem_iUnion₂.mpr ⟨⌊z.2⌋, Int.floor_mono hz.2, hband z⟩
  obtain ⟨e⟩ := nonempty_homeomorph_of_cylinder_ends c a hPc hlower hupper
  exact ⟨e.symm.trans Homeomorph.unitBall⟩

theorem IsTube.image_centroid_notMem_image_splitRim
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3}
    (ht : IsTube K N C D Dbd h N') {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) :
    h (e.centroid ℝ id) ∉ h '' Dbd e := by
  have hc : e.centroid ℝ id ∈ D e ∩ K.space := by
    rw [ht.splitMidpoint he hcard]
    exact mem_singleton _
  have hcN : e.centroid ℝ id ∈ interior N :=
    (subset_interior_iff_mem_nhdsSet.mpr ht.isNeighborhood) hc.2
  rintro ⟨x, hx, heq⟩
  have hxfr : x ∈ frontier N := ((ht.splitProper e he hcard).symm.subset hx).2
  have hxc : x = e.centroid ℝ id := ht.injOn
    (ht.isClosed.closure_eq ▸ frontier_subset_closure hxfr) (interior_subset hcN) heq
  exact disjoint_left.mp disjoint_interior_frontier hcN (hxc ▸ hxfr)

theorem IsTube.isOpenTopologicalCell_annularChain
    {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3}
    {C : E3 → Set E3} {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3}
    (ht : IsTube K N C D Dbd h N') (hu : u ∈ K.vertices)
    (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (hP' : P' = h (({u, v} : Finset E3).centroid ℝ id))
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T''
      (h '' D {u, v}) (h '' Dbd {u, v}) W (interior (h '' C u ∪ h '' C v)) P')
    (hch : IsAnnularChain H B Jlo Jhi (fun i => φ '' S i) S'' T'' P') :
    IsOpenTopologicalCell 2 (annularChain H B P') := by
  apply hch.isOpenTopologicalCell htw (ht.isCompact_closure_interior_pair hu hv)
  rw [hP']
  exact ht.image_centroid_notMem_image_splitRim he (Finset.card_pair huv)

end DifferentialGeometry.Topology.PiecewiseLinear
