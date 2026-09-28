/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicBallMeridians
import DifferentialGeometry.Topology.PiecewiseLinear.EssentialPolygonProductCoordinates
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicFaceCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem Section34CutFrame.intrinsic_splitDisk_meridian
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P : Set E3} {u : E3 → M₂}
    (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (e : Section34EdgeIndex 𝒦 𝒦') (he : Section34Incident e.1 s.1) :
    let D := Function.invFunOn u P '' section34SplitDiskImage src f₁ e
    let G := Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e
    (∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧ G = q '' stdSimplexBoundary 2) ∧
      D ⊆ P ∧ frontier P ∩ D = G ∧ D \ G ⊆ interior P ∧
      IsConnected (frontier P \ G) ∧
      ¬ ∃ (A : Set E3) (r : (Fin 3 → ℝ) → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧ A ⊆ frontier P ∧
          G = r '' stdSimplexBoundary 2 := by
  classical
  dsimp only
  let g := Function.invFunOn u P
  obtain ⟨n, v, -, -, hB, hnext, hedge, hdis, htriple, hcover⟩ :=
    exists_cycle_order_intrinsic_face_vertex_balls hcut hf₁ s hu hUP
  let B := fun i => g '' section34VertexBallImage src f₁ (v i)
  have hDT : section34SplitDiskImage src f₁ e ⊆ u '' P := by
    rw [hUP]
    exact hcut.splitDiskImage_subset_faceTorus hf₁ s e he
  obtain ⟨q, hq, hqb⟩ :=
    (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_invFunOn hu hDT
  obtain ⟨i, j, hij, hD⟩ := hedge e he
  have hqij : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (B i ∩ B j) := hD ▸ hq
  have hDb : IsPLBall 2 (B i ∩ B j) := ⟨q, hqij⟩
  have hDi : B i ∩ B j ⊆ frontier (B i) :=
    (hB j).inter_subset_frontier_of_isPLBall hDb (by norm_num)
  have hDj : B i ∩ B j ⊆ frontier (B j) := by
    rw [inter_comm]
    exact (hB i).inter_subset_frontier_of_isPLBall
      ((inter_comm (B i) (B j)) ▸ hDb) (by norm_num)
  have h3 : ∀ i j k, i ≠ j → k ≠ i → k ≠ j → Disjoint (B i ∩ B j) (B k) := by
    intro i j k hij hki hkj
    exact disjoint_iff_inter_eq_empty.mpr (htriple i j k hij hki.symm hkj.symm)
  have hGP : g '' section34SplitDiskImage srcBd f₁ e ⊆ frontier P := by
    rw [hqb, ← hcover]
    exact image_stdSimplexBoundary_subset_frontier_iUnion hB h3 hij.ne hqij hDi
  have hDP : g '' section34SplitDiskImage src f₁ e ⊆ P := by
    rw [hD]
    exact inter_subset_left.trans ((subset_iUnion B i).trans hcover.subset)
  have hDint : g '' section34SplitDiskImage src f₁ e \
      g '' section34SplitDiskImage srcBd f₁ e ⊆ interior P := by
    rw [hD, hqb]
    have hpair := sdiff_subset_interior_union_of_inter_eq (hB i) (hB j) hqij rfl hDi hDj
    exact hpair.trans (interior_mono (union_subset
      ((subset_iUnion B i).trans hcover.subset) ((subset_iUnion B j).trans hcover.subset)))
  have hmeet : frontier P ∩ g '' section34SplitDiskImage src f₁ e =
      g '' section34SplitDiskImage srcBd f₁ e := by
    apply Subset.antisymm
    · rintro x ⟨hxfr, hxD⟩
      by_contra hxG
      exact disjoint_left.mp disjoint_interior_frontier (hDint ⟨hxD, hxG⟩) hxfr
    · intro x hx
      exact ⟨hGP hx, image_mono (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset hx⟩
  have hnextB : ∀ i j, (SimpleGraph.cycleGraph (n + 3)).Adj i j →
      IsPLBall 2 (B i ∩ B j) := by
    intro i j hij
    obtain ⟨d, hd, hDd⟩ := hnext i j hij
    have hdP : section34SplitDiskImage src f₁ d ⊆ u '' P := by
      rw [hUP]
      exact hcut.splitDiskImage_subset_faceTorus hf₁ s d hd
    obtain ⟨r, hr, -⟩ :=
      (hcut.isPLCellOn_splitDiskImage hf₁ d).exists_isPLHomeomorphOn_invFunOn hu hdP
    exact ⟨r, hDd ▸ hr⟩
  have hess := cyclic_ball_seam_is_essential B hB hnextB hdis htriple hij hqij
  rw [hcover, ← hqb] at hess
  exact ⟨⟨q, hq, hqb⟩, hDP, hmeet, hDint, hess⟩

theorem split_disks_form_intrinsic_marked_meridian_system
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (s : Section34SimplexIndex 𝒦 3) {P : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (hUP : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s) :
    ∃ (J Q : Set E3) (f : E3 × E3 → E3)
      (p : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1} → E3),
      IsPLSphere 1 J ∧ IsPLSphere 1 Q ∧ IsPLHomeomorphOn f (J ×ˢ Q) (frontier P) ∧
      (∀ e, p e ∈ Q) ∧ Function.Injective p ∧
      (∀ e, Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e.1 =
        f '' (J ×ˢ {p e})) ∧
      ∀ e : {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1},
        Function.invFunOn u P '' section34SplitDiskImage src f₁ e.1 ⊆ P ∧
          frontier P ∩ Function.invFunOn u P '' section34SplitDiskImage src f₁ e.1 =
            Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e.1 ∧
          Function.invFunOn u P '' section34SplitDiskImage src f₁ e.1 \
            Function.invFunOn u P '' section34SplitDiskImage srcBd f₁ e.1 ⊆ interior P := by
  classical
  obtain ⟨-, hsubdiv, hmap, -⟩ := id hcut
  let I := {e : Section34EdgeIndex 𝒦 𝒦' // Section34Incident e.1 s.1}
  have hIfin := finite_setOf_section34Incident_graphIndex hsubdiv (graphSkeletonSpace 𝒦) 2 s.2.1
  let _ : Finite I := hIfin.to_subtype
  let _ : Fintype I := Fintype.ofFinite I
  obtain ⟨n, v, -, hv, -⟩ :=
    exists_cycle_order_intrinsic_face_vertex_balls hcut hf₁ s hu hUP
  obtain ⟨e₁, e₂, hne, he₁, he₂, -⟩ :=
    exists_section34EdgeIndex_pair_of_incident hsubdiv hmap s (v 0) ((hv _).mpr ⟨0, rfl⟩)
  have hneI : (⟨e₁, he₁⟩ : I) ≠ ⟨e₂, he₂⟩ := fun h => hne (congrArg Subtype.val h)
  have hcard : 1 < Fintype.card I := by
    have hle := Finset.card_le_card (Finset.subset_univ ({⟨e₁, he₁⟩, ⟨e₂, he₂⟩} : Finset I))
    rw [Finset.card_pair hneI, Finset.card_univ] at hle
    omega
  let a := Fintype.equivFin I
  let g := Function.invFunOn u P
  let G := fun i => g '' section34SplitDiskImage srcBd f₁ (a.symm i).1
  have hmer := fun e : I => hcut.intrinsic_splitDisk_meridian hf₁ s hu hUP e.1 e.2
  have hG : ∀ i, IsPLSphere 1 (G i) := by
    intro i
    obtain ⟨q, hq, hqb⟩ := (hmer (a.symm i)).1
    change IsPLSphere 1 (Function.invFunOn u P ''
      section34SplitDiskImage srcBd f₁ (a.symm i).1)
    rw [hqb]
    exact hq.isPLSphere_image_stdSimplexBoundary
  have hGΘ : ∀ i, G i ⊆ frontier P := fun i x hx =>
    (((hmer (a.symm i)).2.2.1).symm.subset hx).1
  have hGUP (e : I) : section34SplitDiskImage srcBd f₁ e.1 ⊆ u '' P := by
    rw [hUP]
    exact (hcut.isPLCellOn_splitDiskImage hf₁ e.1).boundary_subset.trans
      (hcut.splitDiskImage_subset_faceTorus hf₁ s e.1 e.2)
  have hginj : InjOn g (u '' P) := Function.invFunOn_injOn_image u P
  have hdisj : Pairwise fun i j => Disjoint (G i) (G j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hzy : z = y := hginj (hGUP (a.symm j) hz) (hGUP (a.symm i) hy)
      (hzx.trans hyx.symm)
    have hne : (a.symm i).1 ≠ (a.symm j).1 := fun h =>
      hij (a.symm.injective (Subtype.ext h))
    exact disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁.injOn hne)
      ((hcut.isPLCellOn_splitDiskImage hf₁ (a.symm i).1).boundary_subset hy)
      (hzy ▸ (hcut.isPLCellOn_splitDiskImage hf₁ (a.symm j).1).boundary_subset hz)
  have hess := fun i => (hmer (a.symm i)).2.2.2.2.2
  obtain ⟨J, Q, f, p, hJ, hQ, hf, hpQ, hpinj, hGp⟩ :=
    exists_product_coordinates_for_disjoint_essential_polygons hP G hcard hG hGΘ hdisj hess
  refine ⟨J, Q, f, p ∘ a, hJ, hQ, hf, fun e => hpQ (a e), hpinj.comp a.injective, ?_, ?_⟩
  · intro e
    simpa only [G, a.symm_apply_apply, Function.comp_apply] using hGp (a e)
  · intro e
    exact ⟨(hmer e).2.1, (hmer e).2.2.1, (hmer e).2.2.2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
