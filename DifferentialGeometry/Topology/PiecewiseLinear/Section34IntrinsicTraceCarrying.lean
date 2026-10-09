/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ModelTorusTraceCarrying
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IntrinsicTraceCircles

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ h : M₁ → M₂}
  {H : Finset Ea → Set M₂} {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem exists_positive_finite_section34Trace_model_circles
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {P : Set E3} {u : E3 → M₂}
    (hP : IsCombinatorialSolidTorus P) (hu : IsPLHomeomorphInto 3 u P)
    (himage : u '' P = section34FaceTorus (section34VertexBallImage src f₁) s)
    (hfront : u '' frontier P =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) :
    ∃ (n : ℕ) (J : Fin n → Set E3), 0 < n ∧
      (∀ i, IsPLSphere 1 (J i)) ∧ (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      frontier P ∩ u ⁻¹' fblBd s = ⋃ i, J i ∧
      (∀ i, IsPolyhedralSphere (n := 3) 1 (u '' J i)) ∧
      (Pairwise fun i j => Disjoint (u '' J i) (u '' J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) = ⋃ i, u '' J i ∧
      fblBd s ∩ frontier
        (section34FaceTorus (section34VertexBallImage src f₁) s) = ⋃ i, u '' J i ∧
      CarriesFirstHomologyOnto (⋃ i, u '' J i)
        (section34FaceTorus (section34VertexBallImage src f₁) s) ∧
      ∃ i, IsPreconnected (frontier P \ J i) ∧ CarriesFirstHomologyOnto (u '' J i)
        (section34FaceTorus (section34VertexBallImage src f₁) s) := by
  classical
  let T := section34FaceTorus (section34VertexBallImage src f₁) s
  obtain ⟨ι, hι, J, hJ, hdis, hmodel, hactual, hactualdis, hN, hT⟩ :=
    exists_finite_section34Trace_model_circles hcut hf₁ hinv s hP hu himage hfront
  have htop : IsTopologicalSolidTorus T := by
    change IsTopologicalSolidTorus (section34FaceTorus (section34VertexBallImage src f₁) s)
    rw [← himage]
    exact hP.isTopologicalSolidTorus_image hu
  let eH := htop.integralSingularHomologyOneEquivInt
  let _ : Nontrivial (integralSingularHomology 1 T) :=
    ⟨⟨eH.symm 0, eH.symm 1, fun heq => zero_ne_one (eH.symm.injective heq)⟩⟩
  have hJΘ : ∀ i, J i ⊆ frontier P := fun i x hx =>
    (hmodel.symm.subset (mem_iUnion.mpr ⟨i, hx⟩)).1
  have hΘP := hP.isPolyhedron.isClosed.frontier_subset
  have hΘT : u '' frontier P ⊆ T := (image_mono hΘP).trans himage.subset
  obtain ⟨-, -, -, -, -, -, hcarry, -⟩ := id hinv
  have hcarryJ : CarriesFirstHomologyOnto (⋃ i, u '' J i) T := by
    have hc := hcarry s
    change CarriesFirstHomologyOnto (fblBd s ∩ frontier T) T at hc
    rwa [hT] at hc
  have hcarryImage : CarriesFirstHomologyOnto (u '' ⋃ i, J i) T := by
    rwa [image_iUnion]
  obtain ⟨k, hk, hkc⟩ := hP.isPLTorus_frontier.exists_surjective_circle_image
    hJ hJΘ hdis (hu.continuousOn.mono hΘP) (hu.injOn.mono hΘP) hΘT hcarryImage
  let _ := Fintype.ofFinite ι
  have : Nonempty ι := ⟨k⟩
  let e := Fintype.equivFin ι
  have hU : (⋃ i : Fin (Fintype.card ι), J (e.symm i)) = ⋃ i, J i :=
    e.symm.surjective.iUnion_comp J
  have hUI : (⋃ i : Fin (Fintype.card ι), u '' J (e.symm i)) = ⋃ i, u '' J i :=
    e.symm.surjective.iUnion_comp (fun i => u '' J i)
  refine ⟨Fintype.card ι, fun i => J (e.symm i), Fintype.card_pos,
    fun i => hJ _, fun i j hij => hdis (fun heq => hij (e.symm.injective heq)),
    hmodel.trans hU.symm, fun i => hactual _,
    fun i j hij => hactualdis (fun heq => hij (e.symm.injective heq)),
    hN.trans hUI.symm, hT.trans hUI.symm, ?_, e k, ?_, ?_⟩
  · rwa [hUI]
  · simpa only [e.symm_apply_apply] using hk
  · simpa only [e.symm_apply_apply] using hkc

theorem exists_positive_finite_section34Trace_circles
    {W : Set M₁} {η : M₁ → ℝ} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hgraph : Section34GraphFrame U W h η H 𝒦 𝒦' src cr f₁)
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd) (s : Section34SimplexIndex 𝒦 3) :
    ∃ (r : ℕ) (J : Fin r → Set M₂), 0 < r ∧
      (∀ i, IsPolyhedralSphere (n := 3) 1 (J i)) ∧
      (Pairwise fun i j => Disjoint (J i) (J j)) ∧
      fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) = ⋃ i, J i ∧
      fblBd s ∩ frontier
        (section34FaceTorus (section34VertexBallImage src f₁) s) = ⋃ i, J i := by
  obtain ⟨P, u, hP, hu, hUP, hfront⟩ :=
    exists_section34FaceTorus_intrinsic_model hcut hgraph s
  obtain ⟨r, J, hr, -, -, -, hJ, hdis, hN, hT, -⟩ :=
    exists_positive_finite_section34Trace_model_circles hcut hgraph.2.2.1 hinv
      s hP hu hUP hfront
  exact ⟨r, fun i => u '' J i, hr, hJ, hdis, hN, hT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
