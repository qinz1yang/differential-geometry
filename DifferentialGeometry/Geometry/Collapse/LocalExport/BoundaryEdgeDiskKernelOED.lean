import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskSublevelOED
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBaseChartKernel
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryBallTrivialization
import DifferentialGeometry.Topology.Embedding.CrossModelLinearOCX
import DifferentialGeometry.Topology.Embedding.Diffeomorph
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundary
import DifferentialGeometry.Topology.Handle.Manifold

/-!
# The edge disk kernel (c) with side boundary (lane O-EDGEDISK, G1)

`exists_diskChart_of_sideBoundary_trivialization_OED` (N-level, generic, chain-free): `N` a smooth
boundaryless `3`-manifold (any boundaryless model), `P : N → ℝ¹`, `Bh : N → ℝ` smooth, `R ⊆ N` open
with `P` a submersion on `R ∩ {Bh ≥ 0}`, `(P, Bh)` a submersion on `R ∩ {Bh = 0}`, `P` proper on
`R ∩ {Bh ≥ 0}` over `ball b₀ ε`, and a smooth embedding `ψ` of the closed disk onto the whole fibre
`R ∩ {P = b₀, Bh ≥ 0}` with rim `{Bh = 0}`. Then for `ε' = ε / 2` there is a smooth embedding
`Φ : ℝ¹ × D² → N` onto `R ∩ {P ∈ ball b₀ ε', Bh ≥ 0}` with `P ∘ Φ = univBall b₀ ε' ∘ pr₁` and rim
`Bh (Φ (x, w)) = 0 ↔ ‖w‖ = 1`.

Route (statement frozen in `build-logs/scratch/S-BAUG-D/EdgeDiskKernelSkeleton.lean`; the two
hypotheses `hmaps`, `hsurj` of the frozen text are not needed: strengthened theorem + verbatim
`example`):
1. `exists_sideBoundary_ball_trivialization` on `V = R` for `P - b₀`, `Bh` (radius `ε / 2 < ε`):
   `Θ : Fb × base → V` with left inverse `(Rmap, P - b₀)` on the sublevel;
2. `Fb ≅ D²` by `IsSmoothEmbedding.diffeomorphOfRangeEq` (the inclusion of the regular sublevel `Fb`
   is a smooth embedding for ANY boundaryless model: `regularSublevel_isSmoothEmbedding_val_OED`);
3. the image `S' = {Bh ≥ 0}` inside `W = R ∩ P⁻¹ ball b₀ ε'` is a codimension-`0` regular sublevel
   (`Ψ = 0 : W → ℝ⁰`), and `Θ` is an explicit diffeomorphism `Fb × base ≃ S'`;
4. `D : ℝ¹ × D² ≃ S'` (cross-model) and `Φ = val ∘ val ∘ D` a smooth embedding by
   `IsSmoothEmbedding.comp_diffeomorph_linear_OCX` with the coordinates `diskProdCoordinates_OED`;
5. the rim: boundary points are invariant under the diffeomorphisms `D` and `D² ≅ Fb`, the boundary
   of `ℝ¹ × D²` is `ℝ¹ × ∂D²` (`boundary_of_boundaryless_left`), and the boundaries of the regular
   sublevels are `{Bh = 0}` (`regularSublevel_isBoundaryPoint_iff`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

section Coordinates

/-- Coordinates `ℝ¹ × ℝ² ≃ ℝ³`, `(x, v) ↦ (v₀, v₁, x₀)`: the half-space coordinate of the disk
factor becomes the half-space coordinate of `ℝ³`. -/
def diskProdCoordinates_OED : (ℝ¹ × ℝ²) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 + 1)) :=
  LinearEquiv.toContinuousLinearEquiv <|
    (LinearEquiv.prodCongr (EuclideanSpace.equiv (Fin 1) ℝ).toLinearEquiv
      (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv).trans <|
    (LinearEquiv.prodComm ℝ _ _).trans <|
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℝ ℝ).symm.trans <|
        (LinearEquiv.piCongrLeft' ℝ (fun _ : Fin 2 ⊕ Fin 1 => ℝ)
          (finSumFinEquiv (m := 2) (n := 1))).trans <|
          (EuclideanSpace.equiv (Fin (2 + 1)) ℝ).toLinearEquiv.symm

theorem diskProdCoordinates_OED_apply_zero (p : ℝ¹ × ℝ²) :
    diskProdCoordinates_OED p 0 = p.2 0 := by
  have h : diskProdCoordinates_OED p 0 =
      (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin 1) ℝ ℝ).symm
        (p.2.ofLp, p.1.ofLp) ((finSumFinEquiv (m := 2) (n := 1)).symm 0) := by
    simp only [diskProdCoordinates_OED]
    rw [LinearEquiv.coe_toContinuousLinearEquiv']
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.prodComm_apply, LinearEquiv.piCongrLeft'_apply, EuclideanSpace.equiv,
      Prod.swap_prod_mk,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      PiLp.coe_symm_continuousLinearEquiv, PiLp.coe_continuousLinearEquiv, WithLp.ofLp_toLp]
  rw [h, show (finSumFinEquiv (m := 2) (n := 1)).symm (0 : Fin (2 + 1)) = Sum.inl 0 from rfl,
    LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl]

/-- The coordinates match the model ranges: `(𝓡 1).prod (𝓡∂ 2)` with `𝓡∂ 3`. -/
theorem diskProdCoordinates_OED_range {v : ℝ¹ × ℝ²} :
    diskProdCoordinates_OED v + 0 ∈ range (𝓡∂ (2 + 1)) ↔ v ∈ range ((𝓡 1).prod (𝓡∂ 2)) := by
  rw [add_zero, ModelWithCorners.range_prod, range_modelWithCornersEuclideanHalfSpace,
    range_modelWithCornersEuclideanHalfSpace]
  simp only [mem_ofPred_eq, mem_prod, diskProdCoordinates_OED_apply_zero]
  exact ⟨fun h => ⟨⟨v.1, rfl⟩, h⟩, fun h => h.2⟩

end Coordinates

section Kernel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N] in
/-- Submersivity is unchanged by subtracting a constant. -/
theorem surjective_mfderiv_sub_const_OED {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type} [TopologicalSpace M] [ChartedSpace HN M] {f : M → F} {x : M} (c : F)
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (hs : Surjective (mfderiv I 𝓘(ℝ, F) f x)) :
    Surjective (mfderiv I 𝓘(ℝ, F) (fun z => f z - c) x) := by
  have h : mfderiv I 𝓘(ℝ, F) (fun z => f z - c) x = mfderiv I 𝓘(ℝ, F) f x :=
    (hf.hasMFDerivAt.sub (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ, F)) c x)).mfderiv.trans
      (sub_zero _)
  rw [h]
  exact hs

/-- **The edge disk kernel (c) with side boundary** (strengthened: without the frozen hypotheses
`hmaps`, `hsurj`; verbatim form below). -/
theorem exists_diskChart_of_sideBoundary_trivialization_OED
    (hdim : Module.finrank ℝ E = 1 + 1 + 1)
    (P : N → EuclideanSpace ℝ (Fin 1)) (Bh : N → ℝ)
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ Bh)
    (R : Set N) (hR : IsOpen R) {b₀ : EuclideanSpace ℝ (Fin 1)} {ε : ℝ} (hε : 0 < ε)
    (hreg : ∀ x ∈ R, 0 ≤ Bh x →
      Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) P x))
    (hregb : ∀ x ∈ R, Bh x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (fun z => (P z, Bh z)) x))
    (hprop : ∀ K ⊆ ball b₀ ε, IsCompact K → IsCompact {x | x ∈ R ∧ P x ∈ K ∧ 0 ≤ Bh x})
    (ψ : ClosedCell 2 → N) (hψ : IsSmoothEmbedding (𝓡∂ 2) I ∞ ψ)
    (hψr : range ψ = {x | x ∈ R ∧ P x = b₀ ∧ 0 ≤ Bh x})
    (hψrim : ∀ w, Bh (ψ w) = 0 ↔ ‖(w : ℝ²)‖ = 1) :
    ∃ ε' : ℝ, 0 < ε' ∧ ball b₀ ε' ⊆ ball b₀ ε ∧
      ∃ Φ : EuclideanSpace ℝ (Fin 1) × ClosedCell 2 → N,
        IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) I ∞ Φ ∧
        range Φ = {x | x ∈ R ∧ P x ∈ ball b₀ ε' ∧ 0 ≤ Bh x} ∧
        (∀ x w, P (Φ (x, w)) = OpenPartialHomeomorph.univBall b₀ ε' x) ∧
        ∀ x w, Bh (Φ (x, w)) = 0 ↔ ‖(w : ℝ²)‖ = 1 := by
  classical
  have : Nontrivial ℝ¹ :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact one_pos)
  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  ------------------------------------------------------------------ step 1: the trivialization
  let V : TopologicalSpace.Opens N := ⟨R, hR⟩
  have : LocallyCompactSpace V := hR.locallyCompactSpace
  let P' : V → ℝ¹ := fun y => P y - b₀
  let B' : V → ℝ := fun y => Bh y
  have hP' : ContMDiff I 𝓘(ℝ, ℝ¹) ∞ P' := (hP.comp contMDiff_subtype_val).sub contMDiff_const
  have hB' : ContMDiff I 𝓘(ℝ, ℝ) ∞ B' := hB.comp contMDiff_subtype_val
  have hdim1 : Module.finrank ℝ E = 1 + 1 + Module.finrank ℝ ℝ¹ := by
    rw [finrank_euclideanSpace_fin]
    exact hdim
  have hregV : ∀ y : V, 0 ≤ B' y → Surjective (mfderiv I 𝓘(ℝ, ℝ¹) P' y) := by
    intro y hy
    exact surjective_mfderiv_sub_const_OED b₀
      (((hP.comp contMDiff_subtype_val) y).mdifferentiableAt (by simp))
      (Ehresmann.surjective_mfderiv_comp_opens_val V y ((hP y.1).mdifferentiableAt (by simp))
        (hreg y.1 y.2 hy))
  have hregbV : ∀ y : V, B' y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (P' z, B' z)) y) := by
    intro y hy
    have h1 := Ehresmann.surjective_mfderiv_comp_opens_val V y
      (((hP.prodMk_space hB) y.1).mdifferentiableAt (by simp)) (hregb y.1 y.2 hy)
    have h2 := surjective_mfderiv_sub_const_OED ((b₀, 0) : ℝ¹ × ℝ)
      ((((hP.prodMk_space hB).comp contMDiff_subtype_val) y).mdifferentiableAt (by simp)) h1
    have heq : (fun z : V => (P' z, B' z)) =
        fun z : V => ((P z, Bh z) : ℝ¹ × ℝ) - (b₀, 0) := by
      funext z
      exact Prod.ext rfl (sub_zero _).symm
    rw [heq]
    exact h2
  have hproperV : ∀ K : Set ℝ¹, IsCompact K → K ⊆ ball 0 ε →
      IsCompact (P' ⁻¹' K ∩ {y | 0 ≤ B' y}) := by
    intro K hK hKb
    have hK' : IsCompact ((fun v : ℝ¹ => v - b₀) ⁻¹' K) :=
      (Homeomorph.subRight b₀).isCompact_preimage.mpr hK
    have hsub : (fun v : ℝ¹ => v - b₀) ⁻¹' K ⊆ ball b₀ ε := by
      intro v hv
      have h := hKb hv
      rw [mem_ball_zero_iff] at h
      rw [mem_ball, dist_eq_norm]
      exact h
    have hc := hprop _ hsub hK'
    have heq : P' ⁻¹' K ∩ {y | 0 ≤ B' y} = (Subtype.val : V → N) ⁻¹'
        {x | x ∈ R ∧ P x ∈ (fun v : ℝ¹ => v - b₀) ⁻¹' K ∧ 0 ≤ Bh x} := by
      ext y
      exact ⟨fun h => ⟨y.2, h⟩, fun h => h.2⟩
    rw [heq, Subtype.isCompact_iff, image_preimage_eq_of_subset fun x hx => ⟨⟨x, hx.1⟩, rfl⟩]
    exact hc
  obtain ⟨Θ, hΘs, hΘd, -, hΘi, O, -, hOm, Rm, hRm, hRmΘ⟩ :=
    Ehresmann.exists_sideBoundary_ball_trivialization (Y := V) (P := P') (B := B') hdim1 hP' hB'
      hε2 (half_lt_self hε) (fun y _ hb => hregV y hb) (fun y _ hb => hregbV y hb) hproperV
  have hreg0 : ∀ y : V, P' y = 0 → 0 ≤ B' y → Surjective (mfderiv I 𝓘(ℝ, ℝ¹) P' y) :=
    fun y _ hb => hregV y hb
  have hregb0 : ∀ y : V, P' y = 0 → B' y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z => (P' z, B' z)) y) :=
    fun y _ hb => hregbV y hb
  let _ := regularSublevelChartedSpace hdim1 hP' hB' hreg0 hregb0
  have := regularSublevel_isManifold hdim1 hP' hB' hreg0 hregb0
  let base : TopologicalSpace.Opens ℝ¹ := ⟨ball 0 (ε / 2), isOpen_ball⟩
  ------------------------------------------------------------------ step 2: `D² ≅ Fb`
  have hFb : IsSmoothEmbedding (𝓡∂ (1 + 1)) I ∞
      (Subtype.val : {y : V // P' y = 0 ∧ 0 ≤ B' y} → V) :=
    regularSublevel_isSmoothEmbedding_val_OED hdim1 hP' hB' hreg0 hregb0
  have hι : IsSmoothEmbedding (𝓡∂ (1 + 1)) I ∞
      ((Subtype.val : V → N) ∘ (Subtype.val : {y : V // P' y = 0 ∧ 0 ≤ B' y} → V)) :=
    (IsSmoothEmbedding.of_opens V).comp_of_boundarylessManifold_middle hFb (by simp)
  have hrange1 : range ψ =
      range ((Subtype.val : V → N) ∘ (Subtype.val : {y : V // P' y = 0 ∧ 0 ≤ B' y} → V)) := by
    rw [hψr]
    ext x
    constructor
    · rintro ⟨hxR, hxP, hxB⟩
      exact ⟨⟨⟨x, hxR⟩, sub_eq_zero.mpr hxP, hxB⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1.2, sub_eq_zero.mp z.2.1, z.2.2⟩
  let e₁ := hψ.diffeomorphOfRangeEq hι hrange1
  have he₁ : ∀ w, ((e₁ w).1 : N) = ψ w := hψ.comp_diffeomorphOfRangeEq hι hrange1
  ------------------------------------------------------------------ the base parametrization
  obtain ⟨hcsm, hcemb, hcrange, -, hcinj⟩ := univBall_data_BAUGD b₀ hε2
  let β : ℝ¹ → ℝ¹ := fun x => OpenPartialHomeomorph.univBall b₀ (ε / 2) x - b₀
  have hβemb : IsSmoothEmbedding 𝓘(ℝ, ℝ¹) 𝓘(ℝ, ℝ¹) ∞ β := by
    refine
      DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
      (by simp) (hcsm.sub contDiff_const).contMDiff ?_ ?_
      (fun _ => BoundarylessManifold.isInteriorPoint)
    · exact (Homeomorph.subRight b₀).isEmbedding.comp hcemb
    · intro x
      rw [mfderiv_eq_fderiv, fderiv_sub_const]
      exact hcinj x
  have hβrange : range β = range (Subtype.val : base → ℝ¹) := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      have h : OpenPartialHomeomorph.univBall b₀ (ε / 2) x ∈ ball b₀ (ε / 2) :=
        hcrange ▸ mem_range_self x
      rw [mem_ball, dist_eq_norm] at h
      exact ⟨⟨β x, mem_ball_zero_iff.mpr h⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      have h : (u : ℝ¹) + b₀ ∈ ball b₀ (ε / 2) := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_right]
        exact mem_ball_zero_iff.mp u.2
      rw [← hcrange] at h
      obtain ⟨x, hx⟩ := h
      exact ⟨x, by simp only [β, hx, add_sub_cancel_right]⟩
  let e₂ := hβemb.diffeomorphOfRangeEq (IsSmoothEmbedding.of_opens base) hβrange
  have he₂ : ∀ x, ((e₂ x : base) : ℝ¹) = β x :=
    hβemb.comp_diffeomorphOfRangeEq (IsSmoothEmbedding.of_opens base) hβrange
  ------------------------------------------------------------------ step 3: the image `S'`
  let W : TopologicalSpace.Opens N :=
    ⟨R ∩ P ⁻¹' ball b₀ (ε / 2), hR.inter (isOpen_ball.preimage hP.continuous)⟩
  let Ψ₀ : W → (Fin 0 → ℝ) := fun _ => 0
  let Bw : W → ℝ := fun y => Bh y
  have hΨ₀ : ContMDiff I 𝓘(ℝ, Fin 0 → ℝ) ∞ Ψ₀ := contMDiff_const
  have hBw : ContMDiff I 𝓘(ℝ, ℝ) ∞ Bw := hB.comp contMDiff_subtype_val
  have hdim0 : Module.finrank ℝ E = 2 + 1 + Module.finrank ℝ (Fin 0 → ℝ) := by
    rw [Module.finrank_fin_fun, hdim]
  have hreg₀ : ∀ y : W, Ψ₀ y = 0 → 0 ≤ Bw y →
      Surjective (mfderiv I 𝓘(ℝ, Fin 0 → ℝ) Ψ₀ y) :=
    fun _ _ _ _ => ⟨0, Subsingleton.elim (α := Fin 0 → ℝ) _ _⟩
  have hregb₀ : ∀ y : W, Ψ₀ y = 0 → Bw y = 0 →
      Surjective (mfderiv I 𝓘(ℝ, (Fin 0 → ℝ) × ℝ) (fun z => (Ψ₀ z, Bw z)) y) := by
    intro y _ hy q
    let L₀ : (ℝ¹ × ℝ) →L[ℝ] (Fin 0 → ℝ) × ℝ :=
      (0 : (ℝ¹ × ℝ) →L[ℝ] (Fin 0 → ℝ)).prod (ContinuousLinearMap.snd ℝ ℝ¹ ℝ)
    have h1 := Ehresmann.surjective_mfderiv_comp_opens_val W y
      (((hP.prodMk_space hB) y.1).mdifferentiableAt (by simp)) (hregb y.1 y.2.1 hy)
    obtain ⟨v, hv⟩ := h1 (0, q.2)
    have hg : HasMFDerivAt I 𝓘(ℝ, ℝ¹ × ℝ) (fun z : W => ((P z, Bh z) : ℝ¹ × ℝ)) y
        (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z : W => ((P z, Bh z) : ℝ¹ × ℝ)) y) :=
      ((((hP.prodMk_space hB).comp contMDiff_subtype_val) y).mdifferentiableAt
        (by simp)).hasMFDerivAt
    have hcomp := (L₀.hasMFDerivAt (x := ((P y, Bh y) : ℝ¹ × ℝ))).comp y hg
    have heq : (fun z : W => (Ψ₀ z, Bw z)) = L₀ ∘ fun z : W => ((P z, Bh z) : ℝ¹ × ℝ) := by
      funext z
      rfl
    refine ⟨v, ?_⟩
    rw [heq, hcomp.mfderiv]
    change L₀ (mfderiv I 𝓘(ℝ, ℝ¹ × ℝ) (fun z : W => ((P z, Bh z) : ℝ¹ × ℝ)) y v) = q
    rw [hv]
    exact Prod.ext (Subsingleton.elim _ _) rfl
  let _ := regularSublevelChartedSpace hdim0 hΨ₀ hBw hreg₀ hregb₀
  have := regularSublevel_isManifold hdim0 hΨ₀ hBw hreg₀ hregb₀
  have hS : IsSmoothEmbedding (𝓡∂ (2 + 1)) I ∞
      (Subtype.val : {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} → W) :=
    regularSublevel_isSmoothEmbedding_val_OED hdim0 hΨ₀ hBw hreg₀ hregb₀
  have hval : IsSmoothEmbedding (𝓡∂ (2 + 1)) I ∞
      ((Subtype.val : W → N) ∘ (Subtype.val : {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} → W)) :=
    (IsSmoothEmbedding.of_opens W).comp_of_boundarylessManifold_middle hS (by simp)
  ------------------------------------------------------------------ `Θ : Fb × base ≃ S'`
  have hmemW : ∀ p : {y : V // P' y = 0 ∧ 0 ≤ B' y} × base, ((Θ p : V) : N) ∈ W := by
    intro p
    refine ⟨(Θ p).2, ?_⟩
    change P (Θ p : N) ∈ ball b₀ (ε / 2)
    rw [mem_ball, dist_eq_norm]
    change ‖P' (Θ p)‖ < ε / 2
    rw [(hΘd p).1]
    exact mem_ball_zero_iff.mp p.2.2
  let toS : {y : V // P' y = 0 ∧ 0 ≤ B' y} × base → {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} :=
    fun p => ⟨⟨(Θ p : N), hmemW p⟩, rfl, (hΘd p).2⟩
  let ιV : {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} → V := fun s => ⟨(s : W).1, (s : W).2.1⟩
  have hmemO : ∀ s, P' (ιV s) ∈ base ∧ 0 ≤ B' (ιV s) := by
    intro s
    refine ⟨?_, s.2.2⟩
    change P (s : W).1 - b₀ ∈ ball 0 (ε / 2)
    rw [mem_ball_zero_iff, ← dist_eq_norm]
    exact (s : W).2.2
  let fromS : {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} → {y : V // P' y = 0 ∧ 0 ≤ B' y} × base :=
    fun s => (⟨Rm (ιV s), (hRmΘ (ιV s) (hmemO s).1 (hmemO s).2).fst⟩,
      ⟨P' (ιV s), (hmemO s).1⟩)
  have hRmΘp : ∀ p : {y : V // P' y = 0 ∧ 0 ≤ B' y} × base, Rm (Θ p) = (p.1 : V) := by
    intro p
    have hy : P' (Θ p) ∈ base := by
      rw [(hΘd p).1]
      exact p.2.2
    obtain ⟨hr, he⟩ := hRmΘ (Θ p) hy (hΘd p).2
    exact congrArg (fun q : {y : V // P' y = 0 ∧ 0 ≤ B' y} × base => (q.1 : V)) (hΘi he)
  have hιV : ContMDiff (𝓡∂ (2 + 1)) I ∞ ιV := by
    apply (ContMDiff.subtypeVal_comp_iff V ιV).mp
    exact hval.contMDiff
  let Θ' : Diffeomorph ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ¹)) (𝓡∂ (2 + 1))
      ({y : V // P' y = 0 ∧ 0 ≤ B' y} × base) {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} ∞ :=
    { toFun := toS
      invFun := fromS
      left_inv := fun p => Prod.ext (Subtype.ext (hRmΘp p)) (Subtype.ext (hΘd p).1)
      right_inv := fun s => by
        apply Subtype.ext
        apply Subtype.ext
        change ((Θ (fromS s) : V) : N) = ((s : W) : N)
        exact congrArg Subtype.val (hRmΘ (ιV s) (hmemO s).1 (hmemO s).2).snd
      contMDiff_toFun := by
        apply (regularSublevel_contMDiff_iff hdim0 hΨ₀ hBw hreg₀ hregb₀).mpr
        apply (ContMDiff.subtypeVal_comp_iff W _).mp
        change ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ¹)) I ∞ (fun p => ((Θ p : V) : N))
        exact contMDiff_subtype_val.comp hΘs
      contMDiff_invFun := by
        refine ContMDiff.prodMk ?_ ?_
        · apply (regularSublevel_contMDiff_iff hdim1 hP' hB' hreg0 hregb0).mpr
          exact hRm.comp_contMDiff hιV (fun s => hOm (ιV s) (hmemO s).1 (hmemO s).2)
        · apply (ContMDiff.subtypeVal_comp_iff base _).mp
          exact hP'.comp hιV }
  ------------------------------------------------------------------ step 4: the chart
  let D := (e₂.prodCongr e₁).trans
    ((Diffeomorph.prodComm 𝓘(ℝ, ℝ¹) (𝓡∂ (1 + 1)) base {y : V // P' y = 0 ∧ 0 ≤ B' y} ∞).trans Θ')
  have hΦ : IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) I ∞
      (((Subtype.val : W → N) ∘ (Subtype.val : {y : W // Ψ₀ y = 0 ∧ 0 ≤ Bw y} → W)) ∘ D) :=
    hval.comp_diffeomorph_linear_OCX diskProdCoordinates_OED
      (fun _ => diskProdCoordinates_OED_range) D
  refine ⟨ε / 2, hε2, ball_subset_ball (half_le_self hε.le), _, hΦ, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨(D q).1.2.1, (D q).1.2.2, (D q).2.2⟩
    · rintro ⟨hxR, hxP, hxB⟩
      refine ⟨D.symm ⟨⟨x, hxR, hxP⟩, rfl, hxB⟩, ?_⟩
      change (((D (D.symm ⟨⟨x, hxR, hxP⟩, rfl, hxB⟩)) : W) : N) = x
      rw [D.apply_symm_apply]
  · intro x w
    change P ((Θ (e₁ w, e₂ x) : V) : N) = OpenPartialHomeomorph.univBall b₀ (ε / 2) x
    have h1 : P' (Θ (e₁ w, e₂ x)) = β x := (hΘd (e₁ w, e₂ x)).1.trans (he₂ x)
    exact sub_left_inj.mp h1
  ------------------------------------------------------------------ step 5: the rim
  · intro x w
    have hD := (D.isLocalDiffeomorph (x, w)).isBoundaryPoint_iff (by simp)
    have he := (e₁.isLocalDiffeomorph w).isBoundaryPoint_iff (by simp)
    have hprod : ((𝓡 1).prod (𝓡∂ 2)).IsBoundaryPoint (x, w) ↔ (𝓡∂ 2).IsBoundaryPoint w := by
      change (x, w) ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary (ℝ¹ × ClosedCell 2) ↔
        w ∈ (𝓡∂ 2).boundary (ClosedCell 2)
      rw [ModelWithCorners.boundary_of_boundaryless_left]
      exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    have hS' := regularSublevel_isBoundaryPoint_iff hdim0 hΨ₀ hBw hreg₀ hregb₀ (x := D (x, w))
    have hF := regularSublevel_isBoundaryPoint_iff hdim1 hP' hB' hreg0 hregb0 (x := e₁ w)
    change Bw (D (x, w)).1 = 0 ↔ _
    rw [← hS', ← hD, hprod, he, hF]
    change Bh ((e₁ w).1 : N) = 0 ↔ _
    rw [he₁ w]
    exact hψrim w

/-- The frozen statement of `build-logs/scratch/S-BAUG-D/EdgeDiskKernelSkeleton.lean`, verbatim. -/
example (hdim : Module.finrank ℝ E = 1 + 1 + 1)
    (P : N → EuclideanSpace ℝ (Fin 1)) (Bh : N → ℝ)
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞ P) (hB : ContMDiff I 𝓘(ℝ, ℝ) ∞ Bh)
    (R : Set N) (hR : IsOpen R) {b₀ : EuclideanSpace ℝ (Fin 1)} {ε : ℝ} (hε : 0 < ε)
    (hmaps : ∀ x ∈ R, P x ∈ ball b₀ ε)
    (hreg : ∀ x ∈ R, 0 ≤ Bh x →
      Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) P x))
    (hregb : ∀ x ∈ R, Bh x = 0 →
      Surjective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 1) × ℝ) (fun z => (P z, Bh z)) x))
    (hprop : ∀ K ⊆ ball b₀ ε, IsCompact K → IsCompact {x | x ∈ R ∧ P x ∈ K ∧ 0 ≤ Bh x})
    (hsurj : ∀ b ∈ ball b₀ ε, ∃ x ∈ R, P x = b ∧ 0 ≤ Bh x)
    (ψ : ClosedCell 2 → N) (hψ : IsSmoothEmbedding (𝓡∂ 2) I ∞ ψ)
    (hψr : range ψ = {x | x ∈ R ∧ P x = b₀ ∧ 0 ≤ Bh x})
    (hψrim : ∀ w, Bh (ψ w) = 0 ↔ ‖(w : ℝ²)‖ = 1) :
    ∃ ε' : ℝ, 0 < ε' ∧ ball b₀ ε' ⊆ ball b₀ ε ∧
      ∃ Φ : EuclideanSpace ℝ (Fin 1) × ClosedCell 2 → N,
        IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) I ∞ Φ ∧
        range Φ = {x | x ∈ R ∧ P x ∈ ball b₀ ε' ∧ 0 ≤ Bh x} ∧
        (∀ x w, P (Φ (x, w)) = OpenPartialHomeomorph.univBall b₀ ε' x) ∧
        ∀ x w, Bh (Φ (x, w)) = 0 ↔ ‖(w : ℝ²)‖ = 1 := by
  exact (fun _ _ => exists_diskChart_of_sideBoundary_trivialization_OED hdim P Bh hP hB R hR hε
    hreg hregb hprop ψ hψ hψr hψrim) hmaps hsurj

end Kernel

end DifferentialGeometry.Geometry.Collapse
