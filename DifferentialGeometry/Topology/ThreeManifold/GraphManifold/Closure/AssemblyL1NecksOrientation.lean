import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksFlip
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComposition
import DifferentialGeometry.Topology.Manifold.SmoothOrientationComparison
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.OrientationSign

/-!
# Chapter-14 assembly, item L1, T1′: the orientation of necks (E5 and the general constancy)

Lane ASM-L1d (sub-statements E4/E5 of T1′, frozen in `build-logs/scratch/ASM-L1e/Targets.lean`).

* `orientationMap_differentials_iff`: for maps `f : X → Y`, `g : X → V` with bijective
  differentials on a preconnected manifold `X` (with boundary or corners), whether
  `dg ∘ (df)⁻¹` carries the orientation of `Y` to a fixed orientation of `V` does not depend on
  the point (pullbacks of smooth orientations agree on a clopen set).
* `orientationMap_mfderiv_iff_of_isPreconnected`, `neckPreservesAt_iff_of_isPreconnected`: the
  orientation behaviour of a partial diffeomorphism (of a neck) is constant along a preconnected
  subset of its source.
* `orientationMap_eq_iff_det_pos`: the three-dimensional linear algebra comparing a neck
  differential with the ambient comparison map.
* **E5** `PieceEmbedding.neckPreservesAt_iff_ballNeckDetAmb`: two necks centred on one ball
  preserve the orientation alike iff the product of their chart-free ball determinants is
  positive. The hypothesis `hint` of the frozen statement is not needed and is dropped; the frozen
  statement is kept verbatim as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Linear

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [AddCommGroup V₂] [Module ℝ V₂]
  [AddCommGroup V₃] [Module ℝ V₃]

/-- Transport of orientations along a composite. -/
theorem orientationMap_trans {ι : Type*} (e : V₁ ≃ₗ[ℝ] V₂) (f : V₂ ≃ₗ[ℝ] V₃)
    (o : Orientation ℝ V₁ ι) :
    Orientation.map ι (e.trans f) o = Orientation.map ι f (Orientation.map ι e o) := by
  induction o using Module.Ray.ind with | h v hv => rfl

/-- Transport and reindexing of orientations commute. -/
theorem orientationMap_reindex {ι κ : Type*} (e : V₁ ≃ₗ[ℝ] V₂) (i : ι ≃ κ)
    (o : Orientation ℝ V₁ ι) :
    Orientation.map κ e (Orientation.reindex ℝ V₁ i o) =
      Orientation.reindex ℝ V₂ i (Orientation.map ι e o) := by
  induction o using Module.Ray.ind with
  | h v hv =>
    simp only [Orientation.map_apply, Orientation.reindex_apply]
    have heq : (v.domDomCongr i).compLinearMap (e.symm : V₂ →ₗ[ℝ] V₁) =
        (v.compLinearMap (e.symm : V₂ →ₗ[ℝ] V₁)).domDomCongr i := by
      ext x
      rfl
    simp only [heq]

/-- Reindexing along `finCongr` and back. -/
theorem orientationReindex_finCongr_cancel {a b : ℕ} (h : a = b) (h' : b = a)
    (o : Orientation ℝ V₁ (Fin a)) :
    Orientation.reindex ℝ V₁ (finCongr h') (Orientation.reindex ℝ V₁ (finCongr h) o) = o := by
  subst h
  simp [Orientation.reindex_refl]

/-- Orientations in dimension three: `D` carries `o` to `oT` iff the comparison of `G oT` with `o`
agrees with the sign of `det (G ∘ D)`. -/
theorem orientationMap_eq_iff_det_pos [FiniteDimensional ℝ V₁] (h3 : Module.finrank ℝ V₁ = 3)
    {D : V₁ ≃ₗ[ℝ] V₂} (G : V₂ ≃ₗ[ℝ] V₁) {o : Orientation ℝ V₁ (Fin 3)}
    {oT : Orientation ℝ V₂ (Fin 3)} :
    Orientation.map (Fin 3) D o = oT ↔
      (Orientation.map (Fin 3) G oT = o ↔ 0 < LinearMap.det ((D.trans G : V₁ ≃ₗ[ℝ] V₁) :
        V₁ →ₗ[ℝ] V₁)) := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ V₁ := by rw [h3, Fintype.card_fin]
  rw [← (Orientation.map (Fin 3) G).injective.eq_iff, ← orientationMap_trans]
  rcases Orientation.eq_or_eq_neg (Orientation.map (Fin 3) G oT) o hcard with hT | hT
  · rw [hT, Orientation.map_eq_iff_det_pos _ _ hcard]
    simp
  · rw [hT, ← Orientation.ne_iff_eq_neg _ _ hcard, Ne, Orientation.map_eq_iff_det_pos _ _ hcard]
    have hne : ¬ -o = o := fun h => Module.Ray.ne_neg_self o h.symm
    simp only [hne, false_iff]

end Linear

section Generic

variable {E F V H K X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace Y] [ChartedSpace K Y] [IsManifold J ∞ Y]

/-- **Constancy of the orientation comparison.** For maps `f : X → Y`, `g : X → V` with bijective
differentials on a preconnected manifold `X`, whether `dg ∘ (df)⁻¹` carries the orientation of `Y`
to a fixed orientation of `V` does not depend on the point. -/
theorem orientationMap_differentials_iff [PreconnectedSpace X] {f : X → Y}
    (hf : ContMDiff I J ∞ f) {hbf : ∀ x, Bijective (mfderiv I J f x)} {g : X → V}
    (hg : ContMDiff I 𝓘(ℝ, V) ∞ g) {hbg : ∀ x, Bijective (mfderiv I 𝓘(ℝ, V) g x)} {n : ℕ}
    {oY : ManifoldOrientation J Y n} {oV : Orientation ℝ V (Fin n)} (x y : X) :
    Orientation.map (Fin n) ((differentialEquivOfBijective I J f hbf x).symm.trans
        (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg x)).toLinearEquiv
        (oY.orientation (f x)) = oV ↔
      Orientation.map (Fin n) ((differentialEquivOfBijective I J f hbf y).symm.trans
        (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg y)).toLinearEquiv
        (oY.orientation (f y)) = oV := by
  have hd := oY.dimension_eq
  subst hd
  have hFV : Module.finrank ℝ F = Module.finrank ℝ V :=
    ((differentialEquivOfBijective I J f hbf x).symm.trans
      (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg x)).toLinearEquiv.finrank_eq
  let sY := smoothOrientationOfManifoldOrientation J oY
  let s₁ := pullbackSmoothOrientation I J f hf hbf sY
  let s₂ := pullbackSmoothOrientation I 𝓘(ℝ, V) g hg hbg
    (euclideanSmoothOrientation V (Orientation.reindex ℝ V (finCongr hFV) oV))
  have hc := (smoothOrientation_agreement_locallyConstant I s₁ s₂).apply_eq_of_preconnectedSpace
    x y
  have key : ∀ z : X, (s₁.val z = s₂.val z) ↔
      Orientation.map (Fin (Module.finrank ℝ F))
        ((differentialEquivOfBijective I J f hbf z).symm.trans
          (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg z)).toLinearEquiv
        (oY.orientation (f z)) = oV := by
    intro z
    have htr := tangentOrientationEquiv_trans
      (differentialEquivOfBijective I J f hbf z).symm.toLinearEquiv
      (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg z).toLinearEquiv (oY.orientation (f z))
    rw [← (tangentOrientationEquiv (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg
      z).toLinearEquiv).injective.eq_iff, pullbackSmoothOrientation_pushforward]
    change tangentOrientationEquiv (differentialEquivOfBijective I 𝓘(ℝ, V) g hbg z).toLinearEquiv
      (tangentOrientationEquiv (differentialEquivOfBijective I J f hbf z).symm.toLinearEquiv
        (oY.orientation (f z))) = Orientation.reindex ℝ V (finCongr hFV) oV ↔ _
    rw [← htr]
    exact (Orientation.reindex ℝ V (finCongr hFV)).injective.eq_iff
  exact (key x).symm.trans ((Iff.of_eq hc).trans (key y))

/-- **Constancy along a preconnected set** for a partial diffeomorphism from a vector space. -/
theorem orientationMap_mfderiv_iff_of_isPreconnected
    {Φ : PartialDiffeomorph 𝓘(ℝ, V) J V Y ∞} {n : ℕ} {oY : ManifoldOrientation J Y n}
    {oV : Orientation ℝ V (Fin n)} {s : Set V} (hs : IsPreconnected s)
    {hsource : s ⊆ Φ.source} {x y : V} (hx : x ∈ s) (hy : y ∈ s) :
    Orientation.map (Fin n) ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, V) J ∞
        (hsource hx)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv oV =
        oY.orientation (Φ x) ↔
      Orientation.map (Fin n) ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, V) J ∞
        (hsource hy)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv oV =
        oY.orientation (Φ y) := by
  have hd := oY.dimension_eq
  subst hd
  have hVF : Module.finrank ℝ F = Module.finrank ℝ V :=
    ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, V) J ∞ (hsource hx)).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv.finrank_eq.symm
  have key : ∀ D : V ≃ₗ[ℝ] F, tangentOrientationEquiv D
      (Orientation.reindex ℝ V (finCongr hVF) oV) = Orientation.map _ D oV := by
    intro D
    change Orientation.reindex ℝ F (finCongr D.finrank_eq)
      (Orientation.map _ D (Orientation.reindex ℝ V (finCongr hVF) oV)) = _
    rw [orientationMap_reindex, orientationReindex_finCongr_cancel]
  have h := PartialDiffeomorph.tangentOrientationEquiv_eq_iff_of_isPreconnected Φ
    (euclideanSmoothOrientation V (Orientation.reindex ℝ V (finCongr hVF) oV))
    (smoothOrientationOfManifoldOrientation J oY) hs hsource hx hy
  rw [euclideanSmoothOrientation_apply, euclideanSmoothOrientation_apply] at h
  have hx' := key ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, V) J ∞
    (hsource hx)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  have hy' := key ((Φ.isLocalDiffeomorphAt 𝓘(ℝ, V) J ∞
    (hsource hy)).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  constructor
  · intro h1
    exact hy'.symm.trans (h.mp (hx'.trans h1))
  · intro h1
    exact hx'.symm.trans (h.mpr (hy'.trans h1))

end Generic

/-- **Lemma B.** The orientation behaviour of a neck is constant along a preconnected subset of its
source. -/
theorem neckPreservesAt_iff_of_isPreconnected {W : CompactCarrier.{u}}
    {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞} {s : Set (EuclideanSpace ℝ (Fin 2) × ℝ)}
    (hs : IsPreconnected s) (hsource : s ⊆ N.source) {q q' : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ s) (hq' : q' ∈ s) : NeckPreservesAt N q ↔ NeckPreservesAt N q' := by
  rw [neckPreservesAt_iff (hsource hq), neckPreservesAt_iff (hsource hq')]
  exact orientationMap_mfderiv_iff_of_isPreconnected (Φ := N) (oY := W.orientation)
    (oV := neckSpaceOrientation) (hsource := hsource) hs hq hq'

/-- Two nonzero reals: the comparisons `Q ↔ 0 < a` and `Q ↔ 0 < b` agree iff `0 < a * b`. -/
theorem iff_iff_iff_pos_iff_mul_pos {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (Q : Prop) :
    ((Q ↔ 0 < a) ↔ (Q ↔ 0 < b)) ↔ 0 < a * b := by
  have key : ((Q ↔ 0 < a) ↔ (Q ↔ 0 < b)) ↔ (0 < a ↔ 0 < b) := by tauto
  rw [key]
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb' <;>
    simp [mul_pos_iff, ha', hb', not_lt.mpr ha'.le, not_lt.mpr hb'.le]

section Ball

local instance ballChartsO_ASML1d : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmoothO_ASML1d : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-- The charts of the closed 3-cell indexed as `ClosedCell (2 + 1)`. -/
local instance ballChartsSuccO_ASML1d :
    ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]

/-- A diffeomorphism onto the closed 3-cell, read in `ℝ³`, is smooth. -/
theorem contMDiff_closedCellVal_comp (e : M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ e) :=
  (isSmoothEmbedding_closedCell_inclusion 2).contMDiff.comp e.contMDiff

/-- A diffeomorphism onto the closed 3-cell, read in `ℝ³`, has bijective differentials. -/
theorem bijective_mfderiv_closedCellVal_comp (e : M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (p : M) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ e) p) :=
  bijective_mfderiv_comp (𝓡∂ 3) (𝓡∂ 3) (𝓡 3) e Subtype.val e.contMDiff
    (isSmoothEmbedding_closedCell_inclusion 2).contMDiff
    (fun p => (e.mfderivToContinuousLinearEquiv (by simp) p).bijective)
    (closedCell_inclusion_mfderiv_bijective 2) p

/-- One neck against one ball: the neck at its centre preserves the orientation iff the comparison
of the orientation of `W` with the standard orientation of `ℝ³` through the ball `B ∘ e⁻¹` (at the
point `e⁻¹ x`) agrees with the sign of the chart-free ball determinant. -/
theorem PieceEmbedding.neckPreservesAt_iff_ballSide {W : CompactCarrier.{u}}
    (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞}
    (h : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ N.source) (x : ClosedCell 3)
    (hx : B.map (e.symm x) = N 0) :
    NeckPreservesAt N 0 ↔
      (Orientation.map (Fin 3)
        ((differentialEquivOfBijective (𝓡∂ 3) W.model B.map B.mfderiv_bijective
          (e.symm x)).symm.trans (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
            ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ e)
            (bijective_mfderiv_closedCellVal_comp e) (e.symm x))).toLinearEquiv
        (W.orientation.orientation (B.map (e.symm x))) =
          (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation ↔
        0 < ballNeckDetAmb B e x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0)) := by
  have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hdet : LinearMap.det ((((neckSpaceEquiv.trans (neckDiffEquiv N h)).trans
      ((differentialEquivOfBijective (𝓡∂ 3) W.model B.map B.mfderiv_bijective
          (e.symm x)).symm.trans (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3)
            ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ e)
            (bijective_mfderiv_closedCellVal_comp e) (e.symm x))).toLinearEquiv) :
        EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) :
        EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3)) =
      ballNeckDetAmb B e x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0) := by
    unfold ballNeckDetAmb
    congr 1
    refine LinearMap.ext fun v => ?_
    have hcomp := mfderiv_comp (e.symm x)
      ((isSmoothEmbedding_closedCell_inclusion 2).contMDiff.mdifferentiableAt (by simp) :
        MDifferentiableAt (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3))
          (e (e.symm x)))
      (e.contMDiff.mdifferentiableAt (by simp))
    rw [e.apply_symm_apply] at hcomp
    change mfderiv (𝓡∂ 3) (𝓡 3) ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ e)
      (e.symm x) ((LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
        (B.mfderiv_bijective (e.symm x))).symm (neckDiffEquiv N h (neckSpaceEquiv v))) = _
    rw [hcomp, neckDiffEquiv_apply]
    rfl
  rw [neckPreservesAt_iff h, neckSpaceOrientation, ← orientationMap_trans, ← hx]
  rw [← hdet]
  exact orientationMap_eq_iff_det_pos h3 _

/-- **E5** (stronger form: the hypothesis `hint` of the frozen statement is not needed). Two necks
centred on one ball preserve the orientation alike iff the product of their chart-free ball
determinants is positive. -/
theorem PieceEmbedding.neckPreservesAt_iff_ballNeckDetAmb {W : CompactCarrier.{u}}
    (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    {N₀ N₁ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞}
    (h₀ : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ N₀.source)
    (h₁ : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ N₁.source) (x₀ x₁ : ClosedCell 3)
    (hx₀ : B.map (e.symm x₀) = N₀ 0) (hx₁ : B.map (e.symm x₁) = N₁ 0) :
    (NeckPreservesAt N₀ 0 ↔ NeckPreservesAt N₁ 0) ↔
      0 < ballNeckDetAmb B e x₀ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N₀ 0) *
        ballNeckDetAmb B e x₁ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N₁ 0) := by
  rw [B.neckPreservesAt_iff_ballSide e h₀ x₀ hx₀, B.neckPreservesAt_iff_ballSide e h₁ x₁ hx₁,
    orientationMap_differentials_iff (hbf := B.mfderiv_bijective)
      (hbg := bijective_mfderiv_closedCellVal_comp e) (oY := W.orientation)
      (oV := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation) B.smooth
      (contMDiff_closedCellVal_comp e) (e.symm x₀) (e.symm x₁)]
  exact iff_iff_iff_pos_iff_mul_pos (ballNeckDetAmb_ne_zero B e x₀ N₀ h₀)
    (ballNeckDetAmb_ne_zero B e x₁ N₁ h₁) _

/-- **E5**, the frozen statement verbatim. -/
example {W : CompactCarrier.{u}}
    (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)
    (_hint : range B.map ⊆ (W.interior : Set W.Carrier))
    (N₀ N₁ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (h₀ : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ N₀.source)
    (h₁ : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ N₁.source) (x₀ x₁ : ClosedCell 3)
    (hx₀ : B.map (e.symm x₀) = N₀ 0) (hx₁ : B.map (e.symm x₁) = N₁ 0) :
    (NeckPreservesAt N₀ 0 ↔ NeckPreservesAt N₁ 0) ↔
      0 < ballNeckDetAmb B e x₀ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N₀ 0) *
        ballNeckDetAmb B e x₁ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N₁ 0) :=
  B.neckPreservesAt_iff_ballNeckDetAmb e h₀ h₁ x₀ x₁ hx₀ hx₁

end Ball

end GC.GraphManifold.Assembly
