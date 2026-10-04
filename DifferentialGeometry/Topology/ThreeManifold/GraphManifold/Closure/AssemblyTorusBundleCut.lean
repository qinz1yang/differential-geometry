import DifferentialGeometry.Topology.Ehresmann.CircleFibreTransport
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyClosedModel
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCutSystem
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.CarrierDiffeomorphTransport

/-!
# Chapter-14 assembly, L3-cut: a torus bundle over the circle cut along one fibre

Lane ASM-L3 (design `docs/geometrization/chapter14/design-fc39-fc42-assembly-20261004.md`, §0.7 and
§3 L3; external draft (c) L3). The bundle is NOT cut by taking a closure of a preimage: it is pulled
back to the closed interval `[0, 1]` of the base so that the two ends become two different fibre
copies.

* `exists_circleCut_of_boundary_eq_empty`: the cut map of a fibre bundle over the circle on a carrier
  with empty boundary (B0 closed model, then `CircleFibre.exists_circleCut`, transported back).
* The piece is the actual `T² × I = annulusCircleCarrier` (`productSet 2`), read through the polar
  diffeomorphism `torusMonodromyPolarDiffeomorph : productSet 2 ≃ₘ T² × [0, 1]`; the fold is the cut
  map on `T² × [0, 1]` (`torusCutPiece`).
* Endpoint matching: the end `T² × {1}` is glued to `T² × {0}` by the monodromy `φ`,
  `Ψ (z, 1) = Ψ (φ z, 0)`.
* The self-seam is the cut map on `T² × (-1/10, 1/10)` (an affine strip chart), with source exactly
  `signedCollarSource`; its two half collars are the outer collar (side `false`) and the inner collar
  twisted by `φ⁻¹` (side `true`), with the B2-side equalities on all of `0 ≤ s < 1`.
* `exists_selfSeam_cutData_of_torusBundle` (**L3-cut**, frozen): one piece, one self-seam, the piece
  `annulusCircleCarrier`. No comparison with the mapping-torus carrier of
  `Closure/TorusBundleRaw.lean:45–64` is made; the monodromy need not be isotopic to the identity.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ### The cut map on a carrier with empty boundary -/

theorem mem_interior_of_boundary_eq_empty {W : CompactCarrier.{u}}
    (hW : W.model.boundary W.Carrier = ∅) (x : W.Carrier) : x ∈ W.interior := by
  change x ∈ W.model.interior W.Carrier
  rw [← ModelWithCorners.compl_boundary, hW]
  exact Set.notMem_empty x

/-- **Cut of a fibre bundle over the circle, on a carrier with empty boundary.** -/
theorem exists_circleCut_of_boundary_eq_empty (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    {EF HF F : Type*} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    [TopologicalSpace HF] {IF : ModelWithCorners ℝ EF HF} [IF.Boundaryless]
    [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F] [Nonempty F]
    (f : F → W.Carrier) (hf : IsSmoothEmbedding IF W.model ∞ f) (hr : range f = p ⁻¹' {1}) :
    ∃ (Ψ : F × ℝ → W.Carrier) (φ : F ≃ₘ⟮IF, IF⟯ F),
      ContMDiff (IF.prod 𝓘(ℝ, ℝ)) W.model ∞ Ψ ∧
      (∀ z, Ψ (z, 0) = f z) ∧
      (∀ z s, Ψ (z, s + 1) = Ψ (φ z, s)) ∧
      (∀ α, InjOn Ψ (univ ×ˢ Ico α (α + 1))) ∧
      (∀ α x, ∃ z, ∃ t ∈ Ico α (α + 1), Ψ (z, t) = x) ∧
      ∀ a b u v : ℝ, 0 < b → b * (v - u) ≤ 1 →
        ∃ d : PartialDiffeomorph (IF.prod 𝓘(ℝ, ℝ)) W.model (F × ℝ) W.Carrier ∞,
          d.source = univ ×ˢ Ioo u v ∧ (d : F × ℝ → W.Carrier) = fun q => Ψ (q.1, a + b * q.2) := by
  obtain ⟨Q, e, -⟩ := exists_closedModel_of_boundary_eq_empty W hW
  have hp' : ContMDiff (𝓡 3) (𝓡 1) ∞ (p ∘ e.symm) := hp.comp e.symm.contMDiff
  have hsub' : ∀ y, Surjective (mfderiv (𝓡 3) (𝓡 1) (p ∘ e.symm) y) := by
    intro y
    rw [mfderiv_comp y (hp.mdifferentiableAt (by simp))
      (e.symm.contMDiff.mdifferentiableAt (by simp))]
    obtain ⟨L, hL⟩ := e.symm.isInvertible_mfderiv (x := y) (by simp)
    rw [ContinuousLinearMap.coe_comp, ← hL]
    exact (hsub _).comp L.surjective
  have hfc : ContMDiff IF (𝓡 3) ∞ (e ∘ f) := e.contMDiff.comp hf.isImmersion.contMDiff
  have hf' : IsSmoothEmbedding IF (𝓡 3) ∞ (e ∘ f) := by
    refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by simp) hfc
      fun z => ?_, e.toHomeomorph.isEmbedding.comp hf.isEmbedding⟩
    rw [mfderiv_comp z (e.contMDiff.mdifferentiableAt (by simp))
      (hf.isImmersion.contMDiff.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
    obtain ⟨L, hL⟩ := e.isInvertible_mfderiv (x := f z) (by simp)
    rw [← hL]
    exact L.injective.comp ((hf.isImmersion.isImmersionAt z).mfderiv_injective (by simp))
  have hr' : range (e ∘ f) = (p ∘ e.symm) ⁻¹' {1} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      have h : f z ∈ p ⁻¹' {1} := hr ▸ mem_range_self z
      change p (e.symm (e (f z))) = 1
      rw [e.symm_apply_apply]
      exact h
    · intro hy
      have h : e.symm y ∈ range f := by
        rw [hr]
        exact hy
      obtain ⟨w, hw⟩ := h
      exact ⟨w, by change e (f w) = y; rw [hw, e.apply_symm_apply]⟩
  obtain ⟨Ψ, φ, hΨ, h0, -, hper, hinj, hsurj, hchart⟩ :=
    Ehresmann.CircleFibre.exists_circleCut (p ∘ e.symm) hp' hsub' (e ∘ f) hf' hr'
  refine ⟨fun q => e.symm (Ψ q), φ, e.symm.contMDiff.comp hΨ, fun z => ?_, fun z s => ?_,
    fun α => ?_, fun α x => ?_, fun a b u v hb hbv => ?_⟩
  · change e.symm (Ψ (z, 0)) = f z
    rw [h0]
    exact e.symm_apply_apply (f z)
  · change e.symm (Ψ (z, s + 1)) = e.symm (Ψ (φ z, s))
    rw [hper]
  · exact e.symm.injective.comp_injOn (hinj α)
  · obtain ⟨z, t, ht, hzt⟩ := hsurj α (e x)
    exact ⟨z, t, ht, by change e.symm (Ψ (z, t)) = x; rw [hzt, e.symm_apply_apply]⟩
  · obtain ⟨d, hds, hdf⟩ := hchart a b u v hb hbv
    refine ⟨d.trans e.symm.toPartialDiffeomorph, ?_, ?_⟩
    · rw [PartialDiffeomorph.trans_source, hds]
      exact inter_eq_left.mpr fun q _ => trivial
    · funext q
      change e.symm (d q) = e.symm (Ψ (q.1, a + b * q.2))
      rw [hdf]


/-! ### The polar coordinates of the two collars of `T² × I` -/

theorem halfPoint_val (s : ℝ) (hs : 0 ≤ s) : (halfPoint s hs).val 0 = s := rfl

theorem polar_outerCollar {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyOuterCollar p)).1 = p.1 ∧
      ((torusMonodromyPolarDiffeomorph.{u} (torusMonodromyOuterCollar p)).2 : ℝ) =
        p.2.val 0 / 10 := by
  have hs : 0 ≤ p.2.val 0 := p.2.property
  have hp1 : p.2.val 0 < 1 := hp
  have hr : 0 < (3 : ℝ) - p.2.val 0 / 4 := by linarith
  have hdown := torusMonodromyOuterCollar_down.{u} hp
  have hnorm : ‖(torusMonodromyOuterCollar.{u} p).val.1.down‖ = 3 - p.2.val 0 / 4 := by
    rw [hdown, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have hunit : unitOf (torusMonodromyOuterCollar.{u} p).val.1.down = p.1.1 := by
    rw [hdown]
    exact unitOf_smul hr p.1.1
  refine ⟨Prod.ext ?_ ?_, ?_⟩
  · exact hunit
  · rfl
  · change (3 - ‖(torusMonodromyOuterCollar.{u} p).val.1.down‖) / (5 / 2) = p.2.val 0 / 10
    rw [hnorm]
    ring

theorem polar_innerCollar {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (torusMonodromyPolarDiffeomorph.{u} (torusMonodromyInnerCollar p)).1 = p.1 ∧
      ((torusMonodromyPolarDiffeomorph.{u} (torusMonodromyInnerCollar p)).2 : ℝ) =
        1 - p.2.val 0 / 10 := by
  have hs : 0 ≤ p.2.val 0 := p.2.property
  have hr : 0 < (1 / 2 : ℝ) + p.2.val 0 / 4 := by linarith
  have hdown := torusMonodromyInnerCollar_down.{u} hp
  have hnorm : ‖(torusMonodromyInnerCollar.{u} p).val.1.down‖ = 1 / 2 + p.2.val 0 / 4 := by
    rw [hdown, norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg hr.le]
  have hunit : unitOf (torusMonodromyInnerCollar.{u} p).val.1.down = p.1.1 := by
    rw [hdown]
    exact unitOf_smul hr p.1.1
  refine ⟨Prod.ext ?_ ?_, ?_⟩
  · exact hunit
  · rfl
  · change (3 - ‖(torusMonodromyInnerCollar.{u} p).val.1.down‖) / (5 / 2) = 1 - p.2.val 0 / 10
    rw [hnorm]
    ring

/-- The boundary of `T² × I` is the union of the two ends `T² × {0}` and `T² × {1}`. -/
theorem productSet_two_isBoundaryPoint_iff {x : GC.Seifert.productSet.{u} 2} :
    (𝓡∂ 3).IsBoundaryPoint x ↔
      ((torusMonodromyPolarDiffeomorph.{u} x).2 : ℝ) = 0 ∨
        ((torusMonodromyPolarDiffeomorph.{u} x).2 : ℝ) = 1 := by
  rw [productSet_isBoundaryPoint_iff, planarFunction_eq_zero_iff (Or.inl rfl),
    Fin.exists_fin_two]
  simp only [planarCenter, planarRadius, Fin.val_zero, Fin.val_one, ↓reduceIte,
    one_ne_zero, Complex.ofReal_zero, sub_zero]
  change _ ↔ (3 - ‖x.val.1.down‖) / (5 / 2) = 0 ∨ (3 - ‖x.val.1.down‖) / (5 / 2) = 1
  constructor
  · rintro (h | h)
    · left
      rw [h]
      ring
    · right
      rw [h]
      ring
  · rintro (h | h)
    · left
      linarith
    · right
      linarith


/-! ### The cut piece and the self-seam -/

/-- A smooth map whose affine reparametrizations are partial diffeomorphisms on strips has
bijective differential everywhere. -/
theorem bijective_mfderiv_of_stripCharts {W : CompactCarrier.{u}} {Ψ : Torus × ℝ → W.Carrier}
    (hchart : ∀ a b u v : ℝ, 0 < b → b * (v - u) ≤ 1 →
      ∃ d : PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞,
        d.source = univ ×ˢ Ioo u v ∧ (d : Torus × ℝ → W.Carrier) = fun q => Ψ (q.1, a + b * q.2))
    (q : Torus × ℝ) : Bijective (mfderiv signedCollarModel W.model Ψ q) := by
  obtain ⟨d, hds, hdf⟩ := hchart 0 1 (q.2 - 1 / 2) (q.2 + 1 / 2) one_pos (by linarith)
  have hq : q ∈ d.source := by
    rw [hds]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hdΨ : (d : Torus × ℝ → W.Carrier) = Ψ := by
    rw [hdf]
    funext r
    simp
  have hloc : IsLocalDiffeomorphAt signedCollarModel W.model ∞ Ψ q := by
    rw [← hdΨ]
    exact d.isLocalDiffeomorphAt _ _ _ hq
  obtain ⟨L, hL⟩ := hloc.isInvertible_mfderiv (by simp)
  rw [← hL]
  exact L.bijective

/-- **The cut piece.** The actual `T² × I` (`annulusCircleCarrier`), folded into `W` by the cut map
on `T² × [0, 1]`, read through the polar diffeomorphism. -/
def torusCutPiece (W : CompactCarrier.{u}) (Ψ : Torus × ℝ → W.Carrier)
    (hΨ : ContMDiff signedCollarModel W.model ∞ Ψ)
    (hbij : ∀ q, Bijective (mfderiv signedCollarModel W.model Ψ q)) : PieceFold W where
  Piece := GC.Seifert.productSet.{u} 2
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (GC.Seifert.productSet.{u} 2))
  manifold := (inferInstance : IsManifold (𝓡∂ 3) ∞ (GC.Seifert.productSet.{u} 2))
  compact := annulusCircleCarrier.{u}.compact
  connected := annulusCircleCarrier_connectedSpace
  map q := Ψ ((torusMonodromyPolarDiffeomorph.{u} q).1,
    ((torusMonodromyPolarDiffeomorph.{u} q).2 : ℝ))
  smooth := hΨ.comp ((contMDiff_fst.prodMk (contMDiff_subtypeVal_Icc.comp contMDiff_snd)).comp
    torusMonodromyPolarDiffeomorph.contMDiff)
  mfderiv_bijective q := by
    let pol := torusMonodromyPolarDiffeomorph.{u}
    let ι : Torus × unitInterval → Torus × ℝ := Prod.map id Subtype.val
    have hι : ContMDiff (torusModel.prod (𝓡∂ 1)) signedCollarModel ∞ ι :=
      contMDiff_id.prodMap contMDiff_subtypeVal_Icc
    change Bijective (mfderiv (𝓡∂ 3) W.model (Ψ ∘ (ι ∘ pol)) q)
    rw [mfderiv_comp q (hΨ.mdifferentiableAt (by simp))
      ((hι.comp pol.contMDiff).mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp,
      mfderiv_comp q (hι.mdifferentiableAt (by simp)) (pol.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.coe_comp]
    have hιb : Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) signedCollarModel ι (pol q)) := by
      rw [mfderiv_prodMap mdifferentiableAt_id
        ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiableAt (by simp)), mfderiv_id]
      exact Function.bijective_id.prodMap
        (DifferentialGeometry.Manifold.Interval.tangentCoordinateIcc (pol q).2).bijective
    obtain ⟨L, hL⟩ := pol.isInvertible_mfderiv (x := q) (by simp)
    rw [← hL]
    exact (hbij _).comp (hιb.comp L.bijective)

theorem torusCutPiece_map (W : CompactCarrier.{u}) (Ψ : Torus × ℝ → W.Carrier)
    (hΨ : ContMDiff signedCollarModel W.model ∞ Ψ)
    (hbij : ∀ q, Bijective (mfderiv signedCollarModel W.model Ψ q))
    (q : GC.Seifert.productSet.{u} 2) :
    (torusCutPiece W Ψ hΨ hbij).map q = Ψ ((torusMonodromyPolarDiffeomorph.{u} q).1,
      ((torusMonodromyPolarDiffeomorph.{u} q).2 : ℝ)) := rfl

/-- The inner collar of `T² × I` twisted by `φ⁻¹`: the side-`true` half collar of the self-seam. -/
def twistedInnerCollar (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (GC.Seifert.productSet.{u} 2) ∞ :=
  (φ.symm.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
    torusMonodromyInnerCollar.{u}

theorem twistedInnerCollar_apply (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (p : Torus × EuclideanHalfSpace 1) :
    twistedInnerCollar.{u} φ p = torusMonodromyInnerCollar.{u} (φ.symm p.1, p.2) := rfl

theorem twistedInnerCollar_source (φ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (twistedInnerCollar.{u} φ).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (φ.symm p.1, p.2) ∈ (torusMonodromyInnerCollar.{u}).source) ↔ _
  rw [torusMonodromyInnerCollar_source]
  simp only [mem_univ, true_and]
  rfl


/-! ### L3-cut -/

/-- **L3-cut (torus bundle over the circle, cut at a fibre).** One piece, one self-seam, the
piece an actual `T² × I` (`annulusCircleCarrier`); no comparison with the mapping-torus carrier
of `Closure/TorusBundleRaw.lean:45–64`. -/
theorem exists_selfSeam_cutData_of_torusBundle (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (hW : W.model.boundary W.Carrier = ∅) (p : W.Carrier → Circle)
    (hp : ContMDiff W.model (𝓡 1) ∞ p) (hsub : ∀ x, Surjective (mfderiv W.model (𝓡 1) p x))
    (f : Torus → W.Carrier) (hf : IsSmoothEmbedding torusModel W.model ∞ f)
    (hr : range f = p ⁻¹' {1}) :
    ∃ D : RegularCutData W (BoundaryTori.empty W),
      D.count = 1 ∧ D.seamCount = 1 ∧ (∀ c, D.side c true = D.side c false) ∧
      ∀ j, Nonempty (annulusCircleCarrier.{u}.Carrier ≃ₘ⟮annulusCircleCarrier.{u}.model, 𝓡∂ 3⟯
        (D.piece j).Piece) := by
  obtain ⟨Ψ, φ, hΨ, -, hper, hinj, hsurj, hchart⟩ :=
    exists_circleCut_of_boundary_eq_empty W hW p hp hsub f hf hr
  have hbij := bijective_mfderiv_of_stripCharts hchart
  obtain ⟨d, hds, hdf⟩ := hchart 0 (1 / 10) (-1) 1 (by norm_num) (by norm_num)
  have hd (q : Torus × ℝ) : d q = Ψ (q.1, 0 + 1 / 10 * q.2) := congrFun hdf q
  let S : TorusSeam W :=
    { collar := d
      source_eq := by
        rw [hds]
        ext q
        simp [signedCollarSource]
      target_interior := fun x _ => mem_interior_of_boundary_eq_empty hW x }
  let P := torusCutPiece W Ψ hΨ hbij
  let pol := torusMonodromyPolarDiffeomorph.{u}
  have hmap (q : GC.Seifert.productSet.{u} 2) : P.map q = Ψ ((pol q).1, ((pol q).2 : ℝ)) := rfl
  let L : Bool → PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1)
      (GC.Seifert.productSet.{u} 2) ∞ :=
    fun b => if b then twistedInnerCollar.{u} φ else torusMonodromyOuterCollar.{u}
  have hmem (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
      (t, halfPoint s hs) ∈ halfCollarSource := hs1
  have hzero (t : Torus) : (t, halfZero) ∈ halfCollarSource := hmem t le_rfl one_pos
  -- the fold on the two half collars
  have hfold_false (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
      P.map (torusMonodromyOuterCollar.{u} (t, halfPoint s hs)) = S.collar (t, s) := by
    obtain ⟨h1, h2⟩ := polar_outerCollar.{u} (hmem t hs hs1)
    rw [hmap]
    change Ψ ((pol _).1, ((pol _).2 : ℝ)) = d (t, s)
    rw [h1, h2, hd, halfPoint_val]
    congr 2
    ring
  have hfold_true (t : Torus) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
      P.map (twistedInnerCollar.{u} φ (t, halfPoint s hs)) = S.collar (t, -s) := by
    obtain ⟨h1, h2⟩ := polar_innerCollar.{u} (p := (φ.symm t, halfPoint s hs)) (hmem _ hs hs1)
    rw [hmap, twistedInnerCollar_apply]
    change Ψ ((pol _).1, ((pol _).2 : ℝ)) = d (t, -s)
    rw [h1, h2, hd, halfPoint_val, show (1 : ℝ) - s / 10 = -(s / 10) + 1 by ring, hper,
      φ.apply_symm_apply]
    congr 2
    ring
  let D : RegularCutData W (BoundaryTori.empty W) :=
    { count := 1
      count_pos := Nat.one_pos
      piece := fun _ => P
      covers := by
        refine eq_univ_of_forall fun x => mem_iUnion.mpr ⟨0, ?_⟩
        obtain ⟨z, t, ht, hzt⟩ := hsurj 0 x
        refine ⟨pol.symm (z, ⟨t, ht.1, by linarith [ht.2]⟩), ?_⟩
        rw [hmap, pol.apply_symm_apply]
        exact hzt
      seamCount := 1
      seam := fun _ => S
      seam_disjoint := fun c c' h => (h (Subsingleton.elim c c')).elim
      side := fun _ _ => 0
      lift := fun _ b => L b
      lift_source := by
        intro c b
        cases b
        · exact torusMonodromyOuterCollar_source.{u}
        · exact twistedInnerCollar_source.{u} φ
      lift_eq := by
        intro c b t s hs hs1
        cases b
        · exact hfold_false t hs hs1
        · exact hfold_true t hs hs1
      externalOwner := fun i => i.elim0
      externalLift := fun i => i.elim0
      externalLift_source := fun i => i.elim0
      externalLift_eq := fun i => i.elim0
      boundary_exhausted := by
        intro j
        ext q
        constructor
        · intro hq
          obtain rfl : (0 : Fin 1) = j := Subsingleton.elim _ _
          rcases productSet_two_isBoundaryPoint_iff.mp hq with h | h
          · refine Or.inl ⟨0, false, (pol q).1, rfl, pol.injective ?_⟩
            obtain ⟨h1, h2⟩ := polar_outerCollar.{u} (hzero (pol q).1)
            change pol q = pol (torusMonodromyOuterCollar.{u} ((pol q).1, halfZero))
            refine Prod.ext h1.symm (Subtype.ext ?_)
            rw [h2, h]
            change (0 : ℝ) = 0 / 10
            norm_num
          · refine Or.inl ⟨0, true, φ (pol q).1, rfl, pol.injective ?_⟩
            change pol q = pol (twistedInnerCollar.{u} φ (φ (pol q).1, halfZero))
            rw [twistedInnerCollar_apply, φ.symm_apply_apply]
            obtain ⟨h1, h2⟩ := polar_innerCollar.{u} (hzero (pol q).1)
            refine Prod.ext h1.symm (Subtype.ext ?_)
            rw [h2, h]
            change (1 : ℝ) = 1 - 0 / 10
            norm_num
        · rintro (⟨c, b, t, h, rfl⟩ | ⟨i, -⟩)
          · subst h
            apply productSet_two_isBoundaryPoint_iff.mpr
            cases b
            · left
              obtain ⟨-, h2⟩ := polar_outerCollar.{u} (hzero t)
              change ((pol (torusMonodromyOuterCollar.{u} (t, halfZero))).2 : ℝ) = 0
              rw [h2]
              change (0 : ℝ) / 10 = 0
              norm_num
            · right
              obtain ⟨-, h2⟩ := polar_innerCollar.{u} (hzero (φ.symm t))
              change ((pol (twistedInnerCollar.{u} φ (t, halfZero))).2 : ℝ) = 1
              rw [twistedInnerCollar_apply, h2]
              change (1 : ℝ) - 0 / 10 = 1
              norm_num
          · exact i.elim0
      overlap := by
        intro j j' q q' hqq
        obtain rfl : j = j' := Subsingleton.elim _ _
        have hseam (r : GC.Seifert.productSet.{u} 2) (hr1 : ((pol r).2 : ℝ) = 1) :
            P.map r = S.collar (φ (pol r).1, 0) := by
          rw [hmap]
          change Ψ ((pol r).1, ((pol r).2 : ℝ)) = d (φ (pol r).1, 0)
          rw [hr1, hd, show (1 : ℝ) = 0 + 1 by ring, hper]
          congr 2
          ring
        by_cases h1 : ((pol q).2 : ℝ) = 1
        · exact Or.inr ⟨0, φ (pol q).1, hseam q h1⟩
        by_cases h1' : ((pol q').2 : ℝ) = 1
        · exact Or.inr ⟨0, φ (pol q').1, hqq.trans (hseam q' h1')⟩
        left
        have hlt : ((pol q).2 : ℝ) < 1 := lt_of_le_of_ne (pol q).2.property.2 h1
        have hlt' : ((pol q').2 : ℝ) < 1 := lt_of_le_of_ne (pol q').2.property.2 h1'
        have hΨq : Ψ ((pol q).1, ((pol q).2 : ℝ)) = Ψ ((pol q').1, ((pol q').2 : ℝ)) :=
          (hmap q).symm.trans (hqq.trans (hmap q'))
        have hq := @hinj 0 ((pol q).1, ((pol q).2 : ℝ))
          ⟨mem_univ _, (pol q).2.property.1, by simpa using hlt⟩ ((pol q').1, ((pol q').2 : ℝ))
          ⟨mem_univ _, (pol q').2.property.1, by simpa using hlt'⟩ hΨq
        obtain ⟨hq1, hq2⟩ := Prod.ext_iff.mp hq
        have hpq : pol q = pol q' := Prod.ext hq1 (Subtype.ext hq2)
        rw [pol.injective hpq]
      external_exhausted := by rw [hW, BoundaryTori.empty_image]
      external_seam_disjoint := fun i => i.elim0 }
  exact ⟨D, rfl, rfl, fun _ => rfl,
    fun _ => ⟨Diffeomorph.refl annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.Carrier ∞⟩⟩

end GC.GraphManifold.Assembly
