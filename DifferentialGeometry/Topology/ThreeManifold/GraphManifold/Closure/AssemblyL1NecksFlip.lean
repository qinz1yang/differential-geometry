import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBallSign
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation

/-!
# Chapter-14 assembly, item L1, G3b / T1′: flipped necks and the orientation of a neck

Lane ASM-L1e (the necks of a ball–handle cycle, T1′ of `build-logs/scratch/ASM-L1b/Shortcut.lean`).

* `neckFlipEquiv F`, `flipNeck N F = N ∘ (F × id)` for a linear isometry `F` of the plane: every
  clause of T1′ except the two orientation clauses is invariant under such flips (they only see
  `‖z‖` and `τ`); `flipNeck_apply`, `flipNeck_source`, `flipNeck_target`.
* `neckSpaceOrientation`: the orientation of `ℝ² × ℝ` transported from `ℝ³` by `neckSpaceEquiv`;
  `NeckPreservesAt N q`: the differential of the neck `N` at `q` carries it to the orientation of
  `W` (a definition: the pointwise orientation behaviour of a neck).
* E3: `neckPreservesAt_flipNeck_iff` (the flip by `F` keeps the behaviour iff `det F > 0`),
  `ballNeckDetAmb_flipNeck` (the chart-free ball determinant scales by `det F`),
  `ballNeckDetAmb_ne_zero`, `det_linearIsometryEquiv_eq_one_or_neg_one`,
  `exists_linearIsometryEquiv_det_neg` (a reflection of the plane).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1eF : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1eF : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-! ## Flipped necks -/

/-- The linear flip `(z, τ) ↦ (F z, τ)` of the neck space. -/
def neckFlipEquiv (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    (EuclideanSpace ℝ (Fin 2) × ℝ) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
  F.toContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)

theorem neckFlipEquiv_apply (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (q : EuclideanSpace ℝ (Fin 2) × ℝ) : neckFlipEquiv F q = (F q.1, q.2) :=
  rfl

/-- A neck precomposed with the flip `(z, τ) ↦ (F z, τ)`. -/
def flipNeck {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞ :=
  (neckFlipEquiv F).toDiffeomorph.toPartialDiffeomorph.trans N

section Flip

variable {W : CompactCarrier.{u}}
  (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
    (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
  (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))

theorem flipNeck_apply (q : EuclideanSpace ℝ (Fin 2) × ℝ) : flipNeck N F q = N (F q.1, q.2) :=
  rfl

theorem flipNeck_eq_comp : (flipNeck N F : EuclideanSpace ℝ (Fin 2) × ℝ → W.Carrier) =
    N ∘ neckFlipEquiv F :=
  rfl

theorem mem_neckDomain_flip_iff {ε' : ℝ} {q : EuclideanSpace ℝ (Fin 2) × ℝ} :
    (F q.1, q.2) ∈ neckDomain ε' ↔ q ∈ neckDomain ε' := by
  simp only [neckDomain, mem_ofPred_eq, LinearIsometryEquiv.norm_map]

theorem neckRounding_flip (ε' : ℝ) (q : EuclideanSpace ℝ (Fin 2) × ℝ) :
    neckRounding ε' (F q.1, q.2) = neckRounding ε' q := by
  simp only [neckRounding, LinearIsometryEquiv.norm_map]

theorem flipNeck_source {ε' : ℝ} (hN : N.source = neckDomain ε') :
    (flipNeck N F).source = neckDomain ε' := by
  ext q
  change q ∈ (neckFlipEquiv F).toDiffeomorph.toPartialDiffeomorph.source ∩
    (neckFlipEquiv F) ⁻¹' N.source ↔ q ∈ neckDomain ε'
  rw [hN]
  change q ∈ univ ∩ (fun q : EuclideanSpace ℝ (Fin 2) × ℝ => (F q.1, q.2)) ⁻¹' neckDomain ε' ↔ _
  rw [univ_inter, mem_preimage, mem_neckDomain_flip_iff]

theorem flipNeck_target : (flipNeck N F).target = N.target := by
  change N.target ∩ N.symm ⁻¹' (neckFlipEquiv F).toDiffeomorph.toPartialDiffeomorph.target =
    N.target
  change N.target ∩ N.symm ⁻¹' univ = N.target
  rw [preimage_univ, inter_univ]

end Flip

/-! ## The orientation of a neck -/

/-- The orientation of the neck space `ℝ² × ℝ` transported from `ℝ³` by `neckSpaceEquiv`. -/
def neckSpaceOrientation : Orientation ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) (Fin 3) :=
  Orientation.map (Fin 3) neckSpaceEquiv
    ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation)

/-- The neck `N` carries the orientation of the neck space to the orientation of `W` at `q`
(the tangent spaces of `W` are read as `ℝ³`, as in `ManifoldOrientation`). -/
def NeckPreservesAt {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞) (q : EuclideanSpace ℝ (Fin 2) × ℝ) : Prop :=
  ∃ L : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3),
    (∀ v, L v = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q v) ∧
    Orientation.map (Fin 3) L neckSpaceOrientation = W.orientation.orientation (N q)

theorem finrank_neckSpace : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by
  simp

/-- The differential of a neck at a source point, as a linear equivalence onto `ℝ³`. -/
def neckDiffEquiv {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞) {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ N.source) : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  ((N.isLocalDiffeomorphAt _ _ _ hq).mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv

theorem neckDiffEquiv_apply {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞) {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ N.source) (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
    neckDiffEquiv N hq v = mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q v := by
  have h := (N.isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞
    hq).mfderivToContinuousLinearEquiv_coe (by simp)
  exact congrArg (fun T => T v) h

theorem neckPreservesAt_iff {W : CompactCarrier.{u}}
    {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞} {q : EuclideanSpace ℝ (Fin 2) × ℝ}
    (hq : q ∈ N.source) :
    NeckPreservesAt N q ↔
      Orientation.map (Fin 3) (neckDiffEquiv N hq) neckSpaceOrientation =
        W.orientation.orientation (N q) := by
  constructor
  · rintro ⟨L, hL, hor⟩
    have hLL : L = neckDiffEquiv N hq := by
      ext v
      rw [hL, neckDiffEquiv_apply]
    rw [← hLL]
    exact hor
  · intro h
    exact ⟨neckDiffEquiv N hq, neckDiffEquiv_apply N hq, h⟩

theorem det_neckFlipEquiv (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    LinearMap.det ((neckFlipEquiv F).toLinearEquiv : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ)) = LinearMap.det F.toLinearMap := by
  have h : ((neckFlipEquiv F).toLinearEquiv : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ)) = LinearMap.prodMap F.toLinearMap LinearMap.id := by
    ext v <;> rfl
  rw [h, LinearMap.det_prodMap, LinearMap.det_id, mul_one]

theorem mfderiv_flipNeck {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : neckFlipEquiv F q ∈ N.source)
    (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (flipNeck N F) q v =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N (neckFlipEquiv F q)
        (neckFlipEquiv F v) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N
      (neckFlipEquiv F q) := (N.isLocalDiffeomorphAt _ _ _ hq).mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (neckFlipEquiv F) q :=
    (neckFlipEquiv F).differentiableAt.mdifferentiableAt
  rw [flipNeck_eq_comp, mfderiv_comp q h1 h2, mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  rfl

theorem mfderiv_flipNeck_zero {W : CompactCarrier.{u}}
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hp : neckFlipEquiv F 0 ∈ N.source) (v : EuclideanSpace ℝ (Fin 2) × ℝ) :
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (flipNeck N F) 0 v :
      EuclideanSpace ℝ (Fin 3)) =
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0 (neckFlipEquiv F v) := by
  rw [mfderiv_flipNeck N F hp v]
  exact congrArg (fun y : EuclideanSpace ℝ (Fin 2) × ℝ =>
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N y (neckFlipEquiv F v) :
      EuclideanSpace ℝ (Fin 3))) (map_zero (neckFlipEquiv F))

/-- In a three-dimensional space, `-X = Y` iff `X ≠ Y` for orientations. -/
theorem orientation_neg_eq_iff_ne {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (hM : Module.finrank ℝ M = 3) {X Y : Orientation ℝ M (Fin 3)} :
    -X = Y ↔ ¬ X = Y := by
  have hc : Fintype.card (Fin 3) = Module.finrank ℝ M := by rw [hM, Fintype.card_fin]
  constructor
  · intro h hXY
    rw [← hXY] at h
    exact Module.Ray.ne_neg_self X h.symm
  · intro h
    rw [(Orientation.ne_iff_eq_neg X Y hc).mp h]
    exact neg_neg Y

/-- **E3a.** The flip by `F` keeps the orientation behaviour iff `det F > 0`. -/
theorem neckPreservesAt_flipNeck_iff {W : CompactCarrier.{u}}
    {N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞}
    {F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)} {ε' : ℝ} (hε' : 0 < ε')
    (hN : N.source = neckDomain ε') :
    NeckPreservesAt (flipNeck N F) 0 ↔
      (NeckPreservesAt N 0 ↔ 0 < LinearMap.det F.toLinearMap) := by
  have h0 : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ neckDomain ε' := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hp : neckFlipEquiv F 0 ∈ N.source := by
    rw [map_zero, hN]
    exact h0
  have hq : (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ (flipNeck N F).source := by
    rw [flipNeck_source N F hN]
    exact h0
  -- the differential of the flipped neck
  have hL : neckDiffEquiv (flipNeck N F) hq =
      (neckFlipEquiv F).toLinearEquiv.trans (neckDiffEquiv N hp) := by
    ext v
    rw [neckDiffEquiv_apply, mfderiv_flipNeck N F hp, LinearEquiv.trans_apply,
      neckDiffEquiv_apply]
    rfl
  have hmt : ∀ (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) (Fin 3)),
      Orientation.map (Fin 3) ((neckFlipEquiv F).toLinearEquiv.trans (neckDiffEquiv N hp)) o =
        Orientation.map (Fin 3) (neckDiffEquiv N hp)
          (Orientation.map (Fin 3) (neckFlipEquiv F).toLinearEquiv o) := by
    intro o
    induction o using Module.Ray.ind with | h v hv => rfl
  rw [neckPreservesAt_iff hq, hL, hmt]
  have hp' : NeckPreservesAt N 0 ↔ NeckPreservesAt N (neckFlipEquiv F 0) := by
    rw [map_zero]
  rw [hp', neckPreservesAt_iff hp]
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) := by
    rw [finrank_neckSpace, Fintype.card_fin]
  by_cases hdet : 0 < LinearMap.det F.toLinearMap
  · have hmap : Orientation.map (Fin 3) (neckFlipEquiv F).toLinearEquiv neckSpaceOrientation =
        neckSpaceOrientation := by
      rw [Orientation.map_eq_iff_det_pos _ _ hcard, det_neckFlipEquiv]
      exact hdet
    rw [hmap]
    simp only [hdet, iff_true]
    exact Iff.rfl
  · have hmap : Orientation.map (Fin 3) (neckFlipEquiv F).toLinearEquiv neckSpaceOrientation =
        -neckSpaceOrientation := by
      rw [← Orientation.ne_iff_eq_neg _ _ hcard, Ne, Orientation.map_eq_iff_det_pos _ _ hcard,
        det_neckFlipEquiv]
      exact hdet
    rw [hmap, Orientation.map_neg]
    simp only [hdet, iff_false]
    exact orientation_neg_eq_iff_ne (by simp)

/-- **E3b.** The chart-free ball determinant of a flipped neck scales by `det F`. -/
theorem ballNeckDetAmb_flipNeck {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (x : ClosedCell 3)
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) {ε' : ℝ} (hε' : 0 < ε')
    (hN : N.source = neckDomain ε') :
    ballNeckDetAmb B e x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (flipNeck N F) 0) =
      LinearMap.det F.toLinearMap *
        ballNeckDetAmb B e x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0) := by
  have hp : neckFlipEquiv F 0 ∈ N.source := by
    rw [map_zero, hN]
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  rw [← det_neckFlipEquiv F, mul_comm]
  unfold ballNeckDetAmb
  set M : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap ∘ₗ
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)).toLinearMap ∘ₗ
      (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
        (B.mfderiv_bijective (e.symm x))).symm.toLinearMap with hM
  set φ : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 2) × ℝ) :=
    ((neckFlipEquiv F).toLinearEquiv : (EuclideanSpace ℝ (Fin 2) × ℝ) →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin 2) × ℝ)) with hφ
  have hsplit : M ∘ₗ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (flipNeck N F)
      0).toLinearMap ∘ₗ neckSpaceEquiv.toLinearMap =
      (M ∘ₗ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0).toLinearMap ∘ₗ
        neckSpaceEquiv.toLinearMap) ∘ₗ
        ((neckSpaceEquiv.symm.toLinearMap ∘ₗ φ ∘ₗ neckSpaceEquiv.toLinearMap)) := by
    refine LinearMap.ext fun v => ?_
    have h1 := mfderiv_flipNeck_zero N F hp (neckSpaceEquiv v)
    have h2 : neckSpaceEquiv (neckSpaceEquiv.symm (φ (neckSpaceEquiv v))) =
        φ (neckSpaceEquiv v) := LinearEquiv.apply_symm_apply _ _
    change M (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model (flipNeck N F) 0
        (neckSpaceEquiv v)) =
      M (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N 0
        (neckSpaceEquiv (neckSpaceEquiv.symm (φ (neckSpaceEquiv v)))))
    rw [h2]
    exact congrArg M h1
  have hconj : LinearMap.det (neckSpaceEquiv.symm.toLinearMap ∘ₗ φ ∘ₗ
      neckSpaceEquiv.toLinearMap) = LinearMap.det φ := by
    have := LinearMap.det_conj φ neckSpaceEquiv.symm
    simpa only [LinearEquiv.symm_symm] using this
  calc _ = LinearMap.det ((M ∘ₗ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N
          0).toLinearMap ∘ₗ neckSpaceEquiv.toLinearMap) ∘ₗ
        ((neckSpaceEquiv.symm.toLinearMap ∘ₗ φ ∘ₗ neckSpaceEquiv.toLinearMap))) :=
        congrArg LinearMap.det hsplit
    _ = LinearMap.det (M ∘ₗ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N
          0).toLinearMap ∘ₗ neckSpaceEquiv.toLinearMap) * LinearMap.det φ := by
        rw [LinearMap.det_comp, hconj]
    _ = _ := rfl

/-- **E3c.** The chart-free ball determinant of a neck differential does not vanish. -/
theorem ballNeckDetAmb_ne_zero {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (x : ClosedCell 3)
    (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
      (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)
    {q : EuclideanSpace ℝ (Fin 2) × ℝ} (hq : q ∈ N.source) :
    ballNeckDetAmb B e x (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) ≠ 0 := by
  have hι : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x) :=
    DifferentialGeometry.Topology.Manifold.closedCell_inclusion_mfderiv_bijective 2 x
  have he : Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)) :=
    (e.mfderivToContinuousLinearEquiv (by simp) (e.symm x)).bijective
  have hN : Bijective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) := by
    have h := (neckDiffEquiv N hq).bijective
    have hfun : ⇑(neckDiffEquiv N hq) =
        ⇑(mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q) :=
      funext (neckDiffEquiv_apply N hq)
    rwa [hfun] at h
  have hbij : Bijective ((mfderiv (𝓡∂ 3) (𝓡 3)
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) x).toLinearMap ∘ₗ
      (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)).toLinearMap ∘ₗ
      (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
        (B.mfderiv_bijective (e.symm x))).symm.toLinearMap ∘ₗ
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model N q).toLinearMap ∘ₗ
      neckSpaceEquiv.toLinearMap) :=
    hι.comp (he.comp ((LinearEquiv.ofBijective
      (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
        (B.mfderiv_bijective (e.symm x))).symm.bijective.comp
      (hN.comp neckSpaceEquiv.bijective)))
  have hu := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective _ hbij)
  exact hu.ne_zero

/-- **E3d.** The determinant of a linear isometry of the plane is `±1`. -/
theorem det_linearIsometryEquiv_eq_one_or_neg_one
    (F : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2)) :
    LinearMap.det F.toLinearMap = 1 ∨ LinearMap.det F.toLinearMap = -1 := by
  classical
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have h : b.toBasis.det ⇑(b.map F) = LinearMap.det F.toLinearMap := by
    have hcomp : ⇑(b.map F) = ⇑F.toLinearMap ∘ ⇑b.toBasis := by
      funext i
      rw [OrthonormalBasis.map_apply, OrthonormalBasis.coe_toBasis]
      rfl
    rw [hcomp, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [← h]
  exact b.det_to_matrix_orthonormalBasis_real (b.map F)

/-- **E3e.** A reflection of the plane. -/
theorem exists_linearIsometryEquiv_det_neg :
    ∃ R : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2),
      LinearMap.det R.toLinearMap < 0 := by
  let v : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
    simp [v] at this
  refine ⟨(ℝ ∙ v)ᗮ.reflection, ?_⟩
  have hdet := Submodule.det_reflection (ℝ ∙ v)ᗮ
  rw [Submodule.orthogonal_orthogonal, finrank_span_singleton hv] at hdet
  change LinearMap.det ((ℝ ∙ v)ᗮ.reflection.toLinearEquiv :
    EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) < 0
  rw [hdet]
  norm_num

end GC.GraphManifold.Assembly
