import DifferentialGeometry.Geometry.Collapse.ZeroModel.ProjectiveBallChart
import DifferentialGeometry.Geometry.Collapse.ZeroModel.SublevelEmbedding
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# Q1: the closed `ℝP³` clause of LFR52 — `D(V)` as `ℝP³` minus an open ball

Lane LFR54-QUOT, frozen statement Q1 of `build-logs/scratch/F7-LFR51/QuotInputs.lean`
(blueprint master207A, LFR52 first clause and (LFR52.1); LFR54 type `ℝP³ ∖ int D³`).

Let `V → B` be a smooth Riemannian line bundle over a surface and `ν : S² → TotalSpace F V` a smooth
injective map onto the unit sphere bundle with `ν (-x) = -ν x` and `proj ∘ ν` a local
diffeomorphism. Then the closed unit disc bundle `D(V)` (native boundary charts) embeds smoothly
into `P = projectiveThreeSpaceLift` onto the complement of the unit ball of an oriented ball chart
(`exists_puncturedRP3_embedding_of_antipodal_unit_map`).

Route (LFR52.1): `D(V) = (S² × [-1, 1]) / ((x, t) ∼ (-x, -t))` through `(x, t) ↦ t • ν x`, and the
same quotient is the equatorial band `{w₃² ≤ ½}` of `ℝP³` through `projTheta`. Both maps are
smooth on ambient open sets, so they restrict to a diffeomorphism of the two regular sublevels
(`RegularLevel.exists_sublevel_diffeomorph_of_contMDiffOn`); the band includes as a smooth
embedding (`SublevelEmbedding.isSmoothEmbedding_sublevel_val`); its complement is the polar cap,
the unit ball of the oriented affine chart (`exists_orientedBallChart_image_ball_eq`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Module Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.VectorBundle DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
open DifferentialGeometry.Manifold.RegularLevel

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "S2" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The linear identification `ℝ³ ≃ MorseModel 3` of the model spaces. -/
def rpMorseEquiv : E3 ≃L[ℝ] MorseModel 3 :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

theorem fiberRadiusSquared_eq_norm_sq {F : Type*} {B : Type*} {V : B → Type*}
    [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)] (z : TotalSpace F V) :
    fiberRadiusSquared z = ‖z.2‖ ^ 2 :=
  real_inner_self_eq_norm_sq _

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **`D(V)` is the equatorial band of `ℝP³`.** An explicit smooth embedding of the closed unit
disc bundle onto `{w₃² ≤ ½}`, with `w₃² = ‖z‖² / (1 + ‖z‖²)`. -/
theorem exists_band_embedding_of_antipodal_unit_map
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : S2 → TotalSpace F V) (hν : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ x, ‖(ν x).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    ∃ f : {z : TotalSpace F V // ‖z.2‖ ≤ 1} → projectiveThreeSpaceLift.{u}.Carrier,
      IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
      range f = {y | bandFn y ≤ 1 / 2} ∧
      ∀ z, bandFn (f z) = ‖z.val.2‖ ^ 2 / (1 + ‖z.val.2‖ ^ 2) := by
  let := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let := normClosedDiscBundle_isManifold (IB := 𝓡 2) (V := V) hd 1 one_pos
  have hF : finrank ℝ F = 1 := by
    have h := hd
    rw [Module.finrank_prod, finrank_euclideanSpace_fin] at h
    omega
  obtain ⟨fwd, hfwd, hfwds⟩ := exists_contMDiff_rankOneDescend hF ν hν hνS hνinj hνsurj
    (fun p => -p) hνneg hνloc projTheta.{u} contMDiff_projTheta (fun p t => projTheta_neg p t)
  let bwd := projInvMap.{u} ν hνneg
  have hsurj := rankOneParam_surjective ν hF hνsurj
  let e := rpMorseEquiv
  let I' := (𝓡 3).transContinuousLinearEquiv e
  have hg : ContMDiff I' 𝓘(ℝ, ℝ) ∞ bandFn.{u} :=
    e.contMDiff_transContinuousLinearEquiv_left.mpr contMDiff_bandFn
  have hr : ∀ y, bandFn.{u} y = 1 / 2 → mfderiv I' 𝓘(ℝ, ℝ) bandFn y ≠ 0 :=
    fun y hy => mfderiv_bandFn_ne_zero e y hy
  have hf₁ := contMDiff_fiberRadiusSquared_boundaryModel (IB := 𝓡 2) (V := V) hd
  have hr₁ : ∀ z : TotalSpace F V, fiberRadiusSquared z = 1 ^ 2 →
      mfderiv (bundleRadiusBoundaryModel (IB := 𝓡 2) hd) 𝓘(ℝ, ℝ)
        (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 :=
    fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero hd one_pos z hz
  have hfwdOn : ContMDiffOn (bundleRadiusBoundaryModel (IB := 𝓡 2) hd) I' ∞ fwd univ :=
    ((bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      (e.contMDiff_transContinuousLinearEquiv_right.mpr hfwds)).contMDiffOn
  have hbwdOn : ContMDiffOn I' (bundleRadiusBoundaryModel (IB := 𝓡 2) hd) ∞ bwd
      {y | bandFn y < 1} := by
    intro y hy
    obtain ⟨x, rfl⟩ := exists_rpUp y
    have h := contMDiffAt_projInvMap ν hν hνneg (e4Head_ne_zero_of_bandFn_lt hy)
    exact (e.contMDiffAt_transContinuousLinearEquiv_left.mpr
      ((bundleRadiusBoundaryEquiv hd).contMDiffAt_transContinuousLinearEquiv_right.mpr
        h)).contMDiffWithinAt
  have hbwdfwd : ∀ z, bwd (fwd z) = z := by
    intro z
    obtain ⟨q, rfl⟩ := hsurj z
    rw [hfwd]
    exact projInvMap_projTheta ν hνneg q
  have hfwdbwd : ∀ y, bandFn y ≤ 1 / 2 → fwd (bwd y) = y := by
    intro y hy
    obtain ⟨x, rfl⟩ := exists_rpUp y
    have hne := e4Head_ne_zero_of_bandFn_lt (by linarith : bandFn (rpUp (rpGroup.projection x)) < 1)
    change fwd (projInvMap ν hνneg (rpUp (rpGroup.projection x))) = _
    rw [projInvMap_rpUp, projSphereMap_of_ne ν hne, hfwd]
    exact projTheta_coords hne
  have hband : ∀ z, bandFn (fwd z) = ‖z.2‖ ^ 2 / (1 + ‖z.2‖ ^ 2) := by
    intro z
    obtain ⟨q, rfl⟩ := hsurj z
    rw [hfwd, bandFn_projTheta, norm_rankOneParam ν hνS, sq_abs]
  have hfwdS : ∀ z, fiberRadiusSquared z ≤ 1 ^ 2 → bandFn (fwd z) ≤ 1 / 2 := by
    intro z hz
    rw [fiberRadiusSquared_eq_norm_sq, one_pow] at hz
    rw [hband, div_le_iff₀ (by positivity)]
    linarith
  have hbwdS : ∀ y, bandFn y ≤ 1 / 2 → fiberRadiusSquared (bwd y) ≤ 1 ^ 2 := by
    intro y hy
    obtain ⟨x, rfl⟩ := exists_rpUp y
    have hne := e4Head_ne_zero_of_bandFn_lt (by linarith : bandFn (rpUp (rpGroup.projection x)) < 1)
    change fiberRadiusSquared (projInvMap ν hνneg (rpUp (rpGroup.projection x))) ≤ 1 ^ 2
    rw [projInvMap_rpUp, projSphereMap_of_ne ν hne, fiberRadiusSquared_eq_norm_sq,
      norm_rankOneParam ν hνS, sq_abs, one_pow, sq_le_one_iff_abs_le_one]
    exact abs_coord_le_one_of_bandFn_le hy
  let := closedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let := sublevelChartedSpace I' hg hr
  obtain ⟨Φ₀, hΦ₀⟩ := exists_sublevel_diffeomorph_of_contMDiffOn
    (bundleRadiusBoundaryModel (IB := 𝓡 2) hd) I' hf₁ hr₁ hg hr isOpen_univ
    (isOpen_lt continuous_bandFn continuous_const) (subset_univ _)
    (fun y (hy : bandFn y ≤ 1 / 2) => show bandFn y < 1 by linarith) hfwdOn hbwdOn hfwdS hbwdS
    (fun z _ => hbwdfwd z) hfwdbwd
  let := closedDiscBundle_isManifold (IB := 𝓡 2) (V := V) hd 1 one_pos
  let e₁ := normClosedDiscSublevelHomeomorph (F := F) (V := V) 1 one_pos
  let D₁ := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) e₁
  let Ψ := D₁.trans Φ₀
  have hΨ : ∀ z, (Ψ z : projectiveThreeSpaceLift.{u}.Carrier) = fwd z.val := fun z => hΦ₀ (e₁ z)
  refine ⟨fun z => (Ψ z : projectiveThreeSpaceLift.{u}.Carrier), ?_, ?_, ?_⟩
  · exact (SublevelEmbedding.isSmoothEmbedding_sublevel_val e hg hr).comp_diffeomorph Ψ
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (Ψ z).2
    · intro hy
      refine ⟨Ψ.symm ⟨y, hy⟩, ?_⟩
      change ((Ψ (Ψ.symm ⟨y, hy⟩) : {y // bandFn y ≤ 1 / 2}) : projectiveThreeSpaceLift.{u}.Carrier) = y
      rw [Ψ.apply_symm_apply]
  · intro z
    change bandFn ((Ψ z : {y // bandFn y ≤ 1 / 2}) : projectiveThreeSpaceLift.{u}.Carrier) = _
    rw [hΨ]
    exact hband z.val

end DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective

namespace DifferentialGeometry.Topology.VectorBundle

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Geometry.Collapse.ZeroModel.Projective

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **Q1 (RP² row; LFR52 first clause on the actual disc bundle).** An antipodally equivariant
unit map `ν : S² → S(V)` embeds the closed unit disc bundle `D(V)` (native boundary charts)
smoothly into `ℝP³` onto the complement of the unit ball of an oriented ball chart. -/
theorem exists_puncturedRP3_embedding_of_antipodal_unit_map
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : S2 → TotalSpace F V) (hν : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ x, ‖(ν x).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    ∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : {z : TotalSpace F V // ‖z.2‖ ≤ 1} → projectiveThreeSpaceLift.{u}.Carrier),
      IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
      range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1} := by
  let := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  obtain ⟨f, hf, hrange, -⟩ := exists_band_embedding_of_antipodal_unit_map.{u} hd ν hν hνS hνinj
    hνsurj hνneg hνloc
  obtain ⟨c, hball, -⟩ := exists_orientedBallChart_image_ball_eq.{u}
  refine ⟨c, f, hf, ?_⟩
  rw [hrange, hball]
  ext y
  exact (not_lt (a := (1 / 2 : ℝ)) (b := bandFn y)).symm

end DifferentialGeometry.Topology.VectorBundle
