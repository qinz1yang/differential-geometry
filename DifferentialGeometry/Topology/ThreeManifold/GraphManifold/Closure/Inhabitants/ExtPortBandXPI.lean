import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusMonodromy
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

/-!
# FC39 external-port regression instance (lane FC39-EXTPORT-INST): radial bands of `T² × I`

The carrier of the external-port instance is the annulus carrier `productCarrier 2`
(`{1/2 ≤ |z| ≤ 3} × S¹ ⊆ PlaneLift × Circle`). Its pieces are radial bands
`{(z, θ) : |z| between r₀ and r₁}`, each the regular sublevel `{(|z|² − r₀²)(|z|² − r₁²) ≤ 0}`
of the boundaryless ambient `PlaneLift × Circle` (the pattern of the X135 cusp piece):

* `bandFn_XPI B`, its regularity, the band atlas and the manifold structure of `BandPiece_XPI B`;
* the product diffeomorphism `bandProduct_XPI B : Torus × [0, 1] ≃ₘ BandPiece_XPI B`,
  `(u, θ, s) ↦ ((r₀ + (r₁ − r₀) s) · τ u, θ)` with `τ` the planar twist of the band;
* the inclusion `bandPiece_XPI B : PieceEmbedding annulusCircleCarrier` (bijective differential from
  the two inclusion differentials);
* the model boundary `{|z| = r₀} ∪ {|z| = r₁}`, its two end components `bandModelFace_XPI B b`
  (the end slices of the product) and the exhaustion `bandModelFace_cases_XPI`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology ComplexConjugate

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

/-- The parameters of a radial band: the two end radii in `[1/2, 3]`, distinct, and the planar
twist index of its product parametrization. -/
structure BandRadii_XPI where
  r0 : ℝ
  r1 : ℝ
  twist : Fin 2
  r0_ge : 1 / 2 ≤ r0
  r0_le : r0 ≤ 3
  r1_ge : 1 / 2 ≤ r1
  r1_le : r1 ≤ 3
  ne : r0 ≠ r1

variable (B : BandRadii_XPI)

theorem BandRadii_XPI.r0_pos : 0 < B.r0 := by linarith [B.r0_ge]

theorem BandRadii_XPI.r1_pos : 0 < B.r1 := by linarith [B.r1_ge]

theorem BandRadii_XPI.sub_ne : B.r1 - B.r0 ≠ 0 := sub_ne_zero.mpr B.ne.symm

/-- The ambient band function `(|z|² − r₀²)(|z|² − r₁²)`. -/
def bandFn_XPI (p : PlaneLift.{0} × Circle) : ℝ :=
  sqDist 0 B.r0 p.1.down * sqDist 0 B.r1 p.1.down

/-- The band. -/
def bandSet_XPI : Set (PlaneLift.{0} × Circle) := {p | bandFn_XPI B p ≤ 0}

theorem contDiff_bandProfile_XPI : ContDiff ℝ ∞ (fun z : ℂ => sqDist 0 B.r0 z * sqDist 0 B.r1 z) :=
  (contDiff_sqDist _ _).mul (contDiff_sqDist _ _)

theorem contMDiff_bandFn_XPI :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞ (bandFn_XPI B) :=
  ((contDiff_bandProfile_XPI B).contMDiff.comp contMDiff_planeLift_down).comp contMDiff_fst

theorem sqDist_zero_eq_XPI (r : ℝ) (z : ℂ) : sqDist 0 r z = (‖z‖ - r) * (‖z‖ + r) := by
  rw [sqDist, sub_zero]
  ring

variable {B} in
/-- The band profile vanishes exactly on the two end circles. -/
theorem bandProfile_eq_zero_iff_XPI {z : ℂ} :
    sqDist 0 B.r0 z * sqDist 0 B.r1 z = 0 ↔ ‖z‖ = B.r0 ∨ ‖z‖ = B.r1 := by
  rw [sqDist_zero_eq_XPI, sqDist_zero_eq_XPI]
  have h0 : ‖z‖ + B.r0 ≠ 0 := by linarith [norm_nonneg z, B.r0_pos]
  have h1 : ‖z‖ + B.r1 ≠ 0 := by linarith [norm_nonneg z, B.r1_pos]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right h0))
    · exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right h1))
  · rintro (h | h) <;> simp [h]

variable {B} in
/-- The band profile is nonpositive exactly between the two radii. -/
theorem bandProfile_nonpos_iff_XPI {z : ℂ} :
    sqDist 0 B.r0 z * sqDist 0 B.r1 z ≤ 0 ↔ (‖z‖ - B.r0) * (‖z‖ - B.r1) ≤ 0 := by
  rw [sqDist_zero_eq_XPI, sqDist_zero_eq_XPI]
  have h0 : 0 < ‖z‖ + B.r0 := by linarith [norm_nonneg z, B.r0_pos]
  have h1 : 0 < ‖z‖ + B.r1 := by linarith [norm_nonneg z, B.r1_pos]
  have hp : 0 < (‖z‖ + B.r0) * (‖z‖ + B.r1) := mul_pos h0 h1
  rw [show (‖z‖ - B.r0) * (‖z‖ + B.r0) * ((‖z‖ - B.r1) * (‖z‖ + B.r1)) =
    ((‖z‖ - B.r0) * (‖z‖ - B.r1)) * ((‖z‖ + B.r0) * (‖z‖ + B.r1)) by ring]
  exact ⟨fun h => nonpos_of_mul_nonpos_left h hp, fun h => mul_nonpos_of_nonpos_of_nonneg h hp.le⟩

variable {B} in
theorem mem_bandSet_iff_XPI {p : PlaneLift.{0} × Circle} :
    p ∈ bandSet_XPI B ↔ (‖p.1.down‖ - B.r0) * (‖p.1.down‖ - B.r1) ≤ 0 :=
  bandProfile_nonpos_iff_XPI

/-- A radius between the two band radii lies in `[1/2, 3]`. -/
theorem between_bounds_XPI {ρ : ℝ} (h : (ρ - B.r0) * (ρ - B.r1) ≤ 0) : 1 / 2 ≤ ρ ∧ ρ ≤ 3 := by
  rcases le_total B.r0 B.r1 with hle | hle
  · have h1 : B.r0 ≤ ρ := by nlinarith
    have h2 : ρ ≤ B.r1 := by nlinarith
    exact ⟨B.r0_ge.trans h1, h2.trans B.r1_le⟩
  · have h1 : B.r1 ≤ ρ := by nlinarith
    have h2 : ρ ≤ B.r0 := by nlinarith
    exact ⟨B.r1_ge.trans h1, h2.trans B.r0_le⟩

theorem bandProfile_regular_XPI {z : ℂ} (hz : sqDist 0 B.r0 z * sqDist 0 B.r1 z = 0) :
    fderiv ℝ (fun w => sqDist 0 B.r0 w * sqDist 0 B.r1 w) z ≠ 0 := by
  have hd (c : ℂ) (ρ : ℝ) : DifferentiableAt ℝ (sqDist c ρ) z :=
    (contDiff_sqDist c ρ).differentiable (by simp) z
  rcases mul_eq_zero.mp hz with h | h
  · refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ B.r0_pos.ne'
    have hn := norm_sub_eq_of_sqDist_eq_zero B.r0_pos.le h
    rw [sub_zero] at hn
    rw [sqDist_zero_eq_XPI, hn]
    exact mul_ne_zero (sub_ne_zero.mpr B.ne) (by linarith [B.r0_pos, B.r1_pos])
  · rw [show (fun w => sqDist 0 B.r0 w * sqDist 0 B.r1 w) =
      fun w => sqDist 0 B.r1 w * sqDist 0 B.r0 w from funext fun w => mul_comm _ _]
    refine fderiv_sqDist_mul_ne_zero (hd _ _) h ?_ B.r1_pos.ne'
    have hn := norm_sub_eq_of_sqDist_eq_zero B.r1_pos.le h
    rw [sub_zero] at hn
    rw [sqDist_zero_eq_XPI, hn]
    exact mul_ne_zero (sub_ne_zero.mpr B.ne.symm) (by linarith [B.r0_pos, B.r1_pos])

theorem bandFn_regular_XPI (p : PlaneLift.{0} × Circle) (hp : bandFn_XPI B p = 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) (bandFn_XPI B) p ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{0}), p.2)) (y := p.1.down)
    ((contMDiff_bandFn_XPI B).mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w => sqDist 0 B.r0 w * sqDist 0 B.r1 w) p.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact bandProfile_regular_XPI B hp

/-- The band atlas (regular sublevel of the ambient). -/
def bandAtlas_XPI : SmoothBoundaryAtlas (𝓘(ℝ, ℂ).prod (𝓡 1)) 3 (bandSet_XPI B) :=
  SmoothBoundaryAtlas.regularSublevel (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2) finrank_planeCircleModel
    (contMDiff_bandFn_XPI B) 0 (bandFn_regular_XPI B)

/-- The band as a type. -/
def BandPiece_XPI : Type := bandSet_XPI B

instance bandTop_XPI : TopologicalSpace (BandPiece_XPI B) :=
  inferInstanceAs (TopologicalSpace (bandSet_XPI B))

instance bandCharts_XPI : ChartedSpace (EuclideanHalfSpace 3) (BandPiece_XPI B) :=
  (bandAtlas_XPI B).toChartedSpace

instance bandSmooth_XPI : IsManifold (𝓡∂ 3) ∞ (BandPiece_XPI B) := (bandAtlas_XPI B).isManifold

instance bandT2_XPI : T2Space (BandPiece_XPI B) := inferInstanceAs (T2Space (bandSet_XPI B))

instance bandSecondCountable_XPI : SecondCountableTopology (BandPiece_XPI B) :=
  inferInstanceAs (SecondCountableTopology (bandSet_XPI B))

theorem bandSet_subset_XPI : bandSet_XPI B ⊆ productSet.{0} 2 := by
  intro p hp
  have hb := between_bounds_XPI B (mem_bandSet_iff_XPI.mp hp)
  exact (mem_planarSet_iff (Or.inl rfl) p.1).mpr ((mem_planarModel_two _).mpr ⟨hb.2, hb.1⟩)

instance bandCompact_XPI : CompactSpace (BandPiece_XPI B) := by
  change CompactSpace (bandSet_XPI B)
  refine isCompact_iff_compactSpace.mp ?_
  have hc : IsCompact (productSet.{0} 2) := by
    rw [productSet_eq_prod]
    exact (isCompact_planarSet (Or.inl rfl)).prod isCompact_univ
  exact hc.of_isClosed_subset (isClosed_le (contMDiff_bandFn_XPI B).continuous continuous_const)
    (bandSet_subset_XPI B)

/-- The value of a band point in the ambient. -/
def BandPiece_XPI.val {B : BandRadii_XPI} (p : BandPiece_XPI B) : PlaneLift.{0} × Circle :=
  Subtype.val (p : bandSet_XPI B)

theorem contMDiff_bandVal_XPI :
    ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ (BandPiece_XPI.val : BandPiece_XPI B → _) :=
  (bandAtlas_XPI B).contMDiff_subtype_val


/-! ## The product parametrization -/

/-- The radius of the slice `s`. -/
def bandRadius_XPI (s : ℝ) : ℝ := B.r0 + (B.r1 - B.r0) * s

theorem bandRadius_between_XPI (s : Icc (0 : ℝ) 1) :
    (bandRadius_XPI B s - B.r0) * (bandRadius_XPI B s - B.r1) ≤ 0 := by
  have h : (bandRadius_XPI B s - B.r0) * (bandRadius_XPI B s - B.r1) =
      (B.r1 - B.r0) ^ 2 * ((s : ℝ) * ((s : ℝ) - 1)) := by
    unfold bandRadius_XPI
    ring
  rw [h]
  exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    (mul_nonpos_of_nonneg_of_nonpos s.2.1 (by linarith [s.2.2]))

theorem bandRadius_pos_XPI (s : Icc (0 : ℝ) 1) : 0 < bandRadius_XPI B s := by
  linarith [(between_bounds_XPI B (bandRadius_between_XPI B s)).1]

theorem norm_bandPoint_XPI (s : Icc (0 : ℝ) 1) (u : Circle) :
    ‖(bandRadius_XPI B s) • planarTwist B.twist (u : ℂ)‖ = bandRadius_XPI B s := by
  rw [norm_smul, norm_planarTwist, Circle.norm_coe, mul_one,
    Real.norm_of_nonneg (bandRadius_pos_XPI B s).le]

/-- The product map `(u, θ, s) ↦ ((r₀ + (r₁ − r₀) s) · τ u, θ)`. -/
def bandProductMap_XPI (q : Torus × Icc (0 : ℝ) 1) : BandPiece_XPI B :=
  ⟨(ULift.up ((bandRadius_XPI B q.2) • planarTwist B.twist (q.1.1 : ℂ)), q.1.2), by
    apply (mem_bandSet_iff_XPI (B := B)).mpr
    change (‖(bandRadius_XPI B q.2) • planarTwist B.twist (q.1.1 : ℂ)‖ - B.r0) *
      (‖(bandRadius_XPI B q.2) • planarTwist B.twist (q.1.1 : ℂ)‖ - B.r1) ≤ 0
    rw [norm_bandPoint_XPI]
    exact bandRadius_between_XPI B q.2⟩

theorem bandProductMap_val_XPI (q : Torus × Icc (0 : ℝ) 1) :
    (bandProductMap_XPI B q).val =
      (ULift.up ((bandRadius_XPI B q.2) • planarTwist B.twist (q.1.1 : ℂ)), q.1.2) :=
  rfl

theorem norm_bandProductMap_XPI (q : Torus × Icc (0 : ℝ) 1) :
    ‖(bandProductMap_XPI B q).val.1.down‖ = bandRadius_XPI B q.2 :=
  norm_bandPoint_XPI B q.2 q.1.1

theorem bandPiece_norm_between_XPI (p : BandPiece_XPI B) :
    (‖p.val.1.down‖ - B.r0) * (‖p.val.1.down‖ - B.r1) ≤ 0 :=
  (mem_bandSet_iff_XPI (B := B) (p := p.val)).mp (Subtype.property (p : bandSet_XPI B))

theorem bandPiece_norm_bounds_XPI (p : BandPiece_XPI B) :
    1 / 2 ≤ ‖p.val.1.down‖ ∧ ‖p.val.1.down‖ ≤ 3 :=
  between_bounds_XPI B (bandPiece_norm_between_XPI B p)

theorem bandPiece_ne_zero_XPI (p : BandPiece_XPI B) : p.val.1.down ≠ 0 :=
  norm_pos_iff.mp (by linarith [(bandPiece_norm_bounds_XPI B p).1])

/-- The slice coordinate `(|z| − r₀)/(r₁ − r₀)` of a band point lies in `[0, 1]`. -/
theorem bandCoord_mem_XPI (p : BandPiece_XPI B) :
    (‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0) ∈ Icc (0 : ℝ) 1 := by
  have hb := bandPiece_norm_between_XPI B p
  have hd := B.sub_ne
  set s := (‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0) with hs
  have hkey : s * (s - 1) ≤ 0 := by
    have h1 : s * (s - 1) = (‖p.val.1.down‖ - B.r0) * (‖p.val.1.down‖ - B.r1) /
        (B.r1 - B.r0) ^ 2 := by
      rw [hs]
      field_simp
      ring
    rw [h1]
    exact div_nonpos_of_nonpos_of_nonneg hb (sq_nonneg _)
  constructor
  · by_contra h
    rw [not_le] at h
    nlinarith
  · by_contra h
    rw [not_le] at h
    nlinarith

/-- The inverse of the product map. -/
def bandProductInv_XPI (p : BandPiece_XPI B) : Torus × Icc (0 : ℝ) 1 :=
  ((unitOf (planarTwist B.twist p.val.1.down), p.val.2),
    ⟨(‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0), bandCoord_mem_XPI B p⟩)

theorem bandProduct_left_inv_XPI (q : Torus × Icc (0 : ℝ) 1) :
    bandProductInv_XPI B (bandProductMap_XPI B q) = q := by
  have hr := bandRadius_pos_XPI B q.2
  apply Prod.ext
  · apply Prod.ext
    · change unitOf (planarTwist B.twist ((bandRadius_XPI B q.2) •
        planarTwist B.twist (q.1.1 : ℂ))) = q.1.1
      rw [planarTwist_smul, planarTwist_planarTwist]
      exact unitOf_smul hr q.1.1
    · rfl
  · apply Subtype.ext
    change (‖(bandProductMap_XPI B q).val.1.down‖ - B.r0) / (B.r1 - B.r0) = q.2.val
    rw [norm_bandProductMap_XPI]
    unfold bandRadius_XPI
    field_simp [B.sub_ne]
    ring

theorem bandProduct_right_inv_XPI (p : BandPiece_XPI B) :
    bandProductMap_XPI B (bandProductInv_XPI B p) = p := by
  apply Subtype.ext
  change (ULift.up ((bandRadius_XPI B (bandProductInv_XPI B p).2) •
    planarTwist B.twist ((unitOf (planarTwist B.twist p.val.1.down) : Circle) : ℂ)), p.val.2) =
      p.val
  have hr : bandRadius_XPI B (bandProductInv_XPI B p).2 = ‖p.val.1.down‖ := by
    change B.r0 + (B.r1 - B.r0) * ((‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0)) = _
    field_simp [B.sub_ne]
    ring
  rw [hr]
  apply Prod.ext
  · apply ULift.ext
    change ‖p.val.1.down‖ • planarTwist B.twist
      ((unitOf (planarTwist B.twist p.val.1.down) : Circle) : ℂ) = p.val.1.down
    rw [← planarTwist_smul, ← norm_planarTwist B.twist p.val.1.down, norm_smul_unitOf,
      planarTwist_planarTwist]
  · rfl

theorem bandProductMap_smooth_XPI :
    ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) ∞ (bandProductMap_XPI B) := by
  apply ((bandAtlas_XPI B).contMDiff_iff_subtype_val _).mpr
  have hs : ContMDiff (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun q : Torus × Icc (0 : ℝ) 1 => bandRadius_XPI B q.2) :=
    contMDiff_const.add (contMDiff_const.mul (contMDiff_subtypeVal_Icc.comp contMDiff_snd))
  have ht : ContMDiff (torusModel.prod (𝓡∂ 1)) 𝓘(ℝ, ℂ) ∞
      (fun q : Torus × Icc (0 : ℝ) 1 => planarTwist B.twist (q.1.1 : ℂ)) :=
    (contDiff_planarTwist B.twist).contMDiff.comp
      (contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst))
  exact (contMDiff_planeLift_up.comp (hs.smul ht)).prodMk (contMDiff_snd.comp contMDiff_fst)

theorem bandProductInv_smooth_XPI :
    ContMDiff (𝓡∂ 3) (torusModel.prod (𝓡∂ 1)) ∞ (bandProductInv_XPI B) := by
  have hz : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun p : BandPiece_XPI B => p.val.1.down) :=
    contMDiff_planeLift_down.comp (contMDiff_fst.comp (contMDiff_bandVal_XPI B))
  have hfirst : ContMDiff (𝓡∂ 3) (𝓡 1) ∞
      (fun p : BandPiece_XPI B => unitOf (planarTwist B.twist p.val.1.down)) := by
    intro p
    have hne : planarTwist B.twist p.val.1.down ≠ 0 := by
      intro h
      apply bandPiece_ne_zero_XPI B p
      rw [← norm_eq_zero, ← norm_planarTwist B.twist, h, norm_zero]
    exact (contMDiffOn_unitOf.contMDiffAt (isOpen_ne.mem_nhds hne)).comp p
      (((contDiff_planarTwist B.twist).contMDiff.comp hz) p)
  have hn : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun p : BandPiece_XPI B => ‖p.val.1.down‖) := by
    intro p
    exact (contDiffAt_norm ℝ (bandPiece_ne_zero_XPI B p)).contMDiffAt.comp p hz.contMDiffAt
  have htime : ContMDiff (𝓡∂ 3) (𝓡∂ 1) ∞
      (fun p : BandPiece_XPI B => (bandProductInv_XPI B p).2) := by
    apply contMDiff_iff_comp_subtypeVal_Icc.mpr
    exact ⟨((hn.sub contMDiff_const).div_const _).continuous.subtype_mk _,
      (hn.sub contMDiff_const).div_const _⟩
  exact (hfirst.prodMk (contMDiff_snd.comp (contMDiff_bandVal_XPI B))).prodMk htime

/-- **The product diffeomorphism of a band.** -/
def bandProduct_XPI :
    (Torus × Icc (0 : ℝ) 1) ≃ₘ⟮torusModel.prod (𝓡∂ 1), 𝓡∂ 3⟯ BandPiece_XPI B where
  toFun := bandProductMap_XPI B
  invFun := bandProductInv_XPI B
  left_inv := bandProduct_left_inv_XPI B
  right_inv := bandProduct_right_inv_XPI B
  contMDiff_toFun := bandProductMap_smooth_XPI B
  contMDiff_invFun := bandProductInv_smooth_XPI B

theorem bandProduct_apply_XPI (q : Torus × Icc (0 : ℝ) 1) :
    bandProduct_XPI B q = bandProductMap_XPI B q :=
  rfl

instance bandConnected_XPI : ConnectedSpace (BandPiece_XPI B) :=
  (bandProduct_XPI B).toHomeomorph.connectedSpace_iff.mp inferInstance


/-! ## The inclusion into the annulus carrier -/

local instance carrierCharts_XPI :
    ChartedSpace (EuclideanHalfSpace 3) annulusCircleCarrier.{0}.Carrier := by
  change ChartedSpace (EuclideanHalfSpace 3) (productSet.{0} 2)
  exact inferInstance

local instance carrierSmooth_XPI : IsManifold (𝓡∂ 3) ∞ annulusCircleCarrier.{0}.Carrier := by
  change IsManifold (𝓡∂ 3) ∞ (productSet.{0} 2)
  exact inferInstance

/-- The inclusion of a band into the carrier. -/
def bandToCarrier_XPI (p : BandPiece_XPI B) : annulusCircleCarrier.{0}.Carrier :=
  ⟨p.val, bandSet_subset_XPI B (Subtype.property (p : bandSet_XPI B))⟩

theorem bandToCarrier_val_XPI (p : BandPiece_XPI B) : (bandToCarrier_XPI B p).val = p.val :=
  rfl

theorem contMDiff_carrierVal_XPI :
    ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞
      (Subtype.val : annulusCircleCarrier.{0}.Carrier → PlaneLift.{0} × Circle) :=
  (productAtlas.{0} 2).contMDiff_subtype_val

theorem bandToCarrier_smooth_XPI :
    ContMDiff (𝓡∂ 3) annulusCircleCarrier.{0}.model ∞ (bandToCarrier_XPI B) :=
  ((productAtlas.{0} 2).contMDiff_iff_subtype_val (bandToCarrier_XPI B)).mpr
    (contMDiff_bandVal_XPI B)

theorem bandToCarrier_injective_XPI : Injective (bandToCarrier_XPI B) := by
  intro p q hpq
  have h := congrArg
    (Subtype.val : annulusCircleCarrier.{0}.Carrier → PlaneLift.{0} × Circle) hpq
  exact Subtype.ext h

theorem bandToCarrier_mfderiv_XPI (p : BandPiece_XPI B) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡∂ 3) (bandToCarrier_XPI B) p) := by
  have hw : Bijective (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1))
      (Subtype.val : annulusCircleCarrier.{0}.Carrier → PlaneLift.{0} × Circle)
      (bandToCarrier_XPI B p)) :=
    (productAtlas.{0} 2).mfderiv_subtypeVal_bijective (bandToCarrier_XPI B p)
  have hc : Bijective (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1))
      ((Subtype.val : annulusCircleCarrier.{0}.Carrier → PlaneLift.{0} × Circle) ∘
        bandToCarrier_XPI B) p) :=
    (bandAtlas_XPI B).mfderiv_subtypeVal_bijective p
  have hchain := mfderiv_comp p (contMDiff_carrierVal_XPI.mdifferentiableAt (by simp))
    ((bandToCarrier_smooth_XPI B).mdifferentiableAt (by simp))
  have hcomp := hchain ▸ hc
  exact Function.Bijective.of_comp_left
    (f := mfderiv (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1))
      (Subtype.val : annulusCircleCarrier.{0}.Carrier → PlaneLift.{0} × Circle)
      (bandToCarrier_XPI B p))
    (g := mfderiv (𝓡∂ 3) (𝓡∂ 3) (bandToCarrier_XPI B) p) hcomp hw.1

/-- **The band as a piece of the annulus carrier.** -/
def bandPiece_XPI : PieceEmbedding annulusCircleCarrier.{0} where
  Piece := BandPiece_XPI B
  map := bandToCarrier_XPI B
  smooth := bandToCarrier_smooth_XPI B
  mfderiv_bijective := bandToCarrier_mfderiv_XPI B
  injective := bandToCarrier_injective_XPI B

theorem bandPiece_map_XPI : (bandPiece_XPI B).map = bandToCarrier_XPI B :=
  rfl

/-- The image of a band: the carrier points whose radius lies between the two radii. -/
theorem range_bandPiece_XPI :
    range (bandPiece_XPI B).map =
      {x : annulusCircleCarrier.{0}.Carrier |
        (‖x.val.1.down‖ - B.r0) * (‖x.val.1.down‖ - B.r1) ≤ 0} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact bandPiece_norm_between_XPI B p
  · intro hx
    refine ⟨(⟨x.val, (mem_bandSet_iff_XPI (B := B) (p := x.val)).mpr hx⟩ : bandSet_XPI B), ?_⟩
    exact Subtype.ext rfl

/-! ## The model boundary and its two ends -/

variable {B} in
theorem band_boundary_iff_XPI {p : BandPiece_XPI B} :
    (𝓡∂ 3).IsBoundaryPoint p ↔ ‖p.val.1.down‖ = B.r0 ∨ ‖p.val.1.down‖ = B.r1 := by
  erw [SmoothBoundaryAtlas.regularSublevel_isBoundaryPoint_iff (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2)
    finrank_planeCircleModel (contMDiff_bandFn_XPI B) 0 (bandFn_regular_XPI B)]
  exact bandProfile_eq_zero_iff_XPI

/-- The end radius of the end `b` (`false = r₀`, `true = r₁`). -/
def bandEndRadius_XPI (b : Bool) : ℝ := if b then B.r1 else B.r0

theorem bandRadius_iccEnd_XPI (b : Bool) :
    bandRadius_XPI B (Assembly.iccEnd b) = bandEndRadius_XPI B b := by
  cases b <;> simp [bandRadius_XPI, bandEndRadius_XPI, Assembly.iccEnd]

/-- The end slice `b` of the product. -/
def bandEnd_XPI (b : Bool) (t : Torus) : BandPiece_XPI B := bandProduct_XPI B (t, Assembly.iccEnd b)

theorem bandEnd_continuous_XPI (b : Bool) : Continuous (bandEnd_XPI B b) :=
  (bandProduct_XPI B).continuous.comp (continuous_id.prodMk continuous_const)

theorem norm_bandEnd_XPI (b : Bool) (t : Torus) :
    ‖(bandEnd_XPI B b t).val.1.down‖ = bandEndRadius_XPI B b := by
  rw [bandEnd_XPI, bandProduct_apply_XPI, norm_bandProductMap_XPI, bandRadius_iccEnd_XPI]

theorem bandEnd_range_XPI (b : Bool) :
    range (bandEnd_XPI B b) = {p | ‖p.val.1.down‖ = bandEndRadius_XPI B b} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact norm_bandEnd_XPI B b t
  · intro hp
    have ht : (bandProductInv_XPI B p).2 = Assembly.iccEnd b := by
      apply Subtype.ext
      change (‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0) = (Assembly.iccEnd b).val
      have hp' : ‖p.val.1.down‖ = bandEndRadius_XPI B b := hp
      rw [hp']
      cases b
      · simp [bandEndRadius_XPI, Assembly.iccEnd]
      · simp [bandEndRadius_XPI, Assembly.iccEnd, div_self B.sub_ne]
    refine ⟨(bandProductInv_XPI B p).1, ?_⟩
    change bandProductMap_XPI B ((bandProductInv_XPI B p).1, Assembly.iccEnd b) = p
    rw [← ht]
    exact bandProduct_right_inv_XPI B p

theorem band_boundary_eq_XPI :
    (𝓡∂ 3).boundary (BandPiece_XPI B) =
      range (bandEnd_XPI B false) ∪ range (bandEnd_XPI B true) := by
  rw [bandEnd_range_XPI B false, bandEnd_range_XPI B true]
  ext p
  exact band_boundary_iff_XPI

theorem bandEnd_in_boundary_XPI (b : Bool) :
    range (bandEnd_XPI B b) ⊆ (𝓡∂ 3).boundary (BandPiece_XPI B) := by
  rw [band_boundary_eq_XPI]
  cases b
  · exact subset_union_left
  · exact subset_union_right

/-- A base point of the end `b`. -/
def bandEndPoint_XPI (b : Bool) : BandPiece_XPI B := bandEnd_XPI B b (1, 1)

/-- The slice coordinate of a band point. -/
def bandCoord_XPI (p : BandPiece_XPI B) : ℝ := (‖p.val.1.down‖ - B.r0) / (B.r1 - B.r0)

theorem continuous_bandCoord_XPI : Continuous (bandCoord_XPI B) :=
  ((continuous_norm.comp (contMDiff_planeLift_down.continuous.comp (continuous_fst.comp
    (contMDiff_bandVal_XPI B).continuous))).sub continuous_const).div_const _

theorem bandCoord_of_boundary_XPI {p : BandPiece_XPI B} (hp : (𝓡∂ 3).IsBoundaryPoint p) :
    bandCoord_XPI B p = 0 ∨ bandCoord_XPI B p = 1 := by
  rcases band_boundary_iff_XPI.mp hp with h | h
  · left
    simp [bandCoord_XPI, h]
  · right
    simp [bandCoord_XPI, h, div_self B.sub_ne]

theorem bandCoord_bandEnd_XPI (b : Bool) (t : Torus) :
    bandCoord_XPI B (bandEnd_XPI B b t) = if b then 1 else 0 := by
  rw [bandCoord_XPI, norm_bandEnd_XPI]
  cases b
  · simp [bandEndRadius_XPI]
  · simp [bandEndRadius_XPI, div_self B.sub_ne]

variable {B} in
theorem bandCoord_eq_iff_XPI {p : BandPiece_XPI B} {b : Bool} :
    bandCoord_XPI B p = (if b then 1 else 0) ↔ ‖p.val.1.down‖ = bandEndRadius_XPI B b := by
  rw [bandCoord_XPI]
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bandEndRadius_XPI]
    rw [div_eq_zero_iff, sub_eq_zero]
    exact ⟨fun h => h.resolve_right B.sub_ne, Or.inl⟩
  · simp only [↓reduceIte, bandEndRadius_XPI]
    rw [div_eq_one_iff_eq B.sub_ne, sub_left_inj]

theorem bandEnd_component_XPI (b : Bool) :
    connectedComponentIn ((𝓡∂ 3).boundary (BandPiece_XPI B)) (bandEndPoint_XPI B b) =
      range (bandEnd_XPI B b) := by
  set C := connectedComponentIn ((𝓡∂ 3).boundary (BandPiece_XPI B)) (bandEndPoint_XPI B b)
  have hpoint : bandEndPoint_XPI B b ∈ (𝓡∂ 3).boundary (BandPiece_XPI B) :=
    bandEnd_in_boundary_XPI B b (mem_range_self (1, 1))
  have hmem : bandEndPoint_XPI B b ∈ C := mem_connectedComponentIn hpoint
  have hsub : C ⊆ (𝓡∂ 3).boundary (BandPiece_XPI B) := connectedComponentIn_subset _ _
  have hcover : C ⊆ {p | bandCoord_XPI B p < 1 / 2} ∪ {p | 1 / 2 < bandCoord_XPI B p} := by
    intro p hp
    rcases bandCoord_of_boundary_XPI B (hsub hp) with h | h
    · exact Or.inl (by change bandCoord_XPI B p < 1 / 2; rw [h]; norm_num)
    · exact Or.inr (by change 1 / 2 < bandCoord_XPI B p; rw [h]; norm_num)
  have hdis : Disjoint {p : BandPiece_XPI B | bandCoord_XPI B p < 1 / 2}
      {p | 1 / 2 < bandCoord_XPI B p} := by
    refine Set.disjoint_left.mpr fun p hp hq => ?_
    change bandCoord_XPI B p < 1 / 2 at hp
    change 1 / 2 < bandCoord_XPI B p at hq
    linarith
  have hcases := (isPreconnected_connectedComponentIn : IsPreconnected C).subset_or_subset
    (isOpen_lt (continuous_bandCoord_XPI B) continuous_const)
    (isOpen_lt continuous_const (continuous_bandCoord_XPI B)) hdis hcover
  have hpt := bandCoord_bandEnd_XPI B b (1, 1)
  apply Set.Subset.antisymm
  · intro p hp
    rw [bandEnd_range_XPI]
    apply (bandCoord_eq_iff_XPI (B := B) (b := b)).mp
    rcases bandCoord_of_boundary_XPI B (hsub hp) with h | h
    · cases b
      · exact h
      · exfalso
        rcases hcases with hl | hr
        · have h1 := hl hmem
          change bandCoord_XPI B (bandEnd_XPI B true (1, 1)) < 1 / 2 at h1
          rw [hpt] at h1
          norm_num at h1
        · have h2 := hr hp
          change 1 / 2 < bandCoord_XPI B p at h2
          rw [h] at h2
          norm_num at h2
    · cases b
      · exfalso
        rcases hcases with hl | hr
        · have h1 := hl hp
          change bandCoord_XPI B p < 1 / 2 at h1
          rw [h] at h1
          norm_num at h1
        · have h2 := hr hmem
          change 1 / 2 < bandCoord_XPI B (bandEnd_XPI B false (1, 1)) at h2
          rw [hpt] at h2
          norm_num at h2
      · exact h
  · exact (isPreconnected_range (bandEnd_continuous_XPI B b)).subset_connectedComponentIn
      (mem_range_self (1, 1)) (bandEnd_in_boundary_XPI B b)

/-- **The model face `b` of a band**: the end slice `b` of its product. -/
def bandModelFace_XPI (b : Bool) : ModelBoundaryFace (bandPiece_XPI B) :=
  ⟨range (bandEnd_XPI B b), bandEndPoint_XPI B b,
    bandEnd_in_boundary_XPI B b (mem_range_self (1, 1)), (bandEnd_component_XPI B b).symm⟩

theorem bandModelFace_val_XPI (b : Bool) :
    (bandModelFace_XPI B b).1 = range fun t => bandProduct_XPI B (t, Assembly.iccEnd b) :=
  rfl

/-- **The two ends exhaust the model faces of a band.** -/
theorem bandModelFace_cases_XPI (F : ModelBoundaryFace (bandPiece_XPI B)) :
    F = bandModelFace_XPI B false ∨ F = bandModelFace_XPI B true := by
  obtain ⟨p, hp, hF⟩ := F.property
  have key : ∀ b : Bool, p ∈ range (bandEnd_XPI B b) → F = bandModelFace_XPI B b := by
    intro b hpb
    apply Subtype.ext
    rw [hF]
    change connectedComponentIn ((𝓡∂ 3).boundary (BandPiece_XPI B)) p = range (bandEnd_XPI B b)
    rw [← bandEnd_component_XPI B b]
    symm
    apply connectedComponentIn_eq
    rw [bandEnd_component_XPI B b]
    exact hpb
  have hp' : p ∈ range (bandEnd_XPI B false) ∪ range (bandEnd_XPI B true) := by
    rw [← band_boundary_eq_XPI]
    exact hp
  rcases hp' with h | h
  · exact Or.inl (key false h)
  · exact Or.inr (key true h)

/-- The ambient image of the end slice `b`: the carrier circle-torus of radius `r_b`. -/
theorem range_bandEnd_map_XPI (b : Bool) :
    (range fun t => (bandPiece_XPI B).map (bandEnd_XPI B b t)) =
      {x : annulusCircleCarrier.{0}.Carrier | ‖x.val.1.down‖ = bandEndRadius_XPI B b} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact norm_bandEnd_XPI B b t
  · intro hx
    have hx' : (‖x.val.1.down‖ - B.r0) * (‖x.val.1.down‖ - B.r1) ≤ 0 := by
      have hx2 : ‖x.val.1.down‖ = bandEndRadius_XPI B b := hx
      rw [hx2]
      cases b <;> simp [bandEndRadius_XPI]
    let q : BandPiece_XPI B := (⟨x.val, (mem_bandSet_iff_XPI (B := B) (p := x.val)).mpr hx'⟩ : bandSet_XPI B)
    have hq : q ∈ range (bandEnd_XPI B b) := by
      rw [bandEnd_range_XPI]
      exact hx
    obtain ⟨t, ht⟩ := hq
    refine ⟨t, ?_⟩
    change bandToCarrier_XPI B (bandEnd_XPI B b t) = x
    rw [ht]
    exact Subtype.ext rfl

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
