import DifferentialGeometry.Geometry.Collapse.ZeroModel.PuncturedRP3ZeroModelApplications
import DifferentialGeometry.Geometry.Collapse.ZeroModel.KleinZeroModelApplications
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# LPA05's sublevel-type clause, surface-soul rows, on the actual disc cores (LFR54 pieces)

Frozen blueprint master207A, LFR54 (A:29526) as used by LPA05 (A:30555): "every indicated smooth
radial sublevel has one of the types `D³, S¹ × D², ℝP³ ∖ int D³, D(o(K))` [...] These
identifications apply to the ACTUAL sublevels and include their boundary". For a carrier
`e : TotalSpace F V ≃ N` (LFR47's normal-flow carrier, LC45's disc cores
`D_T = {‖(e⁻¹ x).2‖ ≤ T}` with their boundary charts `discCoreChartedSpace`) over a closed surface
soul with a rank-one normal bundle, the built LFR54 pieces Q1/Q2 (lane LFR54-QUOT, on `D(V)`) move
to EVERY actual disc core `D_T`, `T > 0`, through LC45's unit-disc map `unitDiscCoreDiffeomorph`:

* `exists_puncturedRP3_embedding_discCore_of_antipodal_unit_map`: an antipodal unit map (Q0's first
  case) makes `D_T` a smoothly embedded `ℝP³ ∖ int D³` (range = complement of an open oriented
  ball), the boundary `{‖(e⁻¹ x).2‖ = T}` going onto the boundary sphere;
* `exists_mobiusBundleSet_diffeomorph_discCore_of_klein_unit_map`: a Klein unit map (Q0's second
  case) makes `D_T` diffeomorphic to the twisted `I`-bundle `{Q ≤ 0}` (`mobiusBundleSet`), boundary
  onto the torus `{Q = 0}`;
* (consumer, `LPA05SublevelTypesApplications`) `discCore_surface_soul_types_of_unit_map_dichotomy`:
  Q0's conclusion shape (antipodal OR Klein unit map) gives one of the two surface-soul rows on
  every `D_T` at once.

The circle-soul row on `D_T` is lane LFR54-P1's
`exists_solidTorusCarrier_diffeomorph_discCore_of_orientable`. What is still missing for LPA05's
clause (Q0 itself, the carrier export, base normalization, orientation, closed source sublevels)
is recorded in build-logs/resume/state-LPA02.md (G3).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Module Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle

open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- The unit-disc map of LC45 sends the unit sphere bundle exactly onto the boundary level
`{‖(e⁻¹ x).2‖ = T}` of the disc core. -/
theorem norm_unitDiscCore_symm_eq_one_iff {e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN
    (TotalSpace F V) N ∞} (hd : Module.finrank ℝ (E2 × F) = 2 + 1) {T : ℝ} (hT : 0 < T)
    {x : {x : N // ‖(e.symm x).2‖ ≤ T}} :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    letI := discCoreChartedSpace e hd T hT
    ‖((unitDiscCoreDiffeomorph e hd T hT).symm x).val.2‖ = 1 ↔ ‖(e.symm x.val).2‖ = T := by
  let csNorm_LPA02 := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let csCore_LPA02 := discCoreChartedSpace e hd T hT
  have h := unitDiscCoreDiffeomorph_apply e hd T hT ((unitDiscCoreDiffeomorph e hd T hT).symm x)
  rw [Diffeomorph.apply_symm_apply] at h
  generalize (unitDiscCoreDiffeomorph e hd T hT).symm x = z at h ⊢
  have hzT : ‖(e.symm x.val).2‖ = T * ‖z.val.2‖ := by
    rw [h, e.symm_apply_apply]
    change ‖T • z.val.2‖ = T * ‖z.val.2‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
  rw [hzT]
  constructor
  · intro h1
    rw [h1, mul_one]
  · intro h1
    exact mul_left_cancel₀ hT.ne' (h1.trans (mul_one T).symm)

/-- **LFR54, `ℝP²` soul, on the actual disc core.** An antipodal unit map of the unit sphere bundle
(Q0's first case) makes every disc core `D_T` of the carrier a smoothly embedded `ℝP³ ∖ int D³`:
its range is the complement of an open oriented ball, and the boundary level
`{‖(e⁻¹ x).2‖ = T}` goes exactly onto the boundary sphere. -/
theorem exists_puncturedRP3_embedding_discCore_of_antipodal_unit_map
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : S2 → TotalSpace F V) (hν : ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ x, ‖(ν x).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z)
    (hνneg : ∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e hd T hT
    ∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : {x : N // ‖(e.symm x).2‖ ≤ T} → projectiveThreeSpaceLift.{u}.Carrier),
      IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
      range f = {y | y ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1} ∧
      ∀ x, f x ∈ c.chart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
        ‖(e.symm x.val).2‖ = T := by
  let csNorm_LPA02 := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let csCore_LPA02 := discCoreChartedSpace e hd T hT
  let csNormT_LPA02 := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd T hT
  let mfNormT_LPA02 := normClosedDiscBundle_isManifold (IB := 𝓡 2) (V := V) hd T hT
  let mfCore_LPA02 := DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) (discCoreHomeomorph e T).symm
  obtain ⟨c, f, hf, hrange, hbd⟩ :=
    exists_puncturedRP3_embedding_boundary_of_antipodal_unit_map.{u} hd ν hν hνS hνinj hνsurj
      hνneg hνloc
  let Φ := unitDiscCoreDiffeomorph e hd T hT
  refine ⟨c, f ∘ Φ.symm, hf.comp_diffeomorph Φ.symm, ?_, fun x => ?_⟩
  · rw [range_comp, EquivLike.range_eq_univ, image_univ, hrange]
  · rw [Function.comp_apply, hbd]
    exact norm_unitDiscCore_symm_eq_one_iff hd hT

/-- **LFR54, Klein soul, on the actual disc core.** A Klein unit map of the unit sphere bundle
(Q0's second case) makes every disc core `D_T` of the carrier diffeomorphic to the twisted
`I`-bundle `{Q ≤ 0}`, the boundary level `{‖(e⁻¹ x).2‖ = T}` going onto the torus `{Q = 0}`. -/
theorem exists_mobiusBundleSet_diffeomorph_discCore_of_klein_unit_map
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : T2 → TotalSpace F V) (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (hνneg : ∀ x y : AddCircle (1 : ℝ),
      ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj))
    (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e hd T hT
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {x : N // ‖(e.symm x).2‖ ≤ T} GC.Seifert.mobiusBundleSet.{u} ∞,
      ∀ x, ‖(e.symm x.val).2‖ = T ↔ GC.Seifert.mobiusBundleFunction (Φ x).val = 0 := by
  let csNorm_LPA02 := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let csCore_LPA02 := discCoreChartedSpace e hd T hT
  obtain ⟨Φ₀, hΦ₀⟩ :=
    exists_mobiusBundleSet_diffeomorph_boundary_of_klein_unit_map.{u} hd ν hν hνS hνinj hνsurj
      hνneg hνloc
  refine ⟨(unitDiscCoreDiffeomorph e hd T hT).symm.trans Φ₀, fun x => ?_⟩
  rw [← norm_unitDiscCore_symm_eq_one_iff (e := e) hd hT (x := x)]
  exact hΦ₀ _

end DifferentialGeometry.Topology.VectorBundle
