import DifferentialGeometry.Topology.VectorBundle.CircleBase.OrthonormalFrame
import DifferentialGeometry.Topology.VectorBundle.CircleBase.SolidTorusDiscApplications
import DifferentialGeometry.Topology.Manifold.RegularLevel.SublevelAtlasBridgeApplications

/-!
# The circle-soul zero model: `D(V) ≅ solidTorusCarrier` (LFR54 → `ZeroModel.solidTorus`)

Lane LFR54-P1, group G3: the consumer of P1a + P1b + 51-F/51-D + P2. For a smooth Riemannian
rank-two bundle `V` over `S¹ = AddCircle 1` whose total space carries a smooth orientation:

* `nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orientable`: the closed unit disc bundle
  `D(V)` with its native boundary charts (`morseModelWithCornersHalfSpace 2`) is diffeomorphic to the
  fixed model `GC.GraphManifold.solidTorusCarrier`;
* `exists_solidTorusCarrier_diffeomorph_regularSublevel_of_orientable`: the same in the chapter-14
  model — the sublevel `{‖z.2‖² ≤ 1}` with the smooth boundary atlas
  `SmoothBoundaryAtlas.regularSublevel` (`𝓡∂ 3`) — through an actual diffeomorphism that carries
  the boundary torus `{cliffordHeight = 0}` of the solid torus onto the unit sphere bundle
  `{‖z.2‖ = 1}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Manifold.RegularLevel

namespace DifferentialGeometry.Topology.VectorBundle

universe u

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

/-- **Circle soul, native charts.** For a smooth Riemannian rank-two bundle over `S¹` with orientable
total space, `solidTorusCarrier` is diffeomorphic to the closed unit disc bundle `D(V)` with its
native boundary charts. -/
theorem nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orientable
    (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
      (finrank_real_prod_eq_three hF) 1 one_pos
    Nonempty (Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
      (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞) := by
  obtain ⟨s, hs, hon⟩ := exists_orthonormal_frame_of_orientable_totalSpace_circle hF oV
  exact nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orthonormal.{u} hF s hs hon

/-- **Circle soul, chapter-14 model.** For a smooth Riemannian rank-two bundle over `S¹` with
orientable total space there is a diffeomorphism from `solidTorusCarrier` onto the closed unit disc
bundle `{‖z.2‖² ≤ 1}` with the smooth boundary atlas of chapter 14 (`𝓡∂ 3`); it carries the
boundary torus `{cliffordHeight = 0}` onto the unit sphere bundle. -/
theorem exists_solidTorusCarrier_diffeomorph_regularSublevel_of_orientable
    (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V)) :
    letI := (DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel
      (bundleRadiusBoundaryModel (IB := 𝓘(ℝ, ℝ)) (finrank_real_prod_eq_three hF)) (n := 2)
      finrank_morseModel
      (contMDiff_fiberRadiusSquared_boundaryModel (V := V) (finrank_real_prod_eq_three hF))
      (1 ^ 2) (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero
        (finrank_real_prod_eq_three hF) one_pos z hz)).toChartedSpace
    ∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model (𝓡∂ 3)
        GC.GraphManifold.solidTorusCarrier.{u}.Carrier
        ({z | fiberRadiusSquared z ≤ 1 ^ 2} : Set (TotalSpace F V)) ∞,
      ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
        GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
          ‖(Φ x).val.2‖ = 1 := by
  have hd := finrank_real_prod_eq_three hF
  let csNorm_LFR54P1 := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
  let csDisc_LFR54P1 := closedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
  let mfDisc_LFR54P1 := closedDiscBundle_isManifold (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
  let csAtlas_LFR54P1 := (DifferentialGeometry.Topology.SmoothBoundaryAtlas.regularSublevel
      (bundleRadiusBoundaryModel (IB := 𝓘(ℝ, ℝ)) hd) (n := 2) finrank_morseModel
      (contMDiff_fiberRadiusSquared_boundaryModel (V := V) hd)
      (1 ^ 2) (fun z hz => mfderiv_fiberRadiusSquared_boundaryModel_ne_zero
        hd one_pos z hz)).toChartedSpace
  obtain ⟨Ψ⟩ := nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orientable.{u} hF oV
  let e := normClosedDiscSublevelHomeomorph (F := F) (V := V) 1 one_pos
  let csPull_LFR54P1 := DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace
    (H := MorseHalfSpace 2) e
  let DS := DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
    (I := morseModelWithCornersHalfSpace 2) (n := ∞) e
  obtain ⟨Φ₂, hΦ₂⟩ := exists_closedDisc_regularSublevelAtlas_diffeomorph (IB := 𝓘(ℝ, ℝ)) (V := V)
    hd 1 one_pos
  refine ⟨(Ψ.trans DS).trans Φ₂, fun x => ?_⟩
  have hval : (((Ψ.trans DS).trans Φ₂) x).val = (Ψ x).val := hΦ₂ (DS (Ψ x))
  rw [hval]
  have h1 := GC.GraphManifold.solidTorus_isBoundaryPoint_iff.{u} x
  have h2 : GC.GraphManifold.solidTorusCarrier.{u}.model.IsBoundaryPoint x ↔
      (morseModelWithCornersHalfSpace 2).IsBoundaryPoint (Ψ x) :=
    (Ψ.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)
  have h3 := normClosedDiscBundle_boundary_iff (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos (Ψ x)
  exact h1.symm.trans (h2.trans h3)

end DifferentialGeometry.Topology.VectorBundle
