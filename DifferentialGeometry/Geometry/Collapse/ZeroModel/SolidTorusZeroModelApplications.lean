import DifferentialGeometry.Geometry.Collapse.ZeroModel.SolidTorusZeroModel

/-!
# Consumer of the circle-soul zero model: the actual sublevel is a solid torus

Lane LFR54-P1, group G3. If `e` identifies a carrier `N` with a smooth Riemannian rank-two bundle
over `S¹` whose total space is orientable, every actual radial sublevel
`D_T = {‖(e⁻¹ x).2‖ ≤ T} ⊆ N`, `T > 0`, with its transported boundary charts (X84
`discCoreChartedSpace`), is diffeomorphic to `solidTorusCarrier`, the boundary torus going onto the
sphere bundle `{‖(e⁻¹ x).2‖ = T}` (`exists_solidTorusCarrier_diffeomorph_discCore_of_orientable`):
the LFR54 type `S¹ × D²` on the actual sublevel, including the boundary (ZSP02: one torus).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Topology.VectorBundle

universe u

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

/-- **Circle soul on the actual sublevel.** If `e` identifies `N` with a smooth Riemannian rank-two
bundle over `S¹` with orientable total space, the actual sublevel `{‖(e⁻¹ x).2‖ ≤ T}` with its
transported boundary charts is diffeomorphic to `solidTorusCarrier`, boundary torus onto the
sphere bundle `{‖(e⁻¹ x).2‖ = T}`. -/
theorem exists_solidTorusCarrier_diffeomorph_discCore_of_orientable
    (hF : Module.finrank ℝ F = 2)
    (oV : DifferentialGeometry.Topology.Manifold.SmoothOrientation (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F))
      (TotalSpace F V))
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (e : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e (finrank_real_prod_eq_three hF) T hT
    ∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
        (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
        {x : N // ‖(e.symm x).2‖ ≤ T} ∞,
      ∀ x : GC.GraphManifold.solidTorusCarrier.{u}.Carrier,
        GC.GraphManifold.cliffordHeight (x : GC.GraphManifold.solidTorusSet.{u}).val = 0 ↔
          ‖(e.symm (Φ x).val).2‖ = T := by
  have hd := finrank_real_prod_eq_three hF
  let csNorm_LFR54P1 := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V) hd 1 one_pos
  let csCore_LFR54P1 := discCoreChartedSpace e hd T hT
  obtain ⟨Ψ⟩ := nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orientable.{u} hF oV
  let Φ := Ψ.trans (unitDiscCoreDiffeomorph e hd T hT)
  refine ⟨Φ, fun x => ?_⟩
  have h1 := GC.GraphManifold.solidTorus_isBoundaryPoint_iff.{u} x
  have h2 : GC.GraphManifold.solidTorusCarrier.{u}.model.IsBoundaryPoint x ↔
      (morseModelWithCornersHalfSpace 2).IsBoundaryPoint (Φ x) :=
    (Φ.isLocalDiffeomorph x).isBoundaryPoint_iff (by simp)
  have h3 := discCore_boundary_iff e hd T hT (Φ x)
  exact h1.symm.trans (h2.trans h3)

end DifferentialGeometry.Topology.VectorBundle
