import DifferentialGeometry.Geometry.Collapse.ZeroModel.KleinZeroModel

/-!
# Consumer of Q2: the Klein disc bundle and its boundary torus

Lane LFR54-QUOT. The diffeomorphism of `nonempty_mobiusBundleCarrier_diffeomorph_of_klein_unit_map`
carries the boundary unit sphere bundle `‖z‖ = 1` of `D(V)` exactly onto the boundary torus
`{Q = 0}` of the fixed model (`exists_mobiusBundleSet_diffeomorph_boundary_of_klein_unit_map`):
the twisted `I`-bundle zero model with its single torus boundary (LFR52, ZSP02 boundary type).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Module Metric
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.VectorBundle

open DifferentialGeometry.Topology.Morse

universe u

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "T2" => AddCircle (1 : ℝ) × AddCircle (1 : ℝ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {B : Type*} [TopologicalSpace B] [ChartedSpace E2 B] [IsManifold (𝓡 2) ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V (𝓡 2)]
  [IsContMDiffRiemannianBundle (𝓡 2) ∞ F V]

/-- **Klein zero model with boundary.** `D(V) ≅ {Q ≤ 0}`, the boundary sphere bundle going onto the
boundary torus `{Q = 0}`. -/
theorem exists_mobiusBundleSet_diffeomorph_boundary_of_klein_unit_map
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (ν : T2 → TotalSpace F V) (hν : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν)
    (hνS : ∀ p, ‖(ν p).2‖ = 1) (hνinj : Function.Injective ν)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z)
    (hνneg : ∀ x y : AddCircle (1 : ℝ),
      ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩)
    (hνloc : IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {z : TotalSpace F V // ‖z.2‖ ≤ 1} GC.Seifert.mobiusBundleSet.{u} ∞,
      ∀ z, ‖z.val.2‖ = 1 ↔ GC.Seifert.mobiusBundleFunction (Φ z).val = 0 := by
  let := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  let := normClosedDiscBundle_isManifold (IB := 𝓡 2) (V := V) hd 1 one_pos
  obtain ⟨D⟩ := nonempty_mobiusBundleCarrier_diffeomorph_of_klein_unit_map.{u} hd ν hν hνS hνinj
    hνsurj hνneg hνloc
  let Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} GC.Seifert.mobiusBundleSet.{u} ∞ := D.symm
  refine ⟨Φ, fun z => ?_⟩
  have h1 : (morseModelWithCornersHalfSpace 2).IsBoundaryPoint z ↔ ‖z.val.2‖ = 1 :=
    normClosedDiscBundle_boundary_iff (IB := 𝓡 2) hd 1 one_pos z
  rw [← h1, ← GC.Seifert.mobiusBundleSet_isBoundaryPoint_iff]
  exact (Φ.isLocalDiffeomorph z).isBoundaryPoint_iff (by simp)

end DifferentialGeometry.Topology.VectorBundle
