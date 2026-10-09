import DifferentialGeometry.Topology.VectorBundle.CircleBase.SolidTorusDisc
import DifferentialGeometry.Topology.VectorBundle.FrameTrivializationApplications

/-!
# Consumers of P1b: framed rank-two bundles over the circle and the standard solid torus

A smooth Riemannian rank-two bundle `V` over `S¹ = AddCircle 1` with a smooth orthonormal frame has
closed unit disc bundle diffeomorphic, with boundary, to `solidTorusCarrier`
(`nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orthonormal`: 51-F + 51-D + P1b). If `e`
identifies a carrier `N` with `V`, the same holds for every actual sublevel
`D_T = {‖(e⁻¹ x).2‖ ≤ T}` with its transported boundary charts
(`nonempty_solidTorusCarrier_diffeomorph_discCore_of_orthonormal`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology Manifold
open DifferentialGeometry.Topology.Morse

universe u

namespace DifferentialGeometry.Topology.VectorBundle

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V]

/-- A rank-two bundle over the circle has total dimension three. -/
theorem finrank_real_prod_eq_three (hF : Module.finrank ℝ F = 2) :
    Module.finrank ℝ (ℝ × F) = 2 + 1 := by
  rw [Module.finrank_prod, hF, Module.finrank_self]

/-- **Framed rank-two bundles over the circle.** A smooth orthonormal frame of a smooth Riemannian
rank-two bundle over `S¹` gives a diffeomorphism, with boundary, from `solidTorusCarrier` onto the
closed unit disc bundle (native boundary charts). -/
theorem nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orthonormal
    (hF : Module.finrank ℝ F = 2) (s : Fin 2 → (b : AddCircle (1 : ℝ)) → V b)
    (hs : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun b => (⟨b, s i b⟩ : TotalSpace F V)))
    (hon : ∀ b, Orthonormal ℝ (fun i => s i b)) :
    letI := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
      (finrank_real_prod_eq_three hF) 1 one_pos
    Nonempty (Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
      (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
      {z : TotalSpace F V // ‖z.2‖ ≤ 1} ∞) := by
  let _ := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ))
    (V := Trivial (AddCircle (1 : ℝ)) (EuclideanSpace ℝ (Fin 2))) finrank_circle_plane 1 one_pos
  let _ := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
    (finrank_real_prod_eq_three hF) 1 one_pos
  obtain ⟨Φ, -, hΦn⟩ := exists_normPreserving_trivialization_of_orthonormal hF s hs hon
  obtain ⟨Ψ, -, -⟩ := exists_normClosedDisc_diffeomorph_of_norm_eq finrank_circle_plane
    (finrank_real_prod_eq_three hF) Φ hΦn 1 one_pos
  obtain ⟨D⟩ := nonempty_solidTorusCarrier_diffeomorph_closedDisc.{u}
  exact ⟨D.trans Ψ⟩

/-- **Framed rank-two bundles over the circle, actual sublevels.** If `e` identifies a carrier
`N` with a smooth Riemannian rank-two bundle over `S¹` that has a smooth orthonormal frame, every
actual sublevel `D_T = {‖(e⁻¹ x).2‖ ≤ T}`, `T > 0`, with its transported boundary charts, is
diffeomorphic to `solidTorusCarrier`. -/
theorem nonempty_solidTorusCarrier_diffeomorph_discCore_of_orthonormal
    (hF : Module.finrank ℝ F = 2) (s : Fin 2 → (b : AddCircle (1 : ℝ)) → V b)
    (hs : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) ∞
      (fun b => (⟨b, s i b⟩ : TotalSpace F V)))
    (hon : ∀ b, Orthonormal ℝ (fun i => s i b))
    {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
    {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (e : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e (finrank_real_prod_eq_three hF) T hT
    Nonempty (Diffeomorph GC.GraphManifold.solidTorusCarrier.{u}.model
      (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{u}.Carrier
      {x : N // ‖(e.symm x).2‖ ≤ T} ∞) := by
  let _ := normClosedDiscBundleChartedSpace (IB := 𝓘(ℝ, ℝ)) (V := V)
    (finrank_real_prod_eq_three hF) 1 one_pos
  let _ := discCoreChartedSpace e (finrank_real_prod_eq_three hF) T hT
  obtain ⟨D⟩ := nonempty_solidTorusCarrier_diffeomorph_closedDisc_of_orthonormal.{u} hF s hs hon
  exact ⟨D.trans (unitDiscCoreDiffeomorph e (finrank_real_prod_eq_three hF) T hT)⟩

end DifferentialGeometry.Topology.VectorBundle
