import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypes

/-!
# The surface-soul rows of LFR54 on every disc core, from Q0's conclusion shape (consumer)

`discCore_surface_soul_types_of_unit_map_dichotomy`: if the unit sphere bundle of a rank-one
Riemannian bundle over a closed surface carries an antipodal unit map OR a Klein unit map (exactly
the conclusion of Q0, `exists_antipodal_or_klein_unit_map`, lane LFR54-Q0), then EVERY actual disc
core `D_T` (`T > 0`) of a carrier `e : TotalSpace F V ≃ N` is either a smoothly embedded
`ℝP³ ∖ int D³` (boundary onto the boundary sphere) or diffeomorphic to the twisted `I`-bundle
`{Q ≤ 0}` (boundary onto the torus `{Q = 0}`). Once Q0 is proved, the surface-soul rows of LFR54
on the actual disc cores are this theorem applied to Q0.
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

/-- **LFR54, surface souls, on every actual disc core (from Q0's conclusion shape).** An antipodal
or a Klein unit map of the unit sphere bundle makes every disc core `D_T`, `T > 0`, of the carrier
either a smoothly embedded `ℝP³ ∖ int D³` or diffeomorphic to `{Q ≤ 0}`, with the boundary level
`{‖(e⁻¹ x).2‖ = T}` going onto the boundary sphere, resp. the boundary torus. -/
theorem discCore_surface_soul_types_of_unit_map_dichotomy
    (e : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)
    (hd : Module.finrank ℝ (E2 × F) = 2 + 1)
    (hQ : (∃ ν : S2 → TotalSpace F V, ContMDiff (𝓡 2) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
        (∀ x, ‖(ν x).2‖ = 1) ∧ Function.Injective ν ∧
        (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ x, ν x = z) ∧
        (∀ x, ν (-x) = ⟨(ν x).proj, -(ν x).2⟩) ∧
        IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ (fun x => (ν x).proj)) ∨
      (∃ ν : T2 → TotalSpace F V, ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, F)) ∞ ν ∧
        (∀ p, ‖(ν p).2‖ = 1) ∧ Function.Injective ν ∧
        (∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) ∧
        (∀ x y : AddCircle (1 : ℝ),
          ν (x + ((1 / 2 : ℝ) : AddCircle (1 : ℝ)), -y) = ⟨(ν (x, y)).proj, -(ν (x, y)).2⟩) ∧
        IsLocalDiffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ (fun p => (ν p).proj)))
    (T : ℝ) (hT : 0 < T) :
    letI := discCoreChartedSpace e hd T hT
    (∃ (c : OrientedBallChart projectiveThreeSpaceLift.{u}.toClosedOrientedManifold)
      (f : {x : N // ‖(e.symm x).2‖ ≤ T} → projectiveThreeSpaceLift.{u}.Carrier),
      IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
      range f = {y | y ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1} ∧
      ∀ x, f x ∈ c.chart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔
        ‖(e.symm x.val).2‖ = T) ∨
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {x : N // ‖(e.symm x).2‖ ≤ T} GC.Seifert.mobiusBundleSet.{u} ∞,
      ∀ x, ‖(e.symm x.val).2‖ = T ↔ GC.Seifert.mobiusBundleFunction (Φ x).val = 0 := by
  rcases hQ with ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩ | ⟨ν, hν, hνS, hνinj, hνsurj, hνneg, hνloc⟩
  · exact Or.inl (exists_puncturedRP3_embedding_discCore_of_antipodal_unit_map.{u} e hd ν hν hνS
      hνinj hνsurj hνneg hνloc T hT)
  · exact Or.inr (exists_mobiusBundleSet_diffeomorph_discCore_of_klein_unit_map.{u} e hd ν hν hνS
      hνinj hνsurj hνneg hνloc T hT)

end DifferentialGeometry.Topology.VectorBundle
