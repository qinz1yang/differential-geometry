import DifferentialGeometry.Geometry.Collapse.ZeroModel.PuncturedRP3ZeroModel

/-!
# Consumer of Q1: the punctured `ℝP³` zero model with its boundary sphere

Lane LFR54-QUOT. The embedding of Q1 can be chosen so that, in addition, the boundary unit sphere
bundle `‖z‖ = 1` of `D(V)` is carried exactly onto the boundary sphere `c.chart '' S²` of the removed
ball (`exists_puncturedRP3_embedding_boundary_of_antipodal_unit_map`): the form used by the
connected-sum gluing of the `puncturedRP3` zero model (LFR52, ZSP02 boundary type `S²`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Module Metric Manifold
open scoped Manifold ContDiff Topology

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

/-- **Punctured `ℝP³` zero model with boundary.** Q1 together with the boundary correspondence:
the unit sphere bundle of `D(V)` goes exactly onto the boundary sphere of the removed ball. -/
theorem exists_puncturedRP3_embedding_boundary_of_antipodal_unit_map
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
      range f = {x | x ∉ c.chart '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1} ∧
      ∀ z, f z ∈ c.chart '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↔ ‖z.val.2‖ = 1 := by
  let := normClosedDiscBundleChartedSpace (IB := 𝓡 2) (V := V) hd 1 one_pos
  obtain ⟨f, hf, hrange, hval⟩ := exists_band_embedding_of_antipodal_unit_map.{u} hd ν hν hνS
    hνinj hνsurj hνneg hνloc
  obtain ⟨c, hball, hsphere⟩ := exists_orientedBallChart_image_ball_eq.{u}
  refine ⟨c, f, hf, ?_, fun z => ?_⟩
  · rw [hrange, hball]
    ext y
    exact (not_lt (a := (1 / 2 : ℝ)) (b := bandFn y)).symm
  · rw [hsphere]
    change bandFn (f z) = 1 / 2 ↔ _
    rw [hval]
    have hp : (0 : ℝ) < 1 + ‖z.val.2‖ ^ 2 := by positivity
    rw [div_eq_iff hp.ne']
    constructor
    · intro h
      have h1 : ‖z.val.2‖ ^ 2 = 1 := by linarith
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h1
    · intro h
      rw [h]
      norm_num

end DifferentialGeometry.Topology.VectorBundle
