import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius
import DifferentialGeometry.Topology.VectorBundle.DiscCoreTransport

/-!
# LC45 as one statement: disc cores and the normal-flow coordinate

Blueprint LC45 (master207A.tex:22169). For a smooth Riemannian vector bundle `V → B` over a
COMPACT boundaryless base, of total dimension `m + 1`, and ONE supplied smooth diffeomorphism
`e : TotalSpace F V ≃ N`, write `u x = ‖(e.symm x).2‖` and `D_T = {u ≤ T}`.

* `lc45_disc_cores_and_normal_flow_coordinate`: `u` is continuous and proper, smooth off
  `e (zero section)`, `u²` is smooth; every `D_T` is compact; for `T > 0` it is a smooth manifold
  with boundary (smooth inclusion) whose boundary points are exactly `{u = T}`; the restriction of
  `(q, v) ↦ e (q, T v)` to the unit disc bundle is a diffeomorphism `D(V) ≃ D_T`;
  `D_T ⊆ int D_{T'}` for `T < T'`; the interiors of the `D_T` (`T > 0`) cover `N`; every compact
  set lies in `int D_T` for all large `T`. If moreover a flow `ϕ` with generator `W` satisfies the
  ray identity `e (q, t v) = ϕ (t - ℓ) (e (q, ℓ v))` (`‖v‖ = 1`, `t > ℓ ≥ 0`), then `du(W) = 1` on
  `{u > ℓ}`; in particular `W` is strictly outward transverse to every `∂D_T`, `T > ℓ`.
  The bundle, map and flow are the SAME witnesses throughout.

Assembly of X84 (`Topology/VectorBundle/DiscCoreTransport.lean`) and the generic flow clause
`mvfderiv_discCoreRadius_eq_one_of_ray` (`SublevelCore/PointNormalFlowRadius.lean`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Topology
open DifferentialGeometry.Topology.Morse DifferentialGeometry.Topology.VectorBundle

namespace DifferentialGeometry.Geometry.Collapse

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
  (e : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞)

/-- **LC45 (row form).** -/
theorem lc45_disc_cores_and_normal_flow_coordinate [CompactSpace B] {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) :
    Continuous (fun x : N => ‖(e.symm x).2‖) ∧
    IsProperMap (fun x : N => ‖(e.symm x).2‖) ∧
    ContMDiffOn IN 𝓘(ℝ, ℝ) ∞ (fun x : N => ‖(e.symm x).2‖) {x : N | (e.symm x).2 ≠ 0} ∧
    ContMDiff IN 𝓘(ℝ, ℝ) ∞ (fun x : N => ‖(e.symm x).2‖ ^ 2) ∧
    (∀ T : ℝ, IsCompact {x : N | ‖(e.symm x).2‖ ≤ T}) ∧
    (∀ (T : ℝ) (hT : 0 < T),
      letI := discCoreChartedSpace e hd T hT
      ContMDiff (morseModelWithCornersHalfSpace m) IN ∞
          (Subtype.val : {x : N // ‖(e.symm x).2‖ ≤ T} → N) ∧
        ∀ x : {x : N // ‖(e.symm x).2‖ ≤ T},
          (morseModelWithCornersHalfSpace m).IsBoundaryPoint x ↔ ‖(e.symm x.val).2‖ = T) ∧
    (∀ (T : ℝ) (hT : 0 < T),
      letI := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd 1 one_pos
      letI := discCoreChartedSpace e hd T hT
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
          {z : TotalSpace F V // ‖z.2‖ ≤ 1} {x : N // ‖(e.symm x).2‖ ≤ T} ∞,
        ∀ z, (Φ z).val = e ⟨z.val.proj, T • z.val.2⟩) ∧
    (∀ S T : ℝ, S < T →
      {x : N | ‖(e.symm x).2‖ ≤ S} ⊆ interior {x : N | ‖(e.symm x).2‖ ≤ T}) ∧
    (⋃ (T : ℝ) (_ : 0 < T), interior {x : N | ‖(e.symm x).2‖ ≤ T}) = univ ∧
    (∀ K : Set N, IsCompact K → ∃ T₀ : ℝ, 0 < T₀ ∧
      ∀ T, T₀ ≤ T → K ⊆ interior {x : N | ‖(e.symm x).2‖ ≤ T}) ∧
    (∀ (ϕ : Flow ℝ N) (ℓ : ℝ), 0 ≤ ℓ →
      (∀ (q : B) (v : V q), ‖v‖ = 1 → ∀ t, ℓ < t →
        e ⟨q, t • v⟩ = ϕ (t - ℓ) (e ⟨q, ℓ • v⟩)) →
      ∀ W : (x : N) → TangentSpace IN x,
      (∀ x, HasMFDerivAt 𝓘(ℝ, ℝ) IN (fun t => ϕ t x) 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (W x))) →
      (∀ x, ℓ < ‖(e.symm x).2‖ →
        mvfderiv (I := IN) (fun y : N => ‖(e.symm y).2‖) x (W x) = 1) ∧
      ∀ T, ℓ < T → ∀ x, ‖(e.symm x).2‖ = T →
        0 < mvfderiv (I := IN) (fun y : N => ‖(e.symm y).2‖) x (W x)) := by
  have hsq : (fun x : N => ‖(e.symm x).2‖ ^ 2) = fun x => fiberRadiusSquared (e.symm x) := by
    funext x
    rw [fiberRadiusSquared, real_inner_self_eq_norm_sq]
  refine ⟨continuous_discCoreRadius_of_isContMDiffRiemannianBundle e,
    isProperMap_discCoreRadius e, contMDiffOn_discCoreRadius_off_zero e,
    hsq ▸ contMDiff_discCoreRadiusSquared e, isCompact_discCore e,
    fun T hT => ⟨discCore_inclusion_contMDiff e hd T hT, discCore_boundary_iff e hd T hT⟩,
    fun T hT => ⟨unitDiscCoreDiffeomorph e hd T hT, unitDiscCoreDiffeomorph_apply e hd T hT⟩,
    fun S T hST => discCore_strictly_nested e hST, iUnion_positive_discCore_interior e,
    fun K hK => exists_eventually_compact_subset_discCore_interior e hK, ?_⟩
  intro ϕ ℓ hℓ hray W hW
  have hone : ∀ x, ℓ < ‖(e.symm x).2‖ →
      mvfderiv (I := IN) (fun y : N => ‖(e.symm y).2‖) x (W x) = 1 :=
    fun x hx => mvfderiv_discCoreRadius_eq_one_of_ray e hℓ hray W hW hx
  refine ⟨hone, fun T hT x hx => ?_⟩
  rw [hone x (hx ▸ hT)]
  exact one_pos

end DifferentialGeometry.Geometry.Collapse
