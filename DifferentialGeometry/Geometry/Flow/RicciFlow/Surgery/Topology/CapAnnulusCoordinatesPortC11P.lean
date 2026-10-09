import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import DifferentialGeometry.Geometry.Metric.CompactSourceDerivative
import DifferentialGeometry.Topology.Manifold.SphereDirection

/-!
# CapAnnulusCoordinates (port, S-CH11-PORT-B1)

Source: donor `CapAnnulusCoordinates.lean` (chapter11 HEAD a73e4bdbfd), verbatim except for the
elaboration-level patches below. 来源：donor 原文，仅做 elaboration 层面修补。

Patches (port-file line numbers):
* L38: file-local `Nonempty (Sphere 2)` instance
  (from `NormedSpace.sphere_nonempty`); no global instance exists for the `Metric.sphere` abbrev.
  `Classical.choice (inferInstance : Nonempty (Sphere 2))` in the donor text now resolves.
* L41: file-local `ChartedSpace
  (E × ℝ) NeckCylinder` instance (`ModelProd` is not unfolded by the instance discrimination tree);
  needed by the unchanged signature of `compact_bound_of_self_model`.
* L46: matching file-local `IsManifold` instance for that
  charted-space tag (the call site passes `NeckCylinderModel`).
* L102: explicit `(E := ThreeSpace) (n := 2)` for
  `contMDiffOn_sphereDirection` (the `Fact (finrank = n + 1)` instance was stuck on a metavariable).

No statement/definition/proof idea altered. 声明名、陈述、证明思路均未改动。
-/

set_option autoImplicit false
noncomputable section

open Set Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

private local instance : Nonempty (Sphere 2) :=
  (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype

private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 2) × ℝ) NeckCylinder :=
  inferInstanceAs (ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) NeckCylinder)

private local instance :
    IsManifold (H := EuclideanSpace ℝ (Fin 2) × ℝ) NeckCylinderModel ∞ NeckCylinder :=
  IsManifold.prod (Sphere 2) ℝ

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- A fixed annulus width, selected before any neck, event or fine accuracy. -/
def capSeamWidth : ℝ := min (standardCapL / 8) (1 / 8)

theorem capSeamWidth_pos : 0 < capSeamWidth := by
  apply lt_min
  · exact div_pos (by
      rw [standardCapL_eq_transitionEnd]
      exact StandardCap.transitionEnd_pos) (by norm_num)
  · norm_num

theorem capSeamWidth_le_radius : capSeamWidth ≤ standardCapL / 8 := min_le_left _ _

theorem capSeamWidth_le_one : capSeamWidth ≤ 1 / 8 := min_le_right _ _

def capSeamAnnulus : Set ThreeSpace :=
  {x | standardCapL - 2 * capSeamWidth ≤ ‖x‖ ∧
    ‖x‖ ≤ standardCapL + 2 * capSeamWidth}

/-- The value at the origin is irrelevant to the fixed annulus and makes the map total. -/
def capRadialCoordinates (x : ThreeSpace) : NeckCylinder :=
  (sphereDirection (Classical.choice (inferInstance : Nonempty (Sphere 2))) x,
    ‖x‖ - standardCapL)

theorem capRadialCoordinates_pos_smul (y : Sphere 2) {r : ℝ} (hr : 0 < r) :
    capRadialCoordinates (r • (y : ThreeSpace)) = (y, r - standardCapL) := by
  simp only [capRadialCoordinates, sphereDirection_pos_smul _ _ hr,
    norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]

theorem capSeamAnnulus_ne_zero {x : ThreeSpace} (hx : x ∈ capSeamAnnulus) : x ≠ 0 := by
  have hL : 0 < standardCapL := by
    rw [standardCapL_eq_transitionEnd]
    exact StandardCap.transitionEnd_pos
  apply norm_pos_iff.mp
  have ha := capSeamWidth_le_radius
  have hlo := hx.1
  linarith

theorem isCompact_capSeamAnnulus : IsCompact capSeamAnnulus := by
  apply (isCompact_closedBall (0 : ThreeSpace)
    (standardCapL + 2 * capSeamWidth)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx
    exact Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hx.2)

theorem capRadialCoordinates_smooth :
    ContMDiffOn ThreeModel NeckCylinderModel ∞ capRadialCoordinates ({0}ᶜ : Set ThreeSpace) := by
  have hn : ContMDiffOn ThreeModel 𝓘(ℝ, ℝ) ∞
      (fun x : ThreeSpace => ‖x‖ - standardCapL) ({0}ᶜ : Set ThreeSpace) := by
    intro x hx
    exact ((contDiffAt_norm ℝ (show x ≠ 0 from hx)).sub contDiffAt_const).contMDiffAt.contMDiffWithinAt
  exact (contMDiffOn_sphereDirection (E := ThreeSpace) (n := 2)
    (Classical.choice (inferInstance : Nonempty (Sphere 2)))).prodMk hn

private theorem compact_bound_of_self_model
    (J : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
      (EuclideanSpace ℝ (Fin 2) × ℝ))
    [IsManifold J ∞ NeckCylinder]
    (hJ : J = 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ))
    (g : SmoothRiemannianMetric J NeckCylinder)
    {f : ThreeSpace → NeckCylinder} {U K : Set ThreeSpace}
    (hU : IsOpen U) (hf : ContMDiffOn ThreeModel J 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ B : ℝ≥0, ∀ x ∈ K, ∀ v : ThreeSpace,
      Real.sqrt (g.inner (f x) (mfderiv ThreeModel J f x v)
        (mfderiv ThreeModel J f x v)) ≤ B * ‖v‖ := by
  cases hJ
  exact exists_compact_source_mfderiv_bound g hU hf hK hKU

/-- A single fixed-model derivative constant precedes every actual neck and cap scale. -/
theorem exists_capRadialCoordinates_bound :
    ∃ B : ℝ≥0, 1 ≤ B ∧ ∀ x ∈ capSeamAnnulus, ∀ v : ThreeSpace,
      Real.sqrt (roundCylinderMetric.inner (capRadialCoordinates x)
        (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x v)
        (mfderiv ThreeModel NeckCylinderModel capRadialCoordinates x v)) ≤ B * ‖v‖ := by
  have hmodel : NeckCylinderModel = 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) :=
    modelWithCornersSelf_prod.symm
  obtain ⟨B, hB⟩ := compact_bound_of_self_model NeckCylinderModel hmodel
    roundCylinderMetric isOpen_compl_singleton
    (capRadialCoordinates_smooth.of_le (by decide)) isCompact_capSeamAnnulus
    (fun _ hx => capSeamAnnulus_ne_zero hx)
  refine ⟨max B 1, le_max_right _ _, fun x hx v => (hB x hx v).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left B 1) (norm_nonneg v)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
