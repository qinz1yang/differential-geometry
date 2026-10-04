import DifferentialGeometry.Analysis.Calculus.Cutoff.GraphPacketProfiles
import DifferentialGeometry.Analysis.InnerProductSpace.RetainedCoordinateGraph
import DifferentialGeometry.Analysis.Calculus.MonotoneLineSection
import DifferentialGeometry.Analysis.InnerProductSpace.ReferenceGraphProjectedRank
import DifferentialGeometry.Analysis.Calculus.GraphCoverageAdapters
import DifferentialGeometry.Analysis.Calculus.OrthogonalBlockBounds
import DifferentialGeometry.Topology.FixedPoint.NearIdentityHitsCenter
import DifferentialGeometry.Analysis.InnerProductSpace.SpectralCoordinateBlock
import DifferentialGeometry.Geometry.Metric.MarkedSmoothedWitness
import DifferentialGeometry.Geometry.Collapse.SlimGraphPacket
import DifferentialGeometry.Analysis.Calculus.InjectivePostcomposition
import DifferentialGeometry.Geometry.Collapse.GlobalBlockDerivative
import DifferentialGeometry.Geometry.Collapse.OneSheetBudget
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Concrete consumers of the W4-CGP kernels (CGP01–CGP08, SGP01–SGP06)

Each statement applies one delivered kernel to explicit data: the planar circle cutoff, the slim
model block at the actual scale `ℓ = 10⁵`, an explicit graph over a line, the line `a ↦ a` with
coordinate `2a`, a translation of the plane, the spectral section of one plane, the identity rank
model in the plane, and the actual numerical parameters of SGP01/SGP03/SGP06 and CGP02/CGP05/CGP07.
-/

set_option autoImplicit false
open Set Metric
open scoped ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis

/-- CGP01: the planar circle cutoff is smooth, one on the radius-8 plateau and zero beyond 9. -/
theorem planar_circleCutoff_profile :
    ContDiff ℝ ∞ (circleCutoffProfile (E := EuclideanSpace ℝ (Fin 2))) ∧
      circleCutoffProfile (0 : EuclideanSpace ℝ (Fin 2)) = 1 :=
  ⟨contDiff_circleCutoffProfile, circleCutoffProfile_one (by simp)⟩

/-- SGP04: the slim model block at the actual slim scale `ℓ = 10⁵` and `s = 1`. -/
theorem slim_modelBlock_bounds (x : ℝ) :
    ‖fderiv ℝ (graphPacketModelBlock 100000 1) x‖ ≤ 50 * (edgeProfileDerivativeBound + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (graphPacketModelBlock 100000 1)) x‖ ≤
        50 * (edgeProfileDerivativeBound + 1) :=
  graphPacketModelBlock_derivative_bounds (by norm_num) (by norm_num) x

/-- CGP06: the identity coordinate is injective on any constant graph over the whole line. -/
theorem identity_coordinate_injOn_constant_graph (R c : ℝ) :
    InjOn (fun t : (⊤ : Submodule ℝ ℝ) => ContinuousLinearMap.id ℝ ℝ (0 + t + c))
      (ball 0 R) := by
  refine injOn_retained_coordinate_graph (⊤ : Submodule ℝ ℝ) (ContinuousLinearMap.id ℝ ℝ)
    ContinuousLinearMap.norm_id_le (m := 1) (a := 1 / 2) (fun v _ => by simp) (by norm_num)
    (fun _ => c) (fun t _ => differentiableAt_const c) (fun t _ => ?_) 0
  rw [fderiv_const_apply, ContinuousLinearMap.opNorm_zero]
  norm_num

/-- CGP03: the coordinate `2a` along the line `a ↦ a` has a continuous section over `[-1, 1]`. -/
theorem doubled_line_section :
    ∃ s : ℝ → ℝ, ContinuousOn s (Icc (-1) 1) ∧
      ∀ a ∈ Icc (-1 : ℝ) 1, 2 * s a = a ∧ s a ∈ id '' Icc (-1) 1 := by
  refine exists_continuousOn_section_of_strictMonoOn id (fun x => 2 * x) (by norm_num)
    continuousOn_id (by fun_prop) ?_ (by norm_num) (by norm_num)
  intro x _ y _ hxy
  simp only [Function.comp_apply, id]
  linarith

/-- CGP07: a translation of the plane by a vector of length at most `r` hits every center. -/
theorem translation_hits_center (a v : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : ‖v‖ ≤ r) :
    ∃ u ∈ closedBall a r, u + v = a :=
  DifferentialGeometry.Topology.FixedPoint.exists_eq_center_of_norm_sub_le (fun u => u + v)
    ((norm_nonneg v).trans hr) (by fun_prop) (fun u _ => by simpa using hr)

/-- CGP04: with one plane `⊥` and center `0`, every block passes through the spectral section. -/
theorem one_plane_section_block (J : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) :
    J ((⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ ({()} : Finset Unit), (fun _ _ => (1 : ℝ)) i z •
          ((fun _ => (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin 2)))) i)ᗮ.starProjection).toLinearMap
            μ).starProjection
        (z - ∑ i ∈ ({()} : Finset Unit), (fun _ _ => (1 : ℝ)) i z •
          (fun _ => (0 : EuclideanSpace ℝ (Fin 2))) i)) = J z :=
  Submodule.coordinateBlock_weighted_section_eq {()} univ (fun _ _ => 1) (fun _ _ => by simp)
    (fun _ => ⊥) (fun _ => 0) J
    (fun _ _ _ => ⟨fun v hv => by rw [(Submodule.mem_bot ℝ).mp hv, map_zero], map_zero J⟩) z
    (mem_univ z)

/-- SGP05: the exact rank model `D = T dη` with `T z = z • e`, `dη = ⟪e, ·⟫`, `‖e‖ = 1`. -/
theorem unit_axis_projected_rank (e : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) :
    let T : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2) := ContinuousLinearMap.toSpanSingleton ℝ e
    let P := T.range.orthogonalProjectionOnto.comp (T.comp (innerSL ℝ e))
    Function.Surjective P := by
  intro T
  have hT : ∀ z : ℝ, ‖z‖ ≤ ‖T z‖ := fun z => by
    simp [T, ContinuousLinearMap.toSpanSingleton_apply, norm_smul, he]
  have hTn : ‖T‖ ≤ 1 := by
    rw [ContinuousLinearMap.norm_toSpanSingleton, he]
  have hη : ‖innerSL ℝ e‖ = 1 := by rw [innerSL_apply_norm, he]
  exact (ContinuousLinearMap.projected_rank_of_one_dimensional_reference (C := 1) (e := 0) T hT hTn
    (innerSL ℝ e) (by rw [hη]; norm_num) (by rw [hη]; norm_num) (T.comp (innerSL ℝ e))
    (by simp) (by norm_num) (by norm_num)).1

/-- SGP06: the coverage budget and test radius at `Γ = 1/2`, `C = 1`, `Σ = 10⁻⁶`, `e = 10⁻⁹`. -/
theorem third_cloud_budget_example {r : ℝ} (hr1 : 1 / 2 * (1 / 1000000) ≤ r)
    (hr2 : r ≤ 5 * (1 / 1000000) / 4) :
    3 * (2 * (1 / 1000000000) + 1 * (r / (1 / 2)) ^ 2 / 2) < 1 / 2 / 2 * r ∧
      r / (1 / 2) < 1 / 100 :=
  ⟨GC.MetricGeometry.coverage_budget_lt_half (σ := 1 / 1000000) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith),
    GC.MetricGeometry.test_radius_lt_of_parameters (σ := 1 / 1000000) (by norm_num)
      (by norm_num) hr2⟩

/-- SGP01/SGP03 at the slim scales with `Δ = 1`. -/
theorem slim_enclosures_at_unit_scale :
    Real.sqrt ((8 * (100000 * (1 : ℝ)) + 1 / 100) ^ 2 + (1000 * 1) ^ 2) + 1 / 100 <
        81 / 100 * (1000000 * 1) ∧
      Real.sqrt ((9 * (100000 * (1 : ℝ)) + 1) ^ 2 + (1000 * 1) ^ 2) + 1 / 100 <
        91 / 100 * (1000000 * 1) :=
  ⟨slim_plateau_inside_comparison_ball one_pos, slim_model_support_inside le_rfl⟩

/-- CGP05 at `ε = 1/10`, `Σ = 1/6400`, `R = 1`: the first witness proximity. -/
theorem witness_proximity_example {d σz σy : ℝ} (hσz : 0 ≤ σz) (hzy : σz ≤ 5 / 3 * σy)
    (hy : σy ≤ 16) (hd : d < 1 / 10 * (1 / 6400 * σz)) : d < 1 / 2400 := by
  simpa using GC.MetricGeometry.witness_dist_lt_of_scale_chain (R := 1) (by norm_num)
    le_rfl (by norm_num) hσz hzy (by simpa using hy) hd

/-- CGP02 at `N = 3` blocks, `P₀ = 1`. -/
theorem early_derivative_constant_example {Λ B BE : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 1) (hB0 : 0 ≤ B)
    (hB : B ≤ 82) (hBE0 : 0 ≤ BE) (hBE : BE ≤ 2000) :
    Real.sqrt (Λ ^ 2 + (3 + 1) * B ^ 2 + BE ^ 2) ≤ 5000 := by
  have := early_derivative_constant (N := 3) (P := 1) (by norm_num) le_rfl hΛ0 hΛ hB0
    (by linarith) hBE0 (by linarith)
  linarith

/-- CGP07 at `Ω = 1`, `ε = 1/2000`, `e = Σ/1000`. -/
theorem one_sheet_budget_example {S R rx : ℝ} (hS : 0 < S) (hR : 0 < R)
    (hrx : 9 / 20 * S * R ≤ rx) :
    (2 * (S / 1000) + 25 / 12 * (1 + 1) * (1 / 2000) * S) * R < S * R / 100 :=
  (one_sheet_proximity_budget le_rfl hS hR le_rfl (by norm_num) (by norm_num) hrx).1

/-- CGP08: the identity adjustment does not merge the patches `{w | w ∈ W ∧ w ∈ T i}`. -/
theorem identity_adjustment_injOn {ι α : Type*} (W : Set α) (T : ι → Set α) :
    InjOn (id : α → α) (⋃ i, {w | w ∈ W ∧ w ∈ T i}) :=
  DifferentialGeometry.Analysis.injOn_iUnion_of_retained_blocks W (fun i => {w | w ∈ W ∧ w ∈ T i})
    (fun _ => id) (fun _ => id) T id (fun _ _ => Iff.rfl) (fun _ _ _ => rfl)
    (fun _ => injOn_id _)

/-- SGP04: three unit blocks give a vector of norm at most `√3`. -/
theorem three_block_norm (v : PiLp 2 (fun _ : Fin 3 => ℝ)) (h : ∀ j, ‖v j‖ ≤ 1) :
    ‖v‖ ≤ Real.sqrt 3 := by
  simpa using norm_le_sqrt_card_mul_of_blocks v zero_le_one h

end DifferentialGeometry.Geometry.Collapse
