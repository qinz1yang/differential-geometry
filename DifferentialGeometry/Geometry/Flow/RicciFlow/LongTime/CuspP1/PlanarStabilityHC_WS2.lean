import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Variation.UnitNormalWS2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RegularStabilityHC_WS

/-!
# S-W-STAB-2 G3 consumer（Route W）：`_HC2` 盘的共形坐标 stability，无 `ν` 参数

K16b：`_HC2` 给出的 Morrey disk `q`（开单位盘 `D` 上 `mfderiv` 单射）。`D` 上 `ν` 由 G2 供给
（`(postStage F.observation t)` 的 `orientation` 限制到 `U` 给 `ManifoldOrientation (𝓡 3) U 3`），
对 `N := D`、`W := {ρ ≤ 0}`：
* `VJ ∈ C^∞(D)`，`VJ ≤ K_Σ − R/2`，`∀ ψ ∈ C_c^∞(ℂ)`，`tsupport ψ ⊆ D ⇒ 0 ≤ ∫ ‖dψ‖² + λ VJ ψ²`；
* EIG 形：`ρ = λ`、`Wt = λ·VJ`，`∀ Ω ⊆ D`，`∀ ψ ∈ C_c^∞(Ω)`，`0 ≤ ∫_Ω ‖dψ‖² + Wt ψ²`。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace MeasureTheory
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

namespace GC.LongTime.CuspP1

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Route W planar/conformal stability on the open unit disk (regular part by K16b), with no
`ν` parameter: the unit normal comes from the orientation of the stage (G2). -/
theorem PrescribedCuspMeridianTop_CPQ.exists_planar_stability_nu_free_HC_WS2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : Opens (postStage F.observation t).Carrier) (G : SmoothRiemannianMetric (𝓡 3) U)
        (γU : freeLoop U) (q : C(closedDisk, U)) (Q : ℂ → U)
        (hQ : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun p : D => Q p))
        (hQi : ∀ p : D, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => Q p) p)),
        IsMorreyDisk G γU q ∧ SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
        let gN := G.pullback (fun r : D => Q r) hQ hQi
        (∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (Metric.ball (0 : ℂ) 1) ∧
          (∀ p : D, VJ p ≤ scalarCurv gN p / 2 - scalarCurv G (Q p) / 2) ∧
          ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
            tsupport ψ ⊆ Metric.ball (0 : ℂ) 1 →
            Integrable (fun x => ‖fderiv ℝ ψ x‖ ^ 2 +
              diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2) ∧
            0 ≤ ∫ x, (‖fderiv ℝ ψ x‖ ^ 2 +
              diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2)) ∧
        ∃ ρ Wt : ℂ → ℝ, ContDiffOn ℝ ∞ ρ (Metric.ball (0 : ℂ) 1) ∧
          ContDiffOn ℝ ∞ Wt (Metric.ball (0 : ℂ) 1) ∧
          (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < ρ z) ∧
          (∀ z, ρ z = diskMapConformalCoefficient G Q z) ∧
          ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ →
            HasCompactSupport ψ → tsupport ψ ⊆ Ω →
            0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 + Wt x * ψ x ^ 2) := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, -, -, γU, q, -, hsm, hMor, hrange, -, hneg, -, -, -, ⟨Q, hQ⟩, hinj⟩ :=
    hH T h t ht
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hQs := hQ.contMDiff_unitBall_WS
  have hQi := injective_mfderiv_unitBall_WS (hinj Q hQ)
  refine ⟨_, _, γU, q, Q, hQs, hQi, hMor, hQ, ?_⟩
  have hW : Set.range q ⊆ Subtype.val ⁻¹' {x | ρ x ≤ 0} := by
    rintro _ ⟨z, rfl⟩
    have h1 := hrange ⟨z, rfl⟩
    rw [hreg] at h1
    exact h1
  have hint : ∀ p ∈ Metric.ball (0 : ℂ) 1, Q p ∈ interior (Subtype.val ⁻¹' {x | ρ x ≤ 0}) := by
    intro p hp
    have hpc : p ∈ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall hp
    have hn := hneg ⟨p, hpc⟩ (by simpa only [Metric.mem_ball, dist_zero_right] using hp)
    have hQp : Q p = q ⟨p, hpc⟩ := hQ.1 ⟨p, hpc⟩
    rw [mem_interior]
    refine ⟨Subtype.val ⁻¹' {x | ρ x < 0}, fun x hx => le_of_lt (show ρ x < 0 from hx),
      isOpen_lt (hρ.continuous.comp continuous_subtype_val) continuous_const, ?_⟩
    rw [hQp]
    exact hn
  let U : Opens (postStage F.observation t).Carrier :=
    ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
  let o3 : DifferentialGeometry.ManifoldOrientation (𝓡 3) U 3 :=
    { dimension_eq := by simp
      orientation := ((postStage F.observation t).orientation.restrictOpen U).orientation
      locally_constant :=
        ((postStage F.observation t).orientation.restrictOpen U).locally_constant }
  refine ⟨?_, ?_⟩
  · exact hMor.stability_inequality_conformal_nu_free_WS2 hd3 hsm hQ _ hW o3 D subset_rfl hQs hQi
      hint
  · obtain ⟨Wt, h1, h2, h3, h4⟩ :=
      hMor.planar_stability_nu_free_WS2 hd3 hsm hQ _ hW o3 D subset_rfl hQs hQi hint
    exact ⟨_, Wt, h1, h2, h3, fun _ => rfl, h4⟩

end GC.LongTime.CuspP1

end
