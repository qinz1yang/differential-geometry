import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Variation.UnitNormalWS2
import DifferentialGeometry.Geometry.Curvature.ConformalScalarPlaneWS2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RegularStabilityHC_WS

/-!
# S-W-STAB-2 G4 consumer（Route W）：`_HC2` 盘共形 stability 的平面 `K_Σ` 形式（c3 的 (1)(2)(3)）

K16b：`_HC2` 给出的 Morrey disk `q`（开单位盘 `D` 上 `mfderiv` 单射）。无 `ν` 参数（G2），
`K_Σ` 用平面公式（G4 `scalarCurv_pullback_conformal_WS2`）：`∃ VJ ∈ C^∞(D)`，
`VJ z ≤ −Δ(log λ)(z)/(2λ(z)) − R(Q z)/2`（`λ = diskMapConformalCoefficient G Q`，`C^∞`、`> 0`），且
`∀ Ω ⊆ D`，`∀ ψ ∈ C_c^∞(Ω)`，`0 ≤ ∫_Ω ‖dψ‖² + λ·VJ·ψ²`。
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

/-- Route W 的共形 stability，平面 `K_Σ` 形式、无 `ν`：`VJ`（`C^∞(D)`）、`λ`（`C^∞(D)`、`> 0`）。 -/
theorem PrescribedCuspMeridianTop_CPQ.exists_planarK_stability_nu_free_HC_WS2
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : Opens (postStage F.observation t).Carrier) (G : SmoothRiemannianMetric (𝓡 3) U)
        (γU : freeLoop U) (q : C(closedDisk, U)) (Q : ℂ → U),
        IsMorreyDisk G γU q ∧ SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
        ContDiffOn ℝ ∞ (diskMapConformalCoefficient G Q) (Metric.ball (0 : ℂ) 1) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < diskMapConformalCoefficient G Q z) ∧
        ∃ VJ : ℂ → ℝ, ContDiffOn ℝ ∞ VJ (Metric.ball (0 : ℂ) 1) ∧
          (∀ z ∈ Metric.ball (0 : ℂ) 1, VJ z ≤ -Laplacian.laplacian
              (fun p => Real.log (diskMapConformalCoefficient G Q p)) z /
                (2 * diskMapConformalCoefficient G Q z) - metricScalarAt G (Q z) / 2) ∧
          ∀ Ω : Set ℂ, Ω ⊆ Metric.ball (0 : ℂ) 1 → ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ →
            HasCompactSupport ψ → tsupport ψ ⊆ Ω →
            0 ≤ ∫ x in Ω, (‖fderiv ℝ ψ x‖ ^ 2 +
              diskMapConformalCoefficient G Q x * VJ x * ψ x ^ 2) := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, -, -, γU, q, -, hsm, hMor, hrange, -, hneg, -, -, -, ⟨Q, hQ⟩, hinj⟩ :=
    hH T h t ht
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hQs := hQ.contMDiff_unitBall_WS
  have hQi := injective_mfderiv_unitBall_WS (hinj Q hQ)
  refine ⟨_, _, γU, q, Q, hMor, hQ, ?_⟩
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
  have hconf : ∀ z ∈ D, DiskMapConformalAt _ Q z :=
    fun z hz => hMor.conformal_of_extension hQ z hz
  obtain ⟨hlamC, hlamP⟩ := conformalFactor_data_WS2 _ D hQs hQi hconf
  obtain ⟨VJ, hC, hb, hs⟩ := hMor.stability_inequality_conformal_planar_WS2 hd3 hsm hQ _ hW o3 D
    subset_rfl hQs hQi hint
  refine ⟨hlamC, hlamP, VJ, hC, fun z hz => ?_, ?_⟩
  · rw [metricScalar_eq_scal]
    exact hb z hz
  · intro Ω hΩ ψ hψ hψc hψΩ
    have h := (hs ψ hψ hψc (hψΩ.trans hΩ)).2
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)] at h
    · exact h
    · intro x hx
      have hx' : x ∉ tsupport ψ := fun hh => hx (hψΩ hh)
      obtain ⟨h1, h2⟩ := fderiv_eq_zero_of_notMem_tsupport_WS2 hx'
      simp [h1, h2]

end GC.LongTime.CuspP1

end
