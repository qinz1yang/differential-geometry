import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.InteriorImmersionHC_KP
import DifferentialGeometry.Geometry.Curvature.StabilityGaussWS

/-!
# S-W-STAB G3 consumer（Route W）：`_HC2` 盘的 `R ≥ σ` 弱化 stability（IMS05 用的形式）

K16b 给 regular part = 整个开单位盘 `D`；取 `W := {ρ ≤ 0}`（`_HC2` 的 interior confinement
`ρ < 0` on 开盘像）。对一切光滑单位法向 `ν` 与 `φ ∈ C_c^∞(D)`（`φ ≠ 0` 处 `R∘Q ≥ σ`）：
`(σ/2) ∫_D φ² ≤ ∫_D (|∇φ|²_{gN} + K_Σ φ²) dμ_{gN}`，`K_Σ = scalarCurv gN / 2`。
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

/-- Route W weak stability on the open unit disk (regular part by K16b): for every smooth unit
normal `ν` along `Q|_D`, every `σ` and every `φ ∈ C_c^∞(D)` with `R∘Q ≥ σ` where `φ ≠ 0`,
`(σ/2) ∫_D φ² ≤ ∫_D (|∇φ|² + K_Σ φ²) dμ_{gN}`. -/
theorem PrescribedCuspMeridianTop_CPQ.exists_scalar_stability_inequality_HC_WS
    (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : Opens (postStage F.observation t).Carrier) (G : SmoothRiemannianMetric (𝓡 3) U)
        (γU : freeLoop U) (q : C(closedDisk, U)) (Q : ℂ → U)
        (hQ : ContMDiff 𝓘(ℝ, ℂ) (𝓡 3) ∞ (fun p : D => Q p))
        (hQi : ∀ p : D, Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun p : D => Q p) p)),
        IsMorreyDisk G γU q ∧ SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q Q ∧
        ∀ (ν : ∀ p : D, TangentSpace (𝓡 3) (Q p))
          (_ : ContMDiff 𝓘(ℝ, ℂ) ((𝓡 3).tangent) ∞
            (fun p : D => (⟨Q p, ν p⟩ : TangentBundle (𝓡 3) U)))
          (_ : ∀ p : D, G.inner (Q p) (ν p) (ν p) = 1)
          (_ : ∀ (p : D) (v : ℂ), G.inner (Q p) (ν p)
            (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (fun r : D => Q r) p v) = 0)
          (σ : ℝ),
          let gN := G.pullback (fun r : D => Q r) hQ hQi
          let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gN
          ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
            (∀ p : D, φ p ≠ 0 → σ ≤ metricScalarAt G (Q p)) →
            Integrable (fun p : D =>
              gN.inner p (gradFun gN φ p) (gradFun gN φ p) + (scalarCurv gN p / 2) * φ p ^ 2) μ ∧
            Integrable (fun p : D => φ p ^ 2) μ ∧
            (σ / 2) * ∫ p : D, φ p ^ 2 ∂μ ≤ ∫ p : D,
              (gN.inner p (gradFun gN φ p) (gradFun gN φ p) +
                (scalarCurv gN p / 2) * φ p ^ 2) ∂μ := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ :=
    M.exists_eventual_confined_morrey_disk_interior_immersion_HC_KP tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, hreg, -, -, γU, q, -, hsm, hMor, hrange, -, hneg, -, -, -, ⟨Q, hQ⟩, hinj⟩ :=
    hH T h t ht
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hQs := hQ.contMDiff_unitBall_WS
  have hQi := injective_mfderiv_unitBall_WS (hinj Q hQ)
  refine ⟨_, _, γU, q, Q, hQs, hQi, hMor, hQ, ?_⟩
  intro ν hν hunit hnormal σ
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
  exact hMor.stability_inequality_scalar_lower_WS hd3 hsm hQ _ hW D subset_rfl hQs hQi hint
    ν hν hunit hnormal σ

end GC.LongTime.CuspP1

end
