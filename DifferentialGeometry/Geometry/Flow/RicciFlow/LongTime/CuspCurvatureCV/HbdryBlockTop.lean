import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspCurvatureCV.BoundaryFluxTop
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.RouteWAssemblyWA6

/-!
# IMS04 / G4b（O-W-CURV, suffix `_CV`）：`hbarW` 的 `hbdry` 块（Top，`hvel` 显式）

O-W-ASSEMBLY G6 `hbarW` 的最内层（`∀ a ha ρ hρ, region = {ρ ≤ 0} → let U … → ∀ γU q … → ∀ v Q φ … →
∫k − f < π`）逐字由 G4 `boundary_sub_flux_lt_pi_CV` 给出：Morrey 盘的其余条款不用，只用
`SmoothDiskExtension` 的光滑延拓、迹、degree one、闭盘共形。窗口 `(Gw, Φ)` 任意，只要
`Gw t₀ = g(t₀)` 与 `hvel`（S-A14-STATIC-2 `window_data_flux_of_no_event_ST` 的新增合取）。
-/

set_option autoImplicit false
noncomputable section
open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.MinimalSurface DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G4b**：`t₀ ≥ T₁` 时，对任意满足 `Gw t₀ = g(t₀)` 与 `hvel` 的窗口 `(Gw, Φ)`，`hbarW` 的 `hbdry` 块成立。 -/
theorem PrescribedCuspMeridianTop_CPQ.hbdry_block_of_hvel_CV
    (M : PrescribedCuspMeridianTop_CPQ cores) :
    ∃ T₁ : ℝ, M.exterior.start ≤ T₁ ∧
      ∀ (t₀ : ℝ) (ht₀ : M.exterior.start ≤ t₀), T₁ ≤ t₀ →
      ∀ (Gw : ℝ → SmoothRiemannianMetric (𝓡 3) (postStage F.observation t₀).Carrier)
        (Φ : ℝ → (postStage F.observation t₀).Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯
          (postStage F.observation t₀).Carrier),
        Gw t₀ = postMetric F.observation t₀ →
        (∀ s : ℝ,
          Real.sqrt ((postMetric F.observation t₀).inner (loopLift (M.transported t₀ ht₀) s)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀) s)) t₀ 1)
              (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun r : ℝ => Φ r (loopLift (M.transported t₀ ht₀) s))
                t₀ 1)) * Real.sqrt t₀ < cores.accuracy t₀) →
      ∀ (a : ℝ) (ha : 0 < a) (ρ : (postStage F.observation t₀).Carrier → ℝ)
        (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ), M.exterior.region t₀ = {x | ρ x ≤ 0} →
        let U : Opens (postStage F.observation t₀).Carrier :=
          ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
        let δ : (postStage F.observation t₀).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
        let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
          (cutoff_smooth_P2A a).contMDiff.comp hρ
        let hU : ∀ x : (postStage F.observation t₀).Carrier, x ∈ U ↔ 0 < δ x :=
          fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
        let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t₀) hδ U hU
        let ι : C(U, (postStage F.observation t₀).Carrier) :=
          ⟨Subtype.val, continuous_subtype_val⟩
        ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
          ι.comp γU = M.transported t₀ ht₀ →
          IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
          IsMorreyDisk G γU q →
          range (ι.comp q) ⊆ M.exterior.region t₀ →
          DiskWeakJordanTrace (M.transported t₀ ht₀) (ι.comp q) →
          (∀ z : closedDisk, ∀ᶠ y : U in 𝓝 (q z),
            G.inner y = ((postMetric F.observation t₀).restrictOpen U).inner y ∧
              barrier_P2A a (ρ (y : (postStage F.observation t₀).Carrier)) =
                ρ (y : (postStage F.observation t₀).Carrier)) →
          ∀ (v : C(closedDisk, U)) (Q : ℂ → U) (φ : ℝ → ℝ),
            (v = q ∨ v = q.comp ⟨diskReflection, diskReflection.continuous⟩) →
            SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) v Q → ContDiff ℝ ∞ φ →
            Monotone φ → (∀ θ : ℝ, φ (θ + 2 * Real.pi) = φ θ + 1) →
            (Subtype.val ∘ Q) ∘ circleMap 0 1 =
              (fun s : ℝ =>
                ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier)) ∘ φ →
            (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
              DiskMapConformalAt (postMetric F.observation t₀) (Subtype.val ∘ Q) z) →
            (∫ θ in -Real.pi..Real.pi,
                diskMapTraceBoundaryDensity (postMetric F.observation t₀) (Subtype.val ∘ Q)
                  (fun s : ℝ =>
                    ((γU (s : loopCircle) : U) : (postStage F.observation t₀).Carrier))
                  φ θ) -
              (∫ θ in -Real.pi..Real.pi,
                (Gw t₀).inner ((Subtype.val ∘ Q) (circleMap 0 1 θ))
                  (mfderiv 𝓘(ℝ, ℝ) (𝓡 3)
                    (fun r => Φ r ((Subtype.val ∘ Q) (circleMap 0 1 θ))) t₀ 1)
                  (diskMapInwardConormal (Gw t₀) (Subtype.val ∘ Q) (circleMap 0 1 θ)) *
                    Real.sqrt (diskMapConformalCoefficient (Gw t₀) (Subtype.val ∘ Q)
                      (circleMap 0 1 θ))) < Real.pi := by
  obtain ⟨T₁, hT₁s, hmain⟩ := M.boundary_sub_flux_lt_pi_CV
  refine ⟨T₁, hT₁s, ?_⟩
  intro t₀ ht₀ hT₁ Gw Φ hG₀ hvel a ha ρ hρ hreg U δ hδ hU G ι γU q hγγ hsm hMor hrange hJ hloc
    v Q φ hv hext hφ hmono hper htrace hconf
  obtain ⟨-, N, hN, hDN, hQ⟩ := hext
  exact hmain t₀ ht₀ hT₁ Gw Φ hG₀ hvel U γU Q φ N hN hDN
    (contMDiff_subtype_val.comp_contMDiffOn hQ) hγγ hφ hmono hper htrace hconf

end GC.LongTime.CuspP1
