import DifferentialGeometry.Geometry.Curvature.NegTraceRicci_GB

set_option autoImplicit false

/-!
# G1 consumer（S-A10-GAUSS，后缀 `_GB`）

用 `neg_trace_ricci_le_GB` / `diskMap_neg_ricci_trace_le_GB` 的小定理：带 scalar lower bound
`ρ ≤ R` 的逐点不等式（G3 里 `ρ = −3/(2(t+c))`，来自 `AnalyticSurgeryProfile.scalar_lower`）。
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M]

/-- 带 scalar lower bound 的曲率代数不等式：`ρ ≤ R(x)` ⇒
`−(Ric e₁e₁ + Ric e₂e₂) ≤ −ρ/2 − (sec(e₁,e₂) + det II)`。 -/
theorem neg_trace_ricci_le_of_scalar_lower_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    {ρ : ℝ} (hρ : ρ ≤ metricScalarAt (I := 𝓘(ℝ, E)) g x)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0)
    (II : TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x → ℝ)
    (hsym : II v w = II w v) (htr : II v v + II w w = 0) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w) ≤
      -(ρ / 2) -
        (sectionalCurvature (I := 𝓘(ℝ, E)) g x v w + (II v v * II w w - II v w * II w v)) := by
  have h := neg_trace_ricci_le_GB g x hdim v w hv hw hvw II hsym htr
  linarith

/-- disk 密度版：`ρ ≤ R(U z)` ⇒ `−(Ric(U_x,U_x)+Ric(U_y,U_y)) ≤ −ρ·a/2 − K_Σ·a`
（`a ≥ 0` 为共形系数）。 -/
theorem diskMap_neg_ricci_trace_le_of_scalar_lower_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hdim : Module.finrank ℝ E = 3)
    {U : ℂ → M} {z : ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z)
    {ρ : ℝ} (hρ : ρ ≤ metricScalarAt (I := 𝓘(ℝ, E)) g (U z)) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I)) ≤
      -(ρ * diskMapConformalCoefficient g U z / 2) -
        (-(1 / 2 : ℝ) *
          Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z) := by
  have h := diskMap_neg_ricci_trace_le_GB g hdim hs hU hconf hharm hz ha
  have hmul : ρ * diskMapConformalCoefficient g U z ≤
      metricScalarAt (I := 𝓘(ℝ, E)) g (U z) * diskMapConformalCoefficient g U z :=
    mul_le_mul_of_nonneg_right hρ ha.le
  linarith

end DifferentialGeometry.Geometry
