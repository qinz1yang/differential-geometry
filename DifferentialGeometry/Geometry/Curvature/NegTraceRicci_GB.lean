import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiskVariationCurvature

set_option autoImplicit false

/-!
# IMS09：三维里 `−tr_Σ Ric ≤ −R/2 − K_Σ` 的曲率代数部分（车道 S-A10-GAUSS，G1，后缀 `_GB`）

纯线性代数 / 曲率代数引理，不涉及曲面：
* `neg_ricci_trace_eq_GB`：dim 3，`v ⟂ w` 且等长 ⇒
  `−(Ric v v + Ric w w) = −(sec(v,w)·|v|² + R·|v|²/2)`（非归一化；对应的
  `neg_ricciTrace_eq_neg_sectional_and_half_scalar` 在
  `Extinction/Width/DiskVariationCurvature.lean` 里是 private，这里重证）。
* `neg_trace_ricci_le_GB`：单位正交 e₁ e₂ + 显式 II 参数（对称、`tr II = 0`）⇒
  `−(Ric e₁e₁ + Ric e₂e₂) ≤ −R/2 − (sec(e₁,e₂) + det II)`。
* `diskMap_neg_ricci_trace_eq_GB` / `diskMap_neg_ricci_trace_le_GB`：disk 密度版，
  `−(Ric(U_x,U_x)+Ric(U_y,U_y)) = −(sec·a + R·a/2)` 与
  `… ≤ −R·a/2 − K_Σ·a`（`K_Σ·a = −½Δ log a`，Gauss equation）。
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

private theorem ricciTensor_smul_smul_GB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (s : ℝ) (X Y : TangentSpace 𝓘(ℝ, E) x) :
    ricciTensor (I := 𝓘(ℝ, E)) g x (s • X) (s • Y) =
      s * s * ricciTensor (I := 𝓘(ℝ, E)) g x X Y := by
  rw [map_smul, smul_eq_mul, map_smul, smul_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem inner_smul_smul_GB (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M)
    (s : ℝ) (X Y : TangentSpace 𝓘(ℝ, E) x) :
    g.inner x (s • X) (s • Y) = s * s * g.inner x X Y := by
  rw [map_smul, smul_eq_mul, map_smul, smul_apply, smul_eq_mul]
  ring

/-- dim 3 里，`v ⟂ w` 且 `|v|² = |w|²` 时 `Ric v v + Ric w w = |v|²(sec(v,w) + R/2)`（取负号）。
由单位正交版
`Curvature.ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal`
加缩放得到。 -/
theorem neg_ricci_trace_eq_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hvw : g.inner x v w = 0) (heq : g.inner x v v = g.inner x w w) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w) =
      -(sectionalCurvature (I := 𝓘(ℝ, E)) g x v w * g.inner x v v +
        metricScalarAt (I := 𝓘(ℝ, E)) g x * g.inner x v v / 2) := by
  have hnonneg : 0 ≤ g.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (g.pos x v hv).le
  rcases eq_or_lt_of_le hnonneg with hzero | hpos
  · have hv : v = 0 := by
      by_contra hv
      have hp := g.pos x v hv
      rw [← hzero] at hp
      exact absurd hp (lt_irrefl 0)
    have hw : w = 0 := by
      by_contra hw
      have hp := g.pos x w hw
      rw [← heq, ← hzero] at hp
      exact absurd hp (lt_irrefl 0)
    rw [hv, hw]
    simp
  · let c := Real.sqrt (g.inner x v v)
    have hc : c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
    have hcc : c * c = g.inner x v v := by
      rw [← pow_two, Real.sq_sqrt hpos.le]
    let e1 := c⁻¹ • v
    let e2 := c⁻¹ • w
    have hv_eq : c • e1 = v := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have hw_eq : c • e2 = w := by
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    have he1 : g.inner x e1 e1 = 1 := by
      rw [inner_smul_smul_GB, ← hcc]
      field_simp
    have he2 : g.inner x e2 e2 = 1 := by
      rw [inner_smul_smul_GB, ← heq, ← hcc]
      field_simp
    have he12 : g.inner x e1 e2 = 0 := by
      rw [inner_smul_smul_GB, hvw, mul_zero]
    have hpair :=
      Curvature.ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal
        g x hdim e1 e2 he1 he2 he12
    have hK : sectionalCurvature (I := 𝓘(ℝ, E)) g x v w =
        sectionalCurvature (I := 𝓘(ℝ, E)) g x e1 e2 := by
      rw [← hv_eq, ← hw_eq]
      exact sectionalCurvature_smul_smul (I := 𝓘(ℝ, E)) g x hc hc e1 e2
    have hRv : ricciTensor (I := 𝓘(ℝ, E)) g x v v =
        g.inner x v v * ricciTensor (I := 𝓘(ℝ, E)) g x e1 e1 := by
      conv_lhs => rw [← hv_eq]
      rw [ricciTensor_smul_smul_GB, hcc]
    have hRw : ricciTensor (I := 𝓘(ℝ, E)) g x w w =
        g.inner x v v * ricciTensor (I := 𝓘(ℝ, E)) g x e2 e2 := by
      conv_lhs => rw [← hw_eq]
      rw [ricciTensor_smul_smul_GB, hcc]
    have hRic : ricciTensor (I := 𝓘(ℝ, E)) g x v v +
          ricciTensor (I := 𝓘(ℝ, E)) g x w w =
        g.inner x v v * (ricciTensor (I := 𝓘(ℝ, E)) g x e1 e1 +
          ricciTensor (I := 𝓘(ℝ, E)) g x e2 e2) := by
      rw [hRv, hRw]
      ring
    rw [hRic, hK, hpair]
    ring

/-- **IMS09 的曲率代数部分**：dim 3，`e₁ e₂` 单位正交（第三个方向 ν 由 `finrank = 3` 隐含），
`II` 是 `Σ` 的第二基本形式在 `(e₁,e₂)` 上的分量（显式函数参数，对称、`tr II = 0`，即极小），
则 `−(Ric e₁e₁ + Ric e₂e₂) ≤ −R/2 − (sec(e₁,e₂) + det II)`。
（`sec + det II = K_Σ` 即 Gauss equation；`det II = −|II|²/2 ≤ 0`。） -/
theorem neg_trace_ricci_le_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0)
    (II : TangentSpace 𝓘(ℝ, E) x → TangentSpace 𝓘(ℝ, E) x → ℝ)
    (hsym : II v w = II w v) (htr : II v v + II w w = 0) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w) ≤
      -(metricScalarAt (I := 𝓘(ℝ, E)) g x / 2) -
        (sectionalCurvature (I := 𝓘(ℝ, E)) g x v w + (II v v * II w w - II v w * II w v)) := by
  have h := Curvature.ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal
    g x hdim v w hv hw hvw
  have hww : II w w = -II v v := by linarith
  have hdet : II v v * II w w - II v w * II w v ≤ 0 := by
    rw [hww, ← hsym]
    nlinarith [sq_nonneg (II v v), sq_nonneg (II v w)]
  rw [h]
  linarith

/-- 等式版：`−(Ric e₁e₁ + Ric e₂e₂) = −R/2 − sec(e₁,e₂)`（dim 3，单位正交）。 -/
theorem neg_ricci_trace_eq_neg_half_scalar_sub_sectional_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (v w : TangentSpace 𝓘(ℝ, E) x)
    (hv : g.inner x v v = 1) (hw : g.inner x w w = 1) (hvw : g.inner x v w = 0) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g x v v + ricciTensor (I := 𝓘(ℝ, E)) g x w w) =
      -(metricScalarAt (I := 𝓘(ℝ, E)) g x / 2) -
        sectionalCurvature (I := 𝓘(ℝ, E)) g x v w := by
  have h := Curvature.ricciTensor_add_eq_sectionalCurvature_add_half_metricScalarAt_of_orthonormal
    g x hdim v w hv hw hvw
  rw [h]
  ring

variable {U : ℂ → M} {z : ℂ}

/-- disk 密度版（等式）：共形点上
`−(Ric(U_x,U_x) + Ric(U_y,U_y)) = −(sec(TΣ)·a + R·a/2)`，`a = diskMapConformalCoefficient`。 -/
theorem diskMap_neg_ricci_trace_eq_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hdim : Module.finrank ℝ E = 3)
    (hconf : DiskMapConformalAt g U z) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I)) =
      -(diskMapSectionalDensity g U z +
        metricScalarAt (I := 𝓘(ℝ, E)) g (U z) * diskMapConformalCoefficient g U z / 2) := by
  rw [neg_ricci_trace_eq_GB g (U z) hdim _ _ hconf.1 hconf.2]
  rw [diskMapSectionalDensity, diskMapConformalCoefficient]

/-- disk 密度版（不等式，IMS09 逐点形式）：调和共形盘、`a > 0` 处
`−(Ric(U_x,U_x)+Ric(U_y,U_y)) ≤ −R·a/2 − K_Σ·a`，其中 `K_Σ·a = −½·Δ(log a)`
（Gauss equation：`K_Σ·a = sec·a − |II|²`-项）。 -/
theorem diskMap_neg_ricci_trace_le_GB
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hdim : Module.finrank ℝ E = 3) {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hconf : ∀ q ∈ s, DiskMapConformalAt g U q)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    (hz : z ∈ s) (ha : 0 < diskMapConformalCoefficient g U z) :
    -(ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) +
        ricciTensor (I := 𝓘(ℝ, E)) g (U z) (diskMapPartial U z Complex.I)
          (diskMapPartial U z Complex.I)) ≤
      -(metricScalarAt (I := 𝓘(ℝ, E)) g (U z) * diskMapConformalCoefficient g U z / 2) -
        (-(1 / 2 : ℝ) *
          Laplacian.laplacian (fun q => Real.log (diskMapConformalCoefficient g U q)) z) := by
  rw [diskMap_neg_ricci_trace_eq_GB g hdim (hconf z hz)]
  have hle := diskMap_curvature_density_le_sectional g hs hU hconf hharm hz ha
  rw [diskMapSectionalDensity]
  linarith

end DifferentialGeometry.Geometry
