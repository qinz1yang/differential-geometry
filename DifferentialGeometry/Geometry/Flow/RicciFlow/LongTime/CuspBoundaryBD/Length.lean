import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.MetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Metric.CurveLength

/-!
# IMS04 / G2（S-A10-BOUNDARY, suffix `_BD`）：prescribed 曲线 `γ_t` 的 speed 与 length 界

`γ_t = M.transported t = cores.map model t ∘ cuspMap port ∘ (loop, halfZero)`。

* `truncation_slice_inner_eq_BD`：`cuspIsometry` + cusp 度量 `dr² + e^{-r} g_T` 在 slice `r = 0`
  （`halfZero`）上 ⇒ `h(D(cuspMap ∘ (loop, halfZero)), ·) = g_T(loop', loop')`（等式，无误差）；
* `speed_transported_le_BD`：`|γ_t'(s)|_{g(t)} ≤ √(t (1 + acc t)) · L`，`L < 1` 来自 `short`（G1 +
  chain rule）；
* `length_transported_le_BD`：`L_{g(t)}(γ_t) ≤ √(t (1 + acc t)) · L`（`riemannianCurveLength`，
  `[0,1]` 一周）；
* `eventually_length_transported_le_BD`：对任意 `ℓ > L`，`t` 足够大时 `L_{g(t)}(γ_t) ≤ ℓ √t`
  （取 `ℓ = (1+L)/2 < 1`：长度 `< √t`）。

无新增假设：`ball ⊆ domain`（`advertised_ball`）、`range inclusion ⊆ ball`（`in_ball`）、
`cusp_zero`、`cuspIsometry`、`short` 都是 `PrescribedCuspMeridian` / `PersistentHyperbolicCores`
已有字段。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime
universe u

/-- cusp slice `r = 0` 上的度量：`h` 沿 `cuspMap ∘ (loop, halfZero)` 的速度等于 `torusMetric` 下 `loop` 的速度。 -/
theorem truncation_slice_inner_eq_BD {H : FiniteVolumeHyperbolicModel.{u}}
    (τ : HyperbolicTruncation H) (j : Fin τ.count) (loop : freeLoop Torus)
    (hs : ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop)) (s : ℝ) :
    H.metric.inner (τ.cuspMap j (loopLift loop s, halfZero))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (loopLift loop s, halfZero)) s 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (loopLift loop s, halfZero)) s 1) =
      (τ.cusp j).torusMetric.inner (loopLift loop s)
        (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1)
        (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1) := by
  have hφ : ContMDiff 𝓘(ℝ, ℝ) halfCollarModel ∞
      (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) :=
    hs.prodMk contMDiff_const
  have hψ : ContMDiff halfCollarModel (𝓡 3) ∞ (τ.cuspMap j) := (τ.cuspEmbedding j).contMDiff
  have hdφ : MDifferentiableAt 𝓘(ℝ, ℝ) halfCollarModel
      (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) s :=
    (hφ s).mdifferentiableAt (by simp)
  have hdψ : MDifferentiableAt halfCollarModel (𝓡 3) (τ.cuspMap j) (loopLift loop s, halfZero) :=
    (hψ _).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := halfCollarModel) (I'' := 𝓡 3) s hdψ hdφ
  have hprod : mfderiv 𝓘(ℝ, ℝ) halfCollarModel
      (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) s =
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s).prod
        (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) (fun _ : ℝ => (halfZero : EuclideanHalfSpace 1)) s) :=
    mfderiv_prodMk ((hs s).mdifferentiableAt (by simp)) mdifferentiableAt_const
  have e : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s => τ.cuspMap j (loopLift loop s, halfZero)) s 1 =
      mfderiv halfCollarModel (𝓡 3) (τ.cuspMap j) (loopLift loop s, halfZero)
        (mfderiv 𝓘(ℝ, ℝ) halfCollarModel
          (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) s 1) := by
    rw [show (fun s => τ.cuspMap j (loopLift loop s, halfZero)) =
      (τ.cuspMap j) ∘ (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1))
      from rfl, hcomp]
    rfl
  have hv1 : (mfderiv 𝓘(ℝ, ℝ) halfCollarModel
      (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) s 1).1 =
      mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1 :=
    congrArg (fun L => (L 1).1) hprod
  have hv2 : (mfderiv 𝓘(ℝ, ℝ) halfCollarModel
      (fun s : ℝ => ((loopLift loop s, halfZero) : Torus × EuclideanHalfSpace 1)) s 1).2 = 0 := by
    have := congrArg (fun L => (L 1).2) hprod
    refine this.trans ?_
    simp only [mfderiv_const]
    rfl
  have hz : Real.exp (-(halfZero : EuclideanHalfSpace 1).val 0) = 1 := by
    have h0 : (halfZero : EuclideanHalfSpace 1).val 0 = 0 := rfl
    rw [h0, neg_zero, Real.exp_zero]
  rw [e, τ.cuspIsometry j _ _ _, (τ.cusp j).metric_formula, hv1, hv2]
  simp [hz]

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- `γ_t = cores.map ∘ cuspMap ∘ (loop, halfZero)`：`prescribed` 的函数形式（提升到 `ℝ`）。 -/
theorem PrescribedCuspMeridian.transported_eq_comp_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) :
    ⇑(loopLift (M.transported t ht)) =
      cores.map M.model t (M.exterior.after_cores.trans ht) ∘
        (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
          (loopLift M.loop s, halfZero)) := by
  funext s
  rw [loopLift_apply, M.prescribed t ht]
  rfl

/-- 环面 slice 上的点落在 `PersistentCuspExterior.in_ball` 给出的 ball 内（`cusp_zero`）。 -/
theorem PrescribedCuspMeridian.slice_mem_ball_BD (M : PrescribedCuspMeridian cores)
    (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ) :
    (M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero) ∈
      riemannianBallOf (cores.model M.model).metric (cores.model M.model).basepoint
        (cores.accuracy t)⁻¹ := by
  refine M.exterior.in_ball M.model t ht ?_
  rw [(M.exterior.truncation M.model).cusp_zero M.port]
  exact ⟨_, rfl⟩

/-- **IMS04 逐点 speed 界**：`|γ_t'(s)|_{g(t)} ≤ √(t (1 + acc t)) · L`，`L < 1` 来自 `short`。

`L` 只依赖 `M`（不依赖 `t`、`s`）。证明：chain rule `D(map ∘ cuspMap ∘ (loop, halfZero))`，
G1 的 `sqrt_pullback_inner_le_BD`，`slice_inner_eq_BD`（slice `r = 0` 上 `h = torusMetric`），`short`。 -/
theorem PrescribedCuspMeridian.speed_transported_le_BD (M : PrescribedCuspMeridian cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ (t : ℝ) (ht : M.exterior.start ≤ t) (s : ℝ),
      riemannianCurveSpeed (postMetric F.observation t) (loopLift (M.transported t ht)) s ≤
        Real.sqrt (t * (1 + cores.accuracy t)) * L := by
  obtain ⟨L, hL0, hL1, hshort⟩ := M.short
  refine ⟨L, hL0, hL1, fun t ht s => ?_⟩
  have ht' : cores.start ≤ t := M.exterior.after_cores.trans ht
  have hβ : ContMDiff 𝓘(ℝ, ℝ) (𝓡 3) ∞
      (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
        (loopLift M.loop s, halfZero)) :=
    ((M.exterior.truncation M.model).cuspEmbedding M.port).contMDiff.comp
      (M.smooth.prodMk contMDiff_const)
  have hball := M.slice_mem_ball_BD t ht s
  have hdomain := cores.advertised_ball M.model t ht' hball
  have hdf : MDifferentiableAt (𝓡 3) (𝓡 3) (cores.map M.model t ht')
      ((M.exterior.truncation M.model).cuspMap M.port (loopLift M.loop s, halfZero)) :=
    ((cores.smooth M.model t ht').mdifferentiableOn (by simp)).mdifferentiableAt
      ((cores.domain M.model t).isOpen.mem_nhds hdomain)
  have hdβ := (hβ s).mdifferentiableAt (by simp)
  rw [M.transported_eq_comp_BD t ht]
  unfold riemannianCurveSpeed
  rw [mfderiv_comp s hdf hdβ]
  have h1 := cores.sqrt_pullback_inner_le_BD M.model t ht' hball
    (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) (fun s : ℝ => (M.exterior.truncation M.model).cuspMap M.port
      (loopLift M.loop s, halfZero)) s 1)
  have h2 := truncation_slice_inner_eq_BD (M.exterior.truncation M.model) M.port M.loop M.smooth s
  have h3 : ((M.exterior.truncation M.model).cusp M.port).torusMetric.inner (loopLift M.loop s)
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1)
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1) ≤ L ^ 2 := hshort s
  rw [h2] at h1
  have h4 : Real.sqrt (((M.exterior.truncation M.model).cusp M.port).torusMetric.inner
      (loopLift M.loop s) (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1)
      (mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1)) ≤ L := by
    calc _ ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt h3
      _ = L := Real.sqrt_sq hL0.le
  exact h1.trans (mul_le_mul_of_nonneg_left h4 (Real.sqrt_nonneg _))

/-- **G2 主定理**：`L_{g(t)}(γ_t) ≤ √(t (1 + acc t)) · L`，`0 < L < 1`（`short`），环参数 `[0,1]` 一周。

`riemannianCurveLength g γ 0 1 = ∫_{[0,1]} |γ'|_g`（`Geometry/Metric/CurveLength.lean`）。 -/
theorem PrescribedCuspMeridian.length_transported_le_BD (M : PrescribedCuspMeridian cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ (t : ℝ) (ht : M.exterior.start ≤ t),
      Geometry.riemannianCurveLength (postMetric F.observation t)
        (loopLift (M.transported t ht)) 0 1 ≤
        Real.sqrt (t * (1 + cores.accuracy t)) * L := by
  obtain ⟨L, hL0, hL1, hsp⟩ := M.speed_transported_le_BD
  refine ⟨L, hL0, hL1, fun t ht => ?_⟩
  have hC : 0 ≤ Real.sqrt (t * (1 + cores.accuracy t)) * L :=
    mul_nonneg (Real.sqrt_nonneg _) hL0.le
  have hE := riemannianCurveELength_le (g := postMetric F.observation t)
    (γ := ⇑(loopLift (M.transported t ht)))
    (C := (Real.sqrt (t * (1 + cores.accuracy t)) * L).toNNReal) (a := 0) (b := 1)
    (fun s _ => by rw [Real.coe_toNNReal _ hC]; exact hsp t ht s)
  rw [sub_zero, ENNReal.ofReal_one, mul_one] at hE
  exact ENNReal.toReal_le_of_le_ofReal hC hE

/-- **consumer（IMS04 长度形式）**：对任意 `ℓ > L`，`t` 足够大时 `L_{g(t)}(γ_t) ≤ ℓ √t`。
特别地取 `ℓ = (1 + L)/2 < 1`：长度 `< √t`（`short` 的 `L < 1` 与 `accuracy → 0` 合起来）。 -/
theorem PrescribedCuspMeridian.eventually_length_transported_le_BD
    (M : PrescribedCuspMeridian cores) :
    ∃ L : ℝ, 0 < L ∧ L < 1 ∧ ∀ ℓ : ℝ, L < ℓ → ∃ T : ℝ, ∀ (t : ℝ) (ht : M.exterior.start ≤ t),
      T ≤ t → Geometry.riemannianCurveLength (postMetric F.observation t)
        (loopLift (M.transported t ht)) 0 1 ≤ ℓ * Real.sqrt t := by
  obtain ⟨L, hL0, hL1, hlen⟩ := M.length_transported_le_BD
  refine ⟨L, hL0, hL1, fun ℓ hℓ => ?_⟩
  have hℓ0 : 0 < ℓ := hL0.trans hℓ
  have hL2 : 0 < L ^ 2 := by positivity
  have hε : 0 < ℓ ^ 2 / L ^ 2 - 1 := by
    rw [sub_pos, lt_div_iff₀ hL2, one_mul]
    exact pow_lt_pow_left₀ hℓ hL0.le (by norm_num)
  obtain ⟨T, hT⟩ := cores.accuracy_decay _ hε
  refine ⟨T, fun t ht hTt => (hlen t ht).trans ?_⟩
  have htpos : 0 < t := (cores.start_pos).trans_le (M.exterior.after_cores.trans ht)
  have hacc := hT t hTt
  have h1 : (1 + cores.accuracy t) * L ^ 2 < ℓ ^ 2 := by
    rw [← lt_div_iff₀ hL2]
    linarith
  have haccpos := cores.accuracy_pos t (M.exterior.after_cores.trans ht)
  refine (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hL0.le)
    (mul_nonneg hℓ0.le (Real.sqrt_nonneg _))).mp ?_
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt htpos.le]
  nlinarith

end GC.LongTime
