import DifferentialGeometry.Geometry.MinimalSurface.Plateau.PairedSubdiskReplacement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CorneredRadialR13

/-!
# O-MY-R13 G6a：bi-Lipschitz paired replacement 引擎（R13 的面积换元，cornered 版）

IMS03 `exists_paired_subdisk_replacement`（`Plateau/PairedSubdiskReplacement.lean:80`）要求两个子盘是
`PartialDiffeomorph … 1` 的 chart 盘 `eᵢ '' D̄`，从而 `φ = e₁ ∘ e₂⁻¹` 是 `C¹`。R13 的 cornered 子盘没有
这样的 chart；外审 D-25/26 的替代是 bi-Lipschitz Schoenflies 映射 `B : Ω₂ → Ω₁`（R13-S，`B = b` on `∂Ω₂`），
面积换元只需 `riemannianArea_precomp_on`（bi-Lipschitz，D-26）。本文件把引擎改写成**只要**：

* `K₁ K₂ ⊆ D°`、`K₂` 紧（`K₁ = B '' K₂` 自动紧）、`volume (frontier Kᵢ) = 0`；
* `B` 在 `K₂` 上 bi-Lipschitz（`BilipschitzOn_R13`）、`BijOn B K₂ K₁`、`BijOn B (∂K₂) (∂K₁)`；
* 边界上 `U ∘ B = U`（`U = diskExtension u`）。

结论与 IMS03 引擎同形：competitor `v`（metric-Lipschitz、同 `diskTrace`、`range ⊆ W`、`K₂` 上
`v = U ∘ B`、`interior K₂` 外 `v = u`），面积公式 `A(v) = A(u) − A(U|K₂) + A(U|K₁)`。允许 `K₁ ∩ K₂ ≠ ∅`、
允许 `K₁ = K₂`。证明逐段照搬 IMS03 引擎（`φ := B`、`ψ := invFunOn B K₂`），只把 chart 性质换成上面的前提；
`B '' interior K₂ = interior K₁` 由 `interior K = K \ ∂K`（`K` 闭）与两个 `BijOn` 得到。

* `BilipschitzOn_R13.lipschitzOnWith`、`BilipschitzOn_R13.lipschitzOnWith_invFunOn`：bi-Lipschitz 双射
  及其逆的 Lipschitz 常数。
* `image_interior_of_bijOn_frontier_R13`：`B '' interior K₂ = interior K₁`。
* **`exists_bilipschitz_paired_replacement_R13`**（G6a 主定理）。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- bi-Lipschitz ⇒ Lipschitz（同一常数）。 -/
theorem BilipschitzOn_R13.lipschitzOnWith {b : ℂ → ℂ} {S : Set ℂ} (hb : BilipschitzOn_R13 b S) :
    ∃ K : ℝ≥0, LipschitzOnWith K b S ∧
      ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ K * dist (b x) (b y) := by
  obtain ⟨K, hK⟩ := hb
  exact ⟨K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => (hK x hx y hy).1,
    fun x hx y hy => (hK x hx y hy).2⟩

/-- bi-Lipschitz 双射 `S → T` 的逆 `Function.invFunOn b S` 在 `T` 上 Lipschitz。 -/
theorem BilipschitzOn_R13.lipschitzOnWith_invFunOn {b : ℂ → ℂ} {S T : Set ℂ}
    (hb : BilipschitzOn_R13 b S) (hbij : BijOn b S T) :
    ∃ K : ℝ≥0, LipschitzOnWith K b S ∧ LipschitzOnWith K (Function.invFunOn b S) T := by
  obtain ⟨K, hK⟩ := hb
  refine ⟨K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => (hK x hx y hy).1,
    LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hx' := hbij.surjOn.mapsTo_invFunOn hx
  have hy' := hbij.surjOn.mapsTo_invFunOn hy
  have h := (hK _ hx' _ hy').2
  rwa [hbij.surjOn.rightInvOn_invFunOn hx, hbij.surjOn.rightInvOn_invFunOn hy] at h

/-- `K₂` 闭、`BijOn B K₂ K₁`、`BijOn B (∂K₂) (∂K₁)` ⇒ `B '' interior K₂ = interior K₁`。 -/
theorem image_interior_of_bijOn_frontier_R13 {B : ℂ → ℂ} {K₁ K₂ : Set ℂ}
    (hK₂ : IsClosed K₂) (hBK : BijOn B K₂ K₁)
    (hBfr : BijOn B (frontier K₂) (frontier K₁)) : B '' interior K₂ = interior K₁ := by
  rw [← self_sdiff_frontier K₂, ← self_sdiff_frontier K₁]
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxf⟩, rfl⟩
    refine ⟨hBK.mapsTo hx, fun hyf => hxf ?_⟩
    obtain ⟨x', hx', hxx'⟩ := hBfr.surjOn hyf
    have hx'K : x' ∈ K₂ := hK₂.frontier_subset hx'
    rwa [hBK.injOn hx'K hx hxx'] at hx'
  · rintro ⟨hy, hyf⟩
    obtain ⟨x, hx, rfl⟩ := hBK.surjOn hy
    exact ⟨x, ⟨hx, fun hxf => hyf (hBfr.mapsTo hxf)⟩, rfl⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **G6a 主定理：bi-Lipschitz paired replacement。**  `K₁ K₂ ⊆ D°` 紧、边界 Lebesgue-null；
`B : K₂ → K₁` bi-Lipschitz 双射、边界到边界双射、边界上 `U ∘ B = U`。则把 `u` 在 `K₂` 上换成
`U ∘ B` 得到 metric-Lipschitz competitor `v`：同 `diskTrace`、`range v ⊆ W`、`K₂` 上 `v = U ∘ B`、
`interior K₂` 外 `v = u`，且 `A(v) = A(u) − A(U|K₂) + A(U|K₁)`。允许 `K₁`、`K₂` 相交或相等。 -/
theorem exists_bilipschitz_paired_replacement_R13
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {Uext : ℂ → M} (hUext : SmoothDiskExtension (E := E) u Uext)
    {K₁ K₂ : Set ℂ} (hK₂ : IsCompact K₂)
    (hinside₁ : K₁ ⊆ Metric.ball (0 : ℂ) 1) (hinside₂ : K₂ ⊆ Metric.ball (0 : ℂ) 1)
    (hnull₁ : volume (frontier K₁) = 0) (hnull₂ : volume (frontier K₂) = 0)
    {B : ℂ → ℂ} (hB : BilipschitzOn_R13 B K₂) (hBK : BijOn B K₂ K₁)
    (hBfr : BijOn B (frontier K₂) (frontier K₁))
    (hboundary : ∀ z ∈ frontier K₂, diskExtension u (B z) = diskExtension u z)
    {W : Set M} (huW : Set.range u ⊆ W) :
    ∃ (v : C(closedDisk, M)) (L : ℝ≥0),
      (∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤ (L : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ W ∧
      (∀ z : closedDisk, (z : ℂ) ∈ K₂ → v z = diskExtension u (B z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior K₂ → v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) K₂ + riemannianArea g (diskExtension u) K₁ := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  let U := diskExtension u
  obtain ⟨A, hBLip, hψLip⟩ := hB.lipschitzOnWith_invFunOn hBK
  have hBmaps : MapsTo B K₂ K₁ := hBK.mapsTo
  have hψB (z : ℂ) (hz : z ∈ K₂) : Function.invFunOn B K₂ (B z) = z :=
    hBK.injOn.leftInvOn_invFunOn hz
  have hBlower : ∀ x ∈ K₂, ∀ y ∈ K₂,
      edist x y ≤ (A : ℝ≥0∞) * edist (B x) (B y) := by
    intro x hx y hy
    have h := hψLip (hBmaps hx) (hBmaps hy)
    rwa [hψB x hx, hψB y hy] at h
  have hBinterior : B '' interior K₂ = interior K₁ :=
    image_interior_of_bijOn_frontier_R13 hK₂.isClosed hBK hBfr
  have hmatch : EqOn (U ∘ B) U (frontier K₂) := fun z hz => hboundary z hz
  obtain ⟨C, hC⟩ := hUext.lipschitz g
  have hULip : LipschitzWith C U := diskExtension_riemannian_lipschitz g hC
  have hcopiedLip : LipschitzOnWith (C * A) (U ∘ B) K₂ :=
    hULip.comp_lipschitzOnWith hBLip
  let F : ℂ → M := K₂.piecewise (U ∘ B) U
  have hFinner : EqOn F (U ∘ B) K₂ := fun _ hz => piecewise_eq_of_mem _ _ _ hz
  have hFouter : EqOn F U (interior K₂)ᶜ := by
    intro z hz
    by_cases hzK : z ∈ K₂
    · exact (hFinner hzK).trans (hmatch ((mem_frontier_iff_notMem_interior hzK).mpr hz))
    · exact piecewise_eq_of_notMem _ _ _ hzK
  let cells : Bool → Set ℂ := fun b => if b then (interior K₂)ᶜ else K₂
  let constants : Bool → ℝ≥0 := fun b => if b then C else C * A
  have hcellsClosed : ∀ b, IsClosed ((Subtype.val : closedDisk → ℂ) ⁻¹' cells b) := by
    intro b
    cases b
    · exact hK₂.isClosed.preimage continuous_subtype_val
    · exact isOpen_interior.isClosed_compl.preimage continuous_subtype_val
  have hcover : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, ∃ b, z ∈ cells b := by
    intro z _
    by_cases hz : z ∈ K₂
    · exact ⟨false, hz⟩
    · exact ⟨true, fun hi => hz (interior_subset hi)⟩
  have hcellLip : ∀ b, LipschitzOnWith (constants b) F
      (Metric.closedBall (0 : ℂ) 1 ∩ cells b) := by
    intro b
    cases b
    · intro x hx y hy
      rw [hFinner hx.2, hFinner hy.2]
      exact hcopiedLip hx.2 hy.2
    · intro x hx y hy
      rw [hFouter hx.2, hFouter hy.2]
      exact hULip x y
  have hFLip : LipschitzOnWith (Finset.univ.sup constants) F
      (Metric.closedBall (0 : ℂ) 1) :=
    DifferentialGeometry.Analysis.lipschitzOnWith_of_finite_closed_cover
      (convex_closedBall (0 : ℂ) 1) cells hcellsClosed hcover constants hcellLip
  let v : C(closedDisk, M) := ⟨fun z => F z, hFLip.to_restrict.continuous⟩
  have hvLip : ∀ z w : closedDisk, riemannianEDistOf g (v z) (v w) ≤
      ((Finset.univ.sup constants : ℝ≥0) : ℝ≥0∞) * edist z w :=
    fun z w => hFLip z.property w.property
  have hvinner (z : closedDisk) (hz : (z : ℂ) ∈ K₂) : v z = U (B z) :=
    hFinner hz
  have hvouter (z : closedDisk) (hz : (z : ℂ) ∉ interior K₂) : v z = u z :=
    (hFouter hz).trans (diskExtension_coe u z)
  have hvtrace : diskTrace v = diskTrace u := by
    ext θ
    change v (diskBoundary θ) = u (diskBoundary θ)
    apply hvouter
    intro hz
    have hin := hinside₂ (interior_subset hz)
    have hn : ‖(diskBoundary θ : ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball, dist_zero_right] using hin
    have heq : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := Circle.norm_coe _
    exact (not_lt_of_ge heq.ge) hn
  have hvW : Set.range v ⊆ W := by
    rintro _ ⟨z, rfl⟩
    by_cases hz : (z : ℂ) ∈ K₂
    · rw [hvinner z hz]
      let q : closedDisk := ⟨B z, Metric.ball_subset_closedBall (hinside₁ (hBmaps hz))⟩
      have heq : U (B z) = u q := diskExtension_coe u q
      rw [heq]
      exact huW (mem_range_self q)
    · rw [hvouter z (fun hi => hz (interior_subset hi))]
      exact huW (mem_range_self z)
  have hK₂D : K₂ ⊆ Metric.closedBall (0 : ℂ) 1 :=
    hinside₂.trans Metric.ball_subset_closedBall
  have hclosedInterior (f : ℂ → M) (K : Set ℂ) (hnull : volume (frontier K) = 0) :
      riemannianArea g f K = riemannianArea g f (interior K) := by
    exact setIntegral_congr_set (interior_ae_eq_of_null_frontier hnull).symm
  have hinsArea : riemannianArea g (diskExtension v) K₂ = riemannianArea g U K₁ := by
    calc
      _ = riemannianArea g (diskExtension v) (interior K₂) :=
        hclosedInterior _ _ hnull₂
      _ = riemannianArea g (U ∘ B) (interior K₂) := by
        apply riemannianArea_congr_on_open g isOpen_interior
        intro z hz
        let q : closedDisk := ⟨z, hK₂D (interior_subset hz)⟩
        exact (diskExtension_coe v q).trans (hvinner q (interior_subset hz))
      _ = riemannianArea g U (B '' interior K₂) :=
        riemannianArea_precomp_on g hULip isOpen_interior
          (hBLip.mono interior_subset)
          (fun x hx y hy => hBlower x (interior_subset hx) y (interior_subset hy))
      _ = riemannianArea g U (interior K₁) := by rw [hBinterior]
      _ = riemannianArea g U K₁ := (hclosedInterior _ _ hnull₁).symm
  have hiu : IntegrableOn (riemannianAreaDensity g U) (Metric.closedBall (0 : ℂ) 1) :=
    integrable_riemannianDiskAreaDensity g hC
  have hiv : IntegrableOn (riemannianAreaDensity g (diskExtension v))
      (Metric.closedBall (0 : ℂ) 1) := integrable_riemannianDiskAreaDensity g hvLip
  have houtArea :
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ K₂,
        riemannianAreaDensity g (diskExtension v) z) =
      ∫ z in Metric.closedBall (0 : ℂ) 1 \ K₂, riemannianAreaDensity g U z := by
    have hzint : ∀ᵐ z ∂volume.restrict (Metric.closedBall (0 : ℂ) 1 \ K₂),
        z ∈ Metric.ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzint,
      ae_restrict_mem (measurableSet_closedBall.diff hK₂.measurableSet)] with z hz hzd
    apply riemannianAreaDensity_congr g
    filter_upwards [(Metric.isOpen_ball.inter hK₂.isClosed.isOpen_compl).mem_nhds
      ⟨hz, hzd.2⟩] with y hy
    let q : closedDisk := ⟨y, Metric.ball_subset_closedBall hy.1⟩
    exact (diskExtension_coe v q).trans
      ((hvouter q (fun hi => hy.2 (interior_subset hi))).trans (diskExtension_coe u q).symm)
  have harea : riemannianDiskArea g v = riemannianDiskArea g u -
      riemannianArea g U K₂ + riemannianArea g U K₁ := by
    have hsu := setIntegral_sdiff hK₂.measurableSet hiu hK₂D
    have hsv := setIntegral_sdiff hK₂.measurableSet hiv hK₂D
    change (∫ z in K₂, riemannianAreaDensity g (diskExtension v) z) =
      (∫ z in K₁, riemannianAreaDensity g U z) at hinsArea
    rw [houtArea, hinsArea, hsu] at hsv
    change (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g (diskExtension v) z) =
      (∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity g U z) -
      (∫ z in K₂, riemannianAreaDensity g U z) + ∫ z in K₁, riemannianAreaDensity g U z
    linarith
  exact ⟨v, Finset.univ.sup constants, hvLip, hvtrace, hvW, hvinner, hvouter, harea⟩

end DifferentialGeometry.Geometry
