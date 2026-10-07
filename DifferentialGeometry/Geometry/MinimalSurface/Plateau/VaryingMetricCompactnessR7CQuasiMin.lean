import DifferentialGeometry.Geometry.MinimalSurface.Plateau.VaryingMetricCompactnessR7CCompletion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyExistenceReduction
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MinimizingSequence
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget
import DifferentialGeometry.Geometry.Measure.Area.ManifoldLipschitz
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CompactTransfer
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

/-!
# R7C：completion buffer 上的局部 quasi-minimality（route M 的 L4 核心不等式）

设 `uₙ` 是 `(M, g)`（`g = Gₙ`）的 Morrey 盘，像在开集 `O ⊆ W` 里；`(W, Ĝ)` 是 `C` 的 completion
buffer（`VaryingMetricCompactnessR7CCompletion`）。若 `g ≤ 2Ĝ` 于 `W`、`G ≤ 2g` 于 `O`、`Ĝ = G` 于 `O`，
则对 `W` 里任何 `Ĝ`-Lipschitz、trace 类为 `Γ`、在闭集 `R` 外与 `uₙ` 相同的 competitor `w`：
`∫_{D ∩ R} e_Ĝ(uₙ) ≤ 4 ∫_{D ∩ R} e_Ĝ(w)`。链：`e_Ĝ(uₙ) = e_G(uₙ) ≤ 2 e_g(uₙ) = 2 a_g(uₙ)`（共形）、
`∫_R a_g(uₙ) ≤ ∫_R a_g(ι∘w)`（`uₙ` 面积极小 + `R` 外相同）、`a_g(ι∘w) ≤ 2 a_Ĝ(w) ≤ 2 e_Ĝ(w)`。
这是"每个 `uₙ` 对自己的度量精确极小 ⇒ 对固定的 `Ĝ` 局部 4-quasi-minimal"，常数与 `n` 无关；
树内 HR 版 competitor 构造（常数只依赖 `(W, Ĝ)`）因此给出所有尺度的 hole-filling（无 defect）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Bundle Manifold TopologicalSpace
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- 开包含的距离比较（R7C）：`g ≤ 4Ĝ` 于 `W`（逐点二次型）⇒ `d_g(a, b) ≤ 2 d_Ĝ(a, b)`。 -/
theorem riemannianEDistOf_val_le_two_mul_R7C (W : Opens M)
    (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hle : ∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), g.inner x v v ≤ 4 * Ghat.inner x v v)
    (a b : W) :
    riemannianEDistOf g (a : M) (b : M) ≤ 2 * riemannianEDistOf Ghat a b := by
  have hne : Nonempty W := ⟨a⟩
  let j := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph 𝓘(ℝ, E) W hne
  have hsrc : j.source = univ :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_source 𝓘(ℝ, E) W hne
  have happ : ∀ z : W, j z = (z : M) := fun z =>
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_apply 𝓘(ℝ, E) W hne z
  have h := riemannianEDistOf_map_le_two_mul Ghat g j hsrc (fun z v => by
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (j : W → M) z v = v := by
      have hfun : (j : W → M) = Subtype.val := funext happ
      rw [hfun]
      exact DifferentialGeometry.mfderiv_subtype_val_apply W z v
    rw [hd, happ z]
    exact hle z v) a b
  rwa [happ a, happ b] at h

/-- 开包含下 area density 的比较（R7C）：`g ≤ c·Ĝ` 于 `W` ⇒ `a_g(ι ∘ w) ≤ c · a_Ĝ(w)`。 -/
theorem riemannianAreaDensity_val_le_R7C [T2Space M] (W : Opens M)
    (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {c : ℝ} (hc : 0 < c)
    (hle : ∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), g.inner x v v ≤ c * Ghat.inner x v v)
    (w : ℂ → W) (z : ℂ) :
    riemannianAreaDensity g (Subtype.val ∘ w) z ≤ c * riemannianAreaDensity Ghat w z := by
  rw [← riemannianAreaDensity_restrictOpen g W w z]
  unfold riemannianAreaDensity
  rw [← tangentTwoJacobian_scaleMetric c hc Ghat]
  apply tangentTwoJacobian_mono
  intro v
  rw [scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
  exact hle _ v

/-- **局部 quasi-minimality**（R7C）：见文件头。`u` 为 `(M, g)` 的 Morrey 盘、像在 `O`；`u'` 为其
`W`-lift；`w` 为 `W` 里 `Ĝ`-Lipschitz、`ι∘w` 的 weak trace 为 `Γ`、在闭集 `R` 外与 `u'` 相同 ⇒
`∫_{D∩R} e_Ĝ(u') ≤ 4 ∫_{D∩R} e_Ĝ(w)`。 -/
theorem local_quasi_minimality_R7C [T3Space M]
    {G g : SmoothRiemannianMetric 𝓘(ℝ, E) M} (W : Opens M)
    (Ghat : SmoothRiemannianMetric 𝓘(ℝ, E) W) {O : Set M}
    (hupper : ∀ (x : W) (v : TangentSpace 𝓘(ℝ, E) x), g.inner x v v ≤ 2 * Ghat.inner x v v)
    (hlower : ∀ x ∈ O, ∀ v : TangentSpace 𝓘(ℝ, E) x, G.inner x v v ≤ 2 * g.inner x v v)
    (hagree : ∀ x : W, (x : M) ∈ O → Ghat.inner x = G.inner x)
    {Γ : freeLoop M} {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) (huO : range u ⊆ O)
    (u' : C(closedDisk, W)) (hu' : ∀ z, (u' z : M) = u z)
    (w : C(closedDisk, W))
    (hwΓ : DiskWeakJordanTrace Γ ((ContinuousMap.mk Subtype.val continuous_subtype_val).comp w))
    {L : ℝ≥0} (hwL : ∀ z z', riemannianEDistOf Ghat (w z) (w z') ≤ (L : ℝ≥0∞) * edist z z')
    {R : Set ℂ} (hR : IsClosed R) (hout : ∀ z : closedDisk, (z : ℂ) ∉ R → w z = u' z) :
    (∫ z in closedBall (0 : ℂ) 1 ∩ R, diskMapEnergyDensity Ghat (diskExtension u') z) ≤
      4 * ∫ z in closedBall (0 : ℂ) 1 ∩ R, diskMapEnergyDensity Ghat (diskExtension w) z := by
  set D : Set ℂ := closedBall (0 : ℂ) 1 with hDdef
  let ιC : C(W, M) := ContinuousMap.mk Subtype.val continuous_subtype_val
  set v : C(closedDisk, M) := ιC.comp w with hvdef
  have hle4 : ∀ (x : W) (y : TangentSpace 𝓘(ℝ, E) x), g.inner x y y ≤ 4 * Ghat.inner x y y :=
    fun x y => (hupper x y).trans (by
      have := metric_inner_self_nonneg Ghat x y
      linarith)
  have hvL : ∀ z z', riemannianEDistOf g (v z) (v z') ≤ ((2 * L : ℝ≥0) : ℝ≥0∞) * edist z z' := by
    intro z z'
    refine (riemannianEDistOf_val_le_two_mul_R7C W Ghat g hle4 (w z) (w z')).trans ?_
    calc (2 : ℝ≥0∞) * riemannianEDistOf Ghat (w z) (w z')
        ≤ 2 * ((L : ℝ≥0∞) * edist z z') := by gcongr; exact hwL z z'
      _ = ((2 * L : ℝ≥0) : ℝ≥0∞) * edist z z' := by
        rw [ENNReal.coe_mul, ENNReal.coe_ofNat, mul_assoc]
  have hA := hu.minimizesLipschitz v hwΓ ⟨2 * L, hvL⟩
  have hR' : MeasurableSet (D ∩ R) := measurableSet_closedBall.inter hR.measurableSet
  have hiu : IntegrableOn (riemannianAreaDensity g (diskExtension u)) D := hu.integrableArea
  have hiv : IntegrableOn (riemannianAreaDensity g (diskExtension v)) D :=
    integrable_riemannianDiskAreaDensity g hvL
  -- `R` 外两者 area density 相同
  have hdv : diskExtension v = Subtype.val ∘ diskExtension w := rfl
  have houtEq : (∫ z in D \ (D ∩ R), riemannianAreaDensity g (diskExtension v) z) =
      ∫ z in D \ (D ∩ R), riemannianAreaDensity g (diskExtension u) z := by
    have hzin : ∀ᵐ z ∂volume.restrict (D \ (D ∩ R)), z ∈ ball (0 : ℂ) 1 :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset ae_disk_interior
    apply integral_congr_ae
    filter_upwards [hzin, ae_restrict_mem (measurableSet_closedBall.diff hR')] with z hz hzd
    apply riemannianAreaDensity_congr g
    have hzR : z ∉ R := fun h => hzd.2 ⟨hzd.1, h⟩
    filter_upwards [(isOpen_ball.inter hR.isOpen_compl).mem_nhds ⟨hz, hzR⟩] with y hy
    let q : closedDisk := ⟨y, ball_subset_closedBall hy.1⟩
    rw [diskExtension_coe v q, diskExtension_coe u q, hvdef]
    change ((w q : W) : M) = u q
    rw [hout q hy.2, hu' q]
  have hsu := setIntegral_sdiff hR' hiu inter_subset_left
  have hsv := setIntegral_sdiff hR' hiv inter_subset_left
  have hAu : riemannianDiskArea g u = ∫ z in D, riemannianAreaDensity g (diskExtension u) z :=
    rfl
  have hAv : riemannianDiskArea g v = ∫ z in D, riemannianAreaDensity g (diskExtension v) z :=
    rfl
  have harea : (∫ z in D ∩ R, riemannianAreaDensity g (diskExtension u) z) ≤
      ∫ z in D ∩ R, riemannianAreaDensity g (diskExtension v) z := by
    rw [houtEq] at hsv
    linarith
  -- 逐点：`e_Ĝ(u') ≤ 2 a_g(u)` 于开盘
  have hpu : ∀ᵐ z ∂volume.restrict (D ∩ R),
      diskMapEnergyDensity Ghat (diskExtension u') z ≤
        2 * riemannianAreaDensity g (diskExtension u) z := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset inter_subset_left ae_disk_interior]
      with z hz
    have hzO : ((diskExtension u' z : W) : M) ∈ O := by
      let q : closedDisk := ⟨z, ball_subset_closedBall hz⟩
      have hq : diskExtension u' z = u' q := diskExtension_coe u' q
      rw [hq, hu' q]
      exact huO ⟨q, rfl⟩
    have he1 : diskMapEnergyDensity Ghat (diskExtension u') z =
        diskMapEnergyDensity G (diskExtension u) z := by
      rw [show diskExtension u = Subtype.val ∘ diskExtension u' from
        funext fun y => (hu' _).symm, ← diskMapEnergyDensity_restrictOpen G W]
      unfold diskMapEnergyDensity
      rw [hagree _ hzO]
      rfl
    have hzO' : diskExtension u z ∈ O := by
      let q : closedDisk := ⟨z, ball_subset_closedBall hz⟩
      have hq : diskExtension u z = u q := diskExtension_coe u q
      rw [hq]
      exact huO ⟨q, rfl⟩
    have he2 : diskMapEnergyDensity G (diskExtension u) z ≤
        2 * diskMapEnergyDensity g (diskExtension u) z := by
      unfold diskMapEnergyDensity
      have h1 := hlower _ hzO' (diskMapPartial (diskExtension u) z 1)
      have h2 := hlower _ hzO' (diskMapPartial (diskExtension u) z Complex.I)
      linarith
    have he3 : diskMapEnergyDensity g (diskExtension u) z =
        riemannianAreaDensity g (diskExtension u) z := by
      have hc := hu.conformal z hz
      have hA' : riemannianAreaDensity g (diskExtension u) z =
          tangentTwoJacobian g (diskMapPartial (diskExtension u) z 1)
            (diskMapPartial (diskExtension u) z Complex.I) := rfl
      rw [hA', tangentTwoJacobian_of_conformal g hc.1 hc.2]
      unfold diskMapEnergyDensity
      rw [← hc.2]
      ring
    rw [he1, ← he3]
    exact he2
  -- 逐点：`a_g(ι∘w) ≤ 2 e_Ĝ(w)`
  have hpw : ∀ z, riemannianAreaDensity g (diskExtension v) z ≤
      2 * diskMapEnergyDensity Ghat (diskExtension w) z := by
    intro z
    rw [hdv]
    exact (riemannianAreaDensity_val_le_R7C W Ghat g two_pos hupper _ z).trans
      (mul_le_mul_of_nonneg_left (riemannianAreaDensity_le_diskMapEnergyDensity Ghat _ z)
        (by norm_num))
  have hiw : IntegrableOn (diskMapEnergyDensity Ghat (diskExtension w)) D :=
    integrable_diskMapEnergyDensity Ghat hwL
  have h1 : (∫ z in D ∩ R, diskMapEnergyDensity Ghat (diskExtension u') z) ≤
      ∫ z in D ∩ R, 2 * riemannianAreaDensity g (diskExtension u) z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z =>
      div_nonneg (add_nonneg (metric_inner_self_nonneg _ _ _)
        (metric_inner_self_nonneg _ _ _)) (by norm_num))
      ((hiu.mono_set inter_subset_left).const_mul 2) hpu
  have h3 : (∫ z in D ∩ R, riemannianAreaDensity g (diskExtension v) z) ≤
      ∫ z in D ∩ R, 2 * diskMapEnergyDensity Ghat (diskExtension w) z :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => riemannianAreaDensity_nonneg _ _ _)
      ((hiw.mono_set inter_subset_left).const_mul 2) (Eventually.of_forall hpw)
  rw [integral_const_mul] at h1 h3
  linarith

end DifferentialGeometry.Geometry
