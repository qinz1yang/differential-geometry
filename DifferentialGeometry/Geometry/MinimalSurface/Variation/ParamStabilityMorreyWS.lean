import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamStabilityRegularWS
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import DifferentialGeometry.Geometry.Metric.BilinearTrace
import DifferentialGeometry.Geometry.MinimalSurface.MorreyLeastAreaSmoothAT

/-!
# S-W-STAB G2 consumer：`IsMorreyDisk` 版 stability inequality on the regular part

`hmin` 来自 `IsMorreyDisk.area_eq_morreyLeastAreaS`，`hmean` 来自 harmonic + conformal：
`DiskTensionTrace` 给坐标迹 `II(1,1)+II(i,i) = 0`，共形度量 `gN = λ|dz|²` 下任何 `gN`-标准正交基
`b` 满足 `λ Σ_i II(b_i,b_i) = II(1,1) + II(i,i)`（二维标准正交基的双线性迹不变，
`OrthonormalBasis.sum_bilinear_diag_eq`）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Topology
open DifferentialGeometry.Integral.Measure
open scoped ContDiff Manifold _root_.Topology BigOperators RealInnerProductSpace

namespace DifferentialGeometry.Geometry

open Riemannian Riemannian.CovariantDerivativeAlong

private local instance (N : TopologicalSpace.Opens ℂ) : MeasurableSpace N := borel N
private local instance (N : TopologicalSpace.Opens ℂ) : BorelSpace N := ⟨rfl⟩
private local instance (N : TopologicalSpace.Opens ℂ) : LocallyCompactSpace N :=
  N.isOpen.locallyCompactSpace
private local instance (N : TopologicalSpace.Opens ℂ) : SigmaCompactSpace N := by infer_instance

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 共形 + 调和 ⇒ 任何 `gN`-标准正交基下平均曲率迹为 0。 -/
theorem sum_secondFundamentalForm_orthonormal_eq_zero_WS (N : TopologicalSpace.Opens ℂ)
    (gN : SmoothRiemannianMetric 𝓘(ℝ, ℂ) N)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (U : ℂ → M)
    (hU : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) = gN.inner z v w)
    (z : N) (hconf : DiskMapConformalAt g U z) (htension : diskMapTension g U z = 0)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) z))
    (hb : ∀ i j, gN.inner z (b i) (b j) = if i = j then 1 else 0) :
    ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (fun q : N => U q) z (b i) (b i) = 0 := by
  classical
  let G : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := gN.inner z
  let coeff : ℝ := G (1 : ℂ) (1 : ℂ)
  have hcoeff : 0 < coeff := gN.pos z (1 : ℂ) (show (1 : ℂ) ≠ 0 from one_ne_zero)
  have h1I : G (1 : ℂ) Complex.I = 0 := by
    change gN.inner z (1 : ℂ) Complex.I = 0
    rw [← hmetric]
    exact hconf.1
  have hI1 : G Complex.I (1 : ℂ) = 0 := (gN.symm z Complex.I (1 : ℂ)).trans h1I
  have hII : G Complex.I Complex.I = coeff := by
    calc
      _ = g.inner (U z) (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) :=
        (hmetric z Complex.I Complex.I).symm
      _ = g.inner (U z) (diskMapPartial U z 1) (diskMapPartial U z 1) := hconf.2.symm
      _ = coeff := hmetric z 1 1
  have hexp (v : ℂ) : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  have hGeu (v w : ℂ) : G v w = coeff * ⟪v, w⟫ := by
    conv_lhs => rw [hexp v, hexp w]
    simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul, h1I, hI1, hII,
      mul_zero, add_zero, zero_add]
    rw [Complex.inner]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    have hc : G (1 : ℂ) (1 : ℂ) = coeff := rfl
    simp only [hc]
    ring
  set s : ℝ := Real.sqrt coeff with hs_def
  have hsne : s ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hcoeff)
  have hss : s * s = coeff := Real.mul_self_sqrt hcoeff.le
  let bC : Module.Basis (Fin 2) ℝ ℂ := b
  let b' : Module.Basis (Fin 2) ℝ ℂ := bC.unitsSMul (fun _ => Units.mk0 s hsne)
  have hb' (i : Fin 2) : b' i = s • bC i := by
    rw [Module.Basis.unitsSMul_apply]
    rfl
  have hon : Orthonormal ℝ b' := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hb' i, hb' j, real_inner_smul_left, real_inner_smul_right]
    have h' : G (bC i) (bC j) = if i = j then 1 else 0 := hb i j
    rw [hGeu] at h'
    calc s * (s * ⟪bC i, bC j⟫) = coeff * ⟪bC i, bC j⟫ := by rw [← hss]; ring
      _ = _ := h'
  let f : OrthonormalBasis (Fin 2) ℝ ℂ := b'.toOrthonormalBasis hon
  have hf (i : Fin 2) : f i = s • bC i := by
    rw [Module.Basis.coe_toOrthonormalBasis]
    exact hb' i
  let II : ℂ →L[ℝ] ℂ →L[ℝ] E := secondFundamentalFormAmbientAt gN g (fun q : N => U q) z
  let Bm : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] E :=
    (ContinuousLinearMap.coeLM ℝ : (ℂ →L[ℝ] E) →ₗ[ℝ] ℂ →ₗ[ℝ] E) ∘ₗ II.toLinearMap
  have hkey := OrthonormalBasis.sum_bilinear_diag_eq Complex.orthonormalBasisOneI f Bm
  have hzero : II (1 : ℂ) (1 : ℂ) + II Complex.I Complex.I = 0 :=
    secondFundamentalForm_disk_coordinate_trace_eq_zero_of_tension_eq_zero
      N gN g U hU hmetric z htension
  have hL : (∑ i : Fin 2,
      Bm (Complex.orthonormalBasisOneI i) (Complex.orthonormalBasisOneI i)) = 0 := by
    simp only [Fin.sum_univ_two, Complex.coe_orthonormalBasisOneI]
    exact hzero
  rw [hL] at hkey
  have hR : (∑ j : Fin 2, Bm (f j) (f j)) = coeff • ∑ i : Fin 2, II (bC i) (bC i) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j]
    change II (s • bC j) (s • bC j) = coeff • II (bC j) (bC j)
    have h1 : II (s • bC j) = s • II (bC j) := map_smul II s (bC j)
    rw [h1, _root_.smul_apply, map_smul, smul_smul, hss]
  rw [hR] at hkey
  have hsum : coeff • (∑ i : Fin 2, II (bC i) (bC i)) = 0 := hkey.symm
  change (∑ i : Fin 2, II (bC i) (bC i)) = 0
  exact (smul_eq_zero.mp hsum).resolve_left (ne_of_gt hcoeff)

/-- **G2 `IsMorreyDisk` 版.**  Morrey disk `u` 的 regular part `N ⊆` 开单位盘（`U` 在 `N` 上 immersion）上，
对一切 `φ ∈ C_c^∞(N)`：`∫_N (|∇φ|² − φ²(Ric(ν,ν) + |II|²)) dμ_{gN} ≥ 0`。`hmin` 由
`IsMorreyDisk.area_eq_morreyLeastAreaS` 给出，`hmean` 由 harmonic + conformal 给出（不再是参数）；
`ν`（单位法向）、`hint`（`U z ∈ interior W`）是显式参数。 -/
theorem IsMorreyDisk.stability_inequality_regular_WS [T3Space M] (hdim : Module.finrank ℝ E = 3)
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U) (W : Set M) (hW : Set.range u ⊆ W)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hUN : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : N => U q))
    (hiN : ∀ q : N, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hunit : ∀ q : N, g.inner (U q) (ν q) (ν q) = 1)
    (hnormal : ∀ (q : N) (v : ℂ), g.inner (U q) (ν q)
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : N => U p) q v) = 0)
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ)
    (b : ∀ q : N, Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q))
    (hb : ∀ (q : N) (i j : Fin 2),
      (g.pullback (fun p : N => U p) hUN hiN).inner q (b q i) (b q j) = if i = j then 1 else 0) :
    let gN := g.pullback (fun p : N => U p) hUN hiN
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := N) gN
    let J : N → ℝ := fun q =>
      let II := secondFundamentalFormAmbientAt gN g (fun p : N => U p) q
      gN.inner q (gradFun gN φ q) (gradFun gN φ q) -
        φ q ^ 2 * ((∑ i : Fin 2, g.inner (U q) ((riemannOp (LeviCivita g) (U q)) (ν q)
            (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q (b q i)))
            (ν q)) +
          ∑ i : Fin 2, ∑ j : Fin 2, g.inner (U q) (II (b q i) (b q j)) (II (b q i) (b q j)))
    Integrable J μ ∧ 0 ≤ ∫ q : N, J q ∂μ := by
  intro gN μ J
  have hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W →
        riemannianDiskArea g u ≤ riemannianDiskArea g v := by
    intro v hv hw hWv
    rw [hu.area_eq_morreyLeastAreaS hdim hγ hW]
    exact morreyLeastAreaS_le g hv hw hWv
  have hmetric : ∀ (z : N) (v w : ℂ),
      g.inner (U z) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z v) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z w) =
        gN.inner z v w := by
    intro z v w
    have hdf := DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U N z
    exact (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U z) (L v) (L w)) hdf).symm
  have hmean : ∀ (q : N) (b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q)),
      (∀ i j, gN.inner q (b i) (b j) = if i = j then 1 else 0) →
      ∑ i : Fin 2, secondFundamentalFormAmbientAt gN g (fun p : N => U p) q (b i) (b i) = 0 :=
    fun q b' hb' => sum_secondFundamentalForm_orthonormal_eq_zero_WS N gN g U hUN hmetric q
      (hu.conformal_of_extension hExt q (hNball q.property))
      (hu.tension_eq_zero_of_extension hExt q (hNball q.property)) b' hb'
  exact DifferentialGeometry.Geometry.stability_inequality_regular_WS hdim g W γ hExt hW hu.trace
    hmin N hNball hUN hiN hint ν hν hunit hnormal hmean φ hφ hφc b hb

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- 光滑延拓 `U` 限制到开单位盘上光滑。 -/
theorem SmoothDiskExtension.contMDiff_unitBall_WS {u : C(closedDisk, M)} {U : ℂ → M}
    (hExt : SmoothDiskExtension (E := E) u U) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞
      (fun q : (TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball) => U q) := by
  obtain ⟨_, s, _, hDs, hUs⟩ := hExt
  exact hUs.comp_contMDiff contMDiff_subtype_val
    (fun q => hDs (Metric.ball_subset_closedBall q.property))

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- `U` 在开单位盘各点的微分单射 ⇒ 限制到子流形 `D` 上的微分单射。 -/
theorem injective_mfderiv_unitBall_WS {U : ℂ → M}
    (hinj : ∀ z ∈ Metric.ball (0 : ℂ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ∀ q : (TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball),
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : (TopologicalSpace.Opens.mk
        (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball) => U p) q) := by
  intro q
  rw [DifferentialGeometry.mfderiv_restrict_open (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) U _ q]
  exact hinj q q.property

end DifferentialGeometry.Geometry
