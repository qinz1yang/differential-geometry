import DifferentialGeometry.Geometry.Comparison.Variation.GeneralCurvatureCommutation
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantChainRule
import DifferentialGeometry.Bundle.SmoothScalarGerm
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisBracket
import DifferentialGeometry.Geometry.Connection.ParallelTransport.AlongCurve
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.PointwiseCurvatureDerivative
import DifferentialGeometry.Geometry.Comparison.Variation.PerpFrame

noncomputable section

set_option autoImplicit false

open Set Function Filter Manifold Bundle
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace Variation

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem exists_smooth_exp
    (γ : Real -> M) (V : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hV : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (V s) : TangentBundle I M)))
    (B : Fin (Module.finrank Real E) -> ∀ x : M, TangentSpace I x)
    (hBnear : ∀ᶠ x in 𝓝 (γ t), ∀ i,
      B i x = chartBasisVecFiber (I := I) (γ t) i x) :
    ∃ c : Fin (Module.finrank Real E) -> Real -> Real,
      (∀ i, ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ (c i)) ∧
      (∀ i, c i t =
        chartSectionCoord (E := E) (chartRepAt (I := I) γ V t) i t) ∧
      V =ᶠ[𝓝 t] fun s => ∑ i, c i s • B i (γ s) := by
  classical
  let e := trivializationAt E (TangentSpace I) (γ t)
  let S : Real -> TangentBundle I M := fun s =>
    TotalSpace.mk' E (E := (TangentSpace I : M -> Type _)) (γ s) (V s)
  let U : Set Real := γ ⁻¹' e.baseSet
  let cLoc : Fin (Module.finrank Real E) -> Real -> Real :=
    fun i => chartSectionCoord (E := E) (chartRepAt (I := I) γ V t) i
  have hUopen : IsOpen U :=
    hγ.continuous.isOpen_preimage _ e.open_baseSet
  have htU : t ∈ U :=
    mem_baseSet_trivializationAt E (TangentSpace I) (γ t)
  have hSMaps : MapsTo S U e.source := by
    intro s hs
    exact e.mem_source.mpr hs
  have hcoord :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s => (e (S s)).2) U :=
    (e.contMDiffOn_iff hSMaps).mp hV.contMDiffOn |>.2
  have hcLocOn : ∀ i,
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, Real) ∞ (cLoc i) U := by
    intro i
    refine ((chartCoordCLM (E := E) i).contMDiff.comp_contMDiffOn hcoord).congr ?_
    intro s hs
    change chartCoordCLM (E := E) i
          (e.continuousLinearMapAt Real (γ s) (V s)) =
        chartCoordCLM (E := E) i ((e (S s)).2)
    congr 1
    rw [e.continuousLinearMapAt_apply (R := Real)]
    rw [e.coe_linearMapAt_of_mem hs]
  have hc : ∀ i, ∃ f : Real -> Real,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ f ∧
        f =ᶠ[𝓝 t] cLoc i :=
    fun i => exists_smooth_germ (I := 𝓘(Real, Real))
      hUopen htU (hcLocOn i)
  choose c hcsm hceq using hc
  have hγcont : ContinuousAt γ t := hγ.continuous.continuousAt
  have hBcurve :
      ∀ᶠ s in 𝓝 t, ∀ i, B i (γ s) =
        chartBasisVecFiber (I := I) (γ t) i (γ s) :=
    hγcont hBnear
  have hbase :
      ∀ᶠ s in 𝓝 t,
        γ s ∈ (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
    exact hγcont
      ((trivializationAt E (TangentSpace I) (γ t)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ t)))
  refine ⟨c, hcsm, fun i => (hceq i).self_of_nhds, ?_⟩
  filter_upwards [hBcurve, hbase, Filter.eventually_all.mpr hceq] with s hBs hs hcs
  have hcancel :
      (trivializationAt E (TangentSpace I) (γ t)).symmL Real (γ s)
          ((trivializationAt E (TangentSpace I) (γ t)).continuousLinearMapAt
            Real (γ s) (V s)) =
        V s :=
    (trivializationAt E (TangentSpace I) (γ t)).symmL_continuousLinearMapAt
      (R := Real) hs (V s)
  rw [← hcancel, symmL_eq_sum_chartBasisVecFiber (I := I)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcs i, hBs i]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem curvDeriv_left_at
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X X' Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hX' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X' s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M)))
    (hXt : X t = X' t) :
    curvDerivAlong (I := I) g γ X Y Z t =
      curvDerivAlong (I := I) g γ X' Y Z t := by
  classical
  obtain ⟨B, hBsm, hBnear⟩ :=
    exists_smooth_chartBasisExtension (I := I) (γ t)
  obtain ⟨c, hcsm, hcval, hcexp⟩ :=
    exists_smooth_exp (I := I) γ X t hγ hX B hBnear
  obtain ⟨c', hcsm', hcval', hcexp'⟩ :=
    exists_smooth_exp (I := I) γ X' t hγ hX' B hBnear
  have hBcurve :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (B i (γ s)) : TangentBundle I M)) := by
    intro i
    simpa only [Function.comp_apply] using (hBsm i).comp hγ
  have hcEq : ∀ i, c i t = c' i t := by
    intro i
    rw [hcval i, hcval' i, chartSectionCoord_def, chartSectionCoord_def]
    rw [chartRepAt_apply, chartRepAt_apply, hXt]
  have hscaled :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm i) (hBcurve i)
  have hscaled' :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c' i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm' i) (hBcurve i)
  have hsum :
      curvDerivAlong (I := I) g γ
          (fun s => ∑ i, c i s • B i (γ s)) Y Z t =
        ∑ i, curvDerivAlong (I := I) g γ
          (fun s => c i s • B i (γ s)) Y Z t := by
    simpa using curvDeriv_sum_left (I := I) g γ Finset.univ
      (fun i s => c i s • B i (γ s)) Y Z t hγ
      (fun i _ => hscaled i) hY hZ
  have hsum' :
      curvDerivAlong (I := I) g γ
          (fun s => ∑ i, c' i s • B i (γ s)) Y Z t =
        ∑ i, curvDerivAlong (I := I) g γ
          (fun s => c' i s • B i (γ s)) Y Z t := by
    simpa using curvDeriv_sum_left (I := I) g γ Finset.univ
      (fun i s => c' i s • B i (γ s)) Y Z t hγ
      (fun i _ => hscaled' i) hY hZ
  calc
    curvDerivAlong (I := I) g γ X Y Z t =
        curvDerivAlong (I := I) g γ
          (fun s => ∑ i, c i s • B i (γ s)) Y Z t :=
      curvDeriv_congr (I := I) g γ hcexp
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    _ = ∑ i, curvDerivAlong (I := I) g γ
          (fun s => c i s • B i (γ s)) Y Z t := hsum
    _ = ∑ i, curvDerivAlong (I := I) g γ
          (fun s => c' i s • B i (γ s)) Y Z t := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [curvDeriv_smul_left (I := I) g γ (c i)
        (fun s => B i (γ s)) Y Z t hγ
        ((hcsm i).contDiff.contDiffAt.differentiableAt (by simp))
        (hBcurve i) hY hZ]
      rw [curvDeriv_smul_left (I := I) g γ (c' i)
        (fun s => B i (γ s)) Y Z t hγ
        ((hcsm' i).contDiff.contDiffAt.differentiableAt (by simp))
        (hBcurve i) hY hZ]
      rw [hcEq i]
    _ = curvDerivAlong (I := I) g γ
          (fun s => ∑ i, c' i s • B i (γ s)) Y Z t := hsum'.symm
    _ = curvDerivAlong (I := I) g γ X' Y Z t :=
      (curvDeriv_congr (I := I) g γ hcexp'
        Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem curvDeriv_mid_at
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Y' Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hY' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y' s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M)))
    (hYt : Y t = Y' t) :
    curvDerivAlong (I := I) g γ X Y Z t =
      curvDerivAlong (I := I) g γ X Y' Z t := by
  classical
  obtain ⟨B, hBsm, hBnear⟩ :=
    exists_smooth_chartBasisExtension (I := I) (γ t)
  obtain ⟨c, hcsm, hcval, hcexp⟩ :=
    exists_smooth_exp (I := I) γ Y t hγ hY B hBnear
  obtain ⟨c', hcsm', hcval', hcexp'⟩ :=
    exists_smooth_exp (I := I) γ Y' t hγ hY' B hBnear
  have hBcurve :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (B i (γ s)) : TangentBundle I M)) := by
    intro i
    simpa only [Function.comp_apply] using (hBsm i).comp hγ
  have hcEq : ∀ i, c i t = c' i t := by
    intro i
    rw [hcval i, hcval' i, chartSectionCoord_def, chartSectionCoord_def]
    rw [chartRepAt_apply, chartRepAt_apply, hYt]
  have hscaled :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm i) (hBcurve i)
  have hscaled' :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c' i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm' i) (hBcurve i)
  have hsum :
      curvDerivAlong (I := I) g γ X
          (fun s => ∑ i, c i s • B i (γ s)) Z t =
        ∑ i, curvDerivAlong (I := I) g γ X
          (fun s => c i s • B i (γ s)) Z t := by
    simpa using curvDeriv_sum_mid (I := I) g γ Finset.univ X
      (fun i s => c i s • B i (γ s)) Z t hγ hX
      (fun i _ => hscaled i) hZ
  have hsum' :
      curvDerivAlong (I := I) g γ X
          (fun s => ∑ i, c' i s • B i (γ s)) Z t =
        ∑ i, curvDerivAlong (I := I) g γ X
          (fun s => c' i s • B i (γ s)) Z t := by
    simpa using curvDeriv_sum_mid (I := I) g γ Finset.univ X
      (fun i s => c' i s • B i (γ s)) Z t hγ hX
      (fun i _ => hscaled' i) hZ
  calc
    curvDerivAlong (I := I) g γ X Y Z t =
        curvDerivAlong (I := I) g γ X
          (fun s => ∑ i, c i s • B i (γ s)) Z t :=
      curvDeriv_congr (I := I) g γ Filter.EventuallyEq.rfl hcexp
        Filter.EventuallyEq.rfl
    _ = ∑ i, curvDerivAlong (I := I) g γ X
          (fun s => c i s • B i (γ s)) Z t := hsum
    _ = ∑ i, curvDerivAlong (I := I) g γ X
          (fun s => c' i s • B i (γ s)) Z t := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [curvDeriv_smul_mid (I := I) g γ (c i) X
        (fun s => B i (γ s)) Z t hγ
        ((hcsm i).contDiff.contDiffAt.differentiableAt (by simp))
        hX (hBcurve i) hZ]
      rw [curvDeriv_smul_mid (I := I) g γ (c' i) X
        (fun s => B i (γ s)) Z t hγ
        ((hcsm' i).contDiff.contDiffAt.differentiableAt (by simp))
        hX (hBcurve i) hZ]
      rw [hcEq i]
    _ = curvDerivAlong (I := I) g γ X
          (fun s => ∑ i, c' i s • B i (γ s)) Z t := hsum'.symm
    _ = curvDerivAlong (I := I) g γ X Y' Z t :=
      (curvDeriv_congr (I := I) g γ Filter.EventuallyEq.rfl hcexp'
        Filter.EventuallyEq.rfl).symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private theorem curvDeriv_right_at
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Z Z' : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M)))
    (hZ' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z' s) : TangentBundle I M)))
    (hZt : Z t = Z' t) :
    curvDerivAlong (I := I) g γ X Y Z t =
      curvDerivAlong (I := I) g γ X Y Z' t := by
  classical
  obtain ⟨B, hBsm, hBnear⟩ :=
    exists_smooth_chartBasisExtension (I := I) (γ t)
  obtain ⟨c, hcsm, hcval, hcexp⟩ :=
    exists_smooth_exp (I := I) γ Z t hγ hZ B hBnear
  obtain ⟨c', hcsm', hcval', hcexp'⟩ :=
    exists_smooth_exp (I := I) γ Z' t hγ hZ' B hBnear
  have hBcurve :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (B i (γ s)) : TangentBundle I M)) := by
    intro i
    simpa only [Function.comp_apply] using (hBsm i).comp hγ
  have hcEq : ∀ i, c i t = c' i t := by
    intro i
    rw [hcval i, hcval' i, chartSectionCoord_def, chartSectionCoord_def]
    rw [chartRepAt_apply, chartRepAt_apply, hZt]
  have hscaled :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm i) (hBcurve i)
  have hscaled' :
      ∀ i, ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (c' i s • B i (γ s)) : TangentBundle I M)) := by
    intro i
    exact contMDiff_smul_bundleField_perp (I := I)
      hγ (hcsm' i) (hBcurve i)
  have hsum :
      curvDerivAlong (I := I) g γ X Y
          (fun s => ∑ i, c i s • B i (γ s)) t =
        ∑ i, curvDerivAlong (I := I) g γ X Y
          (fun s => c i s • B i (γ s)) t := by
    simpa using curvDeriv_sum_right (I := I) g γ Finset.univ X Y
      (fun i s => c i s • B i (γ s)) t hγ hX hY
      (fun i _ => hscaled i)
  have hsum' :
      curvDerivAlong (I := I) g γ X Y
          (fun s => ∑ i, c' i s • B i (γ s)) t =
        ∑ i, curvDerivAlong (I := I) g γ X Y
          (fun s => c' i s • B i (γ s)) t := by
    simpa using curvDeriv_sum_right (I := I) g γ Finset.univ X Y
      (fun i s => c' i s • B i (γ s)) t hγ hX hY
      (fun i _ => hscaled' i)
  calc
    curvDerivAlong (I := I) g γ X Y Z t =
        curvDerivAlong (I := I) g γ X Y
          (fun s => ∑ i, c i s • B i (γ s)) t :=
      curvDeriv_congr (I := I) g γ Filter.EventuallyEq.rfl
        Filter.EventuallyEq.rfl hcexp
    _ = ∑ i, curvDerivAlong (I := I) g γ X Y
          (fun s => c i s • B i (γ s)) t := hsum
    _ = ∑ i, curvDerivAlong (I := I) g γ X Y
          (fun s => c' i s • B i (γ s)) t := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [curvDeriv_smul_right (I := I) g γ (c i) X Y
        (fun s => B i (γ s)) t hγ
        ((hcsm i).contDiff.contDiffAt.differentiableAt (by simp))
        hX hY (hBcurve i)]
      rw [curvDeriv_smul_right (I := I) g γ (c' i) X Y
        (fun s => B i (γ s)) t hγ
        ((hcsm' i).contDiff.contDiffAt.differentiableAt (by simp))
        hX hY (hBcurve i)]
      rw [hcEq i]
    _ = curvDerivAlong (I := I) g γ X Y
          (fun s => ∑ i, c' i s • B i (γ s)) t := hsum'.symm
    _ = curvDerivAlong (I := I) g γ X Y Z' t :=
      (curvDeriv_congr (I := I) g γ Filter.EventuallyEq.rfl
        Filter.EventuallyEq.rfl hcexp').symm

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem curvDeriv_congr_at
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X X' Y Y' Z Z' : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hX' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X' s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hY' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y' s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M)))
    (hZ' : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z' s) : TangentBundle I M)))
    (hXt : X t = X' t) (hYt : Y t = Y' t) (hZt : Z t = Z' t) :
    curvDerivAlong (I := I) g γ X Y Z t =
      curvDerivAlong (I := I) g γ X' Y' Z' t := by
  calc
    curvDerivAlong (I := I) g γ X Y Z t =
        curvDerivAlong (I := I) g γ X' Y Z t :=
      curvDeriv_left_at (I := I) g γ X X' Y Z t
        hγ hX hX' hY hZ hXt
    _ = curvDerivAlong (I := I) g γ X' Y' Z t :=
      curvDeriv_mid_at (I := I) g γ X' Y Y' Z t
        hγ hX' hY hY' hZ hYt
    _ = curvDerivAlong (I := I) g γ X' Y' Z' t :=
      curvDeriv_right_at (I := I) g γ X' Y' Z Z' t
        hγ hX' hY' hZ hZ' hZt

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem curvDeriv_restrict
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _))
    (t : Real) (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ) :
    curvDerivAlong (I := I) g γ
        (fun s => X (γ s)) (fun s => Y (γ s)) (fun s => Z (γ s)) t =
      nablaRiemannOp (I := I) g (γ t)
        ((mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real))
        (X (γ t)) (Y (γ t)) (Z (γ t)) := by
  let cov := LeviCivita (I := I) g
  let v : TangentSpace I (γ t) :=
    (mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real)
  let D : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (smoothExtensionTangent (I := I) (γ t) v)
      (smoothExtensionTangent_contMDiff (I := I) (γ t) v)
  have hD : D (γ t) = v :=
    smoothExtensionTangent_eq (I := I) (γ t) v
  have hR :
      (fun s : Real =>
          curvAlong (I := I) g γ
            (fun r => X (γ r)) (fun r => Y (γ r)) (fun r => Z (γ r)) s) =
        fun s : Real => riemannSec cov X Y Z (γ s) := by
    funext s
    exact riemannOp_apply_smooth (cov := cov)
      X.contMDiff Y.contMDiff Z.contMDiff
  have hRsm :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞
        (T% (fun x : M => riemannSec cov X Y Z x)) :=
    riemannSec_contMDiff (cov := cov)
      X.contMDiff Y.contMDiff Z.contMDiff
  have hRcov :
      covDerivAlong (I := I) g γ
          (fun s : Real => riemannSec cov X Y Z (γ s)) t =
        cov.toFun (fun x : M => riemannSec cov X Y Z x) (γ t) v := by
    simpa [cov, v] using
      covDerivAlong_restrict_eq_leviCivita
        (I := I) g γ (fun x : M => riemannSec cov X Y Z x) t hγ
          ((hRsm (γ t)).mdifferentiableAt (by simp))
  have hXcov :
      covDerivAlong (I := I) g γ (fun s => X (γ s)) t =
        (covApply cov D X) (γ t) := by
    rw [covDerivAlong_restrict_eq_leviCivita
      (I := I) g γ (fun x => X x) t hγ
        ((X.contMDiff (γ t)).mdifferentiableAt (by simp))]
    change cov.toFun X (γ t) v = cov.toFun X (γ t) (D (γ t))
    rw [hD]
  have hYcov :
      covDerivAlong (I := I) g γ (fun s => Y (γ s)) t =
        (covApply cov D Y) (γ t) := by
    rw [covDerivAlong_restrict_eq_leviCivita
      (I := I) g γ (fun x => Y x) t hγ
        ((Y.contMDiff (γ t)).mdifferentiableAt (by simp))]
    change cov.toFun Y (γ t) v = cov.toFun Y (γ t) (D (γ t))
    rw [hD]
  have hZcov :
      covDerivAlong (I := I) g γ (fun s => Z (γ s)) t =
        (covApply cov D Z) (γ t) := by
    rw [covDerivAlong_restrict_eq_leviCivita
      (I := I) g γ (fun x => Z x) t hγ
        ((Z.contMDiff (γ t)).mdifferentiableAt (by simp))]
    change cov.toFun Z (γ t) v = cov.toFun Z (γ t) (D (γ t))
    rw [hD]
  have hDXsm :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (covApply cov D X)) :=
    covApply_contMDiff (cov := cov) D.contMDiff X.contMDiff
  have hDYsm :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (covApply cov D Y)) :=
    covApply_contMDiff (cov := cov) D.contMDiff Y.contMDiff
  have hDZsm :
      ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (covApply cov D Z)) :=
    covApply_contMDiff (cov := cov) D.contMDiff Z.contMDiff
  change curvDerivAlong (I := I) g γ
      (fun s => X (γ s)) (fun s => Y (γ s)) (fun s => Z (γ s)) t =
    nablaRiemannOp (I := I) g (γ t) v (X (γ t)) (Y (γ t)) (Z (γ t))
  rw [show v = D (γ t) from hD.symm, nablaRiemannOp_sec]
  rw [show leviCivitaConnectionOfMetric (I := I) g = cov from by
    simp only [cov, LeviCivita_eq_leviCivitaConnectionOfMetric]]
  unfold curvDerivAlong
  rw [hR, hRcov]
  unfold curvAlong
  simp only
  rw [hXcov, hYcov, hZcov]
  rw [riemannOp_apply_smooth (cov := cov) hDXsm Y.contMDiff Z.contMDiff]
  rw [riemannOp_apply_smooth (cov := cov) X.contMDiff hDYsm Z.contMDiff]
  rw [riemannOp_apply_smooth (cov := cov) X.contMDiff Y.contMDiff hDZsm]
  rw [← hD]
  rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
theorem curvDeriv_eq_nabla
    (g : SmoothRiemannianMetric I M) (γ : Real -> M)
    (X Y Z : ∀ s, TangentSpace I (γ s)) (t : Real)
    (hγ : ContMDiff 𝓘(Real, Real) I ∞ γ)
    (hX : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (X s) : TangentBundle I M)))
    (hY : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Y s) : TangentBundle I M)))
    (hZ : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (γ s) (Z s) : TangentBundle I M))) :
    curvDerivAlong (I := I) g γ X Y Z t =
      nablaRiemannOp (I := I) g (γ t)
        ((mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real))
        (X t) (Y t) (Z t) := by
  let X₀ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (smoothExtensionTangent (I := I) (γ t) (X t))
      (smoothExtensionTangent_contMDiff (I := I) (γ t) (X t))
  let Y₀ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (smoothExtensionTangent (I := I) (γ t) (Y t))
      (smoothExtensionTangent_contMDiff (I := I) (γ t) (Y t))
  let Z₀ : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M -> Type _) :=
    ContMDiffSection.mk
      (smoothExtensionTangent (I := I) (γ t) (Z t))
      (smoothExtensionTangent_contMDiff (I := I) (γ t) (Z t))
  have hX₀ :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (X₀ (γ s)) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using X₀.contMDiff.comp hγ
  have hY₀ :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (Y₀ (γ s)) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using Y₀.contMDiff.comp hγ
  have hZ₀ :
      ContMDiff 𝓘(Real, Real) I.tangent ∞
        (fun s : Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (γ s) (Z₀ (γ s)) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using Z₀.contMDiff.comp hγ
  have hXval : X t = X₀ (γ t) :=
    (smoothExtensionTangent_eq (I := I) (γ t) (X t)).symm
  have hYval : Y t = Y₀ (γ t) :=
    (smoothExtensionTangent_eq (I := I) (γ t) (Y t)).symm
  have hZval : Z t = Z₀ (γ t) :=
    (smoothExtensionTangent_eq (I := I) (γ t) (Z t)).symm
  calc
    curvDerivAlong (I := I) g γ X Y Z t =
        curvDerivAlong (I := I) g γ
          (fun s => X₀ (γ s)) (fun s => Y₀ (γ s))
          (fun s => Z₀ (γ s)) t :=
      curvDeriv_congr_at (I := I) g γ
        X (fun s => X₀ (γ s)) Y (fun s => Y₀ (γ s))
        Z (fun s => Z₀ (γ s)) t hγ hX hX₀ hY hY₀ hZ hZ₀
        hXval hYval hZval
    _ = nablaRiemannOp (I := I) g (γ t)
          ((mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real))
          (X₀ (γ t)) (Y₀ (γ t)) (Z₀ (γ t)) :=
      curvDeriv_restrict (I := I) g γ X₀ Y₀ Z₀ t hγ
    _ = nablaRiemannOp (I := I) g (γ t)
          ((mfderiv 𝓘(Real, Real) I γ t : Real →L[Real] _) (1 : Real))
          (X t) (Y t) (Z t) := by
      rw [← hXval, ← hYval, ← hZval]

end Variation
end Riemannian
end Geometry
end DifferentialGeometry

end
