import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointDensityLipschitzTests
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.ChartLocality
import DifferentialGeometry.Geometry.Coordinates.Calculus.ParametricZeroExtension
import DifferentialGeometry.Topology.Manifold.CompactChartNeighborhood
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Integrability
import DifferentialGeometry.Geometry.Operator.Gradient.ChartFamilyIdentification
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Topology.Algebra.Support
import Mathlib.MeasureTheory.Integral.Prod

import DifferentialGeometry.Geometry.Measure.ManifoldRademacher
import DifferentialGeometry.Geometry.Coordinates.Fields.Scalar
import Mathlib.Analysis.Calculus.ContDiff.RCLike


section

open Filter Set Manifold MeasureTheory
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates (scalarOnE)
open scoped Topology ContDiff

namespace DifferentialGeometry.Geometry.Measure

private theorem locallyLipschitzOn_slice
    {P X F : Type*} [PseudoEMetricSpace P] [PseudoEMetricSpace X] [PseudoEMetricSpace F]
    {S : Set P} {T : Set X} {f : P × X → F}
    (hf : LocallyLipschitzOn (S ×ˢ T) f) {t : P} (ht : t ∈ S) :
    LocallyLipschitzOn T (fun x => f (t, x)) := by
  intro x hx
  obtain ⟨K, V, hV, hK⟩ := hf (show (t, x) ∈ S ×ˢ T from ⟨ht, hx⟩)
  have hpair : Tendsto (fun y : X => (t, y)) (𝓝[T] x) (𝓝[S ×ˢ T] (t, x)) := by
    apply (continuous_const.prodMk continuous_id).continuousWithinAt.tendsto_nhdsWithin
    exact fun _ hy => ⟨ht, hy⟩
  refine ⟨K, (fun y : X => (t, y)) ⁻¹' V, hpair hV, ?_⟩
  intro y hy z hz
  simpa only [Prod.edist_eq, edist_self, zero_max] using hK hy hz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn
    [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
    {P : Type*} [PseudoEMetricSpace P]
    (g : P → SmoothRiemannianMetric I M) {S : Set P} {ψ : P × M → ℝ}
    (hψ : ∀ alpha : M, LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)))
    {t : P} (ht : t ∈ S) :
    ∀ᵐ x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := M) (g t),
      MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => ψ (t, x)) x := by
  apply ae_iff.mpr
  apply riemannianVolumeMeasure_nondiff_null
  intro alpha
  exact locallyLipschitzOn_slice (hψ alpha) ht

private theorem locallyLipschitzOn_chart_mul
    [I.Boundaryless] {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (alpha : M) {S : Set P} {rho : M → ℝ} {ψ : P × M → ℝ}
    (hrho : ContMDiff I 𝓘(ℝ, ℝ) ∞ rho)
    (hψ : LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2))) :
    LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2) *
        ψ (z.1, (extChartAt I alpha).symm z.2)) := by
  have hrhoC : ContDiffOn ℝ ∞
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2))
      (univ ×ˢ (extChartAt I alpha).target) := by
    exact (Tensor.Coordinates.scalarOnE_contDiffOn alpha hrho).comp
      contDiffOn_snd (fun _ hz => hz.2)
  have hrhoL : LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => rho ((extChartAt I alpha).symm z.2)) := by
    intro z hz
    have hat : ContDiffAt ℝ 1
        (fun z : P × E => rho ((extChartAt I alpha).symm z.2)) z :=
      (hrhoC.of_le (by simp)).contDiffAt
        ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha)).mem_nhds
          ⟨mem_univ _, hz.2⟩)
    obtain ⟨K, V, hV, hK⟩ := hat.exists_lipschitzOnWith
    exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩
  have hmul : LocallyLipschitz (fun z : ℝ × ℝ => z.1 * z.2) :=
    (contDiff_fst.mul contDiff_snd : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1 * z.2)).locallyLipschitz
  rw [locallyLipschitzOn_iff_restrict]
  exact hmul.comp (hrhoL.restrict.prodMk hψ.restrict)

omit [IsManifold I ∞ M] in
private theorem contDiffOn_scalarOnE_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {k : WithTop ℕ∞} [IsManifold I k M]
    (alpha : M) {f : P × M → ℝ} {s : Set P}
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) k f (s ×ˢ univ)) :
    ContDiffOn ℝ k
      (fun z : P × E => scalarOnE (I := I) alpha (fun x => f (z.1, x)) z.2)
      (s ×ˢ (extChartAt I alpha).target) := by
  have hfst : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, P) k
      (fun z : P × E => z.1) (s ×ˢ (extChartAt I alpha).target) := contMDiffOn_fst
  have hsnd : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) I k
      (fun z : P × E => (extChartAt I alpha).symm z.2)
      (s ×ˢ (extChartAt I alpha).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) alpha).comp contMDiffOn_snd ?_
    exact fun _ hz => hz.2
  have hpair := hfst.prodMk hsnd
  have hcomp := hf.comp hpair (fun _ hz => ⟨hz.1, mem_univ _⟩)
  have hcont : ContDiffOn ℝ k
      (fun z : P × E => f (z.1, (extChartAt I alpha).symm z.2))
      (s ×ˢ (extChartAt I alpha).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  exact hcont

omit [IsManifold I ∞ M] in
private theorem locallyLipschitzOn_chart_prod_of_contMDiff
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [IsManifold I 1 M] [I.Boundaryless]
    (alpha : M) {S : Set P} {ψ : P × M → ℝ}
    (hψ : ContMDiff (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) 1 ψ) :
    LocallyLipschitzOn (S ×ˢ (extChartAt I alpha).target)
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)) := by
  have hraw : ContDiffOn ℝ 1
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2))
      (univ ×ˢ (extChartAt I alpha).target) :=
    contDiffOn_scalarOnE_prod alpha hψ.contMDiffOn
  intro z hz
  have hat : ContDiffAt ℝ 1
      (fun z : P × E => ψ (z.1, (extChartAt I alpha).symm z.2)) z :=
    hraw.contDiffAt
      ((isOpen_univ.prod (isOpen_extChartAt_target (I := I) alpha)).mem_nhds
        ⟨mem_univ _, hz.2⟩)
  obtain ⟨K, V, hV, hK⟩ := hat.exists_lipschitzOnWith
  exact ⟨K, V, mem_nhdsWithin_of_mem_nhds hV, hK⟩

end DifferentialGeometry.Geometry.Measure

end

noncomputable section

open Filter Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem mvfderiv_eq_zero_of_notMem_tsupport
    {f : M → ℝ} {x : M} (hx : x ∉ tsupport f) : mvfderiv I f x = 0 := by
  have heq : f =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hx
  have hd := heq.mfderiv_eq (I := I) (I' := 𝓘(ℝ, ℝ))
  simp only [mfderiv_const] at hd
  rw [mvfderiv, hd]
  ext v
  change NormedSpace.fromTangentSpace (𝕜 := ℝ) (f x) 0 = 0
  exact map_zero _

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem time_spatial_residual_eq_zero_of_notMem_tsupport
    (u ψ : ℝ × M → ℝ) (V : (t : ℝ) → (x : M) → TangentSpace I x)
    {z : ℝ × M} (hz : z ∉ tsupport ψ) :
    u z * (deriv (fun t => ψ (t, z.2)) z.1 +
      mvfderiv I (fun x => ψ (z.1, x)) z.2 (V z.1 z.2)) = 0 := by
  have ht : z.1 ∉ tsupport (fun t => ψ (t, z.2)) := by
    intro h
    apply hz
    exact tsupport_comp_subset_preimage (f := fun t => (t, z.2)) ψ
      (continuous_id.prodMk continuous_const) h
  have hx : z.2 ∉ tsupport (fun x => ψ (z.1, x)) := by
    intro h
    apply hz
    exact tsupport_comp_subset_preimage (f := fun x => (z.1, x)) ψ
      (continuous_const.prodMk continuous_id) h
  rw [deriv_of_notMem_tsupport ht, mvfderiv_eq_zero_of_notMem_tsupport hx]
  simp only [zero_apply, zero_add, mul_zero]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tsupport_time_spatial_residual_subset
    (u ψ : ℝ × M → ℝ) (V : (t : ℝ) → (x : M) → TangentSpace I x) :
    tsupport (fun z : ℝ × M => u z * (deriv (fun t => ψ (t, z.2)) z.1 +
      mvfderiv I (fun x => ψ (z.1, x)) z.2 (V z.1 z.2))) ⊆ tsupport ψ := by
  apply closure_minimal _ (isClosed_tsupport ψ)
  intro z hz
  by_contra hnot
  exact hz (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hnot)

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem hasCompactSupport_time_spatial_residual_slice
    [T2Space M] (u ψ : ℝ × M → ℝ)
    (V : (t : ℝ) → (x : M) → TangentSpace I x) (hψ : HasCompactSupport ψ) (t : ℝ) :
    HasCompactSupport (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
      mvfderiv I (fun y => ψ (t, y)) x (V t x))) := by
  apply HasCompactSupport.of_support_subset_isCompact (hψ.image continuous_snd)
  intro x hx
  exact ⟨(t, x), by
    by_contra hn
    exact hx (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn), rfl⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
private theorem tsupport_time_spatial_residual_slice_subset
    [T2Space M] (u ψ : ℝ × M → ℝ)
    (V : (t : ℝ) → (x : M) → TangentSpace I x) (hψ : HasCompactSupport ψ) (t : ℝ) :
    tsupport (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
      mvfderiv I (fun y => ψ (t, y)) x (V t x))) ⊆ Prod.snd '' tsupport ψ := by
  apply closure_minimal _ (hψ.image continuous_snd).isClosed
  intro x hx
  exact ⟨(t, x), by
    by_contra hn
    exact hx (time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn), rfl⟩

private theorem inner_gradientFun_eq_mvfderiv
    (g : SmoothRiemannianMetric I M) (f ψ : M → ℝ) (x : M) :
    g.inner x (gradientFun g f x) (gradientFun g ψ x) =
      mvfderiv I ψ x (gradientFun g f x) := by
  rw [g.symm, inner_gradientFun]

end DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Integral.Measure

open Geometry.Operator MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {μ : Measure ℝ} [Measure.IsAddHaarMeasure μ]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
    (g : ℝ → SmoothRiemannianMetric I M) (α : M)
    (u f ψ : ℝ × M → ℝ) {S : Set ℝ} {W : Set E}
    (hS : IsOpen S) (hW : IsOpen W) (hWt : W ⊆ (extChartAt I α).target)
    (hψc : HasCompactSupport ψ)
    (hψs : Prod.snd '' tsupport ψ ⊆ (chartAt H α).source)
    (hψW : ∀ z ∈ tsupport ψ, extChartAt I α z.2 ∈ W)
    (hf : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => f (z.1, (extChartAt I α).symm z.2)))
    (hψ : LocallyLipschitzOn (S ×ˢ W)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I α).symm z.2)))
    (hi : ∀ᵐ t ∂μ, t ∈ S → Integrable
      (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y))))
      ((modelHaar (E := E)).restrict W)) :
    ∀ᵐ t ∂μ, t ∈ S →
      Integrable (fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => f (t, y)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x)))
        (riemannianVolumeMeasure (I := I) (M := M) (g t)) ∧
      (∫ x, u (t, x) * (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => f (t, y)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
        ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
      ∫ y in W, chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y)))
        ∂modelHaar := by
  let R : ℝ × M → ℝ := fun z => u z * (deriv (fun t => ψ (t, z.2)) z.1 +
    (g z.1).inner z.2 (gradientFun (g z.1) (fun y => f (z.1, y)) z.2)
      (gradientFun (g z.1) (fun y => ψ (z.1, y)) z.2))
  let V : (t : ℝ) → (x : M) → TangentSpace I x :=
    fun t x => gradientFun (g t) (fun y => f (t, y)) x
  have hR (t : ℝ) : (fun x => R (t, x)) =
      fun x => u (t, x) * (deriv (fun s => ψ (s, x)) t +
        mvfderiv I (fun y => ψ (t, y)) x (V t x)) := by
    funext x
    dsimp only [R]
    rw [inner_gradientFun_eq_mvfderiv]
  have hRc (t : ℝ) : HasCompactSupport (fun x => R (t, x)) := by
    rw [hR t]
    exact hasCompactSupport_time_spatial_residual_slice u ψ V hψc t
  have hRs (t : ℝ) : tsupport (fun x => R (t, x)) ⊆ (chartAt H α).source := by
    rw [hR t]
    exact (tsupport_time_spatial_residual_slice_subset u ψ V hψc t).trans hψs
  have hgrad := ae_chartGradientBilin_fderiv_eq_inner_gradientFun_family
    (μ := μ) (ν := modelHaar (E := E))
    (f := fun t x => f (t, x)) (h := fun t x => ψ (t, x)) g α hS hW hWt hf hψ
  filter_upwards [Measure.ae_ae_of_ae_prod hgrad, hi] with t hgt hit ht
  have hzero (y : E) (hy : y ∈ (extChartAt I α).target \ W) :
      chartDensity (g t) α ((extChartAt I α).symm y) *
        R (t, (extChartAt I α).symm y) = 0 := by
    have hn : (t, (extChartAt I α).symm y) ∉ tsupport ψ := by
      intro hz
      apply hy.2
      simpa only [(extChartAt I α).right_inv hy.1] using hψW _ hz
    have hz := time_spatial_residual_eq_zero_of_notMem_tsupport u ψ V hn
    rw [← congrFun (hR t) ((extChartAt I α).symm y)] at hz
    rw [hz, mul_zero]
  have hEq : (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
      R (t, (extChartAt I α).symm y)) =ᵐ[(modelHaar (E := E)).restrict W]
      (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
        (u (t, (extChartAt I α).symm y) *
          (deriv (fun s => ψ (s, (extChartAt I α).symm y)) t +
            chartGradientBilin (g t) α ((extChartAt I α).symm y)
              (fderiv ℝ (fun v : E => f (t, (extChartAt I α).symm v)) y)
              (fderiv ℝ (fun v : E => ψ (t, (extChartAt I α).symm v)) y)))) := by
    filter_upwards [ae_restrict_of_ae hgt, ae_restrict_mem hW.measurableSet]
      with y hy hyW
    dsimp only [R]
    rw [hy ⟨ht, hyW⟩]
  have hIntW : IntegrableOn (fun y => chartDensity (g t) α ((extChartAt I α).symm y) *
      R (t, (extChartAt I α).symm y)) W (modelHaar (E := E)) :=
    (hit ht).congr hEq.symm
  have hIntT := hIntW.of_forall_sdiff_eq_zero
    (measurableSet_extChartAt_target (I := I) α) hzero
  have hLocal : Integrable (fun x => R (t, x)) (chartLocalMeasure (g t) α) := by
    apply (integrable_chartLocalMeasure_iff (g t) α).mpr
    simpa only [IntegrableOn, smul_eq_mul] using hIntT
  have hIntrinsic : Integrable (fun x => R (t, x))
      (riemannianVolumeMeasure (I := I) (M := M) (g t)) :=
    (integrable_riemannianVolumeMeasure_iff_chartLocalMeasure_of_tsupport_subset
      (g t) α (hRc t) (by simpa only [extChartAt_source] using hRs t)).mpr hLocal
  have hcoord := integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    (g t) α (hRc t) (hRs t) hLocal.aestronglyMeasurable
  refine ⟨hIntrinsic, ?_⟩
  calc
    (∫ x, R (t, x) ∂riemannianVolumeMeasure (I := I) (M := M) (g t)) =
        ∫ y in (extChartAt I α).target,
          chartDensity (g t) α ((extChartAt I α).symm y) *
            R (t, (extChartAt I α).symm y) ∂modelHaar := hcoord
    _ = ∫ y in W, chartDensity (g t) α ((extChartAt I α).symm y) *
          R (t, (extChartAt I α).symm y) ∂modelHaar :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        (measurableSet_extChartAt_target (I := I) α) hWt hzero)
    _ = _ := integral_congr_ae hEq

end DifferentialGeometry.Integral.Measure
namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace MeasureTheory
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)
  (hcar : D.carrier = Iic 0) (hreg : D.regular = Iio 0)
  (b : ℝ) (hbmem : b ∈ D.carrier) (tau : ℕ → ℝ) (q : ℕ → F.M)
  (hsigma : ∀ i, 0 < tau i + b)
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

private local instance : TopologicalSpace F.M := F.topology
private local instance : ChartedSpace H F.M := F.charted
private local instance : IsManifold I ∞ F.M := F.smooth
private local instance : SigmaCompactSpace F.M := F.sigmaCompact
private local instance : T2Space F.M := F.t2

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

local notation "U" => poleRescaledFlowSeq F hcar hreg b hbmem tau q hsigma
local notation "Y" => poleEndpointRescaledFlowSeq F hcar hreg b hbmem tau q hsigma

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

namespace HalfLineMetricConvergenceData

private theorem integrable_and_integral_density_subsolution_of_chart_support
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (x : P.M)
    (hlog : ∀ W : Set E, IsOpen W → IsCompact (closure W) →
      closure W ⊆ (extChartAt I x).target →
      ∀ v : ℝ × E → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ v z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * v z +
          B z (d z) (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I x).target)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I x).symm z.2)))
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set P.M))
    (hψnonneg : ∀ z, 0 ≤ ψ z)
    (hψsource : Prod.snd '' tsupport ψ ⊆ (chartAt H x).source) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (Ioc a' c'),
      Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (Ioc a' c')) ∧
    0 ≤ ∫ t, ∫ x, residual t x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)
      ∂volume.restrict (Ioc a' c') := by
  let C : Set P.M := Prod.snd '' tsupport ψ
  have hC : IsCompact C := hψc.image continuous_snd
  have hCs : C ⊆ (extChartAt I x).source := by
    simpa only [extChartAt_source] using hψsource
  obtain ⟨W, hW, hCW, hWclosure, hWcompact, hJ, _, hWJ⟩ :=
    exists_open_extChartAt_image_isCompact_closure x hC hCs
  let J : Set P.M := (extChartAt I x).symm '' closure W
  have hWt : W ⊆ (extChartAt I x).target := subset_closure.trans hWclosure
  let g := fun t : ℝ => co.gInf (1 - t)
  let u : ℝ × P.M → ℝ := fun z => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let f : ℝ × P.M → ℝ := fun z => ell (z.2, z.1)
  let v : ℝ × E → ℝ := fun z =>
    Integral.DivergenceTheorem.chartPullZero (I := I) x (fun y => ψ (z.1, y)) z.2
  let raw : ℝ × E → ℝ := fun z => ψ (z.1, (extChartAt I x).symm z.2)
  let B := fun z : ℝ × E => chartGradientBilin (g z.1) x ((extChartAt I x).symm z.2)
  let d := fun z : ℝ × E =>
    fderiv ℝ (fun y : E => ell ((extChartAt I x).symm y, z.1)) z.2
  let Q : ℝ × E → ℝ := fun z => chartDensity (g z.1) x ((extChartAt I x).symm z.2) *
    (u (z.1, (extChartAt I x).symm z.2) *
      (deriv (fun t => raw (t, z.2)) z.1 +
        B z (d z) (fderiv ℝ (fun y : E => raw (z.1, y)) z.2)))
  let μ : Measure ℝ := volume.restrict (Ioo a' c')
  let ν : Measure E := (modelHaar (E := E)).restrict W
  have hvCompact : HasCompactSupport v :=
    Integral.DivergenceTheorem.hasCompactSupport_chartPullZero_prod x hψc hψsource
  have hvSupport : tsupport v ⊆ Ioo a' c' ×ˢ W := by
    intro z hz
    obtain ⟨z', hz', rfl⟩ :=
      Integral.DivergenceTheorem.tsupport_chartPullZero_prod_subset_image x hψc hψsource hz
    exact ⟨(hψsupp hz').1, hCW ⟨z'.2, ⟨z', hz', rfl⟩, rfl⟩⟩
  have hvNonneg : ∀ z, 0 ≤ v z := by
    intro z
    by_cases hz : z.2 ∈ (extChartAt I x).target
    · simpa only [v, Integral.DivergenceTheorem.chartPullZero_mem x _ hz,
        Tensor.Coordinates.scalarOnE_def] using hψnonneg (z.1, (extChartAt I x).symm z.2)
    · simp only [v, Integral.DivergenceTheorem.chartPullZero_nmem x _ hz, le_refl]
  let Ω : Set (ℝ × E) := Ioo a c ×ˢ (extChartAt I x).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (isOpen_extChartAt_target (I := I) x)
  have hvLocal : LocallyLipschitzOn Ω v := by
    intro z hz
    obtain ⟨K, V, hV, hLip⟩ := hψ hz
    refine ⟨K, V ∩ Ω, inter_mem hV self_mem_nhdsWithin, ?_⟩
    intro z₁ hz₁ z₂ hz₂
    dsimp only [v]
    rw [Integral.DivergenceTheorem.chartPullZero_mem x _ hz₁.2.2,
      Integral.DivergenceTheorem.chartPullZero_mem x _ hz₂.2.2]
    exact hLip hz₁.1 hz₂.1
  have hvAmbient : tsupport v ⊆ Ω := by
    intro z hz
    have hz' := hvSupport hz
    exact ⟨⟨haa.trans hz'.1.1, hz'.1.2.trans hcc⟩, hWt hz'.2⟩
  have hvLip : LocallyLipschitz v :=
    hvLocal.locallyLipschitz_of_tsupport_subset hΩ hvAmbient
  have hrawLip : LocallyLipschitzOn (Ioo a' c' ×ˢ W) raw :=
    hψ.mono (fun _ hz =>
      ⟨⟨haa.trans hz.1.1, hz.1.2.trans hcc⟩, hWt hz.2⟩)
  have hconvJ : ∀ y ∈ J, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))) :=
    fun y _ t ht => hconv y t ht
  have hlimitLip : LocallyLipschitzOn (Ioo a' c' ×ˢ W)
      (fun z : ℝ × E => f (z.1, (extChartAt I x).symm z.2)) :=
    (locallyLipschitzOn_poleEndpoint_redLength_limit_time_chart
      F hcar hreg b hbmem tau q hsigma Phi R hR co kappa hF p hJ ha.le hbase
      rho hrho ell hconvJ x hWt hWJ).mono
        (fun _ hz => ⟨⟨(haa.trans hz.1.1).le, (hz.1.2.trans hcc).le⟩, hz.2⟩)
  obtain ⟨hvInt, hvNonnegative⟩ :=
    integrable_and_integral_poleEndpoint_redDensity_limit_subsolution_of_logarithmic_inequality
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
      hcomplete hboundary kappa hF p hJ ha hbase rho hrho ell hconvJ
      x hW hWt hWJ (hlog W hW hWcompact hWclosure) haa hac hcc v
      hvLip.locallyLipschitzOn hvCompact hvSupport hvNonneg
  have htime (y : E) (hy : y ∈ W) :
      (fun t => v (t, y)) = fun t => raw (t, y) := by
    funext t
    exact Integral.DivergenceTheorem.chartPullZero_mem x _ (hWt hy)
  have hspace (t : ℝ) (y : E) (hy : y ∈ W) :
      fderiv ℝ (fun z : E => v (t, z)) y =
        fderiv ℝ (fun z : E => raw (t, z)) y := by
    have hEq : (fun z : E => v (t, z)) =ᶠ[𝓝 y] fun z : E => raw (t, z) := by
      filter_upwards [(isOpen_extChartAt_target (I := I) x).mem_nhds (hWt hy)] with z hz
      exact Integral.DivergenceTheorem.chartPullZero_mem x _ hz
    exact hEq.fderiv_eq
  have hEq : (fun z : ℝ × E => chartDensity (g z.1) x ((extChartAt I x).symm z.2) *
      u (z.1, (extChartAt I x).symm z.2) *
      (deriv (fun t => v (t, z.2)) z.1 +
        B z (d z) (fderiv ℝ (fun y : E => v (z.1, y)) z.2))) =ᵐ[
          (volume.restrict (Ioc a' c')).prod ν] Q := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod hW.measurableSet)] with z hz
    dsimp only [Q]
    rw [htime z.2 hz.2, hspace z.1 z.2 hz.2, mul_assoc]
  have hQInt : Integrable Q ((volume.restrict (Ioc a' c')).prod ν) := hvInt.congr hEq
  have hQNonnegative : 0 ≤ ∫ z, Q z ∂(volume.restrict (Ioc a' c')).prod ν := by
    rw [← integral_congr_ae hEq]
    exact hvNonnegative
  have hQIntOpen : Integrable Q (μ.prod ν) := by
    simpa only [μ, restrict_Ioo_eq_restrict_Ioc] using hQInt
  have hQNonnegativeOpen : 0 ≤ ∫ z, Q z ∂μ.prod ν := by
    simpa only [μ, restrict_Ioo_eq_restrict_Ioc] using hQNonnegative
  have hslice : ∀ᵐ t ∂volume, t ∈ Ioo a' c' → Integrable (fun y => Q (t, y)) ν :=
    (ae_restrict_iff' measurableSet_Ioo).mp hQIntOpen.prod_right_ae
  have hψW : ∀ z ∈ tsupport ψ, extChartAt I x z.2 ∈ W := by
    intro z hz
    exact hCW ⟨z.2, ⟨z, hz, rfl⟩, rfl⟩
  have htransport :=
    Integral.Measure.ae_integrable_and_integral_time_gradient_residual_eq_chartDensity
      (μ := volume) g x u f ψ isOpen_Ioo hW hWt hψc hψsource hψW
      hlimitLip hrawLip hslice
  let intrinsic := fun (t : ℝ) (y : P.M) => u (t, y) *
    (deriv (fun s => ψ (s, y)) t +
      (g t).inner y (gradientFun (g t) (fun z => f (t, z)) y)
        (gradientFun (g t) (fun z => ψ (t, z)) y))
  have htransportOpen : ∀ᵐ t ∂μ,
      Integrable (intrinsic t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) ∧
        (∫ y, intrinsic t y ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) =
          ∫ y, Q (t, y) ∂ν :=
    (ae_restrict_iff' measurableSet_Ioo).mpr htransport
  have hspatial : ∀ᵐ t ∂μ, Integrable (intrinsic t)
      (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) :=
    htransportOpen.mono fun _ h => h.1
  have hintegral : (fun t => ∫ y, intrinsic t y
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) =ᵐ[μ]
      (fun t => ∫ y, Q (t, y) ∂ν) := htransportOpen.mono fun _ h => h.2
  have houter : Integrable
      (fun t => ∫ y, intrinsic t y
        ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)) μ :=
    hQIntOpen.integral_prod_left.congr hintegral.symm
  have hnonnegative : 0 ≤ ∫ t, ∫ y, intrinsic t y
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t) ∂μ := by
    rw [integral_congr_ae hintegral, ← integral_prod Q hQIntOpen]
    exact hQNonnegativeOpen
  simpa only [μ, restrict_Ioo_eq_restrict_Ioc] using
    And.intro hspatial (And.intro houter hnonnegative)

theorem integral_poleEndpoint_redDensity_limit_subsolution_of_chart_logarithmic_inequality
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hlog : ∀ (x : P.M) (W : Set E), IsOpen W → IsCompact (closure W) →
      closure W ⊆ (extChartAt I x).target →
      ∀ v : ℝ × E → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ v z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * v z +
          B z (d z) (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ∀ x : P.M, LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I x).target)
      (fun z : ℝ × E => ψ (z.1, (extChartAt I x).symm z.2)))
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set P.M))
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (Ioc a' c'),
      Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (Ioc a' c')) ∧
    0 ≤ ∫ t, ∫ x, residual t x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)
      ∂volume.restrict (Ioc a' c') := by
  classical
  let g := fun t : ℝ => co.gInf (1 - t)
  let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
    (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
  let V : (t : ℝ) → (x : P.M) → TangentSpace I x :=
    fun t x => gradientFun (g t) (fun y => ell (y, t)) x
  let Aop : ∀ z : ℝ × P.M, (TangentSpace I z.2 →L[ℝ] ℝ) →L[ℝ] ℝ :=
    fun z => density z • ContinuousLinearMap.apply ℝ ℝ (V z.1 z.2)
  let L := fun (v : ℝ × P.M → ℝ) (t : ℝ) (x : P.M) =>
    density (t, x) * deriv (fun r => v (r, x)) t +
      Aop (t, x) (mvfderiv I (fun y => v (t, y)) x)
  let μ : Measure ℝ := volume.restrict (Ioc a' c')
  let ν := fun t => Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)
  let ρ := chartAtlasPOU I P.M
  let K := Prod.snd '' tsupport ψ
  have hK : IsCompact K := hψc.image continuous_snd
  have hψK : ∀ t, Function.support (fun x => ψ (t, x)) ⊆ K := by
    intro t x hx
    exact ⟨(t, x), subset_tsupport ψ hx, rfl⟩
  have hρ : ρ.IsSubordinate (fun i : P.M => (chartAt H i).source) :=
    chartAtlasPOU_isSubordinate I P.M
  let v := fun (i : P.M) (z : ℝ × P.M) => ρ i z.2 * ψ z
  have hvc (i : P.M) : HasCompactSupport (v i) := hψc.mul_left
  have hvs (i : P.M) : tsupport (v i) ⊆ tsupport ψ := tsupport_mul_subset_right
  have hvsource (i : P.M) : Prod.snd '' tsupport (v i) ⊆ (chartAt H i).source := by
    rintro x ⟨z, hz, rfl⟩
    apply hρ i
    exact tsupport_comp_subset_preimage (f := Prod.snd) (ρ i) continuous_snd
      (tsupport_mul_subset_left hz)
  have hv (i : P.M) : LocallyLipschitzOn (Ioo a c ×ˢ (extChartAt I i).target)
      (fun z : ℝ × E => v i (z.1, (extChartAt I i).symm z.2)) :=
    Geometry.Measure.locallyLipschitzOn_chart_mul i (ρ i).contMDiff (hψ i)
  have hvnonneg (i : P.M) (z : ℝ × P.M) : 0 ≤ v i z :=
    mul_nonneg (ρ.nonneg i z.2) (hψnonneg z)
  have hlocal (i : P.M) :
      (∀ᵐ t ∂μ, Integrable (L (v i) t) (ν t)) ∧
      Integrable (fun t => ∫ x, L (v i) t x ∂ν t) μ ∧
      0 ≤ ∫ t, ∫ x, L (v i) t x ∂ν t ∂μ := by
    have h := integrable_and_integral_density_subsolution_of_chart_support
      F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co
      hcomplete hboundary kappa hF p ha hbase rho hrho ell hconv i (hlog i)
      haa hac hcc (v i) (hv i) (hvc i) ((hvs i).trans hψsupp) (hvnonneg i)
      (hvsource i)
    simpa only [inner_gradientFun_eq_mvfderiv, L, Aop, V, g, density, μ, ν,
      smul_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using h
  have hLm (i : P.M) (t : ℝ) : HasCompactSupport (L (v i) t) := by
    have h := hasCompactSupport_time_spatial_residual_slice density (v i) V (hvc i) t
    simpa only [L, Aop, smul_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using h
  have hLs (i : P.M) (t : ℝ) : tsupport (L (v i) t) ⊆ (chartAt H i).source := by
    have h := (tsupport_time_spatial_residual_slice_subset density (v i) V (hvc i) t).trans
      (hvsource i)
    simpa only [L, Aop, smul_apply,
      ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using h
  let C := fun (i : P.M) (t : ℝ) (y : E) =>
    chartDensity (g t) i ((extChartAt I i).symm y) *
      L (v i) t ((extChartAt I i).symm y)
  have hCi (i : P.M) : ∀ᵐ t ∂μ,
      Integrable (C i t) ((modelHaar (E := E)).restrict (extChartAt I i).target) := by
    filter_upwards [(hlocal i).1] with t ht
    have h := (integrable_riemannianVolumeMeasure_iff_chartDensity_of_tsupport_subset
      (g t) i (hLm i t) (by simpa only [extChartAt_source] using hLs i t)).mp ht
    simpa only [smul_eq_mul] using h
  have hCe (i : P.M) : (fun t => ∫ x, L (v i) t x ∂ν t) =ᵐ[μ]
      (fun t => ∫ y in (extChartAt I i).target, C i t y ∂(modelHaar (E := E))) := by
    filter_upwards [hCi i] with t ht
    have hm := (integrable_chartLocalMeasure_iff (g t) i (f := L (v i) t)).mpr
      (by simpa only [smul_eq_mul, C] using ht)
    exact integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
      (g t) i (hLm i t) (hLs i t) hm.aestronglyMeasurable
  have hCfinite : ∀ᵐ t ∂μ, ∀ i ∈ ρ.toPartitionOfUnity.fintsupportOn K hK,
      Integrable (C i t) ((modelHaar (E := E)).restrict (extChartAt I i).target) := by
    exact (Filter.eventually_all_finset _).2 (fun i _ => hCi i)
  have htest : ∀ᵐ t ∂μ, ∀ᵐ x ∂ν t,
      MDifferentiableAt I 𝓘(ℝ) (fun y => ψ (t, y)) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Geometry.Measure.ae_mdifferentiableAt_slice_of_chart_locallyLipschitzOn
      g hψ ⟨haa.trans ht.1, ht.2.trans_lt hcc⟩
  have hout := Analysis.integrable_and_integral_parabolic_residual_nonneg_of_chart_integrals
    ρ hρ g μ hK hψK htest density Aop hCfinite
    (fun i _ => (hlocal i).2.1.congr (hCe i))
    (fun i _ => by rw [← integral_congr_ae (hCe i)]; exact (hlocal i).2.2)
  simpa only [inner_gradientFun_eq_mvfderiv, L, Aop, V, g, density, μ, ν,
    smul_apply, ContinuousLinearMap.apply_apply, smul_eq_mul, mul_add] using hout

theorem
    integral_poleEndpoint_redDensity_limit_subsolution_of_chart_logarithmic_inequality_of_contMDiff
    [ConnectedSpace P.M]
    (Phi : PointedCGHMaps Y P phi)
    (R : SmoothRiemannianMetric I P.M) (hR : RiemannianMetricComplete R)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcomplete : MetricComplete
      ({ P with metric := co.gInf 0 } : PointedRiemannianManifold I))
    (hboundary : BoundarylessManifold I P.M)
    (kappa : ℕ → ℝ) (hF : ∀ i, IsAncientKappaSolution (kappa i) ((U).term i))
    (p : F.M) {a c A : ℝ}
    (ha : 1 < a)
    (hbase : ∀ᶠ k in atTop, redLength ((U).term (phi (co.φ k))).S 0
      p (q (phi (co.φ k))) 1 ≤ A)
    (rho : ℕ → ℕ) (hrho : Tendsto rho atTop atTop)
    (ell : P.M × ℝ → ℝ)
    (hconv : ∀ y : P.M, ∀ t ∈ Icc a c,
      Tendsto (fun k => redLength ((U).term (phi (co.φ (rho k)))).S 0 p
        (Phi.map (co.φ (rho k)) y) t) atTop (𝓝 (ell (y, t))))
    (hlog : ∀ (x : P.M) (W : Set E), IsOpen W → IsCompact (closure W) →
      closure W ⊆ (extChartAt I x).target →
      ∀ v : ℝ × E → ℝ, ContDiff ℝ ∞ v → HasCompactSupport v →
        tsupport v ⊆ Ioo a c ×ˢ W → (∀ z, 0 ≤ v z) →
      let f := fun z : ℝ × E => ell ((extChartAt I x).symm z.2, z.1)
      let d := fun z => fderiv ℝ (fun y : E => f (z.1, y)) z.2
      let B := fun z => chartGradientBilin (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let ρ := fun z => chartDensity (co.gInf (1 - z.1)) x
        ((extChartAt I x).symm z.2)
      let S := fun z => metricScalarAt (co.gInf (1 - z.1)) ((extChartAt I x).symm z.2)
      0 ≤ ∫ z, ρ z *
        (((1 / 2 : ℝ) * B z (d z) (d z) - (1 / 2 : ℝ) * S z +
            ((Module.finrank ℝ E : ℝ) - f z) / (2 * z.1)) * v z +
          B z (d z) (fderiv ℝ (fun y => v (z.1, y)) z.2))
        ∂(volume : Measure ℝ).prod (modelHaar (E := E)))
    {a' c' : ℝ} (haa : a < a') (hac : a' ≤ c') (hcc : c' < c)
    (ψ : ℝ × P.M → ℝ)
    (hψ : ContMDiff ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) 1 ψ)
    (hψc : HasCompactSupport ψ)
    (hψsupp : tsupport ψ ⊆ Ioo a' c' ×ˢ (univ : Set P.M))
    (hψnonneg : ∀ z, 0 ≤ ψ z) :
    let g := fun t : ℝ => co.gInf (1 - t)
    let density := fun z : ℝ × P.M => Real.exp (-ell (z.2, z.1) -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log z.1 -
      (Module.finrank ℝ E : ℝ) / 2 * Real.log (4 * Real.pi))
    let residual := fun (t : ℝ) (x : P.M) => density (t, x) *
      (deriv (fun s => ψ (s, x)) t +
        (g t).inner x (gradientFun (g t) (fun y => ell (y, t)) x)
          (gradientFun (g t) (fun y => ψ (t, y)) x))
    (∀ᵐ t ∂volume.restrict (Ioc a' c'),
      Integrable (residual t)
        (Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))) ∧
    Integrable (fun t => ∫ x, residual t x
      ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t))
      (volume.restrict (Ioc a' c')) ∧
    0 ≤ ∫ t, ∫ x, residual t x ∂Integral.Measure.riemannianVolumeMeasure (I := I) (M := P.M) (g t)
      ∂volume.restrict (Ioc a' c') := by
  exact integral_poleEndpoint_redDensity_limit_subsolution_of_chart_logarithmic_inequality
    F hcar hreg b hbmem tau q hsigma Phi R hR bf hsrc htgt co hcomplete hboundary
    kappa hF p ha hbase rho hrho ell hconv hlog haa hac hcc ψ
    (fun x => Geometry.Measure.locallyLipschitzOn_chart_prod_of_contMDiff
      (S := Ioo a c) x hψ) hψc hψsupp hψnonneg

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
