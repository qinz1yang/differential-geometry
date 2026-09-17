import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Connection
import DifferentialGeometry.Analysis.Spectral.Tensor.ChartTensor.Inner.LowerAllUpperIndices
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.ManifoldSmoothness
import DifferentialGeometry.Geometry.Geodesic.Equation.Basic
import DifferentialGeometry.Analysis.Calculus.TimeJet.Evolution
import DifferentialGeometry.Analysis.Calculus.TimeJet.SliceBootstrap
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.MFDerivAlongCurve
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local

noncomputable section

open Manifold
open scoped ContDiff
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem curvatureVector_eq_speed_inv_sq_Dx_sub_tangent
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) (x t : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x) :
    c.curvatureVector g x t =
      (c.speed g x t) ^ (-2 : ℤ) • c.Dx g c.X x t -
        ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
          c.speed g x t ^ 4) • c.X x t := by
  by_cases hx : c.X (I := I) x t = 0
  · have hs0 : c.speed g x t = 0 := by simp [speed, hx]
    simp [curvatureVector, Ds, hs0, hx]
  · have hi : c.X (I := I) x t ≠ 0 := hx
    have hpos : 0 < (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
      (g t).pos _ _ hi
    have hspos : 0 < c.speed g x t := Real.sqrt_pos.mpr hpos
    have hne : c.speed g x t ≠ 0 := hspos.ne'
    have hrep : DifferentiableAt ℝ
        (chartRepAt (I := I) (fun y => c.lift y t) (fun y => c.X y t) x) x := by
      simpa only [X] using differentiableAt_chartRepAt_curveVelocity hc
    have hpair := DifferentialGeometry.Geometry.Riemannian.Variation.inner_deriv_at
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2) (g t) (fun y => c.lift y t)
      (fun y => c.X y t) (fun y => c.X y t) x hc hrep hrep
    have hF : HasDerivAt (fun y => (g t).inner (c.lift y t) (c.X y t) (c.X y t))
        (2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) x := by
      convert hpair using 1
      change 2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) =
        (g t).inner (c.lift x t) (c.Dx g c.X x t) (c.X x t) +
          (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)
      rw [(g t).symm (c.lift x t) (c.Dx g c.X x t) (c.X x t)]
      ring
    have hs : HasDerivAt (fun y => c.speed g y t)
        ((2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t)) /
          (2 * c.speed g x t)) x := by
      simpa only [speed] using hF.sqrt hpos.ne'
    have hinv : HasDerivAt (fun y => (c.speed g y t)⁻¹)
        (-(2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
          (2 * c.speed g x t)) / c.speed g x t ^ 2) x := hs.inv hne
    have hsmul := covDerivAlong_smulFun (g t) (fun y => c.lift y t)
      (fun y => (c.speed g y t)⁻¹) (fun y => c.X y t) x hinv.differentiableAt hrep
    change (c.speed g x t)⁻¹ • covDerivAlong (g t) (fun y => c.lift y t)
      (fun y => (c.speed g y t)⁻¹ • c.X y t) x = _
    rw [hsmul, hinv.deriv, smul_add, smul_smul, smul_smul]
    have hcoef : (c.speed g x t)⁻¹ *
        (-(2 * (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
          (2 * c.speed g x t)) / c.speed g x t ^ 2) =
        -((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
          c.speed g x t ^ 4) := by
      field_simp
    have hz : c.speed g x t ^ (-2 : ℤ) =
        (c.speed g x t)⁻¹ * (c.speed g x t)⁻¹ := by
      rw [zpow_neg, zpow_ofNat, pow_two, mul_inv]
    rw [hcoef, hz, neg_smul]
    change -(((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
        c.speed g x t ^ 4) • c.X x t) +
      ((c.speed g x t)⁻¹ * (c.speed g x t)⁻¹) • c.Dx g c.X x t = _
    abel

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
namespace CurveMap

theorem trivToE_Dx_X_eq_chart (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (β : M) (x t : ℝ) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x)
    (hchart : c.lift x t ∈ (extChartAt I β).source) :
    let u := fun y => extChartAt I β (c.lift y t)
    trivToE I β (c.lift x t) (c.Dx g c.X x t) =
      deriv (deriv u) x + chartChristoffelContraction (I := I) (g t) β
        (deriv u x) (deriv u x) (u x) := by
  let u := fun y => extChartAt I β (c.lift y t)
  have hgood : c.lift x t ∈ chartLeviCivitaGoodSet (I := I) β :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) β (c.lift x t)).mpr hchart
  have hnear : ∀ᶠ y in 𝓝 x, ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) y :=
    (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by decide)).mp hγ
  have hsrc := chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood
  have hchart : ∀ᶠ y in 𝓝 x, c.lift y t ∈ (chartAt H β).source :=
    hγ.continuousAt.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds hsrc)
  have hrep : (fun y => trivToE I β (c.lift y t) (c.X y t)) =ᶠ[𝓝 x] deriv u := by
    filter_upwards [hnear, hchart] with y hy hc
    exact chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (hy.mdifferentiableAt (by norm_num)) β hc
  have hv : MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E))
      (fun y : ℝ => (⟨c.lift y t, c.X y t⟩ : TotalSpace E (TangentSpace I))) univ x := by
    exact ((hγ.velocityLift (m := 1) (by norm_num)).mdifferentiableAt one_ne_zero).mdifferentiableWithinAt
  have hacc := trivToE_Dx_eq_chart g c c.X β x t hgood
    (hγ.mdifferentiableAt (by norm_num)) hv
  change trivToE I β (c.lift x t) (c.Dx g c.X x t) = _
  rw [hacc, hrep.deriv_eq, hrep.eq_of_nhds]
  rfl

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem chartGramBilin_trivToE
    (g : SmoothRiemannianMetric I M) (β b : M)
    (hb : b ∈ (trivializationAt E (TangentSpace I) β).baseSet)
    (V W : TangentSpace I b) :
    Analysis.Parabolic.TensorSpectral.chartGramBilin g β b
      (trivToE I β b V) (trivToE I β b W) = g.inner b V W := by
  have hV := (trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
    (R := ℝ) hb V
  have hW := (trivializationAt E (TangentSpace I) β).symmL_continuousLinearMapAt
    (R := ℝ) hb W
  rw [Analysis.Parabolic.TensorSpectral.chartGramBilin_apply]
  change (∑ i, ∑ j, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g β b i j *
    chartCoord (E := E) i (trivToE I β b V) * chartCoord (E := E) j (trivToE I β b W)) = _
  rw [← inner_eq_chartGramOnE_bilinear_on_baseSet g β (trivToE I β b V) (trivToE I β b W)]
  exact congrArg₂ (fun v w => g.inner b v w) hV hW


namespace CurveMap
variable [I.Boundaryless] [T2Space M]

theorem trivToE_curvatureVector_eq_chart
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M)
    (β : M) (x t : ℝ) (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x)
    (hchart : c.lift x t ∈ (extChartAt I β).source) :
    let u := fun y => extChartAt I β (c.lift y t)
    let p := deriv u x
    let G := Analysis.Parabolic.TensorSpectral.chartGramBilin (g t) β
      ((extChartAt I β).symm (u x))
    let σ := G p p
    let A := deriv (deriv u) x + chartChristoffelContraction (I := I) (g t) β p p (u x)
    trivToE I β (c.lift x t) (c.curvatureVector g x t) =
      σ⁻¹ • A - ((σ ^ 2)⁻¹ * G A p) • p := by
  let u := fun y => extChartAt I β (c.lift y t)
  let p := deriv u x
  let G := Analysis.Parabolic.TensorSpectral.chartGramBilin (g t) β
    ((extChartAt I β).symm (u x))
  let σ := G p p
  let A := deriv (deriv u) x + chartChristoffelContraction (I := I) (g t) β p p (u x)
  have hgood : c.lift x t ∈ chartLeviCivitaGoodSet (I := I) β :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) β (c.lift x t)).mpr hchart
  have hsrc : c.lift x t ∈ (extChartAt I β).source := hchart
  have hb := chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood
  have hp : trivToE I β (c.lift x t) (c.X x t) = p :=
    chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
      (hc.mdifferentiableAt (by norm_num)) β
      (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood)
  have hA : trivToE I β (c.lift x t) (c.Dx g c.X x t) = A :=
    trivToE_Dx_X_eq_chart g c β x t hc hchart
  have hG (V W : TangentSpace I (c.lift x t)) :
      G (trivToE I β (c.lift x t) V) (trivToE I β (c.lift x t) W) =
        (g t).inner (c.lift x t) V W := by
    dsimp only [G, u]
    rw [(extChartAt I β).left_inv hsrc]
    exact chartGramBilin_trivToE (g t) β (c.lift x t) hb V W
  have hσ : σ = c.speed g x t ^ 2 := by
    dsimp [σ]
    rw [← hp, hG]
    exact (Real.sq_sqrt (metric_inner_self_nonneg (g t) (c.lift x t) (c.X x t))).symm
  have hpair : G A p = (g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) := by
    rw [← hA, ← hp, hG]
    exact (g t).symm _ _ _
  have hz : c.speed g x t ^ (-2 : ℤ) = σ⁻¹ := by
    rw [hσ, zpow_neg, zpow_ofNat]
  have hscalar : ((g t).inner (c.lift x t) (c.X x t) (c.Dx g c.X x t) /
      c.speed g x t ^ 4) = (σ ^ 2)⁻¹ * G A p := by
    rw [hσ, hpair]
    rw [show (c.speed g x t ^ 2) ^ 2 = c.speed g x t ^ 4 by ring, div_eq_mul_inv, mul_comm]
  change trivToE I β (c.lift x t) (c.curvatureVector g x t) =
    σ⁻¹ • A - ((σ ^ 2)⁻¹ * G A p) • p
  rw [curvatureVector_eq_speed_inv_sq_Dx_sub_tangent g c x t hc]
  rw [map_sub, map_smul, map_smul, hA, hp, hz, hscalar]

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem contDiffAt_chartGramBilin
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) {t : ℝ} {z : E}
    (ht : t ∈ D.regular) (hz : z ∈ interior (extChartAt I β).target) :
    ContDiffAt ℝ ∞
      (fun q : ℝ × E => chartGramBilin (g q.1) β ((extChartAt I β).symm q.2)) (t, z) := by
  classical
  change ContDiffAt ℝ ∞
    (fun q : ℝ × E => ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
      chartGramOnE (g q.1) β i j q.2 •
        (chartCoordCLM E i).smulRight (chartCoordCLM E j)) (t, z)
  exact ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((hg.chartGramFamilyJointSmoothOn g β) i j ht hz).smul_const _

private theorem contDiffAt_chartChristoffelContraction
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) {q : ℝ × E × E × E}
    (ht : q.1 ∈ D.regular) (hz : q.2.1 ∈ interior (extChartAt I β).target) :
    ContDiffAt ℝ ∞
      (fun q : ℝ × E × E × E =>
        chartChristoffelContraction (g q.1) β q.2.2.1 q.2.2.2 q.2.1) q := by
  classical
  have htz : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => (q.1, q.2.1)) q :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp _ contDiffAt_snd)
  have hv : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => q.2.2.1) q :=
    contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  have hw : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => q.2.2.2) q :=
    contDiffAt_snd.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  have hcoords (i : Fin (Module.finrank ℝ E)) :
      ContDiff ℝ ∞ (chartCoord (E := E) i) := (chartCoordCLM E i).contDiff
  have hcoeff (i j k : Fin (Module.finrank ℝ E)) : ContDiffAt ℝ ∞
      (fun q : ℝ × E × E × E => chartChristoffel (g q.1) β i j k q.2.1) q := by
    exact ContDiffAt.comp
      (g := fun p : ℝ × E => chartChristoffel (g p.1) β i j k p.2)
      (f := fun p : ℝ × E × E × E => (p.1, p.2.1)) q
      (chartChristoffel_joint_contDiffAt g β (hg.chartGramFamilyJointSmoothOn g β) i j k ht hz)
      htz
  change ContDiffAt ℝ ∞
    (fun q : ℝ × E × E × E => ∑ k : Fin (Module.finrank ℝ E),
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartChristoffel (g q.1) β i j k q.2.1 * chartCoord (E := E) i q.2.2.1 *
          chartCoord (E := E) j q.2.2.2) •
            DifferentialGeometry.Tensor.Coordinates.chartModelBasis E k) q
  exact ContDiffAt.sum fun k _ => (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((hcoeff i j k).mul ((hcoords i).contDiffAt.comp q hv)).mul
      ((hcoords j).contDiffAt.comp q hw)).smul_const _

def curveShorteningChartRhs (g : ℝ → SmoothRiemannianMetric I M) (β : M)
    (q : ℝ × E × E × E) : E :=
  let G := chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1)
  let σ := G q.2.2.1 q.2.2.1
  let A := q.2.2.2 + chartChristoffelContraction (g q.1) β q.2.2.1 q.2.2.1 q.2.1
  σ⁻¹ • A - (σ⁻¹ ^ 2 * G A q.2.2.1) • q.2.2.1

def curveShorteningChartDomain (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) : Set (ℝ × E × E × E) :=
  {q | q.1 ∈ D.regular ∧ q.2.1 ∈ interior (extChartAt I β).target ∧
    0 < chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1) q.2.2.1 q.2.2.1}

private theorem contDiffAt_chartGramBilin_eval
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) {q : ℝ × E × E × E}
    (ht : q.1 ∈ D.regular) (hz : q.2.1 ∈ interior (extChartAt I β).target) :
    ContDiffAt ℝ ∞
      (fun q : ℝ × E × E × E =>
        chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1) q.2.2.1 q.2.2.1) q := by
  have hG := (contDiffAt_chartGramBilin hg β ht hz).comp q
    (contDiffAt_fst.prodMk (contDiffAt_fst.comp _ contDiffAt_snd))
  have hp : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => q.2.2.1) q :=
    contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  exact (hG.clm_apply hp).clm_apply hp

theorem isOpen_curveShorteningChartDomain
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    IsOpen (curveShorteningChartDomain D g β) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have hσ := (contDiffAt_chartGramBilin_eval hg β hq.1 hq.2.1).continuousAt
  have ht := (D.regular_isOpen.preimage continuous_fst).mem_nhds hq.1
  have hz := (isOpen_interior.preimage (continuous_fst.comp continuous_snd)).mem_nhds hq.2.1
  have hp := hσ.preimage_mem_nhds (isOpen_Ioi.mem_nhds hq.2.2)
  exact Filter.mem_of_superset (Filter.inter_mem ht (Filter.inter_mem hz hp))
    (fun _ h => h)

theorem contDiffOn_curveShorteningChartRhs
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    ContDiffOn ℝ ∞ (curveShorteningChartRhs g β) (curveShorteningChartDomain D g β) := by
  intro q hq
  have htz : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => (q.1, q.2.1)) q :=
    contDiffAt_fst.prodMk (contDiffAt_fst.comp _ contDiffAt_snd)
  have hp : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => q.2.2.1) q :=
    contDiffAt_fst.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  have hr : ContDiffAt ℝ ∞ (fun q : ℝ × E × E × E => q.2.2.2) q :=
    contDiffAt_snd.comp _ (contDiffAt_snd.comp _ contDiffAt_snd)
  have hG := (contDiffAt_chartGramBilin hg β hq.1 hq.2.1).comp q htz
  have hσ := (contDiffAt_chartGramBilin_eval hg β hq.1 hq.2.1).inv (ne_of_gt hq.2.2)
  have hΓ := (contDiffAt_chartChristoffelContraction hg β
    (q := (q.1, q.2.1, q.2.2.1, q.2.2.1)) hq.1 hq.2.1).comp q
      (contDiffAt_fst.prodMk ((contDiffAt_fst.comp _ contDiffAt_snd).prodMk (hp.prodMk hp)))
  have hA := hr.add hΓ
  exact ((hσ.smul hA).sub (((hσ.pow 2).mul ((hG.clm_apply hA).clm_apply hp)).smul hp)).contDiffWithinAt


def curveShorteningChartRhsJet (g : ℝ → SmoothRiemannianMetric I M) (β : M)
    (p : (ℝ × ℝ) × E × (ℝ →L[ℝ] E) × (ℝ →L[ℝ] (ℝ →L[ℝ] E))) : E :=
  curveShorteningChartRhs g β (p.1.1, p.2.1, p.2.2.1 1, p.2.2.2 1 1)

def curveShorteningChartDomainJet (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) :
    Set ((ℝ × ℝ) × E × (ℝ →L[ℝ] E) × (ℝ →L[ℝ] (ℝ →L[ℝ] E))) :=
  {p | (p.1.1, p.2.1, p.2.2.1 1, p.2.2.2 1 1) ∈ curveShorteningChartDomain D g β}

omit [FiniteDimensional ℝ E] in
private theorem jet2_adapter_smooth : ContDiff ℝ ∞
    (fun p : ((ℝ × ℝ) × E × (ℝ →L[ℝ] E) × (ℝ →L[ℝ] (ℝ →L[ℝ] E))) =>
      (p.1.1, p.2.1, p.2.2.1 1, p.2.2.2 1 1)) := by
  fun_prop

theorem isOpen_curveShorteningChartDomainJet
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    IsOpen (curveShorteningChartDomainJet D g β) := by
  rw [curveShorteningChartDomainJet]
  apply (isOpen_curveShorteningChartDomain hg β).preimage
  exact jet2_adapter_smooth.continuous

theorem contDiffOn_curveShorteningChartRhsJet
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    ContDiffOn ℝ ∞ (curveShorteningChartRhsJet g β)
      (curveShorteningChartDomainJet D g β) := by
  exact ContDiffOn.comp
    (g := curveShorteningChartRhs g β)
    (f := fun p : (ℝ × ℝ) × E × (ℝ →L[ℝ] E) × (ℝ →L[ℝ] (ℝ →L[ℝ] E)) =>
      (p.1.1, p.2.1, p.2.2.1 1, p.2.2.2 1 1))
    (contDiffOn_curveShorteningChartRhs hg β)
    jet2_adapter_smooth.contDiffOn (fun _ h => h)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem IsSolutionOn.hasDerivWithinAt_chart
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (hc : c.IsSolutionOn g J) (β : M) (x t : ℝ) (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) (hchart : c.lift x t ∈ (extChartAt I β).source) :
    let u := fun y => extChartAt I β (c.lift y t)
    let p := deriv u x
    let G := Analysis.Parabolic.TensorSpectral.chartGramBilin (g t) β
      ((extChartAt I β).symm (u x))
    let σ := G p p
    let A := deriv (deriv u) x + chartChristoffelContraction (I := I) (g t) β p p (u x)
    HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
      (σ⁻¹ • A - ((σ ^ 2)⁻¹ * G A p) • p) J t := by
  have htime := (c.time_slice_contMDiffWithinAt J hc.smooth x t ht).mdifferentiableWithinAt
    (by simp)
  have hsrc : c.lift x t ∈ (chartAt H β).source := by
    rwa [extChartAt_source] at hchart
  have hcoord : DifferentiableWithinAt ℝ (fun τ => extChartAt I β (c.lift x τ)) J t :=
    mdifferentiableWithinAt_iff_differentiableWithinAt.mp
      ((mdifferentiableAt_extChartAt (I := I) hsrc).comp_mdifferentiableWithinAt t htime)
  have hbridge := chartCoord_mfderivWithin_along_curve_eq_fderivWithin
    htime htime.continuousWithinAt hJ.uniqueMDiffWithinAt hsrc
  have hslice : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x :=
    ((c.space_slice_contMDiffWithinAt J hc.smooth x t ht).contMDiffAt
      (univ_mem : (univ : Set ℝ) ∈ 𝓝 x)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hcurv := trivToE_curvatureVector_eq_chart g c β x t hslice hchart
  have hvel : derivWithin (fun τ => extChartAt I β (c.lift x τ)) J t =
      trivToE I β (c.lift x t) (c.curvatureVector g x t) := by
    rw [← hc.equation x t ht]
    exact hbridge.symm
  dsimp only at hcurv ⊢
  rw [← hcurv, ← hvel]
  exact hcoord.hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

end

section

open Set Filter
open scoped ContDiff Manifold Topology
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] in
private theorem second_deriv_eq_fderiv_apply_one {u : ℝ → E} {x : ℝ}
    (hu : ContDiffAt ℝ 2 u x) :
    deriv (deriv u) x = fderiv ℝ (fderiv ℝ u) x 1 1 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have he : deriv u = fun y => fderiv ℝ u y 1 := by
    funext y
    exact (fderiv_apply_one_eq_deriv (f := u) (x := y)).symm
  rw [he, deriv_clm_apply hd (differentiableAt_const 1)]
  simp only [deriv_const, map_zero, add_zero, fderiv_apply_one_eq_deriv]

theorem CurveMap.IsSolutionOn.hasDerivWithinAt_chartRhsJet
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (hc : c.IsSolutionOn g J) (β : M) (x t : ℝ) (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t) (hchart : c.lift x t ∈ (extChartAt I β).source) :
    HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
      (curveShorteningChartRhsJet g β
        ((t, x), Analysis.jet2 (fun y => extChartAt I β (c.lift y t)) x)) J t := by
  let u : ℝ → E := fun y => extChartAt I β (c.lift y t)
  have hslice : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x :=
    ((c.space_slice_contMDiffWithinAt J hc.smooth x t ht).contMDiffAt
      (univ_mem : (univ : Set ℝ) ∈ 𝓝 x)).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsrc : c.lift x t ∈ (chartAt H β).source := by
    rwa [extChartAt_source] at hchart
  have hu : ContDiffAt ℝ 2 u x :=
    ((contMDiffAt_extChartAt' hsrc).comp x hslice).contDiffAt
  have hd2 := second_deriv_eq_fderiv_apply_one hu
  have hd1 : fderiv ℝ u x 1 = deriv u x := fderiv_apply_one_eq_deriv
  have hpde := hc.hasDerivWithinAt_chart β x t ht hJ hchart
  dsimp only at hpde
  change HasDerivWithinAt (fun τ => extChartAt I β (c.lift x τ))
    (curveShorteningChartRhsJet g β ((t, x), Analysis.jet2 u x)) J t
  simpa only [curveShorteningChartRhsJet, curveShorteningChartRhs, Analysis.jet2,
    ← hd2, hd1, inv_pow, u] using hpde

theorem CurveMap.IsSolutionOn.hasDerivAt_chartRhsJet
    {g : ℝ → SmoothRiemannianMetric I M} {c : CurveMap M} {J : Set ℝ}
    (hc : c.IsSolutionOn g J) (β : M) (x t : ℝ)
    (hJ : J ∈ 𝓝 t) (hchart : c.lift x t ∈ (extChartAt I β).source) :
    HasDerivAt (fun τ => extChartAt I β (c.lift x τ))
      (curveShorteningChartRhsJet g β
        ((t, x), Analysis.jet2 (fun y => extChartAt I β (c.lift y t)) x)) t :=
  (hc.hasDerivWithinAt_chartRhsJet β x t (mem_of_mem_nhds hJ)
    (uniqueDiffWithinAt_of_mem_nhds hJ) hchart).hasDerivAt hJ

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open Bundle Manifold Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap
variable [I.Boundaryless]

theorem chartJet_mem_curveShorteningChartDomainJet
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (β : M) (c : CurveMap M)
    {x t : ℝ}
    (ht : t ∈ D.regular)
    (hchart : c.lift x t ∈ (extChartAt I β).source)
    (himm : c.X (I := I) x t ≠ 0) :
    ((t, x), Analysis.jet2 (fun y => extChartAt I β (c.lift y t)) x) ∈
      curveShorteningChartDomainJet D g β := by
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x := by
    by_contra h
    apply himm
    rw [X, mfderiv_zero_of_not_mdifferentiableAt h]
    exact zero_apply 1
  change t ∈ D.regular ∧
    extChartAt I β (c.lift x t) ∈ interior (extChartAt I β).target ∧
    0 < chartGramBilin (g t) β ((extChartAt I β).symm (extChartAt I β (c.lift x t)))
      ((fderiv ℝ (fun y => extChartAt I β (c.lift y t)) x) 1)
      ((fderiv ℝ (fun y => extChartAt I β (c.lift y t)) x) 1)
  have hgood : c.lift x t ∈ chartLeviCivitaGoodSet (I := I) β :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) β (c.lift x t)).mpr hchart
  refine ⟨ht, ?_, ?_⟩
  · exact chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hgood
  · let γ : ℝ → M := fun y => c.lift y t
    let u : ℝ → E := fun y => extChartAt I β (γ y)
    let p : E := (fderiv ℝ u x) 1
    have hb := chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood
    have hp : trivToE I β (c.lift x t) (c.X x t) = p := by
      dsimp only [p, u, γ]
      exact chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt
        hc β
        (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood)
    have hG : chartGramBilin (g t) β (c.lift x t)
        (trivToE I β (c.lift x t) (c.X x t))
        (trivToE I β (c.lift x t) (c.X x t)) =
        (g t).inner (c.lift x t) (c.X x t) (c.X x t) :=
      chartGramBilin_trivToE (g t) β (c.lift x t) hb _ _
    rw [show (extChartAt I β).symm (u x) = c.lift x t by
      dsimp [u, γ]; exact (extChartAt I β).left_inv hchart]
    rw [show (fderiv ℝ u x) 1 = p by rfl, ← hp, hG]
    exact (g t).pos (c.lift x t) (c.X x t) himm

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveShorteningChartDiffusionCoefficient
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (q : ℝ × E × E) : ℝ :=
  (chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1) q.2.2 q.2.2)⁻¹

def curveShorteningParametricChartReaction
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (q : ℝ × E × E) : E :=
  curveShorteningChartDiffusionCoefficient g β q •
    chartChristoffelContraction (g q.1) β q.2.2 q.2.2 q.2.1

def curveShorteningParametricChartRhs
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (q : ℝ × E × E × E) : E :=
  curveShorteningChartDiffusionCoefficient g β (q.1, q.2.1, q.2.2.1) • q.2.2.2 +
    curveShorteningParametricChartReaction g β (q.1, q.2.1, q.2.2.1)

def curveShorteningChartFirstJetDomain (D : RealTimeInterval)
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) : Set (ℝ × E × E) :=
  {q | q.1 ∈ D.regular ∧ q.2.1 ∈ interior (extChartAt I β).target ∧
    0 < chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1) q.2.2 q.2.2}

private theorem contDiffAt_chartSpeedSq
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) {q : ℝ × E × E}
    (ht : q.1 ∈ D.regular) (hz : q.2.1 ∈ interior (extChartAt I β).target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E × E =>
      chartGramBilin (g q.1) β ((extChartAt I β).symm q.2.1) q.2.2 q.2.2) q := by
  have hG := (contDiffAt_chartGramBilin hg β ht hz).comp q
    (contDiffAt_fst.prodMk (contDiffAt_fst.comp _ contDiffAt_snd))
  have hp : ContDiffAt ℝ ∞ (fun q : ℝ × E × E => q.2.2) q :=
    contDiffAt_snd.comp _ contDiffAt_snd
  exact (hG.clm_apply hp).clm_apply hp

theorem isOpen_curveShorteningChartFirstJetDomain
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    IsOpen (curveShorteningChartFirstJetDomain D g β) := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  have ht := (D.regular_isOpen.preimage continuous_fst).mem_nhds hq.1
  have hz := (isOpen_interior.preimage (continuous_fst.comp continuous_snd)).mem_nhds hq.2.1
  have hp := (contDiffAt_chartSpeedSq hg β hq.1 hq.2.1).continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds hq.2.2)
  exact Filter.mem_of_superset (Filter.inter_mem ht (Filter.inter_mem hz hp)) (fun _ h => h)

theorem contDiffOn_curveShorteningChartDiffusionCoefficient
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    ContDiffOn ℝ ∞ (curveShorteningChartDiffusionCoefficient g β)
      (curveShorteningChartFirstJetDomain D g β) := by
  intro q hq
  exact ((contDiffAt_chartSpeedSq hg β hq.1 hq.2.1).inv (ne_of_gt hq.2.2)).contDiffWithinAt

theorem contDiffOn_curveShorteningParametricChartReaction
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M) :
    ContDiffOn ℝ ∞ (curveShorteningParametricChartReaction g β)
      (curveShorteningChartFirstJetDomain D g β) := by
  intro q hq
  have hΓ := (contDiffAt_chartChristoffelContraction hg β
    (q := (q.1, q.2.1, q.2.2, q.2.2)) hq.1 hq.2.1).comp q
      (contDiffAt_fst.prodMk ((contDiffAt_fst.comp _ contDiffAt_snd).prodMk
        ((contDiffAt_snd.comp _ contDiffAt_snd).prodMk
          (contDiffAt_snd.comp _ contDiffAt_snd))))
  exact ((contDiffOn_curveShorteningChartDiffusionCoefficient hg β) q hq).smul
    hΓ.contDiffWithinAt

theorem curveShorteningChartDiffusionCoefficient_pos
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M) (β : M)
    {q : ℝ × E × E} (hq : q ∈ curveShorteningChartFirstJetDomain D g β) :
    0 < curveShorteningChartDiffusionCoefficient g β q := inv_pos.mpr hq.2.2

theorem curveShorteningParametricChartRhs_acceleration_sub
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (t : ℝ) (z p r s : E) :
    curveShorteningParametricChartRhs g β (t, z, p, r) -
      curveShorteningParametricChartRhs g β (t, z, p, s) =
      curveShorteningChartDiffusionCoefficient g β (t, z, p) • (r - s) := by
  simp only [curveShorteningParametricChartRhs, smul_sub]
  abel

theorem curveShorteningParametricChartRhs_sub_principal
    (g : ℝ → SmoothRiemannianMetric I M) (β : M) (t : ℝ) (z p r : E) (a : ℝ) :
    curveShorteningParametricChartRhs g β (t, z, p, r) - a • r =
      (curveShorteningChartDiffusionCoefficient g β (t, z, p) - a) • r +
        curveShorteningParametricChartReaction g β (t, z, p) := by
  simp only [curveShorteningParametricChartRhs, sub_smul]
  abel

namespace CurveMap

variable [I.Boundaryless]

theorem chartDiffusionCoefficient_eq_speed_inv_sq
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) (β : M) (x t : ℝ)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x)
    (hchart : c.lift x t ∈ (extChartAt I β).source) :
    curveShorteningChartDiffusionCoefficient g β
      (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x) =
      c.speed g x t ^ (-2 : ℤ) := by
  have hgood : c.lift x t ∈ chartLeviCivitaGoodSet (I := I) β :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) β (c.lift x t)).mpr hchart
  have hp := chartCoord_mfderiv_along_curve_eq_fderiv_of_mdifferentiableAt hc β
    (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hgood)
  have hb := chartLeviCivitaGoodSet_mem_baseSet (I := I) hgood
  unfold curveShorteningChartDiffusionCoefficient
  dsimp only [curveShorteningChartDiffusionCoefficient]
  rw [(extChartAt I β).left_inv hchart]
  change (chartGramBilin (g t) β (c.lift x t)
    (deriv (fun y => extChartAt I β (c.lift y t)) x)
    (deriv (fun y => extChartAt I β (c.lift y t)) x))⁻¹ = _
  have hp' : (trivToE I β (c.lift x t) (c.X x t)) =
      deriv (fun y => extChartAt I β (c.lift y t)) x := by
    change (Trivialization.continuousLinearMapAt ℝ (trivializationAt E (TangentSpace I) β) (c.lift x t))
      (mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x (1 : ℝ)) = _
    rw [hp, fderiv_apply_one_eq_deriv]
    rfl
  rw [← hp', chartGramBilin_trivToE (g t) β (c.lift x t) hb]
  rw [zpow_neg, zpow_ofNat]
  congr 1
  exact (Real.sq_sqrt (metric_inner_self_nonneg (g t) (c.lift x t) (c.X x t))).symm


variable [T2Space M]

theorem trivToE_parametric_acceleration_eq_chart
    (g : ℝ → SmoothRiemannianMetric I M) (c : CurveMap M) (β : M) (x t : ℝ)
    (hc : ContMDiffAt 𝓘(ℝ, ℝ) I 2 (fun y => c.lift y t) x)
    (hchart : c.lift x t ∈ (extChartAt I β).source) :
    trivToE I β (c.lift x t) (c.speed g x t ^ (-2 : ℤ) • c.Dx g c.X x t) =
      curveShorteningParametricChartRhs g β
        (t, extChartAt I β (c.lift x t), deriv (fun y => extChartAt I β (c.lift y t)) x,
          deriv (deriv (fun y => extChartAt I β (c.lift y t))) x) := by
  rw [map_smul, trivToE_Dx_X_eq_chart g c β x t hc hchart]
  rw [← chartDiffusionCoefficient_eq_speed_inv_sq g c β x t
    (hc.mdifferentiableAt (by norm_num)) hchart]
  simp only [curveShorteningParametricChartRhs, curveShorteningParametricChartReaction, smul_add]

end CurveMap


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M]

theorem contDiffOn_one_of_parametric_chart_equation
    {D : RealTimeInterval} {g : ℝ → SmoothRiemannianMetric I M}
    (hg : MetricFamilySmoothOn D g) (β : M)
    {G : ℝ → ℝ → E} {a b : ℝ} {V : Set ℝ} (hab : a < b) (hV : IsOpen V)
    (hG : ContinuousOn (Function.uncurry G) (Icc a b ×ˢ V))
    (hspace : ∀ t ∈ Icc a b, DifferentiableOn ℝ (G t) V)
    (hDx : ContinuousOn (fun p : ℝ × ℝ => deriv (G p.1) p.2) (Icc a b ×ˢ V))
    (hDxx : ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (G p.1)) p.2)
      (Icc a b ×ˢ V))
    (hjet : ∀ t ∈ Icc a b, ∀ x ∈ V,
      (t, G t x, deriv (G t) x) ∈ curveShorteningChartFirstJetDomain D g β)
    (hpde : ∀ t ∈ Icc a b, ∀ x ∈ V,
      HasDerivWithinAt (fun s => G s x)
        (curveShorteningParametricChartRhs g β
          (t, G t x, deriv (G t) x, deriv (deriv (G t)) x)) (Icc a b) t) :
    ContDiffOn ℝ 1 (Function.uncurry G) (Icc a b ×ˢ V) := by
  let R := fun p : ℝ × ℝ => curveShorteningParametricChartRhs g β
    (p.1, G p.1 p.2, deriv (G p.1) p.2, deriv (deriv (G p.1)) p.2)
  let W := fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ (deriv (G p.1) p.2)
  have hfirst : ContinuousOn (fun p : ℝ × ℝ => (p.1, G p.1 p.2, deriv (G p.1) p.2))
      (Icc a b ×ˢ V) := continuousOn_fst.prodMk (hG.prodMk hDx)
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, G p.1 p.2, deriv (G p.1) p.2))
      (Icc a b ×ˢ V) (curveShorteningChartFirstJetDomain D g β) :=
    fun p hp => hjet p.1 hp.1 p.2 hp.2
  have hR : ContinuousOn R (Icc a b ×ˢ V) := by
    exact (((contDiffOn_curveShorteningChartDiffusionCoefficient hg β).continuousOn.comp
      hfirst hmap).smul hDxx).add
        ((contDiffOn_curveShorteningParametricChartReaction hg β).continuousOn.comp hfirst hmap)
  have hW : ContinuousOn W (Icc a b ×ˢ V) := by
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn hDx
  have h := DifferentialGeometry.Analysis.contDiffIcc_succ (q := 0) hab hV
    (R := R) (W := W) (fun p hp => hpde p.1 hp.1 p.2 hp.2)
    (fun p hp => ((hspace p.1 hp.1 p.2 hp.2).differentiableAt (hV.mem_nhds hp.2)).hasDerivAt.hasFDerivAt)
    (contDiffOn_zero.mpr hR) (contDiffOn_zero.mpr hW)
  simpa only [Nat.cast_zero, zero_add, Function.uncurry_def] using h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
