import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballWarp
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballFlat
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyHalfCollar

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology
namespace GC.LongTime.CuspP1
open GC.Endpoint

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Hyperbolic

/-- depth coordinate as a point of the half line -/
def depthPt (x : E3) : EuclideanHalfSpace 1 := halfPoint (max (x 2) 0) (le_max_right _ _)

def depthDeriv : E3 →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun _ : Fin 1 => (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ))))

theorem depthDeriv_apply (z : E3) :
    depthDeriv z = (WithLp.toLp 2 (fun _ : Fin 1 => z 2) : EuclideanSpace ℝ (Fin 1)) := by
  ext i; simp [depthDeriv]

theorem contMDiffOn_depthPt :
    ContMDiffOn 𝓘(ℝ, E3) (𝓡∂ 1) ∞ depthPt {y : E3 | 0 < y 2} :=
  GC.GraphManifold.Assembly.contMDiffOn_halfPoint_max (u := fun y : E3 => y 2)
    ((EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).contDiff.contMDiff.contMDiffOn)
    (fun y hy => hy.le)

theorem hasMFDerivAt_depthPt {x : E3} (hx : 0 < x 2) :
    HasMFDerivAt 𝓘(ℝ, E3) (𝓡∂ 1) depthPt x depthDeriv := by
  have hopen : IsOpen {y : E3 | 0 < y 2} :=
    isOpen_lt continuous_const (EuclideanSpace.proj (2 : Fin 3) : E3 →L[ℝ] ℝ).continuous
  refine ⟨(contMDiffOn_depthPt.contMDiffAt (hopen.mem_nhds hx)).continuousAt, ?_⟩
  have hev : ∀ᶠ z in 𝓝 x, (WithLp.toLp 2 (fun _ : Fin 1 => max (z 2) 0) : EuclideanSpace ℝ (Fin 1)) =
      depthDeriv z := by
    filter_upwards [hopen.mem_nhds hx] with z hz
    rw [depthDeriv_apply]
    simp only [max_eq_left (le_of_lt hz)]
  have hfd : HasFDerivAt (fun z : E3 => (WithLp.toLp 2 (fun _ : Fin 1 => max (z 2) 0) : EuclideanSpace ℝ (Fin 1)))
      depthDeriv x := depthDeriv.hasFDerivAt.congr_of_eventuallyEq hev
  simp only [writtenInExtChartAt, extChartAt, mfld_simps]
  exact hfd.hasFDerivWithinAt

/-- the planar projection `E3 → E2` -/
def planeProj : E3 →L[ℝ] E2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j : Fin 2 => (EuclideanSpace.proj (Fin.castSucc j) : E3 →L[ℝ] ℝ)))

theorem planeProj_apply (x : E3) (j : Fin 2) : planeProj x j = x (Fin.castSucc j) := by
  simp [planeProj]

theorem inner_planeProj (v w : E3) :
    inner ℝ (planeProj v) (planeProj w) = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, planeProj_apply]
  ring

/-- the chart-level map `E3 ⊃ {t>0} → cusp half-space` -/
def cuspChart (cov : E2 → Torus) (x : E3) : CuspHalfSpace := (cov (planeProj x), depthPt x)

theorem hasMFDerivAt_planeProj (x : E3) : HasMFDerivAt 𝓘(ℝ, E3) 𝓘(ℝ, E2) planeProj x planeProj :=
  planeProj.hasFDerivAt.hasMFDerivAt

universe u

theorem hasMFDerivAt_cuspChart {cov : E2 → Torus}
    (hcov : ContMDiff 𝓘(ℝ, E2) torusModel ∞ cov) {x : E3} (hx : 0 < x 2) :
    HasMFDerivAt 𝓘(ℝ, E3) halfCollarModel (cuspChart cov) x
      ((mfderiv 𝓘(ℝ, E2) torusModel cov (planeProj x) ∘L planeProj).prod depthDeriv) := by
  have h1 : HasMFDerivAt 𝓘(ℝ, E3) torusModel (fun y => cov (planeProj y)) x
      (mfderiv 𝓘(ℝ, E2) torusModel cov (planeProj x) ∘L planeProj) :=
    ((hcov.mdifferentiableAt (by simp) (x := planeProj x)).hasMFDerivAt).comp x
      (hasMFDerivAt_planeProj x)
  exact h1.prodMk (hasMFDerivAt_depthPt hx)

theorem cuspChart_metric_CPF3 (C : HyperbolicCusp) (Hm : FiniteVolumeHyperbolicModel.{u})
    (ψ : CuspHalfSpace → Hm.Carrier) (hψ : ContMDiff halfCollarModel (𝓡 3) ∞ ψ)
    (hiso : ∀ p (v w : TangentSpace halfCollarModel p),
      Hm.metric.inner (ψ p) (mfderiv halfCollarModel (𝓡 3) ψ p v)
        (mfderiv halfCollarModel (𝓡 3) ψ p w) = C.metric.inner p v w)
    {cov : E2 → Torus} (hcov : ContMDiff 𝓘(ℝ, E2) torusModel ∞ cov)
    (hcovm : ∀ (x v w : E2), C.torusMetric.inner (cov x) (mfderiv 𝓘(ℝ, E2) torusModel cov x v)
        (mfderiv 𝓘(ℝ, E2) torusModel cov x w) = inner ℝ v w)
    {x : E3} (hx : 0 < x 2) (v w : E3) :
    Hm.metric.inner (ψ (cuspChart cov x))
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x v)
      (mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x w) =
    warpCoeff (EuclideanSpace.proj 0) (EuclideanSpace.proj 1) (EuclideanSpace.proj 2) x v w := by
  have hG := hasMFDerivAt_cuspChart hcov hx
  have hψd : HasMFDerivAt halfCollarModel (𝓡 3) ψ (cuspChart cov x)
      (mfderiv halfCollarModel (𝓡 3) ψ (cuspChart cov x)) :=
    (hψ.mdifferentiableAt (by simp) (x := cuspChart cov x)).hasMFDerivAt
  have hF := hψd.comp x hG
  have hF' : mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x =
      mfderiv halfCollarModel (𝓡 3) ψ (cuspChart cov x) ∘L
        ((mfderiv 𝓘(ℝ, E2) torusModel cov (planeProj x) ∘L planeProj).prod depthDeriv) :=
    hF.mfderiv
  let dg : E3 → TangentSpace halfCollarModel (cuspChart cov x) := fun u =>
    (mfderiv 𝓘(ℝ, E2) torusModel cov (planeProj x) (planeProj u), depthDeriv u)
  have key : ∀ u : E3, mfderiv 𝓘(ℝ, E3) (𝓡 3) (fun y => ψ (cuspChart cov y)) x u =
      mfderiv halfCollarModel (𝓡 3) ψ (cuspChart cov x) (dg u) := fun u => by
    have := congrArg (fun L => L u) hF'
    exact this
  rw [key v, key w, hiso, C.metric_formula]
  have h1 : C.torusMetric.inner (cuspChart cov x).1 (dg v).1 (dg w).1 =
      v 0 * w 0 + v 1 * w 1 := by
    rw [← inner_planeProj]
    exact hcovm (planeProj x) (planeProj v) (planeProj w)
  have h2 : (dg v).2.ofLp 0 = v 2 := by
    change depthDeriv v 0 = v 2
    rw [depthDeriv_apply]
  have h3 : (dg w).2.ofLp 0 = w 2 := by
    change depthDeriv w 0 = w 2
    rw [depthDeriv_apply]
  have h4 : ((cuspChart cov x).2).val.ofLp 0 = x 2 := by
    change max (x 2) 0 = x 2
    exact max_eq_left hx.le
  rw [h1, h2, h3, h4, warpCoeff_apply]
  simp

end GC.LongTime.CuspP1
