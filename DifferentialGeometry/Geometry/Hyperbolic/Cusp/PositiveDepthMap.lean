/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.Hyperbolic.Cusp.OrthonormalCoverProjection
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
open DifferentialGeometry.Topology.Manifold Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

local notation "V₃" => Fin 3 → ℝ
local notation "V₂" => Fin 2 → ℝ

def positiveDepth : TopologicalSpace.Opens V₃ :=
  ⟨{x | 0 < x 0}, isOpen_lt continuous_const (continuous_apply 0)⟩

def horizontal : V₃ →L[ℝ] V₂ :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 1, ContinuousLinearMap.proj 2]

def coordinates (q : V₂ → Torus) (x : V₃) : CuspHalfSpace :=
  (q (horizontal x), halfSpaceOneLift (x 0))

private theorem halfSpace_derivative {r : ℝ} (hr : 0 < r) (v : ℝ) :
    EuclideanSpace.proj 0 (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r v) = v := by
  have hl : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r :=
    (contMDiffOn_halfSpaceOneLift.contMDiffAt
      (Ici_mem_nhds hr)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have he : (fun s : ℝ => (halfSpaceOneLift s).val 0) =ᶠ[𝓝 r] id := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    change max s 0 = s
    exact max_eq_left hs.le
  have hd : HasDerivAt (fun s : ℝ => (halfSpaceOneLift s).val 0) 1 r :=
    (hasDerivAt_id r).congr_of_eventuallyEq he
  have hc := ((hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceOneLift r)).comp r
    hl.hasMFDerivAt).mfderiv
  rw [mfderiv_eq_fderiv] at hc
  have hv := congrArg (fun L : ℝ →L[ℝ] ℝ => L v) hc
  change fderiv ℝ (fun s : ℝ => (halfSpaceOneLift s).val 0) r v =
    (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r v) at hv
  have hcoord (u : EuclideanSpace ℝ (Fin 1)) :
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)) u = EuclideanSpace.proj 0 u := by
    change u (default : Fin 1) = u 0
    exact congrArg (fun j : Fin 1 => u j) (Subsingleton.elim _ _)
  rw [hd.hasFDerivAt.fderiv] at hv
  calc
    _ = (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift r v) := (hcoord _).symm
    _ = v := by simpa using hv.symm

theorem coordinates_contMDiffAt {q : V₂ → Torus}
    (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q) {x : V₃} (hx : 0 < x 0) :
    ContMDiffAt 𝓘(ℝ, V₃) halfCollarModel ∞ (coordinates q) x := by
  have ht : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡∂ 1) ∞ halfSpaceOneLift (x 0) :=
    contMDiffOn_halfSpaceOneLift.contMDiffAt (Ici_mem_nhds hx)
  have hp : ContMDiffAt 𝓘(ℝ, V₃) 𝓘(ℝ, ℝ) ∞ (fun y : V₃ => y 0) x :=
    (ContinuousLinearMap.proj 0 : V₃ →L[ℝ] ℝ).contDiff.contMDiff.contMDiffAt
  have htime := ht.comp x hp
  exact (hq.contMDiffAt.comp x horizontal.contDiff.contMDiff.contMDiffAt).prodMk htime

theorem coordinates_mfderiv {q : V₂ → Torus}
    (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q) {x : V₃} (hx : 0 < x 0) (v : V₃) :
    mfderiv 𝓘(ℝ, V₃) halfCollarModel (coordinates q) x v =
      (mfderiv 𝓘(ℝ, V₂) torusModel q (horizontal x) (horizontal v),
        mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift (x 0) (v 0)) := by
  have hq' := hq.mdifferentiableAt (x := horizontal x) (by simp)
  have hh := horizontal.hasFDerivAt.hasMFDerivAt (x := x)
  have ht : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift (x 0) :=
    (contMDiffOn_halfSpaceOneLift.contMDiffAt
      (Ici_mem_nhds hx)).mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hp := (ContinuousLinearMap.proj 0 : V₃ →L[ℝ] ℝ).hasFDerivAt.hasMFDerivAt (x := x)
  have hhorizontal := hq'.hasMFDerivAt.comp x hh
  have htime := ht.hasMFDerivAt.comp x hp
  have hd := (hhorizontal.prodMk htime).mfderiv
  exact congrArg
    (fun L : V₃ →L[ℝ] TangentSpace halfCollarModel (coordinates q x) => L v) hd

variable {H : FiniteVolumeHyperbolicModel}

def ambientMap (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (q : V₂ → Torus) :
    V₃ → H.Carrier := Tr.cuspMap i ∘ coordinates q

def positiveMap (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (q : V₂ → Torus) :
    positiveDepth → H.Carrier := fun x => ambientMap Tr i q x

theorem ambientMap_contMDiffAt (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    {x : V₃} (hx : 0 < x 0) :
    ContMDiffAt 𝓘(ℝ, V₃) (𝓡 3) ∞ (ambientMap Tr i q) x :=
  (Tr.cuspEmbedding i).isImmersion.contMDiff.contMDiffAt.comp x
    (coordinates_contMDiffAt hq hx)

theorem positiveMap_contMDiff (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q) :
    ContMDiff 𝓘(ℝ, V₃) (𝓡 3) ∞ (positiveMap Tr i q) := by
  intro x
  exact (ambientMap_contMDiffAt Tr i hq x.property).comp x
    (contMDiff_subtype_val (I := 𝓘(ℝ, V₃)) (U := positiveDepth)).contMDiffAt

theorem ambientMap_metric (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    {x : V₃} (hx : 0 < x 0) (v w : V₃) :
    H.metric.inner (ambientMap Tr i q x)
      (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (ambientMap Tr i q) x v)
      (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (ambientMap Tr i q) x w) =
        v 0 * w 0 + Real.exp (-x 0) * (v 1 * w 1 + v 2 * w 2) := by
  have hc := (coordinates_contMDiffAt hq hx).mdifferentiableAt (by simp)
  have ht := (Tr.cuspEmbedding i).isImmersion.contMDiff.mdifferentiableAt
    (x := coordinates q x) (by simp)
  unfold ambientMap
  rw [mfderiv_comp x ht hc]
  change H.metric.inner (Tr.cuspMap i (coordinates q x))
    (mfderiv halfCollarModel (𝓡 3) (Tr.cuspMap i) (coordinates q x)
      (mfderiv 𝓘(ℝ, V₃) halfCollarModel (coordinates q) x v))
    (mfderiv halfCollarModel (𝓡 3) (Tr.cuspMap i) (coordinates q x)
      (mfderiv 𝓘(ℝ, V₃) halfCollarModel (coordinates q) x w)) = _
  rw [Tr.cuspIsometry, (Tr.cusp i).metric_formula,
    coordinates_mfderiv hq hx v, coordinates_mfderiv hq hx w]
  change EuclideanSpace.proj 0
    (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift (x 0) (v 0)) *
    EuclideanSpace.proj 0 (mfderiv 𝓘(ℝ, ℝ) (𝓡∂ 1) halfSpaceOneLift (x 0) (w 0)) +
    Real.exp (-(halfSpaceOneLift (x 0)).val 0) * _ = _
  rw [halfSpace_derivative hx, halfSpace_derivative hx]
  have hmetric : (Tr.cusp i).torusMetric.inner (q (horizontal x))
      (mfderiv 𝓘(ℝ, V₂) torusModel q (horizontal x) (horizontal v))
      (mfderiv 𝓘(ℝ, V₂) torusModel q (horizontal x) (horizontal w)) =
        v 1 * w 1 + v 2 * w 2 :=
    hqmetric (horizontal x) (horizontal v) (horizontal w)
  calc
    _ = v 0 * w 0 + Real.exp (-(halfSpaceOneLift (x 0)).val 0) *
        (v 1 * w 1 + v 2 * w 2) := by
      exact congrArg
        (fun a : ℝ => v 0 * w 0 + Real.exp (-(halfSpaceOneLift (x 0)).val 0) * a) hmetric
    _ = _ := by
      change v 0 * w 0 + Real.exp (-(max (x 0) 0)) *
        (v 1 * w 1 + v 2 * w 2) = _
      rw [max_eq_left hx.le]

theorem positiveMap_metric (Tr : HyperbolicTruncation H) (i : Fin Tr.count)
    {q : V₂ → Torus} (hq : ContMDiff 𝓘(ℝ, V₂) torusModel ∞ q)
    (hqmetric : ∀ z v w, (Tr.cusp i).torusMetric.inner (q z)
      (mfderiv 𝓘(ℝ, V₂) torusModel q z v) (mfderiv 𝓘(ℝ, V₂) torusModel q z w) =
        v 0 * w 0 + v 1 * w 1)
    (x : positiveDepth) (v w : V₃) :
    H.metric.inner (positiveMap Tr i q x)
      (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x v)
      (mfderiv 𝓘(ℝ, V₃) (𝓡 3) (positiveMap Tr i q) x w) =
        v 0 * w 0 + Real.exp (-x.val 0) * (v 1 * w 1 + v 2 * w 2) := by
  unfold positiveMap
  rw [mfderiv_restrict_open]
  exact ambientMap_metric Tr i hq hqmetric x.property v w

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
