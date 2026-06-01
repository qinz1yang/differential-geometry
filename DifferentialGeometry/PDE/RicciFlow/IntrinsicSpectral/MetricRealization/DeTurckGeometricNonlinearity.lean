import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.TensorHsRealize
import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.FaithfulH1Embedding
import DifferentialGeometry.PDE.RicciFlow.DeTurckRHSSection
import DifferentialGeometry.Integral.Connection.RawTensorConnLapIterL2WtwokTwoBound

/-!
# The geometric Ricci–DeTurck nonlinearity on the spectral Sobolev scale

The chart-locality-free maximal-regularity strong-existence engine
`deTurckRemainder_strong_shortTime_exists`
(`DeTurckRemainderStrongExists.lean`) consumes a *locally Lipschitz* first-order
nonlinearity

  `N : tensorHs g_bg 0 2 (a + 1) → tensorHs g_bg 0 2 a`

(`a : ℝ` a non-negative spectral Sobolev exponent), and produces a strong
solution of the quasi-linear tensor heat equation
`∂_t u = Δ_∇ u + N(u)`, `u(0) = u₀`.

This file constructs the *geometric* `N` for the Ricci–DeTurck flow.  The
top-order part of the Ricci–DeTurck right-hand side `deTurckRicciRHS g_bg g`
coincides — by the gauge cancellation `deTurckNonlinearitySpectral_principalPart_cancels`
— with the connection Laplacian `Δ_∇`, so the *remainder*

  `N(u) := deTurckRicciRHS g_bg (g_bg + h(u)) − Δ_∇ h(u)`,
  `h(u) := realized metric perturbation of u`,

is genuinely first order in `h(u)`.

## The realization, and well-typedness via the spectral summability of smooth data

`tensorHs g_bg 0 2 σ` is a structure carrying an abstract spectral coordinate
family `coeff : TensorEigenIdx → ℝ` plus a weighted-`ℓ²` summability witness, not
a pointwise tensor field.  To write `N(u)` we realize the finitely-supported `u`
as a genuine smooth compactly-supported `(0,2)`-tensor section
`T_u = tensorHsSmoothRepr u` (the chart-locality-free smooth
representative on the dense finite-support subspace), assemble the smooth metric
`g_bg + h_sym(T_u)` on its validity domain via `tensorSectionRealizeMetric`, and
take the smooth `(0,2)`-tensor section of the geometric remainder
`deTurckRHSSection g_bg (g_bg + h_sym) − Δ_∇ T_u`.

The geometric remainder section is again a `SmoothCcTensor g_bg 0 2`; by the
spectral-scale summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at *every* real Sobolev
order) its eigenbasis coordinates are weighted square-summable at order `a`,
which is exactly the witness needed to package those coordinates as an element of
`tensorHs g_bg 0 2 a`.  This is the type-level content of the construction.

Off the validity domain — when `u` is not finitely supported, or its
extracted-and-symmetrized form is not `g_bg`-fibre small (so `g_bg + h_sym` is not
an honest metric) — the nonlinearity returns the zero element of
`tensorHs g_bg 0 2 a`.

## Sign convention

Geometer `Δ_∇ = −∇*∇`, spectrum `⊆ (−∞, 0]`; the resolvent is `(1 − Δ_∇)⁻¹`,
weights `(1 + λᵢ)^σ ≥ 1` for `σ ≥ 0`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The validity-domain predicate for realizing `u : H^{a+1}` as a metric
perturbation: `u` is finitely supported and its extracted symmetric bilinear
form is `g_bg`-fibre small with some constant `< 1` (so `g_bg + h_sym` is an
honest, positive-definite smooth metric). -/
def realizableAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) : Prop :=
  ∃ (hu_fs : (Function.support u.coeff).Finite) (δ' : ℝ), δ' < 1 ∧
    gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ'

open scoped Classical in
/-- The smooth metric realized from a finitely-supported, fibre-small order-`σ`
spectral element `u`: the genuine `g_bg + h_sym(u)` on the validity domain
`realizableAt`, and `g_bg` otherwise. -/
def realizeMetricAt (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothRiemannianMetric I M :=
  if h : realizableAt (I := I) g_bg u then
    tensorSectionRealizeMetric (I := I) g_bg
      (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
        (I := I) (M := M) u h.choose)
      h.choose_spec.choose_spec.1 h.choose_spec.choose_spec.2
  else
    g_bg

/-- On the validity domain, the realized metric's inner product is
`g_bg + tensorHsBilinSymm u`. -/
theorem realizeMetricAt_inner_of_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu_fs : (Function.support u.coeff).Finite)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : gFibreOpBound (I := I) (M := M) g_bg
      (tensorHsBilinSymm (I := I) g_bg u hu_fs) δ')
    (x : M) (v w : TangentSpace I x) :
    (realizeMetricAt (I := I) g_bg u).inner x v w =
      g_bg.inner x v w + tensorHsBilinSymm (I := I) g_bg u hu_fs x v w := by
  classical
  have hex : realizableAt (I := I) g_bg u := ⟨hu_fs, δ', hδ'_lt, hδ'⟩
  rw [realizeMetricAt, dif_pos hex, tensorSectionRealizeMetric_inner]
  rfl

/-- Off the validity domain, the realized metric is the background metric. -/
theorem realizeMetricAt_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    {σ : ℝ} (u : tensorHs (I := I) (M := M) g_bg 0 2 σ)
    (hu : ¬ realizableAt (I := I) g_bg u) :
    realizeMetricAt (I := I) g_bg u = g_bg := by
  classical
  rw [realizeMetricAt, dif_neg hu]

open scoped Classical in
/-- The geometric Ricci–DeTurck remainder as a smooth compactly-supported
`(0,2)`-tensor section, re-tagged by the background metric `g_bg`.

On the validity domain, with smooth representative `T_u` of `u` and realized
metric `g_u = g_bg + h_sym(u)`, this is

  `deTurckRHSSection g_bg g_u − rawTensorConnLapSmooth g_bg 0 2 T_u`

(the Ricci–DeTurck right-hand side of `g_u`, minus the connection Laplacian of the
perturbation — the gauge-cancelled first-order remainder).  Off the validity
domain it is the zero section. -/
def deTurckRemainderSection (g_bg : SmoothRiemannianMetric I M) {σ : ℝ}
    (u : tensorHs (I := I) (M := M) g_bg 0 2 σ) :
    SmoothCcTensor g_bg 0 2 :=
  if h : realizableAt (I := I) g_bg u then
    { toSection :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).toSection
      hasCompactSupport :=
        (deTurckRHSSection (I := I) g_bg (realizeMetricAt (I := I) g_bg u)).hasCompactSupport }
      - rawTensorConnLapSmooth (I := I) g_bg 0 2
          (Analysis.Parabolic.TensorSpectral.tensorHsSmoothRepr
            (I := I) (M := M) u h.choose)
  else
    0

/-- The intrinsic resolvent-compactness witness for the rank-`(0,2)` tensor
resolvent on the closed manifold `(M, g_bg)`. -/
private def hCompact (g_bg : SmoothRiemannianMetric I M) :
    IsCompactOperator (tensorResolventL2 (I := I) (M := M) g_bg 0 2) :=
  tensorResolventL2_isCompactOperator (I := I) (M := M) g_bg 0 2

/-- **The geometric Ricci–DeTurck nonlinearity** as a map of spectral Sobolev
spaces

  `N : tensorHs g_bg 0 2 ((a : ℝ) + 1) → tensorHs g_bg 0 2 (a : ℝ)`.

On a finitely-supported, fibre-small `u`, `N(u)` is the order-`a` spectral
element whose eigenbasis coordinates are the `L²` coordinates of the geometric
remainder section `deTurckRemainderSection g_bg u`
(`= deTurckRHSSection g_bg (g_bg + h_sym(u)) − Δ_∇ T_u`).  The weighted
square-summability witness placing these coordinates in `Hᵃ` is supplied by the
spectral-scale summability of a smooth compactly-supported tensor
(`smoothCcTensor_tensorL2Coeff_weighted_summable`, valid at every real order).
Off the validity domain `N(u) = 0`. -/
def deTurckGeometricN (g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1)) :
    tensorHs (I := I) (M := M) g_bg 0 2 (a : ℝ) where
  coeff i :=
    tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
      (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i
  weighted_summable :=
    smoothCcTensor_tensorL2Coeff_weighted_summable (I := I) (M := M) g_bg
      (a : ℝ) (deTurckRemainderSection (I := I) g_bg u) (hCompact (I := I) g_bg)

/-- The eigenbasis coordinate of `deTurckGeometricN g_bg a u` is the `L²`
coordinate of the geometric remainder section. -/
@[simp] theorem deTurckGeometricN_coeff (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (i : Analysis.Parabolic.TensorHeatEquation.TensorEigenIdx
      (I := I) (M := M) g_bg 0 2) :
    (deTurckGeometricN (I := I) g_bg a u).coeff i =
      tensorL2Coeff (I := I) (M := M) (hCompact (I := I) g_bg)
        (SmoothCcTensor.toL2 (deTurckRemainderSection (I := I) g_bg u)) i :=
  rfl

/-- Off the validity domain, the geometric nonlinearity vanishes. -/
theorem deTurckGeometricN_of_not_realizable (g_bg : SmoothRiemannianMetric I M)
    (a : ℕ) (u : tensorHs (I := I) (M := M) g_bg 0 2 ((a : ℝ) + 1))
    (hu : ¬ realizableAt (I := I) g_bg u) :
    deTurckGeometricN (I := I) g_bg a u = 0 := by
  classical
  have hsec : deTurckRemainderSection (I := I) g_bg u = 0 := by
    rw [deTurckRemainderSection, dif_neg hu]
  apply tensorHs.ext (I := I) (M := M)
  funext i
  rw [deTurckGeometricN_coeff, hsec,
    show SmoothCcTensor.toL2 (g := g_bg) (r := 0) (s := 2)
        (0 : SmoothCcTensor g_bg 0 2) = 0 from map_zero _,
    tensorL2Coeff_eq_inner, inner_zero_right]
  rfl

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
