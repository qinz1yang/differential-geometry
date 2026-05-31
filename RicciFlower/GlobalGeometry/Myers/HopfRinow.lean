import RicciFlower.GlobalGeometry.Myers.Basic
import RicciFlower.GlobalGeometry.Myers.DiameterBound
import RicciFlower.GlobalGeometry.Myers.RicciTrace
import RicciFlower.GlobalGeometry.SecondVariation
import RicciFlower.GlobalGeometry.HopfRinow
import RicciFlower.Curvature.Metric

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Hopf-Rinow interfaces for the Myers project

This file isolates the global Riemannian-analysis inputs needed to turn the
index-form/Myers length estimate into compactness.

The whole layer uses Mathlib's canonical Riemannian-distance setup: a single
`[EMetricSpace M]` whose `edist` is, by `IsRiemannianManifold I M`, the
Riemannian path-length distance of the ambient `[RiemannianBundle …]`.  The
explicit smooth metric `g` used by the index form is tied to that bundle by the
coherence hypothesis `hg : ∀ x v w, ⟪v, w⟫ = g.inner x v w`, so the geodesic
length `L` produced by the interface genuinely equals `edist p q`.

The two genuine black boxes are:

* `exists_myersGeometryData`: minimizing geodesics plus the second-variation and
  Ricci-trace/index-data producers needed by `geodesic_length_le_of_index_data`,
  with `ENNReal.ofReal L = edist p q` recording that the geodesic realizes the
  Riemannian distance;
* `compactSpace_of_complete_riemannian_of_ediam_le`: Hopf-Rinow compactness for
  a complete connected finite-dimensional Riemannian manifold of bounded
  diameter.

Everything after those two interfaces is checked metric-space wiring.
-/

noncomputable section

namespace RicciFlower
namespace GlobalGeometry
namespace Myers

open Bundle Filter Lecture07 intervalIntegral
open scoped Manifold ContDiff Topology BigOperators ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [SigmaCompactSpace M] [T2Space M]

/-- Interface bundle: the output of the geometric "minimizing geodesic + index
data" machinery for a single pair of points `p q`.

This packages exactly the data consumed by
`geodesic_length_le_of_index_data`: a positive length `L` realizing the
Riemannian distance (`ENNReal.ofReal L = edist p q`), a finite family of test
fields, pointwise Ricci lower-bound data along the geodesic, the nonnegativity
of each index form, and the summed trigonometric index identity.

Producing this data is the global geometric content: Hopf-Rinow minimizing
geodesics, parallel orthonormal test fields, the second-variation
nonnegativity input, and the Ricci-trace/index-form computation. -/
structure MyersIndexData
    (g : SmoothRiemannianMetric I M)
    (n : Nat) (k : Real) (p q : M) where
  L : Real
  hL_eq : ENNReal.ofReal L = edist p q
  hL_pos : 0 < L
  ι : Type
  [fintypeι : Fintype ι]
  gamma : Curve M
  V : ι -> VectorFieldAlong I gamma
  DV : ι -> VectorFieldAlong I gamma
  CurvV : ι -> VectorFieldAlong I gamma
  r : Real -> Real
  hr_cont : ContinuousOn r (Set.Icc (0 : Real) L)
  hr : forall t, t ∈ Set.Icc (0 : Real) L -> ((n : Real) - 1) * k <= r t
  hnonneg : forall i, 0 <= indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L
  hsum_eq :
    (∑ i, indexForm (I := I) g gamma (V i) (DV i) (CurvV i) 0 L)
      = ∫ t in (0 : Real)..L,
          ((n : Real) - 1) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2
            - Real.sin (Real.pi / L * t) ^ 2 * r t

/-- Pinned geometry interface for the Myers index estimate: the combined output
of the still-missing analytic producers (minimizing geodesic, parallel
orthonormal frame, curvature-trace field, second-variation formula).  All test
fields are the concrete sine fields, so this structure fully fixes the
`V_i/DV_i/CurvV_i` signatures consumed by the index-sum and nonnegativity
lemmas.  The Ricci lower bound is deliberately not used to build this data; it
enters only later through `myers_index_sum_data`. -/
structure MyersGeometryData
    (g : SmoothRiemannianMetric I M)
    (n : Nat) (p q : M) where
  /-- [P1] The minimizing unit-speed geodesic length. -/
  L : Real
  hL_pos : 0 < L
  hL_eq : ENNReal.ofReal L = edist p q
  gamma : Curve M
  hunit : forall t, t ∈ Set.Icc (0 : Real) L ->
    g.inner (gamma t) (velocityAlong I gamma t) (velocityAlong I gamma t) = 1
  /-- [P2] Pullback-parallel orthonormal frame perpendicular to `T`. -/
  Eframe : Fin (n - 1) -> VectorFieldAlong I gamma
  hON : forall t, t ∈ Set.Icc (0 : Real) L -> forall i j,
    g.inner (gamma t) (Eframe i t) (Eframe j t) = if i = j then 1 else 0
  hperp : forall t, t ∈ Set.Icc (0 : Real) L -> forall i,
    g.inner (gamma t) (Eframe i t) (velocityAlong I gamma t) = 0
  /-- [Curvature] Ricci-trace realization data, with `CurvE i` intended to be
  `R(E_i,T)T`. -/
  CurvE : Fin (n - 1) -> VectorFieldAlong I gamma
  r : Real -> Real
  hr_def : forall t, r t =
    Curvature.metricRicci (I := I) g (gamma t)
      (Curvature.vec2 (I := I) (velocityAlong I gamma t) (velocityAlong I gamma t))
  hr_cont : ContinuousOn r (Set.Icc (0 : Real) L)
  hTrace : forall t, t ∈ Set.Icc (0 : Real) L ->
    (∑ i, g.inner (gamma t) (CurvE i t) (Eframe i t)) = r t
  hInt : forall i, IntervalIntegrable
    (fun t =>
      g.inner (gamma t)
          (sinDerivField (I := I) L gamma Eframe i t)
          (sinDerivField (I := I) L gamma Eframe i t)
        - g.inner (gamma t)
          (sinCoeff L t • CurvE i t)
          (sinField (I := I) L gamma Eframe i t))
    MeasureTheory.volume 0 L
  /-- [Second variation] Per-field arc-length functional with a local minimum
  at `0`. -/
  fLen : Fin (n - 1) -> Real -> Real
  secondVar : Fin (n - 1) -> Real
  hmin : forall i, IsLocalMin (fLen i) (0 : Real)
  hderiv2 : forall i, HasDerivAt (deriv (fLen i)) (secondVar i) 0
  hderiv1 : forall i, ∀ᶠ s in 𝓝 (0 : Real), HasDerivAt (fLen i) (deriv (fLen i) s) s
  hEq45 : forall i, secondVar i = ∫ t in (0 : Real)..L,
    (g.inner (gamma t)
        (perpOff (I := I) g (gamma t)
          (sinDerivField (I := I) L gamma Eframe i t) (velocityAlong I gamma t))
        (perpOff (I := I) g (gamma t)
          (sinDerivField (I := I) L gamma Eframe i t) (velocityAlong I gamma t))
      - g.inner (gamma t) (sinCoeff L t • CurvE i t)
          (sinField (I := I) L gamma Eframe i t))

/-- **Combined M5 geometry frontier.**  Existence of `MyersGeometryData`: the
minimizing geodesic, parallel orthonormal frame, curvature-trace field, and the
fixed-endpoint second-variation data along it.  The Ricci lower bound is not
needed here (it is applied later in `myers_index_sum_data`); `hg` records that
the index form's metric `g` is the ambient bundle metric defining `edist`. -/
theorem exists_myersGeometryData
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {n : Nat}
    (_hn : 1 < n)
    (_hdim : Module.finrank Real E = n)
    (_hg : forall (x : M) (v w : TangentSpace I x), (inner Real v w : Real) = g.inner x v w)
    {p q : M} (_hpq : p ≠ q) :
    Nonempty (MyersGeometryData (I := I) g n p q) := by
  sorry

/-- **M5 geometric interface.**

Hopf-Rinow geodesic existence plus the second-variation/index assembly: in a
complete connected Riemannian manifold with `Ric >= (n - 1) k g`, `n >= 2`, and
`k > 0`, for every non-degenerate pair of points there is `MyersIndexData`.

The coherence hypothesis `hg` records that the index form's smooth metric `g`
is exactly the ambient bundle metric defining `edist`; this is what makes the
field `hL_eq : ENNReal.ofReal L = edist p q` an honest statement (the minimizing
`g`-geodesic realizes the Riemannian distance).

This theorem is now a checked assembler from the pinned geometry frontier
`exists_myersGeometryData`, the P3 index-form nonnegativity bridge, and the P4
Ricci trace/index-sum bridge. -/
theorem exists_myersIndexData
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {n : Nat} {k : Real}
    (hn : 1 < n)
    (_hk : 0 < k)
    (hdim : Module.finrank Real E = n)
    (hRic :
      RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
        (((n - 1 : Nat) : Real) * k))
    (hg : forall (x : M) (v w : TangentSpace I x), (inner Real v w : Real) = g.inner x v w)
    {p q : M} (hpq : p ≠ q) :
    Nonempty (MyersIndexData (I := I) g n k p q) := by
  classical
  obtain ⟨D⟩ :=
    exists_myersGeometryData (I := I) (M := M) g hn hdim hg hpq
  have hcard : (Fintype.card (Fin (n - 1)) : Real) = (n : Real) - 1 := by
    rw [Fintype.card_fin, Nat.cast_sub hn.le, Nat.cast_one]
  obtain ⟨hr_cont, hr, hsum_eq⟩ :=
    myers_index_sum_data (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
      D.Eframe D.CurvE D.r
      hn D.hL_pos.le hcard D.hr_def hRic D.hON D.hunit D.hTrace D.hr_cont D.hInt
  refine ⟨{
    L := D.L
    hL_eq := D.hL_eq
    hL_pos := D.hL_pos
    ι := Fin (n - 1)
    gamma := D.gamma
    V := fun i => sinField (I := I) D.L D.gamma D.Eframe i
    DV := fun i => sinDerivField (I := I) D.L D.gamma D.Eframe i
    CurvV := fun i => fun t => sinCoeff D.L t • D.CurvE i t
    r := D.r
    hr_cont := hr_cont
    hr := hr
    hnonneg := ?_
    hsum_eq := hsum_eq }⟩
  intro i
  have hunitT : forall t, t ∈ Set.uIcc (0 : Real) D.L ->
      g.inner (D.gamma t) (velocityAlong I D.gamma t)
        (velocityAlong I D.gamma t) = 1 := by
    intro t ht
    exact D.hunit t (by rwa [Set.uIcc_of_le D.hL_pos.le] at ht)
  have hperp : forall t, t ∈ Set.uIcc (0 : Real) D.L ->
      g.inner (D.gamma t)
        (sinDerivField (I := I) D.L D.gamma D.Eframe i t)
        (velocityAlong I D.gamma t) = 0 := by
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : Real) D.L := by
      rwa [Set.uIcc_of_le D.hL_pos.le] at ht
    have hbase :
        g.inner (D.gamma t) (D.Eframe i t) (curveVelocity I D.gamma t) = 0 := by
      simpa [velocityAlong] using D.hperp t htIcc i
    simp [sinDerivField, hbase]
  exact
    indexForm_nonneg_of_minimizing (I := I) g
      (sinField (I := I) D.L D.gamma D.Eframe i)
      (sinDerivField (I := I) D.L D.gamma D.Eframe i)
      (fun t => sinCoeff D.L t • D.CurvE i t)
      (D.fLen i) (D.hmin i) (D.hderiv2 i) (D.hderiv1 i)
      hunitT hperp (D.hEq45 i)

/-- Pointwise Myers distance bound from the geometric index-data interface.

The degenerate case is handled by `edist p p = 0`; otherwise the interface data
feeds directly into the checked M1 length estimate, and `hL_eq` turns the real
length bound `L <= pi/sqrt(k)` into the extended-distance bound. -/
theorem edist_le_pi_div_sqrt
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {n : Nat} {k : Real}
    (hn : 1 < n)
    (hk : 0 < k)
    (hdim : Module.finrank Real E = n)
    (hRic :
      RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
        (((n - 1 : Nat) : Real) * k))
    (hg : forall (x : M) (v w : TangentSpace I x), (inner Real v w : Real) = g.inner x v w)
    (p q : M) :
    edist p q <= ENNReal.ofReal (Real.pi / Real.sqrt k) := by
  by_cases hpq : p = q
  · subst hpq
    simp
  · obtain ⟨D⟩ :=
      exists_myersIndexData
        (I := I) (M := M) g hn hk hdim hRic hg hpq
    letI : Fintype D.ι := D.fintypeι
    have hlength :=
      geodesic_length_le_of_index_data
        (I := I) g D.V D.DV D.CurvV hn D.hL_pos hk
        D.hr_cont D.hr D.hnonneg D.hsum_eq
    calc
      edist p q = ENNReal.ofReal D.L := D.hL_eq.symm
      _ <= ENNReal.ofReal (Real.pi / Real.sqrt k) :=
        ENNReal.ofReal_le_ofReal hlength

/-- Checked metric-space wiring from Hopf-Rinow compactness and the Myers
diameter estimate to compactness. -/
theorem myers_compactSpace_of_ricci_lower_bound_metric
    [hb : RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [CompleteSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    {n : Nat} {k : Real}
    (hn : 1 < n)
    (hdim : Module.finrank Real E = n)
    (hk : 0 < k)
    (hRic :
      RicciLowerBound (I := I) (M := M) g (Curvature.metricRicci (I := I) g)
        (((n - 1 : Nat) : Real) * k))
    (hg : ∀ (x : M) (v w : TangentSpace I x), (inner ℝ v w : ℝ) = g.inner x v w) :
    CompactSpace M := by
  refine
    compactSpace_of_complete_riemannian_of_ediam_le
      (I := I) (M := M) (C := ENNReal.ofReal (Real.pi / Real.sqrt k))
      ENNReal.ofReal_ne_top ?_
  intro x y
  exact edist_le_pi_div_sqrt (I := I) (M := M) g hn hk hdim hRic hg x y

end Myers
end GlobalGeometry
end RicciFlower
