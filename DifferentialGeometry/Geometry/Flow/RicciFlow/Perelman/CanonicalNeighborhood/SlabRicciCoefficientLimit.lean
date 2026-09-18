import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabMetricCoefficientLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricRicciDifference

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)
open scoped Manifold ContDiff

universe u

section OpenComparison

variable {N M : Type u}
  [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace N] in
private theorem slabOpenPullback_ricci
    (F : PartialDiffeomorph I3 I3 N M ∞)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (g : SmoothRiemannianMetric I3 M) (y : U) (v w : TangentSpace I3 y) :
    ricciTensor (I := I3) (openPullbackMetric F U hU g) y v w =
      ricciTensor (I := I3) g (F (y : N))
        (mfderiv I3 I3 F (y : N) v) (mfderiv I3 I3 F (y : N) w) := by
  let V : TopologicalSpace.Opens M := ⟨F '' (U : Set N), image_opens_isOpen F hU⟩
  let : SigmaCompactSpace V :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 V.isOpen)
  rw [openPullbackMetric, CheegerGromovCompactness.ricciTensor_pullback]
  erw [ricciTensor_restrictOpen g V (PartialDiffeomorph.toOpensDiffeo F hU y),
    mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
    PartialDiffeomorph.mfderiv_toOpensDiffeo F hU y v,
    PartialDiffeomorph.mfderiv_toOpensDiffeo F hU y w]
  rfl

theorem MetricComparisonOn.ricciQuadratic_sub_le
    {h : ℝ → SmoothRiemannianMetric I3 N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : PartialDiffeomorph I3 I3 N M ∞} {K : Set N} {times : Set ℝ}
    {order : ℕ} {eps : ℝ} (P : MetricComparisonOn h g F K times order eps)
    (U : TopologicalSpace.Opens N) (hU : (U : Set N) ⊆ F.source)
    (hUK : (U : Set N) ⊆ K) (horder : 2 ≤ order)
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hsmall : (Module.finrank ℝ ThreeSpace : ℝ) * eps ≤ 1 / 2)
    {s : ℝ} (hs : s ∈ times) (y : U) (v : TangentSpace I3 y) :
    |ricciTensor (I := I3) (g s) (F (y : N))
        (mfderiv I3 I3 F (y : N) v) (mfderiv I3 I3 F (y : N) v) -
      ricciTensor (I := I3) (h s) (y : N) v v| ≤
      (Module.finrank ℝ ThreeSpace : ℝ) * (432 * eps) * (h s).inner (y : N) v v := by
  let : SigmaCompactSpace U :=
    isSigmaCompact_iff_sigmaCompactSpace.mp (Geometry.isSigmaCompact_of_isOpen I3 U.isOpen)
  have hjet (a : ℕ) (ha : a ≤ 2) :
      metricDerivNorm (I := I3) a (openPullbackMetric F U hU (g s))
        ((h s).restrictOpen U) ((h s).restrictOpen U) y ≤ eps := by
    rw [P.openPullback_metricDerivNorm U hU hUK]
    exact P.close a 0 (by omega) s hs (y : N) (hUK y.2)
  have hb := KappaSolutions.metricRicci_difference_le_relative_two_jets
    ((h s).restrictOpen U) (openPullbackMetric F U hU (g s)) y heps heps1 hsmall hjet v
  have hp := slabOpenPullback_ricci F U hU (g s) y v v
  have hr := ricciTensor_restrictOpen (h s) U y v v
  erw [mfderiv_subtype_val_apply] at hr
  have herror := congrArg₂ (fun r q : ℝ => |r - q|) hp hr
  exact (le_of_eq herror.symm).trans hb

end OpenComparison

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : FlowSequence.{u}} {depthBound : ℝ}

def mappedRicciCoefficient (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    (x : L.space.M) (v w : TangentSpace I3 x) (i : ℕ) (t : ℝ) : ℝ :=
  ricciTensor (I := I3) ((X.term (L.subseq (k i))).S.base.metric t)
    (L.maps.partialDiffeomorph (k i) x)
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x v)
    (mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x w)

theorem slabComparison_ricciQuadratic_tendstoUniformlyOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v : TangentSpace I3 x) :
    TendstoUniformlyOn (mappedRicciCoefficient L k x v v)
      (fun t => ricciTensor (I := I3) (g t) x v v) atTop (Set.Icc a b) := by
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (slabComparison_metricCoeff_continuousOn L hle hcomp hab hsub x v v)
  let C : ℝ := |C0| + 1
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hC (t : ℝ) (ht : t ∈ Set.Icc a b) : (g t).inner x v v ≤ C := by
    have hc := hC0 t ht
    rw [Real.norm_eq_abs] at hc
    exact (le_abs_self _).trans (hc.trans (by dsimp only [C]; linarith [le_abs_self C0]))
  obtain ⟨n, hn⟩ := L.maps.source_subset (K := {x}) isCompact_singleton
  let U := sourceOpen (L.maps.partialDiffeomorph n)
  have hx : x ∈ U := hn n le_rfl (Set.mem_singleton x)
  let K : Set L.space.M := closure (L.maps.partialDiffeomorph n).source
  have hK : IsCompact K := L.precompact n
  have hUK : (U : Set L.space.M) ⊆ K := subset_closure
  obtain ⟨m, hm⟩ := L.maps.source_subset hK
  let d : ℝ := Module.finrank ℝ ThreeSpace
  let A : ℝ := d * 432 * C
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  let eps : ℝ := min 1 (min (1 / (2 * (d + 1))) (eta / (A + 1)))
  have heps : 0 < eps := by dsimp only [eps]; positivity
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hsmall : d * eps ≤ 1 / 2 := by
    have ht : eps ≤ 1 / (2 * (d + 1)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (d + 1))).mp ht
    nlinarith [heps.le]
  have hAe : A * eps < eta := by
    have ht : eps ≤ eta / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < A + 1)).mp ht
    nlinarith
  filter_upwards [hcomp K hK a b hab hsub 2 eps heps,
    Filter.eventually_ge_atTop m] with i hi hmi
  obtain ⟨P⟩ := hi
  have hU : (U : Set L.space.M) ⊆ (L.maps.partialDiffeomorph (k i)).source :=
    hUK.trans (hm (k i) (hmi.trans (StrictMono.le_apply hk)))
  intro t ht
  have hb := P.ricciQuadratic_sub_le U hU hUK le_rfl heps.le heps1 hsmall ht ⟨x, hx⟩ v
  change |mappedRicciCoefficient L k x v v i t - ricciTensor (I := I3) (g t) x v v| ≤
    d * (432 * eps) * (g t).inner x v v at hb
  have hscale : d * (432 * eps) * (g t).inner x v v ≤ A * eps := by
    calc
      _ ≤ d * (432 * eps) * C :=
        mul_le_mul_of_nonneg_left (hC t ht) (by positivity)
      _ = _ := by dsimp only [A]; ring
  rw [dist_comm, Real.dist_eq]
  exact hb.trans_lt (hscale.trans_lt hAe)

private theorem slabRicci_polarization {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hB : ∀ v w, B v w = B w v) (v w : V) :
    B v w = (B (v + w) (v + w) - B v v - B w w) / 2 := by
  simp only [map_add, add_apply, hB w v]
  ring

private theorem mappedRicciCoefficient_polarization
    (L : StaticTerminalLimit X depthBound) (k : ℕ → ℕ)
    (x : L.space.M) (v w : TangentSpace I3 x) (i : ℕ) (t : ℝ) :
    mappedRicciCoefficient L k x v w i t =
      (mappedRicciCoefficient L k x (v + w) (v + w) i t -
        mappedRicciCoefficient L k x v v i t - mappedRicciCoefficient L k x w w i t) / 2 := by
  let F := mfderiv I3 I3 (L.maps.partialDiffeomorph (k i)) x
  let B := ricciTensor (I := I3) ((X.term (L.subseq (k i))).S.base.metric t)
    (L.maps.partialDiffeomorph (k i) x)
  change B (F v) (F w) = (B (F (v + w)) (F (v + w)) - B (F v) (F v) -
    B (F w) (F w)) / 2
  rw [F.map_add]
  exact slabRicci_polarization B (ricciTensor_symm _ _) (F v) (F w)

theorem slabComparison_ricciCoeff_tendstoUniformlyOn
    (L : StaticTerminalLimit X depthBound) {delta a b : ℝ}
    (hle : delta ≤ depthBound) {k : ℕ → ℕ} (hk : StrictMono k)
    {g : ℝ → SmoothRiemannianMetric I3 L.space.M}
    (hcomp : SlabComparison L delta k g) (hab : a ≤ b)
    (hsub : Set.Icc a b ⊆ Set.Icc (-delta) 0)
    (x : L.space.M) (v w : TangentSpace I3 x) :
    TendstoUniformlyOn (mappedRicciCoefficient L k x v w)
      (fun t => ricciTensor (I := I3) (g t) x v w) atTop (Set.Icc a b) := by
  have hquad (u : TangentSpace I3 x) := Metric.tendstoUniformlyOn_iff.mp
    (slabComparison_ricciQuadratic_tendstoUniformlyOn L hle hk hcomp hab hsub x u)
  rw [Metric.tendstoUniformlyOn_iff]
  intro eta heta
  have he : 0 < eta / 2 := by positivity
  filter_upwards [hquad (v + w) (eta / 2) he, hquad v (eta / 2) he,
    hquad w (eta / 2) he] with i hsum hv hw
  intro t ht
  have hsum' := hsum t ht
  have hv' := hv t ht
  have hw' := hw t ht
  rw [Real.dist_eq] at hsum' hv' hw' ⊢
  rw [mappedRicciCoefficient_polarization,
    slabRicci_polarization (ricciTensor (I := I3) (g t) x) (ricciTensor_symm _ _) v w]
  obtain ⟨hsl, hsu⟩ := abs_lt.mp hsum'
  obtain ⟨hvl, hvu⟩ := abs_lt.mp hv'
  obtain ⟨hwl, hwu⟩ := abs_lt.mp hw'
  apply abs_lt.mpr
  constructor <;> linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
