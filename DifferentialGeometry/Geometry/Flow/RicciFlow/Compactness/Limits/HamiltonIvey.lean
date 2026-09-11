import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.CurvatureOperator
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.MaximumPrinciple
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.RescaledLimit

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

namespace SmoothCGHConverges

theorem curvatureOperator_nonnegative_of_parabolic_closed_flow
    [I.Boundaryless] [CompactSpace M]
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).regular)
    (basepoint : Nat → M)
    {L : PointedFlowData.{u, uE, uH} (I := I) D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I)
      (parabolicPointedFlowSeq (I := I) S hS time scale hscalePos htimeMem
        hcarrier hregular basepoint) L subseq)
    (hscale : Tendsto (fun k => scale (subseq k)) atTop atTop)
    {T t₀ : Real}
    (htime : Tendsto (fun k => time (subseq k)) atTop (𝓝 T))
    (ht₀T : t₀ < T)
    (hslab : ∀ u ∈ D₀.carrier, t₀ ≤ u → Set.Icc t₀ u ⊆ D₀.carrier)
    (hreg : ∀ u ∈ D₀.carrier, t₀ < u → Set.Ioo t₀ u ⊆ D₀.regular)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ t ∈ D.carrier, ∀ x : L.M,
      metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := L.M) := by
  let X := parabolicPointedFlowSeq (I := I) S hS time scale hscalePos htimeMem
    hcarrier hregular basepoint
  change SmoothCGHConverges (I := I) X L subseq at h
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : IsManifold I 2 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : IsManifold I 3 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  obtain ⟨K, hK, hinit⟩ := exists_pos_curvatureOperatorLowerBound
    (I := I) (M := M) (S.family.metric t₀) hdim
  intro t ht x
  let leastLimit := leastCurvatureOperatorEigenvalueAt (I := I)
    (L.S.family.metric t) x
    (metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x)
  let scalarSeq : Nat → Real := fun k =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I 1 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term (subseq k)).M := by
      change IsManifold I ∞ (X.term (subseq k)).M
      infer_instance
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    (X.term (subseq k)).S.scalar t (h.spatial.maps.map k x) / 2
  let leastSeq : Nat → Real := fun k =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I 1 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : IsManifold I 2 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : IsManifold I 3 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    leastCurvatureOperatorEigenvalueAt (I := I)
      ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)
      (metricAlgebraicCurvatureTensorAt (I := I)
        ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x))
  let sourceTime : Nat → Real := fun k =>
    parabolicTime (time (subseq k)) (scale (subseq k)) t
  let ageSeq : Nat → Real := fun k =>
    (1 + 2 * K * (sourceTime k - t₀)) / K
  let ageLimit : Real := (1 + 2 * K * (T - t₀)) / K
  have hinv : Tendsto (fun k => (scale (subseq k))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hscale
  have hdiv : Tendsto (fun k => t / scale (subseq k)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv)
  have hsourceTime : Tendsto sourceTime atTop (𝓝 T) := by
    simpa [sourceTime, parabolicTime] using htime.add hdiv
  have hage : Tendsto ageSeq atTop (𝓝 ageLimit) := by
    simpa [ageSeq, ageLimit] using
      ((tendsto_const_nhds.add
        (tendsto_const_nhds.mul (hsourceTime.sub_const t₀))).div_const K)
  have hageLimit : 0 < ageLimit := by
    dsimp [ageLimit]
    positivity
  have hscalar : Tendsto scalarSeq atTop (𝓝 (L.S.scalar t x / 2)) := by
    simpa [scalarSeq] using (h.scalar_converges t ht x).div_const 2
  have hleast : ∀ ε : Real, 0 < ε →
      ∀ᶠ k in atTop, leastSeq k < leastLimit + ε := by
    intro ε hε
    simpa [leastSeq, leastLimit] using
      h.leastCurvatureOperatorEigenvalueAt_eventually_lt_add hdim t ht x ε hε
  have hafter : ∀ᶠ k in atTop, t₀ < sourceTime k := by
    exact hsourceTime (Ioi_mem_nhds ht₀T)
  have hbound : ∀ᶠ k in atTop, leastSeq k < 0 →
      scalarSeq k ≥ (-leastSeq k) *
        (Real.log (ageSeq k * scale (subseq k) * (-leastSeq k)) - 3) := by
    filter_upwards [hafter] with k htimeAfter
    intro hleastNeg
    let i := subseq k
    let : TopologicalSpace (X.term i).M := (X.term i).topology
    let : ChartedSpace H (X.term i).M := (X.term i).charted
    let : IsManifold I ∞ (X.term i).M := (X.term i).smooth
    let : IsManifold I 1 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
    let : IsManifold I 2 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
    let : IsManifold I 3 (X.term i).M :=
      IsManifold.of_le (I := I) (M := (X.term i).M) (n := ∞) (by decide)
    let : IsManifold I ((∞ : WithTop ℕ∞) + 1) (X.term i).M := by
      change IsManifold I ∞ (X.term i).M
      infer_instance
    let : SigmaCompactSpace (X.term i).M := (X.term i).sigmaCompact
    let : T2Space (X.term i).M := (X.term i).t2
    let y : M := by
      exact h.spatial.maps.map k x
    let u := sourceTime k
    have huMem : u ∈ D₀.carrier := by
      have hu := hcarrier i ht
      simpa [X, i, u, sourceTime] using hu
    have htimeAfter' : t₀ < u := by
      exact htimeAfter
    have hinit' : ∀ z : M,
        curvatureOperatorLowerBoundAt (I := I) (S.base.metric t₀) z
          ⟨S.base.rm04 t₀ z, metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) (S.base.metric t₀) z⟩ K := by
      intro z
      exact hinit z
    have hpinching := (hamilton_ivey_pinching (I := I) (M := M) S hS
      (T := u - t₀) (by linarith) hK
      (by simpa [show t₀ + (u - t₀) = u by ring] using
        hslab u huMem (le_of_lt htimeAfter'))
      (by simpa [show t₀ + (u - t₀) = u by ring] using
        hreg u huMem htimeAfter') hdim hinit').2
    let leastOriginal := leastCurvatureOperatorEigenvalueAt (I := I)
      (S.family.metric u) y
      (metricAlgebraicCurvatureTensorAt (I := I) (S.family.metric u) y)
    let leastRescaled := leastCurvatureOperatorEigenvalueAt (I := I)
      ((X.term i).S.family.metric t) y
      (metricAlgebraicCurvatureTensorAt (I := I) ((X.term i).S.family.metric t) y)
    have hleastEq : leastRescaled = (scale i)⁻¹ * leastOriginal := by
      dsimp [leastRescaled]
      rw [show (X.term i).S.family.metric t =
          scaleMetric (I := I) (scale i) (hscalePos i) (S.family.metric u) by
        simpa [X, i, u, sourceTime] using
          parabolicPointedFlowSeq_metric (I := I) S hS time scale hscalePos htimeMem
            hcarrier hregular basepoint i t]
      exact leastCurvatureOperatorEigenvalueAt_scaleMetric
        (I := I) (scale i) (hscalePos i) (S.family.metric u) y
          (by change Module.finrank Real E = 3; exact hdim)
    have hleastRescaledNeg : leastRescaled < 0 := by
      exact hleastNeg
    have hleastOriginalNeg : leastOriginal < 0 := by
      rw [hleastEq] at hleastRescaledNeg
      nlinarith [inv_pos.mpr (hscalePos i)]
    have huIcc : u ∈ Set.Icc t₀ (t₀ + (u - t₀)) := by
      constructor <;> linarith
    have hpinch := hpinching u huIcc y hleastOriginalNeg
    change S.scalar u y ≥
      2 * (-leastOriginal) *
        (Real.log ((-leastOriginal) / K) +
          Real.log (1 + 2 * K * (u - t₀)) - 3) at hpinch
    have hscalarEq : (X.term i).S.scalar t y =
        (scale i)⁻¹ * S.scalar u y := by
      simp [X, i, u, sourceTime]
    have hdenPos : 0 < 1 + 2 * K * (u - t₀) := by
      positivity
    have hproduct :
        ageSeq k * scale i * (-leastRescaled) =
          ((-leastOriginal) / K) * (1 + 2 * K * (u - t₀)) := by
      rw [hleastEq]
      dsimp [ageSeq, u, i]
      field_simp [ne_of_gt (hscalePos (subseq k)), ne_of_gt hK]
    have hlog :
        Real.log (ageSeq k * scale i * (-leastRescaled)) =
          Real.log ((-leastOriginal) / K) + Real.log (1 + 2 * K * (u - t₀)) := by
      rw [hproduct, Real.log_mul]
      · exact div_ne_zero (ne_of_gt (by linarith : 0 < -leastOriginal)) (ne_of_gt hK)
      · exact ne_of_gt hdenPos
    change (X.term i).S.scalar t y / 2 ≥
      (-leastRescaled) *
        (Real.log (ageSeq k * scale i * (-leastRescaled)) - 3)
    rw [hscalarEq, hlog, hleastEq]
    have hscaled := mul_le_mul_of_nonneg_left hpinch
      (le_of_lt (inv_pos.mpr (hscalePos i)))
    nlinarith
  apply
    (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      (I := I) (x := x)
      (A := metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x)
      (L.S.family.metric t) (by change Module.finrank Real E = 3; exact hdim)).mp
  change 0 ≤ leastLimit
  exact nonnegative_of_hamilton_ivey_rescaled_upper_limit
    (L.S.scalar t x / 2) leastLimit ageLimit scalarSeq leastSeq
      (fun k => scale (subseq k)) ageSeq hscalar hleast hscale hage hageLimit hbound

theorem leastCurvatureOperatorEigenvalueAt_nonnegative_of_parabolic_closed_flow
    [I.Boundaryless] [CompactSpace M]
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).regular)
    (basepoint : Nat → M)
    {L : PointedFlowData.{u, uE, uH} (I := I) (D := D)}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I)
      (parabolicPointedFlowSeq (I := I) S hS time scale hscalePos htimeMem
        hcarrier hregular basepoint) L subseq)
    (hscale : Tendsto (fun k => scale (subseq k)) atTop atTop)
    {T t₀ : Real}
    (htime : Tendsto (fun k => time (subseq k)) atTop (𝓝 T))
    (ht₀T : t₀ < T)
    (hslab : ∀ u ∈ D₀.carrier, t₀ ≤ u → Set.Icc t₀ u ⊆ D₀.carrier)
    (hreg : ∀ u ∈ D₀.carrier, t₀ < u → Set.Ioo t₀ u ⊆ D₀.regular)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ t ∈ D.carrier, ∀ x : L.M,
      0 ≤ leastCurvatureOperatorEigenvalueAt (I := I)
        (L.S.family.metric t) x
        (metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  have hcone := curvatureOperator_nonnegative_of_parabolic_closed_flow
    (I := I) S hS time scale hscalePos htimeMem hcarrier hregular basepoint h
      hscale htime ht₀T hslab hreg hdim
  intro t ht x
  exact
    (zero_le_leastCurvatureOperatorEigenvalueAt_iff_mem_curvatureOperatorNonnegativeCone
      (I := I) (x := x)
      (A := metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x)
      (L.S.family.metric t) (by change Module.finrank Real E = 3; exact hdim)).mpr
      (hcone t ht x)

theorem curvatureOperator_nonnegative_of_parabolic_closed_flow_on_compact_windows
    [I.Boundaryless] [CompactSpace M]
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ D₀.carrier)
    (basepoint : Nat → M)
    {L : PointedFlowData.{u, uE, uH} (I := I) D}
    (hconverges : ∀ (a b : Real) (hab : a ≤ b)
      (hcar : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular),
      ∃ N : Nat,
      ∃ hcarrier : ∀ i,
        Set.Icc a b ⊆
          (parabolicInterval D₀ (time (i + N)) (scale (i + N)) (htimeMem (i + N))).carrier,
      ∃ hregular : ∀ i,
        Set.Ioo a b ⊆
          (parabolicInterval D₀ (time (i + N)) (scale (i + N)) (htimeMem (i + N))).regular,
      Nonempty (SmoothCGHConverges (I := I)
        (parabolicPointedFlowSeq (D := RealTimeInterval.closed a b hab) S hS
          (fun i => time (i + N)) (fun i => scale (i + N))
          (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N))
          hcarrier hregular (fun i => basepoint (i + N)))
        (L.timeRestrict (RealTimeInterval.closed a b hab) hcar hreg) id))
    (hscale : Tendsto scale atTop atTop)
    {T t₀ : Real}
    (htime : Tendsto time atTop (𝓝 T))
    (ht₀T : t₀ < T)
    (hslab : ∀ u ∈ D₀.carrier, t₀ ≤ u → Set.Icc t₀ u ⊆ D₀.carrier)
    (hreg : ∀ u ∈ D₀.carrier, t₀ < u → Set.Ioo t₀ u ⊆ D₀.regular)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ t ∈ D.carrier, ∀ x : L.M,
      metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := L.M) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  intro t ht x
  have hcar : Set.Icc t t ⊆ D.carrier := by
    simpa only [Set.Icc_self, Set.singleton_subset_iff] using ht
  have hreg' : Set.Ioo t t ⊆ D.regular := by
    simp only [Set.Ioo_self, Set.empty_subset]
  obtain ⟨N, hcarrier, hregular, ⟨h⟩⟩ := hconverges t t le_rfl hcar hreg'
  have hcone := curvatureOperator_nonnegative_of_parabolic_closed_flow
    (I := I) S hS (fun i => time (i + N)) (fun i => scale (i + N))
    (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N)) hcarrier hregular
    (fun i => basepoint (i + N)) h
    (hscale.comp (tendsto_add_atTop_nat N))
    (htime.comp (tendsto_add_atTop_nat N)) ht₀T hslab hreg hdim
  exact hcone t ⟨le_rfl, le_rfl⟩ x

theorem curvatureOperator_nonnegative_of_closed_blowup_limit
    [I.Boundaryless] [CompactSpace M]
    {D : RealTimeInterval}
    {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ (RealTimeInterval.closedOpen 0 T hT).carrier)
    (basepoint : Nat → M)
    {L : PointedFlowData.{u, uE, uH} (I := I) D}
    (hconverges : ∀ (a b : Real) (hab : a ≤ b)
      (hcar : Set.Icc a b ⊆ D.carrier) (hreg : Set.Ioo a b ⊆ D.regular),
      ∃ N : Nat,
      ∃ hcarrier : ∀ i,
        Set.Icc a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).carrier,
      ∃ hregular : ∀ i,
        Set.Ioo a b ⊆
          (parabolicInterval (RealTimeInterval.closedOpen 0 T hT)
            (time (i + N)) (scale (i + N)) (htimeMem (i + N))).regular,
      Nonempty (SmoothCGHConverges (I := I)
        (parabolicPointedFlowSeq (D := RealTimeInterval.closed a b hab) S hS
          (fun i => time (i + N)) (fun i => scale (i + N))
          (fun i => hscalePos (i + N)) (fun i => htimeMem (i + N))
          hcarrier hregular (fun i => basepoint (i + N)))
        (L.timeRestrict (RealTimeInterval.closed a b hab) hcar hreg) id))
    (hscale : Tendsto scale atTop atTop)
    (htime : Tendsto time atTop (𝓝 T))
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    ∀ t ∈ D.carrier, ∀ x : L.M,
      metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := L.M) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  exact curvatureOperator_nonnegative_of_parabolic_closed_flow_on_compact_windows
    (I := I) S hS time scale hscalePos htimeMem basepoint hconverges hscale htime hT
    (fun u hu _ v hv => ⟨hv.1, lt_of_le_of_lt hv.2 hu.2⟩)
    (fun u hu _ v hv => ⟨hv.1, lt_trans hv.2 hu.2⟩) hdim

end SmoothCGHConverges

end DifferentialGeometry.CheegerGromovCompactness
