import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Metric.Bounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.ChartFamily
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Construction
import DifferentialGeometry.Analysis.Calculus.QuadraticEvaluationConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Average.Weights.Convergence
import DifferentialGeometry.Analysis.Calculus.BilinearFormCompactness
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.AtomWeights
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.CenterIndexing

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set
open scoped ContDiff Topology

namespace DifferentialGeometry
namespace HCGCompactness

section OriginMetric

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open scoped Manifold

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] in
theorem quadNormal_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (f : ContDiffBump (0 : Real)) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    quadNormal Y.metric gamma f (expMapDiffeo (I := I) Y.metric beta z) =
      f (normalCoordMetric (I := I) Y gamma 0
        (normalTransition (I := I) Y beta gamma z)
        (normalTransition (I := I) Y beta gamma z)) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  rw [quadNormal_of_mem Y.metric gamma f hsrc,
    normal_coord_metric_zero (I := I) Y gamma]
  rfl

omit [NeZero (Module.finrank ℝ E)] in
theorem gluing_atom_readout
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) {z : E}
    (hsrc :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      expMapDiffeo (I := I) Y.metric beta z ∈
        (normalChartAt (I := I) Y.metric gamma).source) :
    letI : TopologicalSpace Y.M := Y.topology
    letI : ChartedSpace H Y.M := Y.charted
    letI : IsManifold I ∞ Y.M := Y.smooth
    letI : T2Space Y.M := Y.t2
    letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
    gluingAtom Y gamma lam hlam (expMapDiffeo (I := I) Y.metric beta z) =
      gluingBump lam hlam
        (normalCoordMetric (I := I) Y gamma 0
          (normalTransition (I := I) Y beta gamma z)
          (normalTransition (I := I) Y beta gamma z)) := by
  exact quadNormal_readout (I := I) Y beta gamma (gluingBump lam hlam) hsrc

noncomputable def gluingAtomOn
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) (c : NormalChartAt (I := I) Y beta)
    (z : E) : Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  gluingAtom Y gamma lam hlam (c.hom z)

noncomputable def gluingAtomChart
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (beta gamma : Y.M)
    (lam : Real) (hlam : 0 < lam) (z : E) : Real :=
  gluingAtomOn (I := I) Y beta gamma lam hlam
    (c2RadiusNormalBallChart (I := I) Y beta) z

noncomputable def seqAtomOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    (k : Nat) (z : E) : Real :=
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  seqAtom hd hD P L pb r k gamma
    ((chart (L.φ k) (beta k)).hom z)

noncomputable def seqAtomChart
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    (k : Nat) (z : E) : Real :=
  letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  seqAtom hd hD P L pb r k gamma
    (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)

omit [CompleteSpace E] in
@[simp] theorem seqAtomOn_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) (k : Nat) :
    seqAtomOn (I := I) chart hd hD P (L.subseq hψ) pb r
        (fun j => beta (ψ j)) gamma k =
      seqAtomOn (I := I) chart hd hD P L pb r beta gamma (ψ k) := by
  unfold seqAtomOn
  simp only [seqAtom_subseq]
  rfl

@[simp] theorem seqAtomChart_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {ψ : Nat -> Nat} (hψ : StrictMono ψ) (k : Nat) :
    seqAtomChart (I := I) hd hD P (L.subseq hψ) pb r
        (fun j => beta (ψ j)) gamma k =
      seqAtomChart (I := I) hd hD P L pb r beta gamma (ψ k) := by
  exact seqAtomOn_subseq (I := I) (c2RadiusNormalChartFamily (I := I) X)
    hd hD P L pb r beta gamma hψ k

theorem seqAtomOn_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (chart : NormalChartFamily (I := I) X)
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E}
    (hUx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E) (chart (L.φ k) (beta k)).radius) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (seqAtomOn (I := I) chart hd hD P L pb r beta gamma k) U := by
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (seqAtom hd hD P L pb r k gamma ∘
        fun z => (chart (L.φ k) (beta k)).hom z) U
  exact (seqAtom_contMDiff (I := I) hd hD P L pb r k hgp gamma).comp_contMDiffOn
    ((chart (L.φ k) (beta k)).smooth_to.mono hUx)

theorem seqAtomChart_smooth
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E}
    (hUx :
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      U ⊆ Metric.ball (0 : E)
        (expMapC2Radius (I := I) (X.obj (L.φ k)).metric (beta k))) :
    ContDiffOn Real (∞ : WithTop ℕ∞)
      (seqAtomChart (I := I) hd hD P L pb r beta gamma k) U := by
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  rw [← contMDiffOn_iff_contDiffOn]
  change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (seqAtom hd hD P L pb r k gamma ∘
        fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) U
  exact (seqAtom_contMDiff (I := I) hd hD P L pb r k hgp gamma).comp_contMDiffOn
    ((exp_map_diffeo_cont_mdiff_on_exp_ball (I := I) (X.obj (L.φ k)) (beta k)).mono hUx)

theorem seqAtom_live_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (hgp : ∀ k, ExponentialRadiusScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U) {ainf : E -> Real}
    (hgamma : L.alive (gamma : Nat) = true)
    (hconv : MapCInfConvOnCompacts U
      (fun k => gluingAtomChart (I := I) (X.obj (L.φ k)) (beta k)
        (seqCenterD hd P L k (gamma : Nat)) (L.lamInf (gamma : Nat))
        (hd.lambda_pos hD (L.rInf (gamma : Nat)))) ainf) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k) ainf := by
  refine hconv.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [seqCenterD_live hd P L (gamma : Nat) hgamma] with k hk
  intro z _hz
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  let q := expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z
  have hR : 4 * L.lamInf (gamma : Nat) <
      expRadiusGp (I := I) (X.obj (L.φ k)).metric
        (seqCenterD hd P L k (gamma : Nat)) :=
    hgp k gamma (seqCenterD hd P L k (gamma : Nat)) hk
  change seqAtom hd hD P L pb r k gamma q =
    gluingAtom (X.obj (L.φ k)) (seqCenterD hd P L k (gamma : Nat))
      (L.lamInf (gamma : Nat))
      (hd.lambda_pos hD (L.rInf (gamma : Nat))) q
  rw [seqAtom_some hd hD P L pb r k gamma hk]
  exact (gluing_atom_eq_dist (I := I) (X.obj (L.φ k)) (P (L.φ k))
    (L.lamInf (gamma : Nat))
    (hd.lambda_pos hD (L.rInf (gamma : Nat))) hR).symm

theorem seqAtom_dead_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U) (hgamma : L.alive (gamma : Nat) = false) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [seqCenter_dead hd P L (gamma : Nat) hgamma] with k hk
  intro z _hz
  simp [seqAtomChart,     seqAtom_none hd hD P L pb r k gamma hk]

theorem atom_disjoint_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) (alpha gamma : Fin (pb.A r))
    {U : Set E} (hU : IsOpen U)
    (hsource : ∀ᶠ k in Filter.atTop,
      letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
      letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
      letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
      letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
        (X.obj (L.φ k)).t2TangentBundle
      Set.MapsTo
        (fun z => expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z)
        U (L.hatBall hd D P pb r k alpha))
    (hdisjoint : ∀ᶠ k in Filter.atTop,
      ¬ BInter hd D P L.lamInf (alpha : Nat) (gamma : Nat) (L.φ k)) :
    MapCInfConvOnCompacts U
      (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
      (fun _ => 0) := by
  have hzero : MapCInfConvOnCompacts U
      (fun _ : Nat => fun _ : E => (0 : Real)) (fun _ => 0) :=
    mapCInfConv_const (fun _ : E => (0 : Real))
  refine hzero.congr_eventually hU ?_ fun _ _ => rfl
  filter_upwards [hsource, hdisjoint] with k hsourceK hdisjointK
  intro z hz
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  by_contra hne
  apply hdisjointK
  change seqAtom hd hD P L pb r k gamma
      (expMapDiffeo (I := I) (X.obj (L.φ k)).metric (beta k) z) ≠ 0 at hne
  exact L.binter_of_mem_hat hd hD P pb r k (hsourceK hz)
    (seqAtom_mem_hat hd hD P L pb r k gamma hne)

theorem seqAtoms_conv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (hd : InjectivityRadiusDecay (I := I) X) {D : Real} (hD : 0 < D)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    (hgp : ∀ k, ExponentialRadiusScaleAt (I := I) hd D P L pb r k)
    (beta : ∀ k : Nat, (X.obj (L.φ k)).M) {U : Set E} (hU : IsOpen U)
    (ainf : Fin (pb.A r) -> E -> Real)
    (hlive : ∀ gamma : Fin (pb.A r), L.alive (gamma : Nat) = true ->
      MapCInfConvOnCompacts U
        (fun k => gluingAtomChart (I := I) (X.obj (L.φ k)) (beta k)
          (seqCenterD hd P L k (gamma : Nat)) (L.lamInf (gamma : Nat))
          (hd.lambda_pos hD (L.rInf (gamma : Nat)))) (ainf gamma)) :
    ∀ gamma : Fin (pb.A r),
      MapCInfConvOnCompacts U
        (fun k => seqAtomChart (I := I) hd hD P L pb r beta gamma k)
        (if L.alive (gamma : Nat) = true then ainf gamma else fun _ => 0) := by
  intro gamma
  cases hgamma : L.alive (gamma : Nat) with
  | false =>
      simpa only [hgamma, Bool.false_eq_true, ↓reduceIte] using
        seqAtom_dead_conv (I := I) hd hD P L pb r beta gamma hU hgamma
  | true =>
      simpa only [hgamma, ↓reduceIte] using
        seqAtom_live_conv (I := I) hd hD P L pb r hgp beta gamma hU hgamma
          (hlive gamma hgamma)

omit [NeZero (Module.finrank ℝ E)] in
theorem gluing_atom_converges {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (center : ι -> forall k : Nat, (X.obj k).M)
    (beta : forall k : Nat, (X.obj k).M)
    (lam : ι -> Real) (hlam : forall i, 0 < lam i)
    {U : Set E} (hU : IsOpen U)
    {gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))}
    (hg : MapCInfConvOnCompacts U
      (fun k _ i => normalCoordMetric (I := I) (X.obj k) (center i k) 0) gInf)
    (hginf : ContDiffOn Real (∞ : WithTop ℕ∞) gInf U)
    {Jinf : ι -> E -> E}
    (hJ : forall i, MapCInfConvOnCompacts U
      (fun k => normalTransition (I := I) (X.obj k) (beta k) (center i k))
      (Jinf i))
    (hJc : forall i k, ContDiffOn Real (∞ : WithTop ℕ∞)
      (normalTransition (I := I) (X.obj k) (beta k) (center i k)) U)
    (hJinfc : forall i, ContDiffOn Real (∞ : WithTop ℕ∞) (Jinf i) U)
    (hsrc : forall i k z, z ∈ U ->
      letI : TopologicalSpace (X.obj k).M := (X.obj k).topology
      letI : ChartedSpace H (X.obj k).M := (X.obj k).charted
      letI : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      letI : T2Space (X.obj k).M := (X.obj k).t2
      letI : T2Space (TangentBundle I (X.obj k).M) := (X.obj k).t2TangentBundle
      expMapDiffeo (I := I) (X.obj k).metric (beta k) z ∈
        (normalChartAt (I := I) (X.obj k).metric (center i k)).source)
    (i : ι) :
    MapCInfConvOnCompacts U
      (fun k => gluingAtomChart (I := I) (X.obj k) (beta k) (center i k)
        (lam i) (hlam i))
      (fun z => gluingBump (lam i) (hlam i)
        (gInf z i (Jinf i z) (Jinf i z))) := by
  have hraw := quadPiBump_conv hU hg (hJ i)
    (fun _ => contDiffOn_const) hginf (hJc i) (hJinfc i)
    i (gluingBump (lam i) (hlam i)) (gluingBump (lam i) (hlam i)).contDiff
  refine hraw.congr hU (fun k z hz => ?_) (fun _ _ => rfl)
  simpa only [gluingAtomChart, gluingAtomOn, c2_radius_normal_ball_chart_apply] using
    (gluing_atom_readout (I := I) (X.obj k) (beta k) (center i k)
      (lam i) (hlam i) (hsrc i k z hz))

omit [NeZero (Module.finrank ℝ E)] in
theorem existsOriginMetric
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    (c : forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (E →L[Real] E →L[Real] Real)),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ => normalCoordMetric (I := I) (X.obj (phi k)) (c (phi k)) 0)
          gInf ∧
        forall z : E, forall v : E,
          (1 / 2 : Real) * ‖v‖ ^ 2 <= gInf z v v ∧
            gInf z v v <= 2 * ‖v‖ ^ 2 := by
  let g0 : Nat -> E -> (E →L[Real] E →L[Real] Real) :=
    fun k _ => normalCoordMetric (I := I) (X.obj k) (c k) 0
  have hzero : forall k, (0 : E) ∈ Metric.ball 0 (input.radius k (c k)) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c k) 0 (hzero k))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  have hequiv : forall k : Nat, forall z, z ∈ (Set.univ : Set E) -> forall v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 <= g0 k z v v ∧
        g0 k z v v <= 2 * ‖v‖ ^ 2 := by
    intro k _z _hz v
    exact input.metric_equiv k (c k) 0 (hzero k) v
  simpa only [g0, Set.mem_univ, forall_const] using
    (exists_smooth_bilinear_form_limit_subsequence_on (E := E) isOpen_univ g0
      hsmooth hbdd (1 / 2) 2 hequiv)

omit [NeZero (Module.finrank ℝ E)] in
theorem existsMetric0Univ {ι : Type*} [Fintype ι]
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    (c : ι -> forall k : Nat, (X.obj k).M) :
    exists (phi : Nat -> Nat)
        (gInf : E -> (ι -> (E →L[Real] E →L[Real] Real))),
      StrictMono phi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ i => normalCoordMetric (I := I) (X.obj (phi k))
            (c i (phi k)) 0)
          gInf := by
  let g0 : Nat -> E -> (ι -> (E →L[Real] E →L[Real] Real)) :=
    fun k _ i => normalCoordMetric (I := I) (X.obj k) (c i k) 0
  have hzero : forall k i,
      (0 : E) ∈ Metric.ball 0 (input.radius k (c i k)) := by
    intro k i
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos k (c i k)
  have hsmooth : forall k, ContDiffOn Real (∞ : WithTop ℕ∞) (g0 k) Set.univ :=
    fun _ => contDiffOn_const
  have hbdd : forall r : Nat, forall K : Set E, IsCompact K -> K ⊆ Set.univ ->
      exists M : Real, forall k : Nat, forall x, x ∈ K ->
        ‖iteratedFDeriv Real r (g0 k) x‖ <= M := by
    intro r K _hK _hKU
    refine ⟨input.metricC 0, fun k x _hx => ?_⟩
    by_cases hr : r = 0
    · subst r
      rw [norm_iteratedFDeriv_zero, pi_norm_le_iff_of_nonneg (input.metricC_nonneg 0)]
      intro i
      simpa only [g0, norm_iteratedFDeriv_zero] using
        (input.metric_deriv k 0 (c i k) 0 (hzero k i))
    · simp only [g0, iteratedFDeriv_const_of_ne hr, Pi.zero_apply, norm_zero]
      exact input.metricC_nonneg 0
  obtain ⟨phi, gInf, hphi, hginf, hconv⟩ :=
    exists_cInf_subseq_on isOpen_univ g0 hsmooth hbdd
  simpa only [g0] using ⟨phi, gInf, hphi, hginf, hconv⟩

theorem existsLiveMetric0
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) :
    exists (psi : Nat -> Nat)
        (gInf : E -> (LiveSlot L pb r -> (E →L[Real] E →L[Real] Real))),
      StrictMono psi ∧ ContDiffOn Real (∞ : WithTop ℕ∞) gInf Set.univ ∧
        MapCInfConvOnCompacts Set.univ
          (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
            (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
          gInf := by
  classical
  let X' := X.subseq L.φ
  let input' : NormalCoordMetricBounds (I := I) X' := input.subseq L.φ
  let c : LiveSlot L pb r -> forall k : Nat, (X'.obj k).M :=
    fun gamma k => seqCenterD hd P L k (gamma.1 : Nat)
  obtain ⟨psi, gInf, hpsi, hginf, hconv⟩ :=
    existsMetric0Univ (I := I) input' c
  refine ⟨psi, gInf, hpsi, hginf, ?_⟩
  simpa only [X', c, PointedRiemannianSeq.subseq] using hconv

theorem liveMetric0_equiv
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (input : NormalCoordMetricBounds (I := I) X)
    {hd : InjectivityRadiusDecay (I := I) X} {D : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {psi : Nat → Nat}
    {gInf : E → (LiveSlot L pb r → (E →L[Real] E →L[Real] Real))}
    (hconv : MapCInfConvOnCompacts Set.univ
      (fun k _ gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      gInf) :
    ∀ gamma : LiveSlot L pb r, ∀ v : E,
      (1 / 2 : Real) * ‖v‖ ^ 2 ≤ gInf 0 gamma v v ∧
        gInf 0 gamma v v ≤ 2 * ‖v‖ ^ 2 := by
  intro gamma v
  have htendAll : Filter.Tendsto
      (fun k gamma => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      Filter.atTop (𝓝 (gInf 0)) :=
    tendsto_of_cInf hconv (Set.mem_univ 0)
  have htend : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0)
      Filter.atTop (𝓝 (gInf 0 gamma)) :=
    (tendsto_pi_nhds.mp htendAll) gamma
  have hcont : Continuous
      (fun c : E →L[Real] E →L[Real] Real => c v v) := by
    fun_prop
  have htendv : Filter.Tendsto
      (fun k => normalCoordMetric (I := I) (X.obj (L.φ (psi k)))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 v v)
      Filter.atTop (𝓝 (gInf 0 gamma v v)) :=
    (hcont.tendsto (gInf 0 gamma)).comp htend
  have hzero : ∀ k : Nat, (0 : E) ∈ Metric.ball 0
      (input.radius (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat))) := by
    intro k
    rw [Metric.mem_ball, dist_self]
    exact input.radius_pos _ _
  exact ⟨
    ge_of_tendsto htendv (Filter.Eventually.of_forall fun k =>
      (input.metric_equiv (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 (hzero k) v).1),
    le_of_tendsto htendv (Filter.Eventually.of_forall fun k =>
      (input.metric_equiv (L.φ (psi k))
        (seqCenterD hd P L (psi k) (gamma.1 : Nat)) 0 (hzero k) v).2)⟩

end OriginMetric

end HCGCompactness
end DifferentialGeometry
