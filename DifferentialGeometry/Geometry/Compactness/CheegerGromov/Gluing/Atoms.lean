import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.NormalBump


import DifferentialGeometry.Geometry.Compactness.CheegerGromov.CenterOfMass.Weights
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.ExponentialBallCovering
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Gluing.UniformData
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Set Bundle Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

noncomputable def gluingBump (lam : Real) (hlam : 0 < lam) : ContDiffBump (0 : Real) where
  rIn := (3 * lam) ^ 2
  rOut := (7 * lam / 2) ^ 2
  rIn_pos := sq_pos_of_pos (by positivity)
  rIn_lt_rOut := by nlinarith

@[simp] theorem gluing_bump_inner_radius (lam : Real) (hlam : 0 < lam) :
    (gluingBump lam hlam).rIn = (3 * lam) ^ 2 := rfl

@[simp] theorem gluing_bump_outer_radius (lam : Real) (hlam : 0 < lam) :
    (gluingBump lam hlam).rOut = (7 * lam / 2) ^ 2 := rfl

theorem gluing_bump_sqrt_outer_radius (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (gluingBump lam hlam).rOut = 7 * lam / 2 := by
  rw [gluing_bump_outer_radius, Real.sqrt_sq_eq_abs, abs_of_pos]
  positivity

theorem gluing_bump_outer_radius_lt (lam : Real) (hlam : 0 < lam) :
    Real.sqrt (gluingBump lam hlam).rOut < 4 * lam := by
  rw [gluing_bump_sqrt_outer_radius lam hlam]
  linarith

noncomputable def gluingAtom
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) : Y.M → Real :=
  letI : TopologicalSpace Y.M := Y.topology
  letI : ChartedSpace H Y.M := Y.charted
  letI : IsManifold I ∞ Y.M := Y.smooth
  letI : T2Space Y.M := Y.t2
  letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  quadNormal Y.metric p (gluingBump lam hlam)

omit [NeZero (Module.finrank ℝ E)] in
theorem gluing_atom_mem_Icc
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    gluingAtom Y p lam hlam q ∈ Set.Icc (0 : Real) 1 := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  exact quadNormal_mem_Icc Y.metric p (gluingBump lam hlam) q

omit [NeZero (Module.finrank ℝ E)] in
theorem gluing_atom_nonneg
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (p : Y.M)
    (lam : Real) (hlam : 0 < lam) (q : Y.M) :
    0 ≤ gluingAtom Y p lam hlam q :=
  (gluing_atom_mem_Icc Y p lam hlam q).1

theorem gluing_atom_mem_ball
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {p q : Y.M}
    (lam : Real) (hlam : 0 < lam)
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      4 * lam < expRadiusGp (I := I) Y.metric p)
    (hq : gluingAtom Y p lam hlam q ≠ 0) :
    letI : MetricSpace Y.M := P.ms
    q ∈ Metric.ball p (4 * lam) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  have hsupp : q ∈ Function.support
      (quadNormal Y.metric p (gluingBump lam hlam)) := by
    rw [Function.mem_support]
    simpa only [gluingAtom] using hq
  obtain ⟨v, hv, hqv⟩ := quadNormal_tsupport Y.metric p
    (gluingBump lam hlam) ((gluing_bump_outer_radius_lt lam hlam).trans hR)
    (subset_tsupport _ hsupp)
  have hsqrt_lt : Real.sqrt (Y.metric.inner p v v) < 4 * lam :=
    (Real.sqrt_le_sqrt hv).trans_lt (gluing_bump_outer_radius_lt lam hlam)
  have hsmall : Real.sqrt (Y.metric.inner p v v) <
      expRadiusGp (I := I) Y.metric p := hsqrt_lt.trans hR
  have hvnorm : ‖v‖ < expMapC2Radius (I := I) Y.metric p :=
    norm_lt_expMapC2Radius_of_sqrt_inner_lt (I := I) Y.metric p hsmall
  have hvtgt : v ∈ (normalChartAt (I := I) Y.metric p).target :=
    ball_subset_normalChartAt_target (I := I) Y.metric p hvnorm
  have hsymm : (normalChartAt (I := I) Y.metric p).symm v =
      expMap (I := I) Y.metric p (show TangentSpace I p from v) :=
    normalChartAt_symm_apply (I := I) Y.metric p hvtgt
  have hqexp : q =
      expMap (I := I) Y.metric p (show TangentSpace I p from v) :=
    hqv.symm.trans hsymm
  have hdist_eq : dist p q = Real.sqrt (Y.metric.inner p v v) := by
    rw [hqexp]
    exact properExpDist (I := I) Y P p hsmall
  rw [Metric.mem_ball, dist_comm, hdist_eq]
  exact hsqrt_lt

theorem gluing_atom_eq_dist
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (P : ProperMetricOn (I := I) Y) {p q : Y.M}
    (lam : Real) (hlam : 0 < lam)
    (hR :
      letI : TopologicalSpace Y.M := Y.topology
      letI : ChartedSpace H Y.M := Y.charted
      letI : IsManifold I ∞ Y.M := Y.smooth
      letI : T2Space Y.M := Y.t2
      letI : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
      4 * lam < expRadiusGp (I := I) Y.metric p) :
    letI : MetricSpace Y.M := P.ms
    gluingAtom Y p lam hlam q =
      gluingBump lam hlam ((dist p q) ^ 2) := by
  let : TopologicalSpace Y.M := Y.topology
  let : ChartedSpace H Y.M := Y.charted
  let : IsManifold I ∞ Y.M := Y.smooth
  let : T2Space Y.M := Y.t2
  let : T2Space (TangentBundle I Y.M) := Y.t2TangentBundle
  let : MetricSpace Y.M := P.ms
  have hlocal (hdist : dist p q < 4 * lam) :
      gluingAtom Y p lam hlam q =
        gluingBump lam hlam ((dist p q) ^ 2) := by
    obtain ⟨v, hvtgt, _hvdom, hvlen, hqexp⟩ :=
      properBallNormal (I := I) Y P hR (by
        rw [Metric.mem_ball, dist_comm]
        exact hdist)
    let ψ := normalChartAt (I := I) Y.metric p
    have hsymm : ψ.symm v =
        expMap (I := I) Y.metric p (show TangentSpace I p from v) := by
      simpa only [ψ] using
        normalChartAt_symm_apply (I := I) Y.metric p hvtgt
    have hqSymm : q = ψ.symm v := hqexp.trans hsymm.symm
    have hqsrc : q ∈ ψ.source := by
      rw [hqSymm]
      exact ψ.symm.map_source hvtgt
    have hchart : ψ q = v := by
      rw [hqSymm]
      exact ψ.toPartialEquiv.right_inv hvtgt
    have hquad_nonneg : 0 ≤ Y.metric.inner p v v := by
      exact (mul_nonneg
        (gpCoerciveConst_pos (I := I) Y.metric p).le
        (sq_nonneg ‖v‖)).trans
          (gpCoerciveConst_le (I := I) Y.metric p v)
    rw [gluingAtom, quadNormal_of_mem Y.metric p
      (gluingBump lam hlam) (by simpa only [ψ] using hqsrc)]
    rw [show normalChartAt (I := I) Y.metric p q = v by
      simpa only [ψ] using hchart]
    congr 1
    calc
      Y.metric.inner p v v =
          (Real.sqrt (Y.metric.inner p v v)) ^ 2 :=
        (Real.sq_sqrt hquad_nonneg).symm
      _ = (dist p q) ^ 2 := by rw [hvlen]
  by_cases hq : gluingAtom Y p lam hlam q = 0
  · by_cases hb : gluingBump lam hlam ((dist p q) ^ 2) = 0
    · exact hq.trans hb.symm
    · have hsupp : (dist p q) ^ 2 ∈
          Function.support (gluingBump lam hlam) := by
        simpa only [Function.mem_support] using hb
      rw [(gluingBump lam hlam).support_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (dist p q)), gluing_bump_outer_radius] at hsupp
      have hdist : dist p q < 4 * lam := by
        have hdist0 : 0 ≤ dist p q := dist_nonneg
        nlinarith
      exact False.elim (hb ((hlocal hdist).symm.trans hq))
  · have hmem := gluing_atom_mem_ball (I := I) Y P lam hlam hR hq
    have hdist : dist p q < 4 * lam := by
      simpa only [Metric.mem_ball, dist_comm] using hmem
    exact hlocal hdist

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

noncomputable def seqAtom (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) : (X.obj (L.φ k)).M → Real :=
  match seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => 0
  | some c => by
      letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      exact fun q =>
        gluingBump (L.lamInf (gamma : Nat))
          (hd.lambda_pos hD (L.rInf (gamma : Nat))) ((dist c q) ^ 2)


@[simp] theorem seqAtom_subseq (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) (k : Nat) (gamma : Fin (pb.A r)) :
    seqAtom hd hD P (L.subseq hψ) pb r k gamma =
      seqAtom hd hD P L pb r (ψ k) gamma := by
  funext y
  unfold seqAtom
  simp only [NetLimitData.subseq_phi, NetLimitData.subseq_lamInf,
    Function.comp_apply]
  cases hcenter : seqCenter hd D P (L.φ (ψ k)) (gamma : Nat) with
  | none => rfl
  | some c => congr 2


@[simp] theorem seqAtom_none (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r))
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = none) :
    seqAtom hd hD P L pb r k gamma = 0 := by
  simp [seqAtom, hc]


theorem seqAtom_some (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {c : (X.obj (L.φ k)).M}
    (hc : seqCenter hd D P (L.φ k) (gamma : Nat) = some c) :
    letI : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
    seqAtom hd hD P L pb r k gamma = fun q =>
      gluingBump (L.lamInf (gamma : Nat))
        (hd.lambda_pos hD (L.rInf (gamma : Nat))) ((dist c q) ^ 2) := by
  let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  simp [seqAtom, hc]

theorem seqAtom_contMDiff (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (hgp : ExponentialRadiusScaleAt (I := I) hd D P L pb r k) (gamma : Fin (pb.A r)) :
    letI : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
    letI : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
    letI : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
    letI : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
    letI : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
      (X.obj (L.φ k)).t2TangentBundle
    ContMDiff I (modelWithCornersSelf Real Real) ∞
      (seqAtom hd hD P L pb r k gamma) := by
  let : TopologicalSpace (X.obj (L.φ k)).M := (X.obj (L.φ k)).topology
  let : ChartedSpace H (X.obj (L.φ k)).M := (X.obj (L.φ k)).charted
  let : IsManifold I ∞ (X.obj (L.φ k)).M := (X.obj (L.φ k)).smooth
  let : T2Space (X.obj (L.φ k)).M := (X.obj (L.φ k)).t2
  let : T2Space (TangentBundle I (X.obj (L.φ k)).M) :=
    (X.obj (L.φ k)).t2TangentBundle
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      rw [seqAtom_none hd hD P L pb r k gamma hc]
      exact contMDiff_const
  | some c =>
      let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      let lam := L.lamInf (gamma : Nat)
      let hlam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      have hR : 4 * lam <
          expRadiusGp (I := I) (X.obj (L.φ k)).metric c := by
        simpa only [lam] using hgp gamma c hc
      have heq :
          (fun q => gluingBump lam hlam ((dist c q) ^ 2)) =
            gluingAtom (X.obj (L.φ k)) c lam hlam := by
        funext q
        exact (gluing_atom_eq_dist (I := I)
          (X.obj (L.φ k)) (P (L.φ k)) lam hlam hR).symm
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      rw [heq]
      simpa only [gluingAtom] using
        quadNormal_contMDiff (X.obj (L.φ k)).metric c
          (gluingBump lam hlam) ((gluing_bump_outer_radius_lt lam hlam).trans hR)


theorem seqAtom_Icc (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    seqAtom hd hD P L pb r k gamma q ∈ Set.Icc (0 : Real) 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none => simp [seqAtom, hc]
  | some c =>
      let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      exact ⟨(gluingBump _ _).nonneg, (gluingBump _ _).le_one⟩

theorem seqAtom_nonneg (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) (q : (X.obj (L.φ k)).M) :
    0 ≤ seqAtom hd hD P L pb r k gamma q :=
  (seqAtom_Icc hd hD P L pb r k gamma q).1


theorem seqAtom_one_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : q ∈ L.innerBall hd D P pb r k gamma) :
    seqAtom hd hD P L pb r k gamma q = 1 := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      simp [NetLimitData.innerBall, hc] at hq
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hdist_lt : dist c q < 3 * lam := by
        simpa only [NetLimitData.innerBall, hc, Metric.mem_ball, dist_comm] using hq
      rw [seqAtom_some hd hD P L pb r k gamma hc]
      apply (gluingBump lam hlam).one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg (dist c q)), gluing_bump_inner_radius]
      exact (sq_le_sq₀ dist_nonneg (by positivity)).2 hdist_lt.le

theorem seqAtom_one (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : q ∈ L.innerBall hd D P pb r k gamma) :
    seqAtom hd hD P L pb r k gamma q = 1 :=
  seqAtom_one_raw hd hD P L pb r k gamma hq


theorem seqAtom_mem_hat_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : seqAtom hd hD P L pb r k gamma q ≠ 0) :
    q ∈ L.hatBall hd D P pb r k gamma := by
  cases hc : seqCenter hd D P (L.φ k) (gamma : Nat) with
  | none =>
      exact False.elim (hq (by simp [seqAtom, hc]))
  | some c =>
      let lam := L.lamInf (gamma : Nat)
      have hlam : 0 < lam := hd.lambda_pos hD (L.rInf (gamma : Nat))
      let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
      have hsupp : (dist c q) ^ 2 ∈
          Function.support (gluingBump lam hlam) := by
        rw [Function.mem_support]
        simpa [seqAtom, hc, lam] using hq
      rw [(gluingBump lam hlam).support_eq, Metric.mem_ball,
        dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (dist c q)),
        gluing_bump_outer_radius] at hsupp
      simp only [NetLimitData.hatBall, hc, Metric.mem_ball]
      rw [dist_comm]
      have hdist0 : 0 ≤ dist c q := dist_nonneg
      nlinarith

theorem seqAtom_mem_hat (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (gamma : Fin (pb.A r)) {q : (X.obj (L.φ k)).M}
    (hq : seqAtom hd hD P L pb r k gamma q ≠ 0) :
    q ∈ L.hatBall hd D P pb r k gamma :=
  seqAtom_mem_hat_raw hd hD P L pb r k gamma hq

theorem seqWeights_data_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (i0 : Fin (pb.A r))
    {s : Set (X.obj (L.φ k)).M}
    (hcover : s ⊆ ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) :
    centerAverage.WeightDataOn s
      (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
      (rawWeights
        (cutRaw (seqAtom hd hD P L pb r k i0)
          (seqAtom hd hD P L pb r k) i0)) := by
  apply cutWeights_data
  · intro x _hx
    exact seqAtom_Icc hd hD P L pb r k i0 x
  · intro x _hx gamma
    exact seqAtom_nonneg hd hD P L pb r k gamma x
  · intro x hx
    obtain ⟨gamma, hgamma⟩ := Set.mem_iUnion.mp (hcover hx)
    refine ⟨gamma, ?_⟩
    rw [seqAtom_one_raw hd hD P L pb r k gamma hgamma]
    exact zero_lt_one
  · intro x _hx hne
    exact lt_of_le_of_ne (seqAtom_nonneg hd hD P L pb r k i0 x) (Ne.symm hne)
  · intro x _hx gamma hne
    exact seqAtom_mem_hat_raw hd hD P L pb r k gamma hne

theorem seqWeights_data (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (pb : hd.PackingBound D) (r : Real) (k : Nat)
    (i0 : Fin (pb.A r))
    {s : Set (X.obj (L.φ k)).M}
    (hcover : s ⊆ ⋃ gamma : Fin (pb.A r), L.innerBall hd D P pb r k gamma) :
    centerAverage.WeightDataOn s
      (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
      (rawWeights
        (cutRaw (seqAtom hd hD P L pb r k i0)
          (seqAtom hd hD P L pb r k) i0)) := by
  exact seqWeights_data_raw hd hD P L pb r k i0 hcover

theorem seqWeights_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    (r : Real) (i0 : Fin (pb.A r)) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k i0)
            (seqAtom hd hD P L pb r k) i0)) := by
  filter_upwards [L.innerBall_cover hd hD P hre pb r] with k hcover
  exact seqWeights_data hd hD P L pb r k i0 hcover


private theorem packA_pos (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    0 < pb.A r := by
  let O := (X.obj 0).basepoint
  have hself : hd.dist 0 O O = 0 := by
    have hz : ENNReal.ofReal (hd.dist 0 O O) = 0 := by
      let : EMetricSpace (X.obj 0).M := (X.obj 0).emetricSpace
      rw [← hre.edist_eq 0 O O, edist_self]
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (hre.dist_nonneg 0 O O)
  have hcard := pb.card_le 0 r ({O} : Finset (X.obj 0).M) (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst x
    change hd.dist 0 O O ≤ r
    simpa only [hself] using hr) (by
      intro x hx y hy hxy
      rw [Finset.mem_singleton] at hx hy
      exact False.elim (hxy (hx.trans hy.symm)))
  simpa only [Finset.card_singleton, Nat.succ_le_iff] using hcard

noncomputable def baseIndex (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    Fin (pb.A r) :=
  ⟨0, packA_pos hd hre pb hr⟩


@[simp] theorem baseIndex_val (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hre : hd.RealizesEdist) (pb : hd.PackingBound D) {r : Real} (hr : 0 ≤ r) :
    (baseIndex hd hre pb hr : Nat) = 0 := rfl

theorem seqAtom_base_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat) :
    seqAtom hd hD P L pb r k (baseIndex hd hre pb hr)
        (X.obj (L.φ k)).basepoint = 1 := by
  apply seqAtom_one_raw hd hD P L pb r k
  let : MetricSpace (X.obj (L.φ k)).M := (P (L.φ k)).ms
  simp only [NetLimitData.innerBall, baseIndex_val, seqCenter_zero, Metric.mem_ball,
    dist_self]
  exact mul_pos (by norm_num) (hd.lambda_pos hD (L.rInf 0))

theorem seqAtom_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    :
    seqAtom hd hD P L pb r k (baseIndex hd hre pb hr)
        (X.obj (L.φ k)).basepoint = 1 :=
  seqAtom_base_raw hd hD P L hre pb hr k

theorem seqWeights_base_raw (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat) :
    let i0 := baseIndex hd hre pb hr
    let num := cutRaw (seqAtom hd hD P L pb r k i0)
      (seqAtom hd hD P L pb r k) i0
    rawWeights num (X.obj (L.φ k)).basepoint i0 = 1 ∧
      ∀ j, j ≠ i0 → rawWeights num (X.obj (L.φ k)).basepoint j = 0 := by
  dsimp only
  have hbase := seqAtom_base_raw hd hD P L hre pb hr k
  have hdelta := cutRaw_delta
    (cut := seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
    (a := seqAtom hd hD P L pb r k) (i0 := baseIndex hd hre pb hr)
    (x := (X.obj (L.φ k)).basepoint) hbase
  apply rawWeights_delta (baseIndex hd hre pb hr) hdelta.2
  rw [hdelta.1, hbase]
  exact one_ne_zero

theorem seqWeights_base (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) (k : Nat)
    :
    let i0 := baseIndex hd hre pb hr
    let num := cutRaw (seqAtom hd hD P L pb r k i0)
      (seqAtom hd hD P L pb r k) i0
    rawWeights num (X.obj (L.φ k)).basepoint i0 = 1 ∧
      ∀ j, j ≠ i0 → rawWeights num (X.obj (L.φ k)).basepoint j = 0 :=
  seqWeights_base_raw hd hD P L hre pb hr k

theorem seqWeights_zero_ev (hd : InjRadiusDecayInput (I := I) X) {D : Real}
    (hD : 0 < D) (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData hd D P) (hre : hd.RealizesEdist) (pb : hd.PackingBound D)
    {r : Real} (hr : 0 ≤ r) :
    ∀ᶠ k in Filter.atTop,
      centerAverage.WeightDataOn (L.hatSourceBall hd P r k)
        (fun gamma : Fin (pb.A r) => L.hatBall hd D P pb r k gamma)
        (rawWeights
          (cutRaw (seqAtom hd hD P L pb r k (baseIndex hd hre pb hr))
            (seqAtom hd hD P L pb r k) (baseIndex hd hre pb hr))) :=
  seqWeights_ev hd hD P L hre pb r (baseIndex hd hre pb hr)

end HCGCompactness
end DifferentialGeometry
