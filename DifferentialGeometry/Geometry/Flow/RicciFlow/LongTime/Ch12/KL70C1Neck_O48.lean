import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70C1Core_O39
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.KL70SubBinders_O38
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TruncatedNeckScalar
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Metric.Pullback.LocalRestriction
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# CH12-O48, group 1: KL70.2 C1 in the shape of O38's `hC1` (`[FROZEN] CH12-O48 G1`)

* `strongNeck_scalar_sub_le_O48` / `strongNeck_scalar_le_O48`: on the whole strong-neck region
  `map '' (S² × (-ε⁻¹, ε⁻¹))` and the whole window `[t - Q⁻¹, t]`, `R ≤ (1 + 2400 ε) Q`
  (the proof of `TruncatedNeck.abs_scalar_center_sub_le` at every neck point).
* `C1_neck_region_O48`: shrink the hStrong v2 open `U` to the neck region `U'` (local pull-back of
  the flow along `Opens.inclusion`); full-window Hamilton–Ivey on the trace then gives
  `sec ≥ -η R(x)` on all of `U'` with `η = Φ((1 + 2400 ε) R) / R` (closes finding D2 of O39).
* `hC1_O48`: the `hC1` binder of `hNoEscPos_of_ABC_O38` from hStrong v2 and the cap-exclusion
  binder `hCapEx` (finding D1 of O39, frozen as inline hypothesis).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set Filter Topology
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace GC.LongTime.Ch12

universe u

private instance kl70C1NeckSphereFact_O48 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

private theorem abs_trace_le_of_sqrt_inner_bound_O48
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    (g : SmoothRiemannianMetric I N) (x : N)
    (A : TangentSpace I x →ₗ[ℝ] TangentSpace I x) (c : ℝ)
    (hA : ∀ v, Real.sqrt (g.inner x (A v) (A v)) ≤ c * Real.sqrt (g.inner x v v)) :
    |LinearMap.trace ℝ (TangentSpace I x) A| ≤ (Module.finrank ℝ E : ℝ) * c := by
  classical
  obtain ⟨b, hb⟩ := DifferentialGeometry.Tensor0SBundle.exists_orthonormal_basis (I := I) g x
  have hinv := DifferentialGeometry.Tensor0SBundle.metricInverseInBasis_of_orthonormal
    (I := I) g b hb
  have hdiag (i : Fin (Module.finrank ℝ (TangentSpace I x))) :
      b.repr (A (b i)) i = g.inner x (A (b i)) (b i) := by
    rw [DifferentialGeometry.Tensor0SBundle.basis_repr_eq_sum_inv_inner (I := I) g x b _ hinv]
    simp [DifferentialGeometry.Tensor0SBundle.identityInvMetric,
      DifferentialGeometry.Tensor0SBundle.diagonalInvMetric]
  have htrace : LinearMap.trace ℝ (TangentSpace I x) A =
      ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)), g.inner x (A (b i)) (b i) := by
    rw [LinearMap.trace_eq_matrix_trace ℝ b]
    exact Finset.sum_congr rfl fun i _ => by
      simpa only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply] using hdiag i
  rw [htrace]
  calc
    |∑ i : Fin (Module.finrank ℝ (TangentSpace I x)), g.inner x (A (b i)) (b i)| ≤
        ∑ i : Fin (Module.finrank ℝ (TangentSpace I x)),
          |g.inner x (A (b i)) (b i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I x)), c := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hu : g.inner x (b i) (b i) = 1 := by simpa only [ite_true] using hb i i
      have hcs := DifferentialGeometry.SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
        g x (A (b i)) (b i)
      rw [hu, Real.sqrt_one, mul_one] at hcs
      exact hcs.trans (by simpa only [hu, Real.sqrt_one, mul_one] using hA (b i))
    _ = (Module.finrank ℝ E : ℝ) * c := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]

section NeckScalar

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps t : ℝ} {x : M}

/-- The scalar comparison of `TruncatedNeck.abs_scalar_center_sub_le` at every point of the
strong-neck region (not only at the centre). -/
theorem strongNeck_scalar_sub_le_O48 (nk : StrongNeck S eps x t) {r : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 0) (z : Cylinder) (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
    |(S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) (nk.map z) - (1 - r)⁻¹| ≤
      2400 * eps := by
  let Q : ℝ := S.scalar t x
  have hQ : 0 < Q := nk.Q_pos
  have heps0 : 0 < eps := nk.eps_pos
  have heps1 : eps < 1 / 11 := nk.eps_small
  let O : TopologicalSpace.Opens Cylinder :=
    ⟨univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, isOpen_univ.prod isOpen_Ioo⟩
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)
  let f : O → M := fun z => nk.map z.val
  have hf : IsLocalDiffeomorph IC I3 ∞ f := by
    intro z
    exact (DifferentialGeometry.isLocalDiffeomorph_subtype_val O z).comp I3 M
      (nk.map.isLocalDiffeomorphAt IC I3 ∞ (nk.domain z.property))
  have hfd (z : O) (v : TangentSpace IC z) :
      mfderiv IC I3 f z v = mfderiv IC I3 nk.map z.val v := by
    change mfderiv IC I3 (nk.map ∘ (Subtype.val : O → Cylinder)) z v = _
    have hd := (nk.map.contMDiffOn_toFun.contMDiffAt
      (nk.map.open_source.mem_nhds (nk.domain z.property))).mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    rw [mfderiv_comp z hd
      (DifferentialGeometry.hasMFDerivAt_subtype_val O z).mdifferentiableAt]
    simp only [ContinuousLinearMap.comp_apply, DifferentialGeometry.mfderiv_subtype_val_apply]
  let G : SmoothRiemannianMetric IC O :=
    localPullMetric (rescaledMetric S t Q hQ r) f hf
  have hG (z : O) (v w : TangentSpace IC z) :
      G.inner z v w = (rescaledMetric S t Q hQ r).inner (nk.map z.val)
        (mfderiv IC I3 nk.map z.val v) (mfderiv IC I3 nk.map z.val w) := by
    change (localPullMetric (rescaledMetric S t Q hQ r) f hf).inner z v w = _
    rw [localPullMetric_inner, hfd, hfd]
  let gRef : SmoothRiemannianMetric IC O := (nk.cylinder.metric r).restrictOpen O
  let y : O := ⟨z, hz⟩
  have horder : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have hinv : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps0).2
      linarith
    exact_mod_cast hinv.trans (Nat.le_ceil eps⁻¹)
  have hclose : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k G gRef gRef y ≤ eps := by
    intro k hk
    rw [nk.comparison.metricDerivNorm_of_local_metric O subset_rfl r G hG k y]
    exact nk.comparison.close k 0 (by simpa using hk.trans horder) r hr y.val y.property
  have hcyl : nk.cylinder.metric r = cylinderReferenceMetric r :=
    nk.cylinder.metric_eq_cylinderReferenceMetric hr.2
  have hrefSharp (w : TangentSpace IC y) :
      ricciSharp gRef y w = ricciSharp (nk.cylinder.metric r) (y : Cylinder) w := by
    have hh := ricciSharp_restrictOpen (nk.cylinder.metric r) O y w
    rw [mfderiv_subtype_val] at hh
    exact hh
  have hbound (v : TangentSpace IC y) :
      Real.sqrt (gRef.inner y (ricciSharp G y v - ricciSharp gRef y v)
          (ricciSharp G y v - ricciSharp gRef y v)) ≤
        (800 * eps) * Real.sqrt (gRef.inner y v v) := by
    have h := ricciSharp_difference_bound_of_small_metric_derivatives G gRef y eps
      (by linarith) hclose v
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
    dsimp only at h
    rw [hdim] at h
    push_cast at h
    have hb : Real.sqrt (gRef.inner y (ricciSharp gRef y v) (ricciSharp gRef y v)) ≤
        (1 / 2) * Real.sqrt (gRef.inner y v v) := by
      have hh := sqrt_inner_ricciSharp_cylinderReferenceMetric_le hr.2 (y : Cylinder) v
      rw [← hcyl] at hh
      change Real.sqrt ((nk.cylinder.metric r).inner (y : Cylinder) (ricciSharp gRef y v)
          (ricciSharp gRef y v)) ≤ (1 / 2) * Real.sqrt ((nk.cylinder.metric r).inner
            (y : Cylinder) v v)
      rw [hrefSharp]
      exact hh
    have hs0 : 0 ≤ Real.sqrt (gRef.inner y v v) := Real.sqrt_nonneg _
    have hden : 0 < 1 - eps := by linarith
    apply h.trans
    rw [div_le_iff₀ hden]
    have hb' := mul_le_mul_of_nonneg_left hb heps0.le
    have h2 : eps * (eps * Real.sqrt (gRef.inner y v v)) ≤
        (1 / 11) * (eps * Real.sqrt (gRef.inner y v v)) :=
      mul_le_mul_of_nonneg_right heps1.le (mul_nonneg heps0.le hs0)
    have h3 : 0 ≤ eps * Real.sqrt (gRef.inner y v v) := mul_nonneg heps0.le hs0
    linarith
  have htrace := abs_trace_le_of_sqrt_inner_bound_O48 gRef y
    ((ricciSharp G y).toLinearMap - (ricciSharp gRef y).toLinearMap) (800 * eps)
    (fun v => by simpa only [LinearMap.sub_apply, ContinuousLinearMap.coe_coe] using hbound v)
  rw [map_sub, ← metricScalar_eq_trace_ricciSharp, ← metricScalar_eq_trace_ricciSharp] at htrace
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at htrace
  have hGscalar : metricScalarAt G y = Q⁻¹ * S.scalar (t + r / Q) (nk.map z) := by
    change metricScalarAt (localPullMetric (rescaledMetric S t Q hQ r) f hf) y = _
    rw [metricScalarAt_localPull]
    change metricScalarAt (scaleMetric Q hQ (S.base.metric (parabolicTime t Q r)))
      (nk.map z) = _
    rw [metricScalarAt_scaleMetric]
    rfl
  have hRscalar : metricScalarAt gRef y = (1 - r)⁻¹ := by
    change metricScalarAt ((nk.cylinder.metric r).restrictOpen O) y = _
    rw [metricScalarAt_restrictOpen, hcyl]
    exact cylinderReferenceMetric_scalar r hr.2 _
  rw [hGscalar, hRscalar] at htrace
  change |Q⁻¹ * S.scalar (t + r / Q) (nk.map z) - (1 - r)⁻¹| ≤ 2400 * eps
  push_cast at htrace
  linarith

/-- Window scalar bound on the strong-neck region: `R ≤ (1 + 2400 ε) Q` on `[t - Q⁻¹, t]`. -/
theorem strongNeck_scalar_le_O48 (nk : StrongNeck S eps x t) {z : Cylinder}
    (hz : z ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) {v : ℝ}
    (hv : v ∈ Icc (t - (S.scalar t x)⁻¹) t) :
    S.scalar v (nk.map z) ≤ (1 + 2400 * eps) * S.scalar t x := by
  have hQ : 0 < S.scalar t x := nk.Q_pos
  set Q := S.scalar t x with hQdef
  have hr : Q * (v - t) ∈ Icc (-1 : ℝ) 0 := by
    constructor
    · have h1 : t - Q⁻¹ ≤ v := hv.1
      have : -Q⁻¹ ≤ v - t := by linarith
      have := mul_le_mul_of_nonneg_left this hQ.le
      rwa [mul_neg, mul_inv_cancel₀ hQ.ne'] at this
    · exact mul_nonpos_of_nonneg_of_nonpos hQ.le (by linarith [hv.2])
  have hmain := strongNeck_scalar_sub_le_O48 nk hr z hz
  have htv : t + Q * (v - t) / Q = v := by field_simp; ring
  rw [← hQdef, htv] at hmain
  have hle1 : (1 - Q * (v - t))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hr.2])
  have hab := (abs_le.mp hmain).2
  have hQinv : Q⁻¹ * S.scalar v (nk.map z) ≤ 1 + 2400 * eps := by linarith
  have := mul_le_mul_of_nonneg_left hQinv hQ.le
  rwa [← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul, mul_comm] at this

end NeckScalar

/-- Sectional lower bounds pull back along local diffeomorphisms. -/
theorem sectionalBoundedBelowAt_localPull_O48 {M N : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I3 N) (f : M → N) (hf : IsLocalDiffeomorph I3 I3 ∞ f)
    (x : M) (K : ℝ) (h : SectionalBoundedBelowAt g (f x) K) :
    SectionalBoundedBelowAt (localPullMetric g f hf) x K := by
  intro v w
  rw [metricRm04StandardAt_localPullMetric]
  simp only [localPullMetric_inner]
  exact h _ _

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **C1 on the neck region** (`[FROZEN] CH12-O48 G1 (4)`). -/
theorem C1_neck_region_O48 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) :
    ∃ Phi : ℝ → ℝ, Perelman.AdmissiblePinchingFunction Phi ∧
      ∀ (s : RegularSlice F.observation) (x : s.stage.Carrier),
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∀ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
        (a : Icc (0 : ℝ) s.history.horizon)
        (E : RegularOpenBackwardTrace_O31 s.history (s.history.activeStage a) U)
        (S : SolutionOn (I := ThreeModel) (M := U)
          (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
            (sub_le_self _ (inv_nonneg.mpr
              (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
        (a : ℝ) = s.time - (metricScalarAt s.metric x)⁻¹ →
        (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
          S.base.metric v =
            localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
              (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                (Fin.le_last _))
              (E.atStage_isLocalDiffeomorph _ _ _)) →
        IsSolutionOn S →
        S.base.metric s.time = s.metric.restrictOpen U →
        StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time →
        ∃ (U' : TopologicalSpace.Opens s.stage.Carrier) (_ : x ∈ U')
          (S' : SolutionOn (I := ThreeModel) (M := U')
            (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
              (sub_le_self _ (inv_nonneg.mpr
                (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
          IsSolutionOn S' ∧ S'.base.metric s.time = s.metric.restrictOpen U' ∧
          ∀ v ∈ Icc (s.time - (metricScalarAt s.metric x)⁻¹) s.time, ∀ q : U',
            SectionalBoundedBelowAt (S'.base.metric v) q
              (-(Phi ((1 + 2400 * Hp.epsilon) * metricScalarAt s.metric x) /
                metricScalarAt s.metric x * metricScalarAt s.metric x)) := by
  obtain ⟨Phi, hPhi, hpin⟩ := pinch_on_trace_O39 Hp
  refine ⟨Phi, hPhi, fun s x hR U hxU a E S ha hbind hS hterm nk => ?_⟩
  have hRx : 0 < metricScalarAt s.metric x :=
    lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR
  have hQ : S.scalar s.time ⟨x, hxU⟩ = metricScalarAt s.metric x := by
    change metricScalarAt (S.base.metric s.time) ⟨x, hxU⟩ = _
    rw [hterm, metricScalarAt_restrictOpen]
  let O : Set Cylinder := univ ×ˢ Ioo (-Hp.epsilon⁻¹) Hp.epsilon⁻¹
  have hOo : IsOpen O := isOpen_univ.prod isOpen_Ioo
  let V : Set U := nk.map '' O
  have hVo : IsOpen V := nk.map.toOpenPartialHomeomorph.isOpen_image_of_subset_source hOo nk.domain
  let U' : TopologicalSpace.Opens s.stage.Carrier :=
    ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val V hVo⟩
  have hU'U : U' ≤ U := by
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  have hε : 0 < Hp.epsilon⁻¹ := inv_pos.mpr nk.eps_pos
  have hxU' : x ∈ U' :=
    ⟨⟨x, hxU⟩, ⟨(nk.center, 0), ⟨mem_univ _, neg_lt_zero.mpr hε, hε⟩, nk.center_eq⟩, rfl⟩
  let ι : U' → U := TopologicalSpace.Opens.inclusion hU'U
  have hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ι := fun y =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun z : U' => hU'U z.property)
      (isLocalDiffeomorph_subtype_val U' y)
  have : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel U.isOpen)
  refine ⟨U', hxU', S.localPullback ι hι, hS.localPullback ι hι, ?_, ?_⟩
  · rw [SolutionOn.localPullback_metric, hterm]
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, mfderiv_opens_incl]
    rfl
  · intro v hv q
    rw [SolutionOn.localPullback_metric]
    apply sectionalBoundedBelowAt_localPull_O48
    obtain ⟨w, ⟨z, hz, rfl⟩, hwq⟩ := q.2
    have hιq : ι q = nk.map z := Subtype.ext hwq.symm
    rw [hιq]
    have h0 : 0 ≤ v := by
      have := a.2.1
      rw [ha] at this
      exact this.trans hv.1
    have hvh : v ≤ s.history.horizon := hv.2.trans (sliceTop_S8 s).2.2
    let v' : Icc (0 : ℝ) s.history.horizon := ⟨v, h0, hvh⟩
    have hav : a ≤ v' := by
      change (a : ℝ) ≤ v
      rw [ha]
      exact hv.1
    have hscal : metricScalarAt (S.base.metric v) (nk.map z) ≤
        (1 + 2400 * Hp.epsilon) * metricScalarAt s.metric x := by
      have hv' : v ∈ Icc (s.time - (S.scalar s.time ⟨x, hxU⟩)⁻¹) s.time := by
        rw [hQ]
        exact hv
      have := strongNeck_scalar_le_O48 nk hz hv'
      rw [hQ] at this
      exact this
    exact (hpin s U a E S hbind v' hav (nk.map z)).mono (neg_eta_le_O39 hPhi hRx hscal)

/-- **The `hC1` binder of `hNoEscPos_of_ABC_O38`** (verbatim type) from hStrong v2 and the
cap-exclusion binder `hCapEx` (`[FROZEN] CH12-O48 G1 (5)`). -/
theorem hC1_O48 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hStrong2 : ∃ T : ℝ, ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ x : s.stage.Carrier,
      ∀ hR : (Hp.parameters.neckRadius s.time ^ 2)⁻¹ < metricScalarAt s.metric x,
      ∃ W : SpatialCanonicalWitness s.metric Hp.epsilon Hp.C1 Hp.C2 x,
        W.capTubeHasNeckChart Hp.epsilon ∧
        ∀ nk, W.alternative = SpatialCanonicalAlternative.neck nk →
          ∃ (U : TopologicalSpace.Opens s.stage.Carrier) (hxU : x ∈ U)
            (a : Icc (0 : ℝ) s.history.horizon)
            (E : RegularOpenBackwardTrace_O31 s.history (s.history.activeStage a) U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed (s.time - (metricScalarAt s.metric x)⁻¹) s.time
                (sub_le_self _ (inv_nonneg.mpr
                  (lt_of_le_of_lt (inv_nonneg.mpr (sq_nonneg _)) hR).le)))),
            (a : ℝ) = s.time - (metricScalarAt s.metric x)⁻¹ ∧
            IsSolutionOn S ∧
            (∀ v : Icc (0 : ℝ) s.history.horizon, ∀ hav : a ≤ v,
              S.base.metric v =
                localPullMetric (s.history.stageMetric (s.history.activeStage v) v)
                  (E.atStage (s.history.activeStage v) (s.history.activeStage_mono hav)
                    (Fin.le_last _))
                  (E.atStage_isLocalDiffeomorph _ _ _)) ∧
            S.base.metric s.time = s.metric.restrictOpen U ∧
            Nonempty (StrongNeck S Hp.epsilon ⟨x, hxU⟩ s.time))
    (hCapEx : ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      0 ≤ ρ → ρ ≤ A →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      1 / 4 ≤ ρ →
      ∀ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f →
      ∀ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          ((∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ)) ∧
          (∀ r : ℝ, r < ρ → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      ∀ γ : ℝ → LM, (γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) →
      ∀ᶠ t in 𝓝[<] ρ, ∀ᶠ k in atTop,
        ∀ W : SpatialCanonicalWitness (s (f k)).metric Hp.epsilon Hp.C1 Hp.C2 (φ k (γ t)),
          W.capTubeHasNeckChart Hp.epsilon →
            ∃ nk, W.alternative = SpatialCanonicalAlternative.neck nk) :
    ∀ A : ℝ, 0 < A → ∀ (s : ℕ → RegularSlice F.observation)
      (y : ∀ n, (s n).stage.Carrier) (ρ : ℝ),
      Tendsto (fun n => (s n).time) atTop atTop →
      (∀ n, (Hp.parameters.neckRadius (s n).time ^ 2)⁻¹ ≤
        metricScalarAt (s n).metric (y n)) →
      Tendsto (fun n => metricScalarAt (s n).metric (y n)) atTop atTop →
      0 ≤ ρ → ρ ≤ A →
      (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ᶠ n in atTop,
        ∀ w ∈ riemannianBallOf (s n).metric (y n)
          (r / Real.sqrt (metricScalarAt (s n).metric (y n))),
          metricScalarAt (s n).metric w ≤ C * metricScalarAt (s n).metric (y n)) →
      1 / 4 ≤ ρ →
      ∀ (LM : Type u) (_ : TopologicalSpace LM) (_ : ChartedSpace ThreeSpace LM)
          (_ : IsManifold ThreeModel ∞ LM) (_ : T2Space LM)
          (_ : SigmaCompactSpace LM) (gL : SmoothRiemannianMetric ThreeModel LM) (x₀ : LM) (f : ℕ → ℕ), StrictMono f →
      ∀ φ : ∀ k, LM → (s (f k)).stage.Carrier,
          ((∀ k, ContMDiff ThreeModel ThreeModel ∞ (φ k)) ∧ (∀ k, φ k x₀ = y (f k)) ∧
          (∀ x : LM, riemannianEDistOf gL x₀ x < ENNReal.ofReal (ρ)) ∧
          (∀ r : ℝ, r < ρ → IsCompact (riemannianClosedBallOf gL x₀ r)) ∧
          (∀ K : Set LM, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ x ∈ K,
            |metricScalarAt (s (f k)).metric (φ k x) / metricScalarAt (s (f k)).metric (y (f k)) - metricScalarAt gL x| < ε ∧
            ∀ x' ∈ K, |Real.sqrt (metricScalarAt (s (f k)).metric (y (f k))) *
                (riemannianEDistOf (s (f k)).metric (φ k x) (φ k x')).toReal -
              (riemannianEDistOf gL x x').toReal| < ε) ∧
          (∀ x : LM, SectionalBoundedBelowAt gL x 0) ∧
          (∀ r : ℝ, r < ρ → ∃ C : ℝ, ∀ x : LM,
            riemannianEDistOf gL x₀ x < ENNReal.ofReal r → metricScalarAt gL x ≤ C)) →
      ∀ γ : ℝ → LM, (γ 0 = x₀ ∧
          (∀ t₁ ∈ Ico (0 : ℝ) ρ, ∀ t₂ ∈ Ico (0 : ℝ) ρ,
            riemannianEDistOf gL (γ t₁) (γ t₂) = ENNReal.ofReal |t₁ - t₂|) ∧
          Tendsto (fun t => metricScalarAt gL (γ t)) (𝓝[<] ρ) atTop) →
      ∀ (CM : Type u) (_ : TopologicalSpace CM) (_ : ChartedSpace ThreeSpace CM)
          (_ : IsManifold ThreeModel ∞ CM) (gC : SmoothRiemannianMetric ThreeModel CM) (c₀ : CM) (ψ : ℕ → CM → LM),
        (∀ x : CM, SectionalBoundedBelowAt gC x 0) → 0 < metricScalarAt gC c₀ →
        (∀ j, ψ j c₀ = γ (ρ - (2 : ℝ)⁻¹ ^ j)) →
      (∃ (f₂ : ℕ → ℕ), StrictMono f₂ ∧ ∃ (p : ∀ k, (s (f (f₂ k))).stage.Carrier) (η : ℕ → ℝ),
        Tendsto η atTop (𝓝 0) ∧
        (∃ Rinf : ℝ, 0 < Rinf ∧ Tendsto (fun k => metricScalarAt (s (f (f₂ k))).metric (p k) /
          metricScalarAt (s (f (f₂ k))).metric (y (f (f₂ k)))) atTop (𝓝 Rinf)) ∧
        ∀ k, ∃ hRp : 0 < metricScalarAt (s (f (f₂ k))).metric (p k),
          ∃ (U : TopologicalSpace.Opens (s (f (f₂ k))).stage.Carrier) (_ : p k ∈ U)
            (S : SolutionOn (I := ThreeModel) (M := U)
              (RealTimeInterval.closed ((s (f (f₂ k))).time -
                (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹) (s (f (f₂ k))).time
                (sub_le_self _ (inv_nonneg.mpr hRp.le)))),
            IsSolutionOn S ∧ S.base.metric (s (f (f₂ k))).time = (s (f (f₂ k))).metric.restrictOpen U ∧
            ∀ v ∈ Icc ((s (f (f₂ k))).time - (metricScalarAt (s (f (f₂ k))).metric (p k))⁻¹)
                (s (f (f₂ k))).time, ∀ q : U,
              SectionalBoundedBelowAt (S.base.metric v) q
                (-(η k * metricScalarAt (s (f (f₂ k))).metric (p k)))) := by
  obtain ⟨Phi, hPhi, hneck⟩ := C1_neck_region_O48 Hp
  obtain ⟨T, hT⟩ := hStrong2
  intro A hA s y ρ h1 h2 h3 h5 h6 h9 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ
    CM j1 j2 j3 gC c₀ ψ _hC0 _hCpos _hψ0
  have hcap := hCapEx A hA s y ρ h1 h2 h3 h5 h6 h9 h11 LM i1 i2 i3 i4 i5 gL x₀ f hf φ hL γ hγ
  have hev4 : ∀ᶠ t in 𝓝[<] ρ, (4 : ℝ) ≤ metricScalarAt gL (γ t) :=
    hγ.2.2.eventually_ge_atTop 4
  obtain ⟨t, ht4, htcap⟩ := (hev4.and hcap).exists
  have hratio : Tendsto (fun k => metricScalarAt (s (f k)).metric (φ k (γ t)) /
      metricScalarAt (s (f k)).metric (y (f k))) atTop (𝓝 (metricScalarAt gL (γ t))) := by
    refine Metric.tendsto_nhds.mpr fun e he => ?_
    filter_upwards [hL.2.2.2.2.1 {γ t} isCompact_singleton e he] with k hk
    rw [Real.dist_eq]
    exact (hk (γ t) rfl).1
  have hfT := h1.comp hf.tendsto_atTop
  have hfy := h3.comp hf.tendsto_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hfT.eventually_ge_atTop T).and
    ((hfy.eventually_gt_atTop 0).and
      ((hratio.eventually (lt_mem_nhds (by linarith : (2 : ℝ) < metricScalarAt gL (γ t)))).and
        htcap)))
  have hpos : ∀ k, 0 < metricScalarAt (s (f (k + N))).metric (y (f (k + N))) := fun k =>
    (hN (k + N) (Nat.le_add_left N k)).2.1
  have hRpk : ∀ k, 2 * metricScalarAt (s (f (k + N))).metric (y (f (k + N))) <
      metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t)) := fun k =>
    (lt_div_iff₀ (hpos k)).mp (hN (k + N) (Nat.le_add_left N k)).2.2.1
  have hratioN := hratio.comp (tendsto_add_atTop_nat N)
  have hRtop : Tendsto (fun k => metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t)))
      atTop atTop := by
    have hprod := Tendsto.pos_mul_atTop (by linarith : (0 : ℝ) < metricScalarAt gL (γ t))
      hratioN (hfy.comp (tendsto_add_atTop_nat N))
    refine hprod.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [div_mul_cancel₀ _ (hpos k).ne']
  have hΛ : (0 : ℝ) < 1 + 2400 * Hp.epsilon := by linarith [Hp.epsilon_pos]
  refine ⟨fun k => k + N, fun a b hab => Nat.add_lt_add_right hab N,
    fun k => φ (k + N) (γ t),
    fun k => Phi ((1 + 2400 * Hp.epsilon) *
        metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t))) /
      metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t)),
    (eta_of_pinching_O39 hPhi hΛ).comp hRtop,
    ⟨metricScalarAt gL (γ t), by linarith, hratioN⟩, fun k => ?_⟩
  have hRp : 0 < metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t)) :=
    lt_trans (by linarith [hpos k]) (hRpk k)
  have hR : (Hp.parameters.neckRadius (s (f (k + N))).time ^ 2)⁻¹ <
      metricScalarAt (s (f (k + N))).metric (φ (k + N) (γ t)) :=
    lt_of_le_of_lt (h2 (f (k + N))) (by linarith [hpos k, hRpk k])
  obtain ⟨W, hchart, hnb⟩ := hT (s (f (k + N))) (hN (k + N) (Nat.le_add_left N k)).1 _ hR
  obtain ⟨nk0, hnk0⟩ := (hN (k + N) (Nat.le_add_left N k)).2.2.2 W hchart
  obtain ⟨U, hxU, a, E, S, ha, hS, hbind, hterm, ⟨nkS⟩⟩ := hnb nk0 hnk0
  obtain ⟨U', hxU', S', hS', hterm', hsec⟩ :=
    hneck (s (f (k + N))) _ hR U hxU a E S ha hbind hS hterm nkS
  exact ⟨hRp, U', hxU', S', hS', hterm', hsec⟩

end GC.LongTime.Ch12
