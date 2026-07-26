import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicGalerkin
import DifferentialGeometry.Geometry.Flow.RicciFlow.Pullback.HarmonicTension
import DifferentialGeometry.Analysis.Integration.Measure.FamilyContinuityParam

/-!
# Dirichlet energy in exponential-section coordinates

On a connected compact manifold, a smooth `(0,1)` tensor `S` is raised with a
fixed target metric `q` and inserted into the intrinsic diagonal exponential.
The resulting self-map

`x ↦ exp^q_x (q♯ S(x))`

is the local-addition realization used by the harmonic-map heat-flow gauge.
This file defines its moving-domain Dirichlet energy and, on every finite
spectral trial space, the concrete first-variation covector which drives the
moving-mass Galerkin ODE.

The first variation is taken after freezing the time variable.  This is
essential at the initial edge: the metric coefficients are assumed continuous
in time there, but need not be time differentiable.  Taking the Fréchet
derivative of the *joint* `(time, coefficient)` function would therefore be
incorrect (Lean's total `fderiv` is zero when total differentiability fails).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Pullback

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [T2Space M]
  [SigmaCompactSpace M] [BoundarylessManifold I M] [ConnectedSpace M]

/-! ## The global intrinsic local addition on a connected component -/

private noncomputable def hmfRiemBundle
    (q : SmoothRiemannianMetric I M) :
    RiemannianBundle (fun x : M => TangentSpace I x) :=
  ⟨q.toRiemannianMetric⟩

private noncomputable def hmfContBundle
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      hmfRiemBundle (I := I) q
    IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    hmfRiemBundle (I := I) q
  exact ⟨q.inner, q.contMDiff.continuous, fun _ _ _ => rfl⟩

private noncomputable def hmfEMetric
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      hmfRiemBundle (I := I) q
    PseudoEMetricSpace M := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    hmfRiemBundle (I := I) q
  exact PseudoEMetricSpace.ofRiemannianMetric I M

private theorem hmfEnorm
    (q : SmoothRiemannianMetric I M) :
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      hmfRiemBundle (I := I) q
    ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (q.inner x v v)) := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    hmfRiemBundle (I := I) q
  intro x v
  rw [← ofReal_norm_eq_enorm, norm_eq_sqrt_real_inner]
  rfl

/-- The intrinsic diagonal exponential for the fixed target metric `q`, with
all metric-space structures kept local to the definition. -/
noncomputable def hmfDiagExp
    (q : SmoothRiemannianMetric I M) : TangentBundle I M → M × M := by
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    hmfRiemBundle (I := I) q
  letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    hmfContBundle (I := I) q
  letI : PseudoEMetricSpace M := hmfEMetric (I := I) q
  exact diagExp (I := I) q (hmfEnorm (I := I) q)

/-- The intrinsic diagonal exponential used by the HMF local addition is
finite-order smooth at every point of the zero section. -/
theorem hmfDiagExp_cd_zero
    (q : SmoothRiemannianMetric I M) (x : M) (n : ℕ) (hn : 1 ≤ n) :
    ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (hmfDiagExp (I := I) (M := M) q)
      (⟨x, (0 : E)⟩ : TangentBundle I M) := by
  letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
    hmfRiemBundle (I := I) q
  letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    hmfContBundle (I := I) q
  letI : PseudoEMetricSpace M := hmfEMetric (I := I) q
  change ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
    (diagExp (I := I) q (hmfEnorm (I := I) q))
    (⟨x, (0 : E)⟩ : TangentBundle I M)
  exact diagExp_contMDiffAt_zero (I := I)
    q (hmfEnorm (I := I) q) x n hn

/-- Exponential-section realization of a lowered tangent field. -/
noncomputable def hmfAdd
    (q : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) : M → M :=
  fun x =>
    (hmfDiagExp (I := I) (M := M) q
      (⟨x, hmfUnknown (I := I) q S x⟩ : TangentBundle I M)).2

@[simp] theorem hmfUnknown_zero
    (q : SmoothRiemannianMetric I M) (x : M) :
    hmfUnknown (I := I) q (0 : SmoothCcTensor q 0 1) x = 0 := by
  simp only [hmfUnknown, unitEvalSection_apply, SmoothCcTensor.toSection_zero,
    ContMDiffSection.coe_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply,
    map_zero]

/-- The exponential-section realization sends the zero section to the identity
map.  This is the base point for the finite-dimensional first-variation and
Jacobi calculations. -/
@[simp] theorem hmfAdd_zero
    (q : SmoothRiemannianMetric I M) :
    hmfAdd (I := I) (M := M) q (0 : SmoothCcTensor q 0 1) = id := by
  funext x
  letI : RiemannianBundle (fun y : M => TangentSpace I y) :=
    hmfRiemBundle (I := I) q
  letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    hmfContBundle (I := I) q
  letI : PseudoEMetricSpace M := hmfEMetric (I := I) q
  change (diagExp (I := I) q (hmfEnorm (I := I) q)
      (⟨x, hmfUnknown (I := I) q (0 : SmoothCcTensor q 0 1) x⟩ :
        TangentBundle I M)).2 = x
  rw [hmfUnknown_zero, diagExp_snd,
    expMapIntrinsic_zero (I := I) q (hmfEnorm (I := I) q) x]

@[simp] theorem hmfAdd_zero_md
    (q : SmoothRiemannianMetric I M) (x : M) (v : TangentSpace I x) :
    mfderiv I I (hmfAdd (I := I) (M := M) q
      (0 : SmoothCcTensor q 0 1)) x v = v := by
  rw [hmfAdd_zero, mfderiv_id]
  rfl

/-! ## Uniform finite-spectral local-addition chart -/

/-- The tangent-bundle launch field obtained from a finite spectral
coefficient and a point of the manifold. -/
noncomputable def hmfSpecLaunch
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (p : EuclideanSpace ℝ {i // i ∈ S} × M) : TangentBundle I M :=
  TotalSpace.mk' E p.2
    (hmfUnknown (I := I) q
      (hmfSpecIncl (I := I) (M := M) q S p.1) p.2)

@[simp] theorem hmfSpecLaunch_zero
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) (x : M) :
    hmfSpecLaunch (I := I) (M := M) q S (0, x) =
      (⟨x, (0 : E)⟩ : TangentBundle I M) := by
  simp only [hmfSpecLaunch, map_zero, hmfUnknown_zero]

/-- The finite spectral launch field is jointly smooth in the coefficient and
the base point.  This is proved as a finite sum of smooth scalar coefficients
times fixed smooth tangent sections; no topology on the full space of smooth
sections is introduced. -/
theorem hmfSpecLaunch_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1)) :
    ContMDiff (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent ∞
      (hmfSpecLaunch (I := I) (M := M) q S) := by
  classical
  have hterm : ∀ j : {i // i ∈ S},
      ContMDiff (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent ∞
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          TotalSpace.mk' E p.2
            (p.1 j • hmfUnknown (I := I) q
              (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) := by
    intro j
    have hc : ContMDiff
        (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) 𝒘(ℝ, ℝ) ∞
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M => p.1 j) := by
      have hp : ContDiff ℝ ∞
          (EuclideanSpace.proj (𝕜 := ℝ) j :
            EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ) :=
        (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
      exact hp.contMDiff.comp contMDiff_fst
    have hs : ContMDiff
        (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent ∞
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          TotalSpace.mk' E p.2
            (hmfUnknown (I := I) q
              (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) :=
      (hmfUnknownSec (I := I) q
        (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1)).contMDiff.comp
          contMDiff_snd
    simpa only [EuclideanSpace.coe_proj] using hc.smul_section hs
  have hsum : ContMDiff
      (𝒘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent ∞
      (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
        TotalSpace.mk' E p.2
          (∑ j : {i // i ∈ S}, p.1 j • hmfUnknown (I := I) q
            (eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) p.2)) := by
    exact ContMDiff.sum_section (s := Finset.univ) (fun j _ => hterm j)
  refine hsum.congr (fun p => ?_)
  simp only [hmfSpecLaunch, hmfSpecIncl_apply]
  apply congrArg (TotalSpace.mk' E p.2)
  change hmfUnknownLM (I := I) q p.2
      (∑ j : {i // i ∈ S},
        p.1 j • eigenvectorSmooth (I := I) (M := M) q 0 1 j.1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, hmfUnknownLM_apply]

/-- For a fixed finite spectral trial space and finite differentiability
order, one coefficient ball launches entirely into the smooth locus of the
intrinsic diagonal exponential.  The radius is uniform in the manifold point
but may depend on the finite mode set. -/
theorem hmfSpecChart
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧
      ∀ u : EuclideanSpace ℝ {i // i ∈ S}, u ∈ Metric.ball 0 R →
        ∀ x : M,
          ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
            (hmfDiagExp (I := I) (M := M) q)
            (hmfSpecLaunch (I := I) (M := M) q S (u, x)) := by
  classical
  let U : Set (TangentBundle I M) :=
    {z | ContMDiffAt I.tangent (I.prod I) (n : ℕ∞)
      (hmfDiagExp (I := I) (M := M) q) z}
  have hfinite : (n : ℕ∞) ≠ ∞ := by simp
  have hU_open : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact (contMDiffAt_iff_contMDiffAt_nhds hfinite).1 hz
  let P : Set (EuclideanSpace ℝ {i // i ∈ S} × M) :=
    (hmfSpecLaunch (I := I) (M := M) q S) ⁻¹' U
  have hP_open : IsOpen P :=
    hU_open.preimage (hmfSpecLaunch_cd (I := I) (M := M) q S).continuous
  have hslice :
      ({(0 : EuclideanSpace ℝ {i // i ∈ S})} ×ˢ (Set.univ : Set M)) ⊆ P := by
    rintro ⟨u, x⟩ ⟨hu, -⟩
    simp only [Set.mem_singleton_iff] at hu
    subst u
    change hmfSpecLaunch (I := I) (M := M) q S (0, x) ∈ U
    rw [hmfSpecLaunch_zero]
    exact hmfDiagExp_cd_zero (I := I) (M := M) q x n hn
  obtain ⟨A, B, hA_open, _hB_open, hzeroA, hunivB, hAB⟩ :=
    generalized_tube_lemma
      (isCompact_singleton (x := (0 : EuclideanSpace ℝ {i // i ∈ S})))
      (isCompact_univ : IsCompact (Set.univ : Set M)) hP_open hslice
  have hzeroA' : (0 : EuclideanSpace ℝ {i // i ∈ S}) ∈ A := hzeroA rfl
  obtain ⟨R, hR_pos, hR_ball⟩ := Metric.isOpen_iff.mp hA_open 0 hzeroA'
  refine ⟨R, hR_pos, ?_⟩
  intro u hu x
  have hux : (u, x) ∈ A ×ˢ B :=
    ⟨hR_ball hu, hunivB (Set.mem_univ x)⟩
  exact hAB hux

/-- On the fixed finite-spectral coefficient ball supplied by
`hmfSpecChart`, the exponential-section map is jointly smooth in the
coefficient and the manifold point. -/
theorem hmfSpecAdd_cd
    (q : SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ R : ℝ, 0 < R ∧
      ContMDiffOn (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) (I.prod I)
        (n : ℕ∞)
        (fun p : EuclideanSpace ℝ {i // i ∈ S} × M =>
          hmfDiagExp (I := I) (M := M) q
            (hmfSpecLaunch (I := I) (M := M) q S p))
        (Metric.ball 0 R ×ˢ (Set.univ : Set M)) := by
  obtain ⟨R, hR, hchart⟩ :=
    hmfSpecChart (I := I) (M := M) q S n hn
  refine ⟨R, hR, ?_⟩
  intro p hp
  have hlaunch :
      ContMDiffAt (𝓘(ℝ, EuclideanSpace ℝ {i // i ∈ S}).prod I) I.tangent
        (n : ℕ∞) (hmfSpecLaunch (I := I) (M := M) q S) p :=
    (hmfSpecLaunch_cd (I := I) (M := M) q S).contMDiffAt.of_le (by simp)
  exact ((hchart p.1 hp.1 p.2).comp p hlaunch).contMDiffWithinAt

/-! ## Moving-domain Dirichlet energy -/

/-- Pointwise Dirichlet density of a self-map `Phi : (M,h) → (M,q)`.  The
trace is written in the fixed `q`-orthonormal frame: insertion of
`h sharp o q flat` in the first derivative slot changes the trace from
`q^{-1}` to `h^{-1}`.  Thus the moving metric appears only through the same
zeroth-order inverse-cometric coefficient as `hmfFlux`, avoiding a
time-dependent choice of orthonormal frame.

The total `mfderiv` makes the definition meaningful before regularity is
proved; the later geometric regularity theorem identifies it with the
ordinary map differential on the local-addition ball. -/
noncomputable def hmfDirDensity
    (q h : SmoothRiemannianMetric I M) (Phi : M → M) (x : M) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i : Fin (Module.finrank ℝ E),
      q.inner (Phi x)
        (mfderiv I I Phi x
          (gInvRaisedEndo (I := I) q h x
            (smoothOrthoFrame (I := I) q x i x)))
        (mfderiv I I Phi x (smoothOrthoFrame (I := I) q x i x))

@[simp] theorem hmfDirDensity_zero
    (q h : SmoothRiemannianMetric I M) (x : M) :
    hmfDirDensity (I := I) (M := M) q h
        (hmfAdd (I := I) (M := M) q (0 : SmoothCcTensor q 0 1)) x =
      (1 / 2 : ℝ) *
        ∑ i : Fin (Module.finrank ℝ E),
          q.inner x
            (gInvRaisedEndo (I := I) q h x
              (smoothOrthoFrame (I := I) q x i x))
            (smoothOrthoFrame (I := I) q x i x) := by
  simp only [hmfDirDensity, hmfAdd_zero, id_eq, mfderiv_id,
    ContinuousLinearMap.id_apply]

/-- Dirichlet energy of the exponential-section map represented by `S`, with
moving domain metric `h` and fixed target metric `q`. -/
noncomputable def hmfDirEnergy
    (q h : SmoothRiemannianMetric I M) (S : SmoothCcTensor q 0 1) : ℝ :=
  ∫ x, hmfDirDensity (I := I) (M := M) q h
      (hmfAdd (I := I) (M := M) q S) x
    ∂(riemannianVolumeMeasure (I := I) (M := M) h)

/-! ## Concrete finite spectral first variation -/

/-- The Dirichlet energy restricted to one finite intrinsic spectral trial
space. -/
noncomputable def hmfSpecEnergy
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) : ℝ :=
  hmfDirEnergy (I := I) (M := M) q (g t)
    (hmfSpecIncl (I := I) (M := M) q S u)

/-- The negative vertical first variation of the finite Dirichlet energy.
This is the concrete covector residual in the moving-mass Galerkin equation.
Time is frozen before differentiating, so the definition remains meaningful
when the metric family is only continuous at the initial edge. -/
noncomputable def hmfSpecResid
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  -fderiv ℝ (hmfSpecEnergy (I := I) (M := M) q g S t) u

/-! ### Forced principal/low-order split

The moving-mass equation is written with the negative energy variation on the
right.  Consequently its coercive divergence-form part has the sign
`-hmfWeakForm`.  The following definitions isolate that sign once, before any
regularity or tame estimate for the genuinely nonlinear remainder is proved.
-/

/-- The finite spectral realization of the signed moving weak principal
operator.  This is the part of the negative Dirichlet variation forced by the
zero-section vertical derivative of the exponential local addition. -/
noncomputable def hmfSpecPrin
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  -(hmfFinForm (I := I) (M := M) q (g t)
      (hmfSpecIncl (I := I) (M := M) q S) u)

@[simp] theorem hmfSpecPrin_apply
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u v : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfSpecPrin (I := I) (M := M) q g S t u v =
      -hmfWeakForm (I := I) (M := M) q (g t)
        (hmfSpecIncl (I := I) (M := M) q S u)
        (hmfSpecIncl (I := I) (M := M) q S v) := by
  simp only [hmfSpecPrin, ContinuousLinearMap.neg_apply, hmfFinForm_apply]

/-- The exact residual left after subtracting the signed moving weak
principal operator.  No low-order estimate is hidden in this definition: the
local-addition first-variation theorem must prove that this remainder has the
required tame bounds uniformly in the spectral cutoff. -/
noncomputable def hmfSpecLow
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  hmfSpecResid (I := I) (M := M) q g S t u -
    hmfSpecPrin (I := I) (M := M) q g S t u

/-- Exact principal/remainder decomposition of the finite Dirichlet residual.
The content of the subsequent analytic step is to estimate `hmfSpecLow`, not
to alter this identity. -/
theorem hmfSpec_split
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfSpecResid (I := I) (M := M) q g S t u =
      hmfSpecPrin (I := I) (M := M) q g S t u +
        hmfSpecLow (I := I) (M := M) q g S t u := by
  simp only [hmfSpecLow]
  abel

@[simp] theorem hmfSpecPrin_zero
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) :
    hmfSpecPrin (I := I) (M := M) q g S t 0 = 0 := by
  simp only [hmfSpecPrin, map_zero, neg_zero]

/-- On a metric ball where the moving inverse cometric remains elliptic, the
signed spectral principal part is dissipative. -/
theorem hmfSpecPrin_nonpos
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ)
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      (g t).inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) q k δ)
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    hmfSpecPrin (I := I) (M := M) q g S t u u ≤ 0 := by
  rw [hmfSpecPrin_apply]
  exact neg_nonpos.mpr (hmfWeak_nonneg (I := I) (M := M)
    q (g t) k htie hδ_half hδ_nn hδ
    (hmfSpecIncl (I := I) (M := M) q S u))

/-- Quantitative frozen-gradient coercivity of the negative spectral
principal part.  This is exactly the smooth-core estimate needed in the
Galerkin energy identity; its constant is independent of the spectral
cutoff. -/
theorem hmfSpecPrin_lower
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) (C : ℝ≥0∞) (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hvol : riemannianVolumeMeasure (I := I) (M := M) q ≤
      C • riemannianVolumeMeasure (I := I) (M := M) (g t))
    (k : ∀ y : M, TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
    (htie : ∀ (y : M) (v w : TangentSpace I y),
      (g t).inner y v w = q.inner y v w + k y v w)
    {δ : ℝ} (hδ_half : δ < 1 / 2) (hδ_nn : 0 ≤ δ)
    (hδ : gFibreOpBound (I := I) (M := M) q k δ)
    (u : EuclideanSpace ℝ {i // i ∈ S}) :
    (1 - δ / (1 - δ)) *
        hmfWeakForm (I := I) (M := M) q q
          (hmfSpecIncl (I := I) (M := M) q S u)
          (hmfSpecIncl (I := I) (M := M) q S u) ≤
      C.toReal *
        (-hmfSpecPrin (I := I) (M := M) q g S t u u) := by
  simpa only [hmfSpecPrin_apply, neg_neg] using
    (hmfForm_self_rev (I := I) (M := M) q (g t) C hC0 hCtop hvol
      k htie hδ_half hδ_nn hδ
      (hmfSpecIncl (I := I) (M := M) q S u))

@[simp] theorem hmfSpecLow_zero
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (t : ℝ) :
    hmfSpecLow (I := I) (M := M) q g S t 0 =
      hmfSpecResid (I := I) (M := M) q g S t 0 := by
  simp only [hmfSpecLow, hmfSpecPrin_zero, sub_zero]

/-- Radially globalized finite first variation.  It agrees with the true
Dirichlet-energy residual throughout the chosen coefficient ball. -/
noncomputable def hmfSpecResidR
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    (R t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S}) :
    EuclideanSpace ℝ {i // i ∈ S} →L[ℝ] ℝ :=
  hmfSpecResid (I := I) (M := M) q g S t (ballRetraction R u)

theorem hmfSpecResidR_eq
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    {R : ℝ} (t : ℝ) (u : EuclideanSpace ℝ {i // i ∈ S})
    (hu : ‖u‖ ≤ R) :
    hmfSpecResidR (I := I) (M := M) q g S R t u =
      hmfSpecResid (I := I) (M := M) q g S t u := by
  rw [hmfSpecResidR, ballRetraction_eq_self_of_mem hu]

/-- Consumer-shaped radial-globalization theorem for the actual finite
Dirichlet residual.  Once its joint continuity and state derivative are proved
on a fixed coefficient ball, no additional growth hypothesis is needed for
the finite ODE: global Lipschitz and affine bounds follow automatically. -/
theorem hmfSpecRes_data
    (q : SmoothRiemannianMetric I M)
    (g : ℝ → SmoothRiemannianMetric I M)
    (S : Finset (TensorEigenIdx (I := I) (M := M) q 0 1))
    {T R : ℝ} (hR : 0 ≤ R)
    (hF : ContinuousOn
      (Function.uncurry (hmfSpecResid (I := I) (M := M) q g S))
      (Icc (0 : ℝ) T ×ˢ
        Metric.closedBall
          (0 : EuclideanSpace ℝ {i // i ∈ S}) R))
    (hD : ContinuousOn
      (fun p : ℝ × EuclideanSpace ℝ {i // i ∈ S} =>
        fderiv ℝ (hmfSpecResid (I := I) (M := M) q g S p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ
        Metric.closedBall
          (0 : EuclideanSpace ℝ {i // i ∈ S}) R))
    (hdiff : ∀ t ∈ Icc (0 : ℝ) T,
      ∀ u ∈ Metric.closedBall
        (0 : EuclideanSpace ℝ {i // i ∈ S}) R,
        DifferentiableAt ℝ
          (hmfSpecResid (I := I) (M := M) q g S t) u) :
    ∃ A : ℝ, ∃ L : ℝ≥0, 0 ≤ A ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        LipschitzWith L
          (hmfSpecResidR (I := I) (M := M) q g S R t)) ∧
      (∀ u : EuclideanSpace ℝ {i // i ∈ S},
        ContinuousOn
          (fun t => hmfSpecResidR (I := I) (M := M) q g S R t u)
          (Icc (0 : ℝ) T)) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        ∀ u : EuclideanSpace ℝ {i // i ∈ S},
          ‖hmfSpecResidR (I := I) (M := M) q g S R t u‖ ≤
            A + (L : ℝ) * ‖u‖) := by
  simpa only [hmfSpecResidR] using
    (retractResid_data
      (F := hmfSpecResid (I := I) (M := M) q g S) hR hF hD hdiff)

end DifferentialGeometry.PDE.RicciFlow.Pullback

end
