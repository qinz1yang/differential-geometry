import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TruncatedNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderReferenceModel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedWitnessTransport
import DifferentialGeometry.Geometry.Curvature.RicciSharpUniformPerturbation
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Cylinder
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Curvature.ScalarTrace

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry (roundMetric roundMetric_ricciTensor)
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology (ThreeSpace)

universe u

private instance truncatedNeckScalarSphereFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

theorem CylinderReference.metric_eq_cylinderReferenceMetric (C : CylinderReference) {s : ℝ}
    (hs : s ≤ 0) : C.metric s = cylinderReferenceMetric s := by
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [C.inner_eq s hs, cylinderReferenceMetric_inner s hs]

theorem ricciSharp_cylinderReferenceMetric {s : ℝ} (hs : s ≤ 0) (y : Cylinder)
    (v : TangentSpace IC y) :
    ricciSharp (cylinderReferenceMetric s) y v = ((2 * (1 - s))⁻¹ • v.1, (0 : ℝ)) := by
  have hmax : max (2 * (1 - s)) 1 = 2 * (1 - s) := max_eq_left (by linarith)
  have hc : 0 < 2 * (1 - s) := by linarith
  have hpos : (0 : ℝ) < max (2 * (1 - s)) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let h := scaleMetric (I := I2) (max (2 * (1 - s)) 1) hpos
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))
  let g := cylinderReferenceMetric s
  apply DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq g
  intro w
  rw [inner_ricciSharp]
  have hric : ricciTensor g y v w = (((2 : ℕ) : ℝ) - 1) *
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 v.1 w.1 :=
    (ricciTensor_cylinderMetric h y v w).trans
      ((ricciTensor_scaleMetric _ hpos _ y.1 v.1 w.1).trans
        (roundMetric_ricciTensor y.1 v.1 w.1))
  rw [hric]
  have hi := cylinderMetric_inner h y (((2 * (1 - s))⁻¹ • v.1, (0 : ℝ))) w
  change _ = (cylinderMetric h).inner y (((2 * (1 - s))⁻¹ • v.1, (0 : ℝ))) w
  rw [hi]
  change (((2 : ℕ) : ℝ) - 1) *
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 v.1 w.1 =
    max (2 * (1 - s)) 1 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1
      ((2 * (1 - s))⁻¹ • v.1) w.1 + 0 * w.2
  have hsmul := congrArg (fun L : TangentSpace I2 y.1 →L[ℝ] ℝ => L w.1)
    (((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1).map_smul
      (2 * (1 - s))⁻¹ v.1)
  change (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1
      ((2 * (1 - s))⁻¹ • v.1) w.1 =
    (2 * (1 - s))⁻¹ * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 v.1 w.1
    at hsmul
  rw [hsmul, hmax, ← mul_assoc, mul_inv_cancel₀ hc.ne']
  push_cast
  ring

theorem sqrt_inner_ricciSharp_cylinderReferenceMetric_le {s : ℝ} (hs : s ≤ 0) (y : Cylinder)
    (v : TangentSpace IC y) :
    Real.sqrt ((cylinderReferenceMetric s).inner y (ricciSharp (cylinderReferenceMetric s) y v)
        (ricciSharp (cylinderReferenceMetric s) y v)) ≤
      (1 / 2) * Real.sqrt ((cylinderReferenceMetric s).inner y v v) := by
  let g := cylinderReferenceMetric s
  let u : TangentSpace IC y := (v.1, 0)
  have hc : 0 < 2 * (1 - s) := by linarith
  have he : ricciSharp g y v = (2 * (1 - s))⁻¹ • u := by
    refine (ricciSharp_cylinderReferenceMetric hs y v).trans ?_
    apply Prod.ext
    · rfl
    · change (0 : ℝ) = (2 * (1 - s))⁻¹ * 0
      ring
  have hn : Real.sqrt (g.inner y u u) ≤ Real.sqrt (g.inner y v v) := by
    apply Real.sqrt_le_sqrt
    rw [cylinderReferenceMetric_inner s hs, cylinderReferenceMetric_inner s hs]
    nlinarith [sq_nonneg v.2]
  have hcoef : |(2 * (1 - s))⁻¹| ≤ 1 / 2 := by
    rw [abs_of_pos (inv_pos.mpr hc)]
    rw [inv_le_comm₀ hc (by norm_num)]
    linarith
  change Real.sqrt (g.inner y (ricciSharp g y v) (ricciSharp g y v)) ≤
    (1 / 2) * Real.sqrt (g.inner y v v)
  calc
    _ = Real.sqrt (g.inner y ((2 * (1 - s))⁻¹ • u) ((2 * (1 - s))⁻¹ • u)) := by rw [he]
    _ = |(2 * (1 - s))⁻¹| * Real.sqrt (g.inner y u u) :=
      DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul g y _ u
    _ ≤ (1 / 2) * Real.sqrt (g.inner y v v) :=
      mul_le_mul hcoef hn (Real.sqrt_nonneg _) (by norm_num)

private theorem abs_trace_le_of_sqrt_inner_bound
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

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {eps depth t : ℝ} {x : M}

theorem TruncatedNeck.abs_scalar_center_sub_le (nk : TruncatedNeck S eps depth x t) {r : ℝ}
    (hr : r ∈ Icc (-depth) 0) :
    |(S.scalar t x)⁻¹ * S.scalar (t + r / S.scalar t x) x - (1 - r)⁻¹| ≤ 2400 * eps := by
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
  let y : O := ⟨(nk.center, 0), mem_univ _, neg_lt_zero.mpr (inv_pos.mpr heps0),
    inv_pos.mpr heps0⟩
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
  have htrace := abs_trace_le_of_sqrt_inner_bound gRef y
    ((ricciSharp G y).toLinearMap - (ricciSharp gRef y).toLinearMap) (800 * eps)
    (fun v => by simpa only [LinearMap.sub_apply, ContinuousLinearMap.coe_coe] using hbound v)
  rw [map_sub, ← metricScalar_eq_trace_ricciSharp, ← metricScalar_eq_trace_ricciSharp] at htrace
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = 3 := by simp
  rw [hdim] at htrace
  have hGscalar : metricScalarAt G y = Q⁻¹ * S.scalar (t + r / Q) x := by
    change metricScalarAt (localPullMetric (rescaledMetric S t Q hQ r) f hf) y = _
    rw [metricScalarAt_localPull]
    change metricScalarAt (scaleMetric Q hQ (S.base.metric (parabolicTime t Q r)))
      (nk.map (nk.center, 0)) = _
    rw [metricScalarAt_scaleMetric, nk.center_eq]
    rfl
  have hRscalar : metricScalarAt gRef y = (1 - r)⁻¹ := by
    change metricScalarAt ((nk.cylinder.metric r).restrictOpen O) y = _
    rw [metricScalarAt_restrictOpen, hcyl]
    exact cylinderReferenceMetric_scalar r hr.2 _
  rw [hGscalar, hRscalar] at htrace
  change |Q⁻¹ * S.scalar (t + r / Q) x - (1 - r)⁻¹| ≤ 2400 * eps
  push_cast at htrace
  linarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
