import DifferentialGeometry.Geometry.Connection.LeviCivita.Reconcile
import DifferentialGeometry.Geometry.Curvature.Basic
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CurvatureBundling
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Field
import DifferentialGeometry.Geometry.Curvature.Riemann.Basic.Sections
import DifferentialGeometry.Geometry.Curvature.Metric

/-!
# Curvature/Ricci lift of the Levi-Civita reconciliation

`Connection/LeviCivita/Reconcile.lean` proves the two Levi-Civita constructions agree on
differentiable sections.  This file lifts that to the Riemann-curvature field: the
connection-curvature field of `leviCivitaConnectionOfMetric g` (which drives `metricRicciAt`/
`metricRm04`) equals that of the stitched `LeviCivita g` (which drives `ricciTensor`), on smooth
sections (step 1), and then the pointwise `(1,3)` Riemann tensors agree (step 2).  This is the
path toward `metricRicciAt = ricciTensor` and hence `ricciCont`.
-/

namespace DifferentialGeometry

open Bundle Manifold Set Tensor0SBundle
open scoped Manifold Topology ContDiff
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Local smoothness of the stitched Levi-Civita connection** — the canonical producer.
Transferred from the Koszul connection's local smoothness (`metricCov_smooth`) across the
agreement of the two Levi-Civita constructions on differentiable sections
(`leviCivitaConnectionOfMetric_apply_eq_leviCivita`).  This discharges the standing
`ContMDiffCovariantDerivativeLocally (LeviCivita g)` hypothesis that the curvature reconcile
previously had to carry. -/
theorem leviCivita_contMDiffCovariantDerivativeLocally (g : SmoothRiemannianMetric I M) :
    CovariantDerivative.ContMDiffCovariantDerivativeLocally (LeviCivita (I := I) g) ∞ := by
  simpa [LeviCivita, metricCov] using (metricCov_smooth (I := I) g)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Curvature-field cov-congruence.**  On smooth sections, the connection-curvature field of
`leviCivitaConnectionOfMetric g` equals that of the stitched `LeviCivita g` — the curvature-level
consequence of the connection reconciliation.  The smoothness of `∇_Y Z` (needed to apply the
reconciliation at the second covariant level) comes from the public `cov_smooth_apply_contMDiffAt`,
which only requires `∞`-sections. -/
theorem connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (X Y Z : ContMDiffSection I E (∞ : WithTop ℕ∞) (TangentSpace I : M → Type _))
    (x : M) :
    connectionRiemannCurvatureField (I := I) (leviCivitaConnectionOfMetric (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x
      = connectionRiemannCurvatureField (I := I) (LeviCivita (I := I) g)
        (fun p => X p) (fun p => Y p) (fun p => Z p) x := by
  simp [LeviCivita]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **Step 2: `riemannCurvatureAt` agreement.**  The pointwise `(1,3)` Riemann tensors of the
two Levi-Civita constructions coincide, lifted from the curvature-field cov-congruence (step 1)
by `riemannCurvatureAt_apply_smooth` + tensor extensionality.  Arbitrary tangent inputs are
extended to global smooth (`∞`-)sections via `ContMDiffSection.exists_eq_at`. -/
theorem riemannCurvatureAt_lcOfMetric_eq_leviCivita
    (g : SmoothRiemannianMetric I M)
    (x : M) :
    riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g)
        (metricCov_smooth (I := I) g) x
      = riemannCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  classical
  have hcov₁ := metricCov_smooth (I := I) g
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  apply tensorRSSpace_ext (𝕜 := ℝ) 1 3 x
  intro α
  apply ContinuousMultilinearMap.ext
  intro v
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 0)
  obtain ⟨Y, hY⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 1)
  obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x (v 2)
  have hv : v = vec3 (X x) (Y x) (Z x) := by
    funext i; fin_cases i <;> simp_all [vec3]
  rw [hv]
  change riemannCurvatureAt (leviCivitaConnectionOfMetric (I := I) g) hcov₁ x α
      (vec3 (X x) (Y x) (Z x)) =
    riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x α
      (vec3 (X x) (Y x) (Z x))
  rw [riemannCurvatureAt_apply_smooth (I := I) (leviCivitaConnectionOfMetric (I := I) g)
      hcov₁ X Y Z α,
    riemannCurvatureAt_apply_smooth (I := I) (LeviCivita (I := I) g) hcov₂ X Y Z α]
  exact congrArg _
    (connectionRiemannCurvatureField_lcOfMetric_eq_leviCivita (I := I) g X Y Z x)

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Tensoriality bridge.**  The raw curvature `riemannCurvatureAux` on the *chart-constant*
extensions of fibre vectors equals the bundled `riemannOp` (built from *globally smooth*
extensions).  Proof chain: rewrite the raw curvature as `connectionRiemannCurvatureField` on the
constant extensions (`riemannCurvatureAux_eq_connectionRiemannCurvatureField`); replace those by
genuinely smooth extensions agreeing with the constants near `x`
(`connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst`); then identify
`connectionRiemannCurvatureField = riemannSec = riemannOp` on smooth sections
(`riemannOp_apply_smooth`).  The local smoothness hypothesis supplies the global
`ContMDiffCovariantDerivative` instance that `riemannOp` needs, by specialization to `univ`. -/
theorem riemannCurvatureAux_tangentConst_eq_riemannOp
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative cov ∞]
    (hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞)
    (x : M) (X Y Z : TangentSpace I x) :
    riemannCurvatureAux cov (CovariantDerivative.tangentConstAt (I := I) x X)
        (CovariantDerivative.tangentConstAt (I := I) x Y)
        (CovariantDerivative.tangentConstAt (I := I) x Z) x
      = riemannOp cov x X Y Z := by
  obtain ⟨Xc, hXc, hXcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x X
  obtain ⟨Yc, hYc, hYcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Y
  obtain ⟨Zc, hZc, hZcx⟩ :=
    exists_contMDiffSection_eventuallyEq_tangentConstAt (I := I) x Z
  rw [riemannCurvatureAux_eq_connectionRiemannCurvatureField,
    connectionRiemannCurvatureField_eq_smooth_of_eventuallyEq_tangentConst
      (I := I) cov hcov X Y Z Xc Yc Zc hXc hYc hZc]
  have hsec :
      connectionRiemannCurvatureField cov
          (fun p : M => Xc p) (fun p : M => Yc p) (fun p : M => Zc p) x
        = riemannSec cov (fun p : M => Xc p) (fun p : M => Yc p)
            (fun p : M => Zc p) x := rfl
  rw [hsec, ← riemannOp_apply_smooth (cov := cov) Xc.contMDiff Yc.contMDiff Zc.contMDiff,
    hXcx, hYcx, hZcx]

/-- **Step 3: contraction-Ricci = trace-Ricci (within `LeviCivita g`).**  The contracted
`(1,3)` Ricci `ricciCurvatureAt (LeviCivita g)` agrees with the trace-of-`riemannOp` Ricci
`ricciTensor g`, as scalars.  Both reduce to the `chartModelBasis` trace-sum of the same Riemann
operator: the left via `ricciFromRm13At_apply_basis_trace` + `riemannCurvatureAt_apply_const`, the
right via `ricciTensor_apply_basisSum`, bridged term-by-term by
`riemannCurvatureAux_tangentConst_eq_riemannOp`. -/
theorem ricciCurvatureAt_leviCivita_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ricciCurvatureAt (LeviCivita (I := I) g)
        (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x (vec2 v w)
      = ricciTensor (I := I) g x v w := by
  classical
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  rw [ricciCurvatureAt_eq_trace,
    ricciFromRm13At_apply_basis_trace (chartModelBasis E)
      (riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x) v w,
    ricciTensor_apply_basisSum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [riemannCurvatureAt_apply_const,
    riemannCurvatureAux_tangentConst_eq_riemannOp (cov := LeviCivita (I := I) g) (hcov := hcov₂),
    cotangentToDual_dualToCotangent_gen, Module.Basis.coord_apply]
  rfl

/-- **Step 4 (the bridge): `metricRicciAt = ricciTensor` as scalars.**  The metric Ricci tensor
`metricRicciAt g` (Koszul / `metricCov` world, driving a folder-level `SolutionOn`) agrees with
`ricciTensor g` (stitched-`LeviCivita` world, with chart bridges) on every pair of tangent
vectors.  Chains step 2 (Riemann-tensor agreement) with step 3 (contraction = trace).  The
stitched-Levi-Civita local smoothness is now supplied internally by
`leviCivita_contMDiffCovariantDerivativeLocally`, so this bridge is hypothesis-free. -/
theorem metricRicciAt_apply_eq_ricciTensor
    (g : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) g x (vec2 v w) = ricciTensor (I := I) g x v w := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  rw [metricRicciAt, ricciCurvatureAt_eq_trace, key, ← ricciCurvatureAt_eq_trace]
  exact ricciCurvatureAt_leviCivita_apply_eq_ricciTensor (I := I) g x v w

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **(1,3) Rm two-worlds bridge.**  The canonical Koszul `(1,3)` Riemann tensor `metricRm13At g`
(driving every `SolutionOn`) equals the stitched-`LeviCivita` `(1,3)` Riemann tensor, as a pointwise
tensor.  `metricRm13At` is by definition the Koszul connection's `riemannCurvatureAt`, so this is
exactly the connection-level agreement `riemannCurvatureAt_lcOfMetric_eq_leviCivita`. -/
theorem metricRm13At_eq_riemannCurvatureAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm13At (I := I) g x
      = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  change riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvatureAt (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x
  exact riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] in
/-- **(0,4) Rm two-worlds bridge.**  The canonical Koszul lowered `(0,4)` Riemann tensor
`metricRm04At g` equals the stitched-`LeviCivita` lowered `(0,4)` Riemann tensor.  Both are the same
metric-lowering of their respective `(1,3)` Riemann tensors (`riemannCurvature04At` depends on the
connection only through `riemannCurvatureAt`), which agree by the connection-level
`riemannCurvatureAt_lcOfMetric_eq_leviCivita`. -/
theorem metricRm04At_eq_riemannCurvature04At
    (g : SmoothRiemannianMetric I M) (x : M) :
    metricRm04At (I := I) g x
      = riemannCurvature04At (I := I) g (LeviCivita (I := I) g)
          (leviCivita_contMDiffCovariantDerivativeLocally (I := I) g) x := by
  have hcov₂ := leviCivita_contMDiffCovariantDerivativeLocally (I := I) g
  have key : riemannCurvatureAt (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
           = riemannCurvatureAt (LeviCivita (I := I) g) hcov₂ x :=
    riemannCurvatureAt_lcOfMetric_eq_leviCivita (I := I) g x
  change riemannCurvature04At (I := I) g (metricCov (I := I) g) (metricCov_smooth (I := I) g) x
     = riemannCurvature04At (I := I) g (LeviCivita (I := I) g) hcov₂ x
  unfold riemannCurvature04At
  rw [key]

end DifferentialGeometry
