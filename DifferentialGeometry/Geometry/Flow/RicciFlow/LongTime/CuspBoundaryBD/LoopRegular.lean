import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Comparison.Variation.FirstVariation.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeAlong

/-!
# IMS04 / G4c（S-A10-BOUNDARY, suffix `_BD`）：`PrescribedCuspMeridian.loop` 处处正则

`PrescribedCuspMeridian.geodesic`（`torusMetric` 下的 geodesic）+ `embedded`（单射）⇒ `loop'(s) ≠ 0`
处处成立。曲率估计（`riemannianCurveCurvature` 的 `σ⁻¹`、unit tangent 光滑性）需要这一点：
geodesic 的 speed 为常数（`d/ds g(γ',γ') = 2 g(D γ', γ') = 0`），speed = 0 则 `γ' ≡ 0`，
`γ` locally constant ⇒ 常值，与 `embedded` 矛盾。
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ContDiff
namespace GC.LongTime
universe u
open GC.Endpoint DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- geodesic 的 speed² 是常数。 -/
theorem inner_velocity_const_of_isGeodesic_BD (g : SmoothRiemannianMetric I M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hgeo : IsGeodesic (I := I) g γ) (s : ℝ) :
    g.inner (γ s) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) (mfderiv 𝓘(ℝ, ℝ) I γ s 1) =
      g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1) := by
  have hd : ∀ x, HasDerivAt (fun y => g.inner (γ y) (mfderiv 𝓘(ℝ, ℝ) I γ y 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ y 1)) 0 x := by
    intro x
    have hγ2 : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ x :=
      (hγ x).of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ (⊤ : ℕ∞)))
    have hr := differentiableAt_chartRepAt_curveVelocity (I := I) hγ2
    have h := inner_deriv_at (I := I) (by simp : (1 : WithTop ℕ∞) ≤ ∞) g γ
      (fun y => mfderiv 𝓘(ℝ, ℝ) I γ y 1) (fun y => mfderiv 𝓘(ℝ, ℝ) I γ y 1) x
      (hγ x) hr hr
    have hacc := covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ x hγ2 (hgeo x)
    erw [hacc] at h
    simpa using h
  have hdiff : Differentiable ℝ (fun y => g.inner (γ y) (mfderiv 𝓘(ℝ, ℝ) I γ y 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ y 1)) := fun x => (hd x).differentiableAt
  have hzero : ∀ x, deriv (fun y => g.inner (γ y) (mfderiv 𝓘(ℝ, ℝ) I γ y 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ y 1)) x = 0 := fun x => (hd x).deriv
  exact is_const_of_deriv_eq_zero hdiff hzero s 0

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] in
/-- `ℝ → M` 光滑曲线速度处处为 `0` ⇒ locally constant（`Topology/Diffeomorph/Product.lean` 里
同名 private 引理的 `V = ℝ` 版本，原样搬运）。 -/
theorem isLocallyConstant_of_mfderiv_eq_zero_BD [IsManifold I 1 M] {f : ℝ → M}
    (hf : MDifferentiable 𝓘(ℝ, ℝ) I f) (hz : ∀ r, mfderiv 𝓘(ℝ, ℝ) I f r = 0) :
    IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  let e := extChartAt I (f x)
  let U : Set ℝ := f ⁻¹' e.source
  let F : ℝ → E := e ∘ f
  have hU : IsOpen U := (isOpen_extChartAt_source (I := I) (f x)).preimage hf.continuous
  have hxU : x ∈ U := mem_extChartAt_source (f x)
  have hmd (r : ℝ) (hr : r ∈ U) : MDifferentiableAt I 𝓘(ℝ, E) e (f r) := by
    apply mdifferentiableAt_extChartAt
    simpa only [U, e, Set.mem_preimage, extChartAt_source] using hr
  have hF : DifferentiableOn ℝ F U := by
    intro r hr
    exact ((hmd r hr).comp r (hf r)).differentiableAt.differentiableWithinAt
  have hFzero : U.EqOn (fderiv ℝ F) 0 := by
    intro r hr
    have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) r (hmd r hr) (hf r)
    rw [hz r, ContinuousLinearMap.comp_zero, mfderiv_eq_fderiv] at hchain
    exact hchain
  have hopen : IsOpen (U ∩ F ⁻¹' ({F x} : Set E)) :=
    hU.isOpen_inter_preimage_of_fderiv_eq_zero hF hFzero {F x}
  have hxmem : x ∈ U ∩ F ⁻¹' ({F x} : Set E) := ⟨hxU, rfl⟩
  filter_upwards [hopen.mem_nhds hxmem] with r hr
  exact e.injOn hr.1 hxU hr.2

/-- 嵌入的 geodesic 圈速度处处非零：speed 常数；为 `0` 则 `γ` 常值，与单射矛盾。 -/
theorem loop_velocity_ne_zero_BD (g : SmoothRiemannianMetric I M) (loop : freeLoop M)
    (hs : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift loop)) (hgeo : IsGeodesic (I := I) g (loopLift loop))
    (hemb : Topology.IsEmbedding loop) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) I (loopLift loop) s 1 ≠ 0 := by
  intro h0
  have hconst := inner_velocity_const_of_isGeodesic_BD g hs hgeo
  have hq0 : ∀ x, g.inner (loopLift loop x) (mfderiv 𝓘(ℝ, ℝ) I (loopLift loop) x 1)
      (mfderiv 𝓘(ℝ, ℝ) I (loopLift loop) x 1) = 0 := by
    intro x
    rw [hconst x, ← hconst s, h0]
    simp
  have hvel : ∀ x, mfderiv 𝓘(ℝ, ℝ) I (loopLift loop) x 1 = 0 := by
    intro x
    by_contra hne
    exact (g.pos _ _ hne).ne' (hq0 x)
  have hzero : ∀ x, mfderiv 𝓘(ℝ, ℝ) I (loopLift loop) x = 0 := fun x =>
    ContinuousLinearMap.ext_ring (hvel x)
  have hloc := isLocallyConstant_of_mfderiv_eq_zero_BD
    (fun x => (hs x).mdifferentiableAt (by simp)) hzero
  have heq : loopLift loop 0 = loopLift loop (1 / 2) := hloc.apply_eq_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ _)
  rw [loopLift_apply, loopLift_apply] at heq
  have hinj := hemb.injective heq
  obtain ⟨n, hn⟩ := (loopCircle_coe_eq_coe_iff 0 (1 / 2)).mp hinj
  have h1 : (n : ℝ) = -1 / 2 := by linarith
  rcases le_or_gt 0 n with hn0 | hn0
  · have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    linarith
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn0
    linarith

end Generic

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- **G4c**：`PrescribedCuspMeridian.loop` 的速度（`torusMetric` 下）处处非零。 -/
theorem PrescribedCuspMeridian.loop_velocity_ne_zero_BD (M : PrescribedCuspMeridian cores)
    (s : ℝ) : mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift M.loop) s 1 ≠ 0 :=
  GC.LongTime.loop_velocity_ne_zero_BD _ M.loop M.smooth M.geodesic M.embedded s

end GC.LongTime
