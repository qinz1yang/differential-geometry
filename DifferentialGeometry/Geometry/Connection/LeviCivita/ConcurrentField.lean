import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Cross
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenSubtype
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Bundle TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Connection

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {G : Type*} [TopologicalSpace G] {I : ModelWithCorners ℝ E G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold I ∞ N] [T2Space N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {H : Type*} [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

theorem exists_concurrent_field_of_partialDiffeomorph
    (g : SmoothRiemannianMetric J M)
    (Φ : PartialDiffeomorph I J N M ∞)
    (gE : SmoothRiemannianMetric I N)
    (V : Opens N) (hV : (V : Set N) ⊆ Φ.source)
    (hmetric : ∀ y ∈ V, ∀ v w : TangentSpace I y, gE.inner y v w =
      g.inner (Φ y) (mfderiv I J Φ y v)
        (mfderiv I J Φ y w))
    (Z : ContMDiffSection I E ∞ (TangentSpace I : N → Type _))
    (hZ : ∀ y ∈ V, ∀ v : TangentSpace I y, metricCov gE Z y v = v) :
    ∃ W : Opens M, (W : Set M) = Φ '' (V : Set N) ∧
      ∃ ZM : ContMDiffSection J F ∞ (TangentSpace J : W → Type _),
        ∀ y : W, ∀ v : TangentSpace J y,
          metricCov (g.restrictOpen W) ZM y v = v := by
  let W : Opens M := ⟨Φ '' (V : Set N), image_opens_isOpen Φ hV⟩
  let Ψ : Diffeomorph I J V W ∞ :=
    DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hV
  let ZV : ContMDiffSection I E ∞ (TangentSpace I : V → Type _) :=
    ⟨restrictOpenTangentField V Z, contMDiff_restrictOpen_section V Z⟩
  have hd (y : V) (v : TangentSpace I y) : mfderiv I J Ψ y v =
      mfderiv I J Φ (y : N) v :=
    DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hV y v
  have hg : gE.restrictOpen V = Diffeomorph.pullbackMetricCross (g.restrictOpen W) Ψ := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    erw [SmoothRiemannianMetric.restrictOpen_inner,
      Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      hd, hd]
    exact hmetric y y.2 v w
  refine ⟨W, rfl, pushFwdSectionCross Ψ ZV, ?_⟩
  intro y v
  obtain ⟨x, rfl⟩ := Ψ.surjective y
  let dΨ := Ψ.mfderivToContinuousLinearEquiv (by simp : (∞ : WithTop ℕ∞) ≠ 0) x
  let a := dΨ.symm v
  have ha : mfderiv I J Ψ x a = v := by
    rw [← Ψ.mfderivToContinuousLinearEquiv_coe
      (by simp : (∞ : WithTop ℕ∞) ≠ 0)]
    exact dΨ.apply_symm_apply v
  have hcov : metricCov (gE.restrictOpen V) ZV x a = a := by
    change metricCov (gE.restrictOpen V) (restrictOpenTangentField V Z) x a = a
    rw [metricCov_restrictOpen_globalSection gE V Z x a]
    exact hZ x x.2 a
  rw [hg] at hcov
  have h := metricCov_pullbackCross (g.restrictOpen W) Ψ ZV x a
  rw [hcov, ha] at h
  exact h.symm

end DifferentialGeometry.Geometry.Connection
