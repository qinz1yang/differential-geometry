import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMap
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.PartialDiffeomorph
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem originalChartFrame_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit [CompleteSpace E] in
/-- The original interior chart is a genuine local isometry into the complete pole chart
metric; injectivity on the chart domain upgrades it to the partial isometry used for frame
transport. -/
theorem boundaryOriginal_chart_partial_isometry
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ v w : E,
      G.inner y v w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y v w) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      originalChartFrame_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    let F := fun x : U => extChartAt I p (x : M)
    let S := {x : U | (x : M) ∈
        (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F x ∈ O}
    (∃ x : U, x ∈ S) →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) U E ∞,
        Φ.source = S ∧ (∀ x ∈ S, Φ x = F x) ∧
        ∀ x ∈ S, ∀ v w : TangentSpace 𝓘(ℝ, E) x,
          k.inner x v w = G.inner (Φ x)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ x v)
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) Φ x w) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    originalChartFrame_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  let F := fun x : U => extChartAt I p (x : M)
  let S := {x : U | (x : M) ∈
      (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧ F x ∈ O}
  dsimp only
  intro hSnonempty
  obtain ⟨hSopen, hlocal, hmetric⟩ := boundaryInteriorChart_metric_isometry g p G O hG
  have hinj : Set.InjOn F S := by
    intro x hx y hy hxy
    apply Subtype.ext
    have hxsource : (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source :=
      hx.1
    have hysource : (y : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source :=
      hy.1
    have hxleft : (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm (F x) = (x : M) := by
      convert (DifferentialGeometry.Manifold.interiorChart I ∞ p).left_inv hxsource using 1
      rfl
    have hyleft : (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm (F y) = (y : M) := by
      convert (DifferentialGeometry.Manifold.interiorChart I ∞ p).left_inv hysource using 1
      rfl
    calc
      (x : M) = (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm (F x) := hxleft.symm
      _ = (DifferentialGeometry.Manifold.interiorChart I ∞ p).symm (F y) := by rw [hxy]
      _ = (y : M) := hyleft
  obtain ⟨Φ, hsource, _htarget, hfun⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      hlocal hSopen hSnonempty hinj
  refine ⟨Φ, ?_, ?_, ?_⟩
  · exact hsource
  · intro x hx
    rw [hfun]
  · intro x hx v w
    have hFx : Φ x = F x := by
      rw [hfun]
    rw [hFx, hfun]
    exact hmetric x hx v w

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₂ H₁}
  [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁] [T2Space M₁]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace E₂ M₂]
  [IsManifold 𝓘(ℝ, E₂) ∞ M₂] [T2Space M₂]

omit [I₁.Boundaryless] in
/-- A metric-preserving partial diffeomorphism has the corresponding inverse metric identity
on its open source and image, with the genuine inverse differential. -/
theorem partialIsometry_inverse_inner_on_opens
    (g : SmoothRiemannianMetric I₁ M₁)
    (h : SmoothRiemannianMetric 𝓘(ℝ, E₂) M₂)
    (Φ : PartialDiffeomorph I₁ 𝓘(ℝ, E₂) M₁ M₂ ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I₁ x,
      h.inner (Φ x) (mfderiv I₁ 𝓘(ℝ, E₂) Φ x v)
        (mfderiv I₁ 𝓘(ℝ, E₂) Φ x w) =
        g.inner x v w) :
    let U : Opens M₁ := ⟨Φ.source, Φ.open_source⟩
    let V : Opens M₂ := ⟨(Φ : M₁ → M₂) '' (U : Set M₁),
      DifferentialGeometry.image_opens_isOpen Φ (by intro x hx; exact hx)⟩
    let Ψ : U ≃ₘ⟮I₁, 𝓘(ℝ, E₂)⟯ V := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo
      Φ (by intro x hx; exact hx)
    ∀ y : V, ∀ v w : TangentSpace (𝓘(ℝ, E₂)) y,
      (h.restrictOpen V).inner y v w =
        (g.restrictOpen U).inner (Ψ.symm y)
          (mfderiv 𝓘(ℝ, E₂) I₁ (Ψ.symm : V → U) y v)
          (mfderiv 𝓘(ℝ, E₂) I₁ (Ψ.symm : V → U) y w) := by
  let U : Opens M₁ := ⟨Φ.source, Φ.open_source⟩
  have hU : (U : Set M₁) ⊆ Φ.source := fun _ hx => hx
  let V : Opens M₂ := ⟨(Φ : M₁ → M₂) '' (U : Set M₁),
    DifferentialGeometry.image_opens_isOpen Φ hU⟩
  let Ψ : U ≃ₘ⟮I₁, 𝓘(ℝ, E₂)⟯ V := DifferentialGeometry.PartialDiffeomorph.toOpensDiffeo Φ hU
  dsimp only
  intro y v w
  have hforward (x : U) (a b : TangentSpace I₁ x) :
      (h.restrictOpen V).inner (Ψ x)
          (mfderiv I₁ 𝓘(ℝ, E₂) Ψ x a) (mfderiv I₁ 𝓘(ℝ, E₂) Ψ x b) =
        (g.restrictOpen U).inner x a b := by
    have hda : mfderiv I₁ 𝓘(ℝ, E₂) Ψ x a =
        mfderiv I₁ 𝓘(ℝ, E₂) Φ (x : M₁) a :=
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU x a
    have hdb : mfderiv I₁ 𝓘(ℝ, E₂) Ψ x b =
        mfderiv I₁ 𝓘(ℝ, E₂) Φ (x : M₁) b :=
      DifferentialGeometry.PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hU x b
    change h.inner (Φ (x : M₁)) (mfderiv I₁ 𝓘(ℝ, E₂) Ψ x a)
      (mfderiv I₁ 𝓘(ℝ, E₂) Ψ x b) = g.inner (x : M₁) a b
    rw [hda, hdb]
    exact hmet (x : M₁) x.property a b
  have hinv (q : TangentSpace (𝓘(ℝ, E₂)) y) :
      mfderiv I₁ 𝓘(ℝ, E₂) Ψ (Ψ.symm y)
          (mfderiv 𝓘(ℝ, E₂) I₁ (Ψ.symm : V → U) y q) = q :=
    DifferentialGeometry.Diffeomorph.mfderiv_apply_mfderiv_symm_apply
      (I := I₁) (E := E₂) (Φ := Ψ) y q
  have h := hforward (Ψ.symm y)
    (mfderiv 𝓘(ℝ, E₂) I₁ (Ψ.symm : V → U) y v)
    (mfderiv 𝓘(ℝ, E₂) I₁ (Ψ.symm : V → U) y w)
  simp only [hinv v, hinv w] at h
  have hy : Ψ (Ψ.symm y) = y := Ψ.apply_symm_apply y
  rw [hy] at h
  exact h

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  [I₁.Boundaryless]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁] [T2Space M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  [I₂.Boundaryless]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂] [T2Space M₂]

/-- Parallel fields transfer through a partial local isometry by the actual Levi-Civita
connection naturality law. -/
theorem partialIsometry_preserves_parallel
    (g : SmoothRiemannianMetric I₁ M₁) (h : SmoothRiemannianMetric I₂ M₂)
    (Φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞)
    (hmet : ∀ x ∈ Φ.source, ∀ v w : TangentSpace I₁ x,
      h.inner (Φ x) (mfderiv I₁ I₂ Φ x v) (mfderiv I₁ I₂ Φ x w) =
        g.inner x v w)
    (γ : ℝ → M₁) (V : ∀ s, TangentSpace I₁ (γ s)) {t : ℝ}
    (ht : γ t ∈ Φ.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I₁ γ t)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I₁) γ V t) t)
    (hpar : covDerivAlong g γ V t = 0) :
    covDerivAlong h (fun s => Φ (γ s))
      (fun s => mfderiv I₁ I₂ Φ (γ s) (V s)) t = 0 := by
  have hnat := mfderiv_covDerivAlong_partialDiffeomorph g h Φ hmet γ V ht hγ hV
  rw [hpar] at hnat
  simpa using hnat.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
