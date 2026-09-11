import DifferentialGeometry.Geometry.Comparison.Variation.EndpointInterpolation
import DifferentialGeometry.Geometry.Comparison.Variation.Curve.ArcLength

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


lemma velocity_contMDiff {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun t =>
      (⟨γ t, mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)⟩ : TangentBundle I M)) := by
  have hconst : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  exact (hγ.contMDiff_tangentMap (m := ∞) (by simp)).comp hconst

variable [FiniteDimensional ℝ E] [I.Boundaryless]

theorem parallelTransportSection_velocity (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (hg : IsGeodesicOn (I := I) g γ (Icc 0 L)) :
    let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by decide)
    ∀ t ∈ Icc (0 : ℝ) L,
      parallelTransportSectionOnIcc (I := I) g γ hγ2 hL
        (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) t = mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ) := by
  dsimp only
  have hvel := velocity_contMDiff hγ
  have hh := parallel_field_eq_section g γ (hγ.of_le (by decide)) hL
    (fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) rfl
    (fun t _ => DifferentialGeometry.Geometry.Riemannian.Variation.chartRepAt_differentiableAt_of_total_contMDiffAt
      (hvel.contMDiffAt.of_le (by decide)))
    (fun t ht => covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t
      (hγ.contMDiffAt.of_le (by decide)) (hg t ht))
  exact fun t ht => (hh t ht).symm

theorem exists_smooth_parallel_unit_normal_field (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (hg : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (v : TangentSpace I (γ 0)) (hunit : g.inner (γ 0) v v = 1)
    (hnormal : g.inner (γ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) v = 0) :
    let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by decide)
    ∃ (δ : ℝ) (V : ∀ t, TangentSpace I (γ t)), 0 < δ ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
        (fun t => (⟨γ t, V t⟩ : TangentBundle I M)) (Ioo (-δ) (L + δ)) ∧
      V 0 = v ∧
      (∀ t ∈ Icc (0 : ℝ) L, covDerivAlong (I := I) g γ V t = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (V t) (V t) = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) L, g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) (V t) = 0) ∧
      (∀ t ∈ Icc (0 : ℝ) L,
        V t = parallelTransportSectionOnIcc (I := I) g γ hγ2 hL v t) := by
  dsimp only
  let hγ2 : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ := hγ.of_le (by decide)
  obtain ⟨δ, hδ, V, hV0, hdiff, hpar, hsmooth⟩ :=
    parallelTransport_section_contMDiffOn_Ioo g γ hγ hL v
  have hcc : Icc (0 : ℝ) L ⊆ Ioo (-δ) (L + δ) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hVdiff := fun t ht => hdiff t (hcc ht)
  have hVpar := fun t ht => hpar t (hcc ht)
  have hVeq := parallel_field_eq_section g γ hγ2 hL V v hV0 hVdiff hVpar
  have hTdiff := fun t (_ : t ∈ Icc (0 : ℝ) L) =>
    DifferentialGeometry.Geometry.Riemannian.Variation.chartRepAt_differentiableAt_of_total_contMDiffAt
      ((velocity_contMDiff hγ).contMDiffAt (x := t) |>.of_le (by decide))
  have hTpar := fun t (ht : t ∈ Icc (0 : ℝ) L) =>
    covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g γ t
      (hγ.contMDiffAt.of_le (by decide)) (hg t ht)
  refine ⟨δ, V, hδ, hsmooth, hV0, hVpar, ?_, ?_, hVeq⟩
  · intro t ht
    have hh := parallel_transport_preserves_inner_product g γ le_rfl hγ2 V V
      hVdiff hVdiff hVpar hVpar t ht
    rw [hV0, hunit] at hh
    exact hh
  · intro t ht
    have hh := parallel_transport_preserves_inner_product g γ le_rfl hγ2
      (fun t => mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)) V hTdiff hVdiff hTpar hVpar t ht
    rw [hV0, hnormal] at hh
    exact hh

end DifferentialGeometry.Geometry.Riemannian.Geodesic
