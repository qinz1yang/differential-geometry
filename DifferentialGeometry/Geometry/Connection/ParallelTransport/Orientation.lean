import DifferentialGeometry.Geometry.Comparison.Variation.EndpointInterpolation
import DifferentialGeometry.Bundle.Orientation.FrameTransport

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.VectorBundle

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def parallelTransportLinearMapToTime (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    (t : Icc (0 : ℝ) L) : TangentSpace I (γ 0) →ₗ[ℝ] TangentSpace I (γ t) where
  toFun v := parallelTransportSectionOnIcc (I := I) g γ hγ hL v t
  map_add' v w := parallelTransportSectionOnIcc_add g γ hγ hL v w t.property
  map_smul' c v := parallelTransportSectionOnIcc_smul g γ hγ hL c v t.property


theorem parallelTransportLinearMapToTime_injective (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    (t : Icc (0 : ℝ) L) : Function.Injective (parallelTransportLinearMapToTime g γ hγ hL t) := by
  intro v w hvw
  have hh := parallel_transport_unique_of_eq_at_point (I := I) g γ le_rfl hγ
    (parallelTransportSectionOnIcc (I := I) g γ hγ hL v)
    (parallelTransportSectionOnIcc (I := I) g γ hγ hL w)
    (fun s hs => parallelTransportSectionOnIcc_differentiableAt g γ hγ hL v hs)
    (fun s hs => parallelTransportSectionOnIcc_differentiableAt g γ hγ hL w hs)
    (fun s hs => parallelTransportSectionOnIcc_covDerivAlong g γ hγ hL v hs)
    (fun s hs => parallelTransportSectionOnIcc_covDerivAlong g γ hγ hL w hs)
    t.property hvw 0 ⟨le_rfl, hL.le⟩
  simpa only [parallelTransportSectionOnIcc_initial] using hh


def parallelTransportLinearEquivToTime (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I (2 : ℕ∞) γ) {L : ℝ} (hL : 0 < L)
    (t : Icc (0 : ℝ) L) : TangentSpace I (γ 0) ≃ₗ[ℝ] TangentSpace I (γ t) :=
  LinearEquiv.ofBijective (parallelTransportLinearMapToTime g γ hγ hL t)
    ⟨parallelTransportLinearMapToTime_injective g γ hγ hL t,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rfl)).mp
        (parallelTransportLinearMapToTime_injective g γ hγ hL t)⟩

theorem parallelTransportToTime_continuous (g : SmoothRiemannianMetric I M) (γ : ℝ → M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (v : TangentSpace I (γ 0)) :
    Continuous (fun t : Icc (0 : ℝ) L =>
      (⟨γ t, parallelTransportLinearEquivToTime g γ (hγ.of_le (by decide)) hL t v⟩ :
        TangentBundle I M)) := by
  obtain ⟨V, hV0, hdiff, hpar, hs⟩ := parallelTransport_section_contMDiffOn g γ hγ hL v
  have heq := parallel_field_eq_section g γ (hγ.of_le (by decide)) hL V v hV0 hdiff hpar
  have hc := continuousOn_iff_continuous_domRestrict.mp hs.continuousOn
  convert hc using 1
  funext t
  exact congrArg (fun w => (⟨γ t, w⟩ : TangentBundle I M)) (heq t t.property).symm

theorem parallelTransport_preserves_orientation {n : ℕ} [NeZero n]
    (hdim : Module.finrank ℝ E = n) (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) {L : ℝ} (hL : 0 < L)
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin n))
    (ho : IsCompatibleOrientation (F := E) (TangentSpace I) o) :
    Orientation.map (Fin n)
      (parallelTransportLinearEquivOnIcc (I := I) g γ (hγ.of_le (by decide)) hL)
      (o (γ 0)) = o (γ L) := by
  obtain ⟨b₀, hb₀⟩ := orientation_has_basis (V := E) hdim (o (γ 0))
  let t₀ : Icc (0 : ℝ) L := ⟨0, le_rfl, hL.le⟩
  let t₁ : Icc (0 : ℝ) L := ⟨L, hL.le, le_rfl⟩
  let P := parallelTransportLinearEquivToTime g γ (hγ.of_le (by decide)) hL
  let b := fun t : Icc (0 : ℝ) L => b₀.map (P t)
  have hb (i : Fin n) : Continuous (fun t : Icc (0 : ℝ) L =>
      (⟨γ t, b t i⟩ : TangentBundle I M)) :=
    parallelTransportToTime_continuous g γ hγ hL (b₀ i)
  have hP₀ : P t₀ = LinearEquiv.refl ℝ (TangentSpace I (γ 0)) := by
    ext v
    exact parallelTransportSectionOnIcc_initial g γ (hγ.of_le (by decide)) hL v
  have hstart : (b t₀).orientation = o (γ t₀) := by
    change (b₀.map (P t₀)).orientation = o (γ 0)
    rw [hP₀]
    have heq : b₀.map (LinearEquiv.refl ℝ (TangentSpace I (γ 0))) = b₀ := by
      ext i
      rfl
    rw [heq]
    exact hb₀
  let : PreconnectedSpace (Icc (0 : ℝ) L) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hend := (frame_orientation_eq_iff (tangentBundleCore I M) hdim
    (fun t : Icc (0 : ℝ) L => γ t) (hγ.continuous.comp continuous_subtype_val)
    o ho b hb t₀ t₁).mp hstart
  rw [← hb₀]
  exact (b₀.orientation_map (parallelTransportLinearEquivOnIcc (I := I) g γ
    (hγ.of_le (by decide)) hL)).symm.trans hend

end DifferentialGeometry.Geometry.Riemannian.Geodesic
