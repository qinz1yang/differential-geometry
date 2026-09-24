import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Compactness.OpenCoverImages

set_option autoImplicit false
noncomputable section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Nat → Type u}
  [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace H (M k)] [∀ k, IsManifold I ∞ (M k)]
  [∀ k, T2Space (M k)] [∀ k, SigmaCompactSpace (M k)]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [∀ k, PseudoEMetricSpace (M k)] [∀ k, RiemannianBundle (fun x : M k => TangentSpace I x)]
  [∀ k, IsRiemannianManifold I (M k)] [∀ k, CompleteSpace (M k)]
  [∀ k, IsContinuousRiemannianBundle E (fun x : M k => TangentSpace I x)]

variable
    {ι : Type uE} (g : ∀ k, SmoothRiemannianMetric I (M k))
    (hEnorm : ∀ k (x : M k) (v : TangentSpace I x), ‖v‖ₑ = ENNReal.ofReal (Real.sqrt ((g k).inner x v v)))
    (x : ι → ∀ k, M k) {ρ : Real} (hρ : 0 < ρ)
    (c : ∀ i k, IntrinsicBallChart (I := I) (g k) (hEnorm k) (x i k) ρ)
    (near : ι → ι → Bool)
    (hclass : ∀ i j, ∀ᶠ k in atTop,
      (near i j = true → edist (x i k) (x j k) < ENNReal.ofReal (ρ / 4)) ∧
      (near i j = false → ENNReal.ofReal (ρ / 4) ≤ edist (x i k) (x j k)))
    (J : {a : ι × ι // near a.1 a.2 = true} → E → E)
    (hcont : ∀ a, ContinuousOn (J a) (Metric.ball (0 : E) (ρ / 2)))
    (hconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball (0 : E) (ρ / 2))
      (fun k => ((c a.1.1 k).toNormalBallChart (g k) (hEnorm k) (x a.1.1 k) hρ).transition
        ((c a.1.2 k).toNormalBallChart (g k) (hEnorm k) (x a.1.2 k) hρ)) (J a))



theorem IntrinsicBallChart.eventually_mapsTo_eball_on_compact
    (b : ∀ k, M k) {r : ℝ} (hr : 0 ≤ r)
    (hcenter : ∀ i, ∀ᶠ k in atTop, edist (b k) (x i k) ≤ ENNReal.ofReal r) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    ∀ (V : TopologicalSpace.Opens D.toGlueData.glued) (A : Set D.toGlueData.glued),
      IsCompact A → A ⊆ V →
      ∀ (F : ∀ k, D.toGlueData.glued → M k),
      (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
          F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) →
      ∀ᶠ k in atTop, MapsTo (F k) A (Metric.eball (b k) (ENNReal.ofReal (r + ρ))) := by
  intro D U chartDomain V A hA hAV F hFtarget
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hlocal : ∀ i (L : Set U), IsCompact L →
      L ⊆ (fun z : U => D.toGlueData.ι i z) ⁻¹' (V : Set D.toGlueData.glued) →
      ∀ᶠ k in atTop, MapsTo (fun z : U => F k (D.toGlueData.ι i z)) L
        (Metric.eball (b k) (ENNReal.ofReal (r + ρ))) := by
    intro i L hL hLV
    have hL' : IsCompact (Subtype.val '' L : Set E) := hL.image continuous_subtype_val
    have hL'V : Subtype.val '' L ⊆ chartDomain V i := image_mono hLV
    filter_upwards [hFtarget i (Subtype.val '' L) hL' hL'V, hcenter i] with k hk hc
    intro z hz
    have ht := hk z z.property ⟨z, hz, rfl⟩
    rw [IntrinsicBallChart.target_eq_eball (g k) (hEnorm k) (x i k) (c i k),
      Metric.mem_eball'] at ht
    rw [Metric.mem_eball']
    calc
      edist (b k) (F k (D.toGlueData.ι i z)) ≤
          edist (b k) (x i k) + edist (x i k) (F k (D.toGlueData.ι i z)) := edist_triangle _ _ _
      _ ≤ ENNReal.ofReal r + edist (x i k) (F k (D.toGlueData.ι i z)) := add_le_add hc le_rfl
      _ < ENNReal.ofReal r + ENNReal.ofReal ρ :=
        (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mpr ht
      _ = ENNReal.ofReal (r + ρ) := (ENNReal.ofReal_add hr hρ.le).symm
  have hcapture := hA.eventually_mapsTo_iUnion_of_open_cover V.isOpen hAV
    (fun i (z : U) => D.toGlueData.ι i z)
    (fun i => (D.toGlueData.ι i).hom.continuous)
    (fun i => (D.ι_isOpenEmbedding i).isOpenMap)
    (fun q _ => D.ι_jointly_surjective q)
    F (fun _ k => Metric.eball (b k) (ENNReal.ofReal (r + ρ))) hlocal
  filter_upwards [hcapture] with k hk
  intro q hq
  obtain ⟨_, h⟩ := mem_iUnion.mp (hk hq)
  exact h

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
