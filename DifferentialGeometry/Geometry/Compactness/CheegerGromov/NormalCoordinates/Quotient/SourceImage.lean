import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates
import DifferentialGeometry.Analysis.Calculus.MapConvergence.Image

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



theorem IntrinsicBallChart.eventually_chart_core_subset_image [Finite ι] :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      (∀ i : ι, ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued),
      IntrinsicBallChart.transitionGlueCompactCore g hEnorm x hρ c near hclass J hcont hconv ⊆ V →
      ∀ (F : ∀ k, D.toGlueData.glued → M k),
      (∀ᶠ k in atTop, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) →
      (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
        (fun k => coords F i k) id) →
      (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
          F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) →
      ∀ᶠ k in atTop, ∀ i, (c i k).hom '' Metric.closedBall 0 (ρ / 10) ⊆ F k '' V := by
  intro D U chartDomain coords C hchart V hcore F hFsmooth hFconv hFtarget
  apply eventually_all.mpr
  intro i
  have hopen : IsOpen (chartDomain V i) :=
    U.isOpen.isOpenMap_subtype_val _
      (V.isOpen.preimage (D.toGlueData.ι i).hom.continuous)
  have hdomU : chartDomain V i ⊆ U := by
    rintro _ ⟨z, _, rfl⟩
    exact z.property
  have hdomV : ∀ (z : E) (hz : z ∈ chartDomain V i),
      D.toGlueData.ι i ⟨z, hdomU hz⟩ ∈ V := by
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    exact hw
  have hsmooth : ∀ L : Set E, IsCompact L → L ⊆ chartDomain V i →
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (coords F i k) L := by
    intro L hL hLdom
    filter_upwards [hFtarget i L hL hLdom, hFsmooth] with k hk hsk
    exact DifferentialGeometry.Topology.Manifold.contDiffOn_of_open_coordinate_map
      U V.isOpen (hchart i) hsk (c i k).hom (hLdom.trans hdomU)
      (fun z hz => hdomV z (hLdom hz))
      (fun z hz => hk z (hdomU (hLdom hz)) hz)
      (fun z => by dsimp only [coords]; rw [dif_pos z.property]; rfl)
  have hball : Metric.closedBall (0 : E) (ρ / 10) ⊆ chartDomain V i := by
    intro z hz
    have hzU : z ∈ U := Metric.closedBall_subset_ball (by linarith) hz
    refine ⟨⟨z, hzU⟩, hcore ?_, rfl⟩
    exact mem_iUnion.mpr ⟨i, ⟨⟨z, hz⟩, rfl⟩⟩
  obtain ⟨L, hL, _, hLdom, hcapture⟩ :=
    (hFconv i).exists_compact_eventually_subset_image hopen hsmooth
      (isCompact_closedBall _ _) hball
  filter_upwards [hcapture, hFtarget i L hL hLdom] with k hcap ht
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := hcap hz
  have hwU : w ∈ U := hdomU (hLdom hw)
  refine ⟨D.toGlueData.ι i ⟨w, hwU⟩, hdomV w (hLdom hw), ?_⟩
  have hcoord : (c i k).hom.symm (F k (D.toGlueData.ι i ⟨w, hwU⟩)) = z := by
    simpa only [coords, dif_pos hwU] using hwz
  exact ((c i k).hom.right_inv (ht w hwU hw)).symm.trans (congrArg (c i k).hom hcoord)

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end
