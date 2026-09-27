import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology
import DifferentialGeometry.Topology.Attachment.TransitionGluing.CollisionLimits
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Convergence
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.SourceMaps
import DifferentialGeometry.Topology.Compactness.EventualLocality
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Compactness.EventualInjectivity
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Smooth

section

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



theorem IntrinsicBallChart.eventually_injOn_of_chart_convergence [Finite ι] :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued) (K : Set D.toGlueData.glued),
      IsCompact K → K ⊆ V →
      ∀ (F : ∀ k, D.toGlueData.glued → M k),
      (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) →
      (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
        (fun k => coords F i k) id) →
      (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
          F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) →
      ∀ᶠ k in atTop, Set.InjOn (F k) K := by
  intro D U chartDomain coords C hman hchart V K hK hKV F hFsmooth hFconv hFimage
  let := hman
  let : Nonempty U := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  let : Countable D.J := by
    change Countable ι
    infer_instance
  let : ∀ i : D.J, SecondCountableTopology (D.U i) := by
    intro i
    change SecondCountableTopology U
    infer_instance
  let : SecondCountableTopology D.toGlueData.glued := TopCat.GlueData.secondCountableTopology D
  apply IsCompact.eventually_injOn_of_local_injOn_of_collision_limits hK F
  · intro p hp
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    let : Nonempty (D.U i) := ⟨Classical.choice (show Nonempty U from inferInstance)⟩
    let e : OpenPartialHomeomorph U D.toGlueData.glued :=
      (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)
    exact CheegerGromovCompactness.eventually_injOn_nhds_of_open_coordinate_convergence
      U e rfl (hchart i).contMDiff V (fun n => (c i n).hom) F hFsmooth
      (fun n => coords F i n) (hFconv i)
      (fun n z => by dsimp only [coords]; rw [dif_pos z.property]; rfl)
      (fun L hL hLdom => (hFimage i L hL hLdom).mono fun n hn z hz => hn z z.property hz)
      (hKV hp)
  · intro φ hφ q r hqK hrK a ha b hb hq hr heq
    have hsource : ∀ i n, (U : Set E) ⊆ (c i n).hom.source := by
      intro i n z hz
      rw [(c i n).source_eq]
      exact Metric.ball_subset_ball (by linarith) hz
    have hfar : ∀ i j, near i j = false →
        ∀ᶠ n in atTop, Disjoint ((c i n).hom '' (U : Set E)) ((c j n).hom '' (U : Set E)) := by
      intro i j hij
      filter_upwards [hclass i j] with n hn
      apply (c i n).disjoint_image_ball_of_add_le_edist
        (g n) (hEnorm n) (x i n) (x j n) (c j n) (by linarith) (by linarith)
      apply le_trans _ (hn.2 hij)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hcontU : ∀ a, ContinuousOn (J a) U :=
      fun a => (hcont a).mono (Metric.ball_subset_ball (by linarith))
    have htransconv : ∀ a, CheegerGromovCompactness.MapCInfConvergenceOnCompacts
        (Metric.ball (0 : E) (ρ / 2))
        (fun n z => (c a.1.2 n).hom.symm ((c a.1.1 n).hom z)) (J a) := hconv
    dsimp only [D, IntrinsicBallChart.bufferedTransitionGlueData] at *
    exact TopCat.GlueData.ofTransitionMaps_collision_limits_of_chart_convergence
      U near J hcontU _ _ _ _ _
      (fun i n => (c i n).hom.toOpenPartialHomeomorph) hsource hfar
      Metric.isOpen_ball (Metric.ball_subset_ball (by linarith)) htransconv hcont
      V F (fun i n => coords F i n) hFconv
      (fun i n z => by dsimp only [coords]; rw [dif_pos z.property]; rfl)
      (fun i L hL hLdom => (hFimage i L hL hLdom).mono fun n hn z hz => hn z z.property hz)
      φ hφ q r a b (hKV ha) (hKV hb) hq hr heq

theorem IntrinsicBallChart.exists_open_eventually_injOn_of_chart_convergence [Finite ι] :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued) (K : Set D.toGlueData.glued),
      IsCompact K → K ⊆ V →
      ∀ (F : ∀ k, D.toGlueData.glued → M k),
      (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) →
      (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
        (fun k => coords F i k) id) →
      (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
          F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) →
      ∃ S : Set D.toGlueData.glued, IsOpen S ∧ K ⊆ S ∧ S ⊆ V ∧
        ∀ᶠ k in atTop, Set.InjOn (F k) S := by
  intro D U chartDomain coords C hman hchart V K hK hKV F hFsmooth hFconv hFimage
  let : IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued := hman
  let : LocallyCompactSpace D.toGlueData.glued := ChartedSpace.locallyCompactSpace E D.toGlueData.glued
  obtain ⟨L, hL, hKL, hLV⟩ := exists_compact_between hK V.isOpen hKV
  have htail := IntrinsicBallChart.eventually_injOn_of_chart_convergence
    g hEnorm x hρ c near hclass J hcont hconv C hman hchart V L hL hLV
    F hFsmooth hFconv hFimage
  exact ⟨interior L, isOpen_interior, hKL, interior_subset.trans hLV,
    htail.mono fun _ hn => hn.mono interior_subset⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

section

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



theorem IntrinsicBallChart.eventually_exists_partialDiffeomorph_of_chart_convergence [Finite ι] [Nonempty ι] :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued) (K : Set D.toGlueData.glued),
      IsCompact K → K ⊆ V →
      ∀ (F : ∀ k, D.toGlueData.glued → M k),
      (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) →
      (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
        (fun k => coords F i k) id) →
      (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
        ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
          F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) →
      ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I D.toGlueData.glued (M k) ∞,
        K ⊆ Φ.source ∧ Φ.source ⊆ V ∧ EqOn Φ (F k) Φ.source := by
  intro D U chartDomain coords C hman hchart V K hK hKV F hFsmooth hFconv hFimage
  let := hman
  let : Nonempty U := ⟨⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  let : Nonempty D.toGlueData.glued :=
    ⟨D.toGlueData.ι (Classical.choice (show Nonempty ι from inferInstance))
      ⟨0, Metric.mem_ball_self (by positivity)⟩⟩
  obtain ⟨S, hS, hKS, hSV, hSinj⟩ :=
    IntrinsicBallChart.exists_open_eventually_injOn_of_chart_convergence
      g hEnorm x hρ c near hclass J hcont hconv C hman hchart V K hK hKV
      F hFsmooth hFconv hFimage
  have hlocal : ∀ p ∈ K, ∃ W : Set D.toGlueData.glued,
      IsOpen W ∧ p ∈ W ∧ W ⊆ V ∧ ∀ᶠ n in atTop,
        ∀ q ∈ W, IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) I ∞ (F n) q := by
    intro p hp
    obtain ⟨i, z, rfl⟩ := D.ι_jointly_surjective p
    let : Nonempty (D.U i) := ⟨Classical.choice (show Nonempty U from inferInstance)⟩
    let e : OpenPartialHomeomorph U D.toGlueData.glued :=
      (D.ι_isOpenEmbedding i).toOpenPartialHomeomorph (D.toGlueData.ι i)
    obtain ⟨W, hW, hzW, hWV, hWlocal⟩ :=
      CheegerGromovCompactness.eventually_isLocalDiffeomorphOn_nhds_of_open_coordinate_convergence
        U e rfl (hchart i) V (fun n => (c i n).hom) F hFsmooth
        (fun n => coords F i n) (hFconv i)
        (fun n z => by dsimp only [coords]; rw [dif_pos z.property]; rfl)
        (fun L hL hLdom => (hFimage i L hL hLdom).mono fun n hn z hz => hn z z.property hz)
        (hKV hp)
    exact ⟨W, hW, hzW, hWV, hWlocal.mono fun n hn q hq => hn ⟨q, hq⟩⟩
  obtain ⟨W, hW, hKW, hWV, hWlocal⟩ := hK.exists_open_eventually_forall hlocal
  filter_upwards [hSinj, hWlocal] with n hn hln
  obtain ⟨Φ, hΦsource, hΦtarget, hΦeq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
      (hS.inter hW) (fun q => hln q q.property.2) (hn.mono inter_subset_left)
  refine ⟨Φ, ?_, ?_, ?_⟩
  · rw [hΦsource]
    exact subset_inter hKS hKW
  · rw [hΦsource]
    exact inter_subset_left.trans hSV
  · exact fun q hq => congrFun hΦeq q

theorem IntrinsicBallChart.exists_source_partialDiffeomorphs_on_compact [Finite ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball 0 ρ))
    (hBconv : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k)) (B i))
    (hell : ∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ≤ 2 * ‖v‖ ^ 2)
    (i₀ : ι) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ C : ChartedSpace E D.toGlueData.glued, letI := C
      IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued →
      (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
        (fun z : U => D.toGlueData.ι i z)) →
      ∀ (V : TopologicalSpace.Opens D.toGlueData.glued), IsCompact (closure (V : Set D.toGlueData.glued)) →
      D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ V →
      ∀ (K : Set D.toGlueData.glued), IsCompact K → K ⊆ V →
      D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ K →
      ∃ F : ∀ k, D.toGlueData.glued → M k,
        (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) ∧
        (∀ᶠ k in atTop, F k (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k) ∧
        (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
          (fun k => coords F i k) id) ∧
        (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
          ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
            F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) ∧
        ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I D.toGlueData.glued (M k) ∞,
          K ⊆ Φ.source ∧ Φ.source ⊆ V ∧ EqOn Φ (F k) Φ.source ∧
          Φ (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k := by
  intro D U chartDomain coords C hman hchart V hV hbase K hK hKV hbaseK
  obtain ⟨F, hFsmooth, hFbase, hFconv, hFimage⟩ :=
    IntrinsicBallChart.exists_local_source_maps_on_compact g hEnorm x hρ c near hclass J hcont hconv
      hJsmooth B hBsmooth hBconv hell i₀ C hman hchart V hV hbase
  let : Nonempty ι := ⟨i₀⟩
  have hΦ := IntrinsicBallChart.eventually_exists_partialDiffeomorph_of_chart_convergence
    g hEnorm x hρ c near hclass J hcont hconv C hman hchart V K hK hKV
    F hFsmooth hFconv hFimage
  refine ⟨F, hFsmooth, hFbase, hFconv, hFimage, ?_⟩
  filter_upwards [hΦ, hFbase] with k hk hbk
  obtain ⟨Φ, hKΦ, hΦV, heq⟩ := hk
  refine ⟨Φ, hKΦ, hΦV, heq, ?_⟩
  exact (heq (hKΦ hbaseK)).trans hbk

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

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



theorem IntrinsicBallChart.exists_source_partialDiffeomorphs_on_compact_neighborhood [Finite ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball 0 ρ))
    (hBconv : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k)) (B i))
    (hell : ∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ≤ 2 * ‖v‖ ^ 2)
    (i₀ : ι) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ (K : Set D.toGlueData.glued), IsCompact K →
      D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ K →
      ∃ C : ChartedSpace E D.toGlueData.glued, letI := C
        IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued ∧
        (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
          (fun z : U => D.toGlueData.ι i z)) ∧
        ∃ V : TopologicalSpace.Opens D.toGlueData.glued,
          IsCompact (closure (V : Set D.toGlueData.glued)) ∧ K ⊆ V ∧
      ∃ F : ∀ k, D.toGlueData.glued → M k,
        (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) V) ∧
        (∀ᶠ k in atTop, F k (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k) ∧
        (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain V i)
          (fun k => coords F i k) id) ∧
        (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain V i →
          ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
            F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) ∧
        ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I D.toGlueData.glued (M k) ∞,
          K ⊆ Φ.source ∧ Φ.source ⊆ V ∧ EqOn Φ (F k) Φ.source ∧
          Φ (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k := by
  intro D U chartDomain coords K hK hbaseK
  obtain ⟨C, hman, hchart⟩ := IntrinsicBallChart.exists_smooth_atlas_bufferedTransitionGlueData
    g hEnorm x hρ c near hclass J hcont hconv hJsmooth
  let := C
  let : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space g hEnorm x hρ c near hclass J hcont hconv
  let : LocallyCompactSpace D.toGlueData.glued := ChartedSpace.locallyCompactSpace E D.toGlueData.glued
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let V : TopologicalSpace.Opens D.toGlueData.glued := ⟨interior L, isOpen_interior⟩
  have hV : IsCompact (closure (V : Set D.toGlueData.glued)) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hL.isClosed)
  refine ⟨C, hman, hchart, V, hV, hKL, ?_⟩
  exact IntrinsicBallChart.exists_source_partialDiffeomorphs_on_compact
    g hEnorm x hρ c near hclass J hcont hconv hJsmooth B hBsmooth hBconv hell i₀
    C hman hchart V hV (hKL hbaseK) K hK hKL hbaseK

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

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



theorem IntrinsicBallChart.exists_source_partialDiffeomorphs_on_precompact_neighborhood [Finite ι]
    (hJsmooth : ∀ a, ContDiffOn ℝ ∞ (J a) (Metric.ball (0 : E) (ρ / 2)))
    (B : ι → E → E →L[ℝ] E →L[ℝ] ℝ)
    (hBsmooth : ∀ i, ContDiffOn ℝ ∞ (B i) (Metric.ball 0 ρ))
    (hBconv : ∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (Metric.ball 0 ρ)
      (fun k => intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k)) (B i))
    (hell : ∀ i k, ∀ z ∈ Metric.ball (0 : E) ρ, ∀ v : E,
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤ intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ∧
      intrinsicFrameMetric (I := I) (g k) (hEnorm k) (x i k) z v v ≤ 2 * ‖v‖ ^ 2)
    (i₀ : ι) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    let chartDomain : Set D.toGlueData.glued → ι → Set E := fun V i =>
      Subtype.val '' ((fun z : U => D.toGlueData.ι i z) ⁻¹' V)
    let coords : (∀ k, D.toGlueData.glued → M k) → ι → ℕ → E → E := fun F i k z =>
      @dite E (z ∈ U) (Classical.propDecidable _) (fun hz =>
        (c i k).hom.symm (F k (D.toGlueData.ι i ⟨z, hz⟩))) (fun _ => 0)
    ∀ (K : Set D.toGlueData.glued), IsCompact K →
      D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩ ∈ K →
      ∃ C : ChartedSpace E D.toGlueData.glued, letI := C
        IsManifold (modelWithCornersSelf ℝ E) ∞ D.toGlueData.glued ∧
        (∀ i : ι, IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
          (fun z : U => D.toGlueData.ι i z)) ∧
        ∃ V W : TopologicalSpace.Opens D.toGlueData.glued,
          IsCompact (closure (V : Set D.toGlueData.glued)) ∧
          IsCompact (closure (W : Set D.toGlueData.glued)) ∧ K ⊆ V ∧
          closure (V : Set D.toGlueData.glued) ⊆ W ∧
      ∃ F : ∀ k, D.toGlueData.glued → M k,
        (∀ k, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F k) W) ∧
        (∀ᶠ k in atTop, F k (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k) ∧
        (∀ i, CheegerGromovCompactness.MapCInfConvergenceOnCompacts (chartDomain W i)
          (fun k => coords F i k) id) ∧
        (∀ i (L : Set E), IsCompact L → L ⊆ chartDomain W i →
          ∀ᶠ k in atTop, ∀ (z : E) (hz : z ∈ U), z ∈ L →
            F k (D.toGlueData.ι i ⟨z, hz⟩) ∈ (c i k).hom.target) ∧
        ∀ᶠ k in atTop, ∃ Φ : PartialDiffeomorph (modelWithCornersSelf ℝ E) I D.toGlueData.glued (M k) ∞,
          closure (V : Set D.toGlueData.glued) ⊆ Φ.source ∧ Φ.source ⊆ W ∧ EqOn Φ (F k) Φ.source ∧
          Φ (D.toGlueData.ι i₀ ⟨0, Metric.mem_ball_self (by positivity)⟩) = x i₀ k := by
  intro D U chartDomain coords K hK hbaseK
  obtain ⟨C₀, _, _⟩ := IntrinsicBallChart.exists_smooth_atlas_bufferedTransitionGlueData
    g hEnorm x hρ c near hclass J hcont hconv hJsmooth
  let := C₀
  let : T2Space D.toGlueData.glued :=
    IntrinsicBallChart.bufferedTransitionGlueData_t2Space g hEnorm x hρ c near hclass J hcont hconv
  let : LocallyCompactSpace D.toGlueData.glued := ChartedSpace.locallyCompactSpace E D.toGlueData.glued
  obtain ⟨L, hL, hKL, _⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  let V : TopologicalSpace.Opens D.toGlueData.glued := ⟨interior L, isOpen_interior⟩
  have hV : IsCompact (closure (V : Set D.toGlueData.glued)) :=
    hL.of_isClosed_subset isClosed_closure (closure_minimal interior_subset hL.isClosed)
  obtain ⟨C, hman, hchart, W, hW, hVW, F, hFsmooth, hFbase, hFconv, hFtarget, hPhi⟩ :=
    IntrinsicBallChart.exists_source_partialDiffeomorphs_on_compact_neighborhood
      g hEnorm x hρ c near hclass J hcont hconv hJsmooth B hBsmooth hBconv hell i₀
      (closure (V : Set D.toGlueData.glued)) hV (subset_closure (hKL hbaseK))
  exact ⟨C, hman, hchart, V, W, hV, hW, hKL, hVW, F, hFsmooth, hFbase, hFconv, hFtarget, hPhi⟩

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end
