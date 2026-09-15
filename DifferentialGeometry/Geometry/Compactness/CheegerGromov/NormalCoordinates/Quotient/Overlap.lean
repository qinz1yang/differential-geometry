import DifferentialGeometry.Topology.Attachment.TransitionGluing.Overlap
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.NormalCoordinates.Quotient.Topology

section

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


theorem IntrinsicBallChart.bufferedTransitionGlueData_ι_eq_iff_graph
    (i j : ι) (z w : Metric.ball (0 : E) (ρ / 8)) :
    (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i z =
      (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι j w ↔
      ∃ h : near i j = true, J ⟨(i, j), h⟩ z = w := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData
  exact TopCat.GlueData.ofTransitionMaps_ι_eq_iff_graph _ _ _ _ _ _ _ _ _ _ i j z w


theorem IntrinsicBallChart.bufferedTransitionGlueData_near_of_nonempty_inter_range (i j : ι)
    (h : (range ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i) ∩
      range ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι j)).Nonempty) :
    near i j = true := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData at h
  exact TopCat.GlueData.ofTransitionMaps_near_of_nonempty_inter_range _ _ _ _ _ _ _ _ _ _ i j h

theorem IntrinsicBallChart.bufferedTransitionGlueData_mapsTo_of_subset_image (i j : ι)
    (h : near i j = true)
    {L : Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued}
    {W : Set E}
    (hL : L ⊆ (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι j ''
      {z : Metric.ball (0 : E) (ρ / 8) | (z : E) ∈ W}) :
    MapsTo (J ⟨(i, j), h⟩)
      (Subtype.val '' ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i ⁻¹' L)) W := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData at L hL ⊢
  exact TopCat.GlueData.ofTransitionMaps_mapsTo_of_subset_image _ _ _ _ _ _ _ _ _ _ i j h hL


theorem IntrinsicBallChart.bufferedTransitionGlueData_compact_overlap (i j : ι)
    {L : Set (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.glued}
    {Wi Wj : Set E} (hL : IsCompact L) (hLn : L.Nonempty)
    (hLi : L ⊆ (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i ''
      {z : Metric.ball (0 : E) (ρ / 8) | (z : E) ∈ Wi})
    (hLj : L ⊆ (IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι j ''
      {z : Metric.ball (0 : E) (ρ / 8) | (z : E) ∈ Wj}) :
    let K := Subtype.val '' ((IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv).toGlueData.ι i ⁻¹' L)
    IsCompact K ∧ K ⊆ Wi ∧
      ∃ h : near i j = true, MapsTo (J ⟨(i, j), h⟩) K Wj := by
  unfold IntrinsicBallChart.bufferedTransitionGlueData at L hLi hLj ⊢
  exact TopCat.GlueData.ofTransitionMaps_compact_overlap _ _ _ _ _ _ _ _ _ _ i j hL hLn hLi hLj

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

end

section

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


theorem IntrinsicBallChart.eventually_eqOn_extend_of_transition_eqOn_compact
    {S : Type*} {Y : S → Type*} (l : Filter S) :
    let D := IntrinsicBallChart.bufferedTransitionGlueData g hEnorm x hρ c near hclass J hcont hconv
    let U : TopologicalSpace.Opens E := ⟨Metric.ball (0 : E) (ρ / 8), Metric.isOpen_ball⟩
    ∀ (W : ι × U → Set E) (f : (ι × U) → ∀ k, E → Y k) (b : ∀ k, Y k),
      (∀ (a a' : ι × U) (h : near a'.1 a.1 = true) (K : Set E), IsCompact K →
        K ⊆ W a' → MapsTo (J ⟨(a'.1, a.1), h⟩) K (W a) →
        ∀ᶠ k in l, EqOn (f a k ∘ J ⟨(a'.1, a.1), h⟩) (f a' k) K) →
      ∀ (a a' : ι × U) (L : Set D.toGlueData.glued), IsCompact L →
        L ⊆ (D.toGlueData.ι a.1 '' (Subtype.val ⁻¹' W a)) ∩
          (D.toGlueData.ι a'.1 '' (Subtype.val ⁻¹' W a')) →
        ∀ᶠ k in l, EqOn
          (Function.extend (D.toGlueData.ι a.1) (fun z : U => f a k z) (fun _ => b k))
          (Function.extend (D.toGlueData.ι a'.1) (fun z : U => f a' k z) (fun _ => b k)) L := by
  intro D U W f b hcompat a a' L hL hLsub
  by_cases hLn : L.Nonempty
  · have hLa : L ⊆ D.toGlueData.ι a.1 '' (Subtype.val ⁻¹' W a) :=
      hLsub.trans inter_subset_left
    have hLa' : L ⊆ D.toGlueData.ι a'.1 '' (Subtype.val ⁻¹' W a') :=
      hLsub.trans inter_subset_right
    obtain ⟨hK, hKW, hnear, hKJ⟩ :=
      IntrinsicBallChart.bufferedTransitionGlueData_compact_overlap
        g hEnorm x hρ c near hclass J hcont hconv a'.1 a.1 hL hLn hLa' hLa
    filter_upwards [hcompat a a' hnear _ hK hKW hKJ] with k hk p hp
    obtain ⟨z, hz, hzp⟩ := hLa hp
    obtain ⟨w, hw, hwp⟩ := hLa' hp
    change U at z w
    have hrep : D.toGlueData.ι a'.1 w = D.toGlueData.ι a.1 z := hwp.trans hzp.symm
    obtain ⟨hnear', hJ⟩ :=
      (IntrinsicBallChart.bufferedTransitionGlueData_ι_eq_iff_graph
        g hEnorm x hρ c near hclass J hcont hconv a'.1 a.1 w z).mp hrep
    have hcoord := hk (show (w : E) ∈ Subtype.val '' (D.toGlueData.ι a'.1 ⁻¹' L) from
      ⟨w, by change D.toGlueData.ι a'.1 w ∈ L; rwa [hwp], rfl⟩)
    change f a k (J ⟨(a'.1, a.1), hnear⟩ w) = f a' k w at hcoord
    rw [hJ] at hcoord
    calc
      Function.extend (D.toGlueData.ι a.1) (fun z : U => f a k z) (fun _ => b k) p =
          f a k z := by
        rw [← hzp]
        have hinj : Function.Injective (fun z : U => D.toGlueData.ι a.1 z) :=
          (D.ι_isOpenEmbedding a.1).injective
        exact hinj.extend_apply (fun z : U => f a k z) (fun _ => b k) z
      _ = f a' k w := hcoord
      _ = Function.extend (D.toGlueData.ι a'.1) (fun z : U => f a' k z) (fun _ => b k) p := by
        rw [← hwp]
        have hinj : Function.Injective (fun z : U => D.toGlueData.ι a'.1 z) :=
          (D.ι_isOpenEmbedding a'.1).injective
        exact (hinj.extend_apply (fun z : U => f a' k z) (fun _ => b k) w).symm
  · exact Filter.Eventually.of_forall fun _ _ hp => (hLn ⟨_, hp⟩).elim

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end

end
