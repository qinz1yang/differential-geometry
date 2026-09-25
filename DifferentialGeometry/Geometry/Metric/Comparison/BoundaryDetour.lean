import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.OpenSubtype
import DifferentialGeometry.Topology.Embedding.CompactFrontier
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Topology.FirstExit

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem metricPathELength_add (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    metricPathELength g γ a b + metricPathELength g γ b c = metricPathELength g γ a c := by
  let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength I γ a b + Manifold.pathELength I γ b c = _
  exact Manifold.pathELength_add (I := I) (γ := γ) hab hbc

private theorem metricPathELength_ends_le (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    metricPathELength g γ 0 s + metricPathELength g γ t 1 ≤ metricPathELength g γ 0 1 := by
  calc
    _ ≤ metricPathELength g γ 0 s + metricPathELength g γ s 1 :=
      add_le_add le_rfl (metricPathELength_mono g γ hst (le_rfl : (1 : ℝ) ≤ 1))
    _ = _ := metricPathELength_add g γ hs (hst.trans ht)

private theorem riemannianEDistOf_map_le_metricPathELength_add_of_frontier_detour
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {K : Set M}
    {B : ℝ} (hB : 0 ≤ B) (D : ℝ≥0∞)
    (hsource : K ⊆ Φ.source)
    (hupper : ∀ z ∈ K, ∀ v : TangentSpace I z,
      h.inner (Φ z) (mfderiv I J Φ z v) (mfderiv I J Φ z v) ≤ B ^ 2 * g.inner z v v)
    (hfront : ∀ u ∈ frontier K, ∀ v ∈ frontier K,
      riemannianEDistOf h (Φ u) (Φ v) ≤ D)
    (γ : ℝ → M) (hγ : ContMDiffOn 𝓘(ℝ) I 1 γ (Icc 0 1))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hleft : ∀ r ∈ Icc 0 s, γ r ∈ K) (hright : ∀ r ∈ Icc t 1, γ r ∈ K)
    (hsfront : γ s ∈ frontier K) (htfront : γ t ∈ frontier K) :
    riemannianEDistOf h (Φ (γ 0)) (Φ (γ 1)) ≤
      ENNReal.ofReal B * metricPathELength g γ 0 1 + D := by
  have hprefix := hγ.mono (Icc_subset_Icc le_rfl (hst.trans ht))
  have hsuffix := hγ.mono (Icc_subset_Icc (hs.trans hst) le_rfl)
  have hlengthL := metricPathELength_comp_le g h Φ hB hprefix
    (fun r hr => hsource (hleft r hr)) (fun r hr => hupper (γ r) (hleft r ⟨hr.1.le, hr.2.le⟩))
  have hlengthR := metricPathELength_comp_le g h Φ hB hsuffix
    (fun r hr => hsource (hright r hr)) (fun r hr => hupper (γ r) (hright r ⟨hr.1.le, hr.2.le⟩))
  have hL := edistOf_le_metricPathELength h hs
    ((Φ.contMDiffOn_toFun.of_le (by simp)).comp hprefix
      (fun r hr => hsource (hleft r hr)))
  have hR := edistOf_le_metricPathELength h ht
    ((Φ.contMDiffOn_toFun.of_le (by simp)).comp hsuffix
      (fun r hr => hsource (hright r hr)))
  calc
    _ ≤ riemannianEDistOf h (Φ (γ 0)) (Φ (γ s)) +
        riemannianEDistOf h (Φ (γ s)) (Φ (γ 1)) := riemannianEDistOf_triangle h _ _ _
    _ ≤ ENNReal.ofReal B * metricPathELength g γ 0 s +
        (D + ENNReal.ofReal B * metricPathELength g γ t 1) :=
      add_le_add (hL.trans hlengthL)
        ((riemannianEDistOf_triangle h _ _ _).trans (add_le_add
          (hfront (γ s) hsfront (γ t) htfront) (hR.trans hlengthR)))
    _ = ENNReal.ofReal B * (metricPathELength g γ 0 s + metricPathELength g γ t 1) + D := by
      ring
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl (metricPathELength_ends_le g γ hs hst ht)) le_rfl

theorem riemannianEDistOf_map_le_mul_add_of_frontier_bound
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Φ : PartialDiffeomorph I J M N ∞) {K : Set M} (hK : IsClosed K)
    {B : ℝ} (hB : 0 < B) (D : ℝ≥0∞)
    (hsource : K ⊆ Φ.source)
    (hupper : ∀ z ∈ K, ∀ v : TangentSpace I z,
      h.inner (Φ z) (mfderiv I J Φ z v) (mfderiv I J Φ z v) ≤ B ^ 2 * g.inner z v v)
    (hfront : ∀ u ∈ frontier K, ∀ v ∈ frontier K,
      riemannianEDistOf h (Φ u) (Φ v) ≤ D)
    {x y : M} (hx : x ∈ K) (hy : y ∈ K) :
    riemannianEDistOf h (Φ x) (Φ y) ≤ ENNReal.ofReal B * riemannianEDistOf g x y + D := by
  have hB0 : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hB).ne'
  by_cases htop : riemannianEDistOf g x y = ⊤
  · rw [htop, ENNReal.mul_top hB0, top_add]
    exact le_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let η : ℝ≥0∞ := ε / ENNReal.ofReal B
  have hη : 0 < η := ENNReal.div_pos (by exact_mod_cast hε.ne') ENNReal.ofReal_ne_top
  have hnear : riemannianEDistOf g x y < riemannianEDistOf g x y + η :=
    ENNReal.lt_add_right htop hη.ne'
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_edistOf_lt g hnear
  have hbound : riemannianEDistOf h (Φ x) (Φ y) ≤
      ENNReal.ofReal B * metricPathELength g γ 0 1 + D := by
    rcases mapsTo_or_exists_frontier_pair hK hγ.continuousOn (hγ0 ▸ hx) (hγ1 ▸ hy) with hstay |
      ⟨s, t, hs, ht, hst, hsfront, htfront, hleft, hright⟩
    · have hmap : ContMDiffOn 𝓘(ℝ) J 1 (Φ ∘ γ) (Icc 0 1) :=
        (Φ.contMDiffOn_toFun.of_le (by simp)).comp hγ (fun r hr => hsource (hstay hr))
      have hdist := edistOf_le_metricPathELength h zero_le_one hmap
      have hlen := metricPathELength_comp_le g h Φ hB.le hγ
        (fun r hr => hsource (hstay hr)) (fun r hr => hupper (γ r) (hstay ⟨hr.1.le, hr.2.le⟩))
      simp only [Function.comp_apply, hγ0, hγ1] at hdist
      exact (hdist.trans hlen).trans le_self_add
    · have hdetour := riemannianEDistOf_map_le_metricPathELength_add_of_frontier_detour
        g h Φ hB.le D hsource hupper hfront γ hγ hs.1 hst.le ht.2
        (fun r hr => hleft hr) (fun r hr => hright hr) hsfront htfront
      simpa only [hγ0, hγ1] using hdetour
  calc
    _ ≤ ENNReal.ofReal B * (riemannianEDistOf g x y + η) + D :=
      hbound.trans (add_le_add (mul_le_mul' le_rfl hlength.le) le_rfl)
    _ = (ENNReal.ofReal B * riemannianEDistOf g x y + D) + ε := by
      rw [mul_add, ENNReal.mul_div_cancel hB0 ENNReal.ofReal_ne_top]
      ac_rfl

end DifferentialGeometry.Geometry.Metric

noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem riemannianEDistOf_subtype_le_mul_add_of_frontier_bound
    (g : SmoothRiemannianMetric I M) (Ω : TopologicalSpace.Opens M)
    (h : SmoothRiemannianMetric I Ω) {K : Set Ω} (hK : IsCompact K)
    {B : ℝ} (hB : 0 < B) (D : ℝ≥0∞)
    (hupper : ∀ z ∈ K, ∀ v : TangentSpace I z,
      h.inner z v v ≤ B ^ 2 * g.inner z.val v v)
    (hfront : ∀ u ∈ frontier K, ∀ v ∈ frontier K,
      riemannianEDistOf h u v ≤ D)
    {x y : Ω} (hx : x ∈ K) (hy : y ∈ K) :
    riemannianEDistOf h x y ≤ ENNReal.ofReal B * riemannianEDistOf g x.val y.val + D := by
  let F := (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) Ω ⟨x⟩).symm
  have hsource : (F.source : Set M) = Ω := Ω.openPartialHomeomorphSubtypeCoe_target ⟨x⟩
  have hF (z : Ω) : F z.val = z := by
    apply Subtype.ext
    exact (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) Ω ⟨x⟩).right_inv
      ((Ω.openPartialHomeomorphSubtypeCoe_target ⟨x⟩).symm ▸ z.property)
  have hder (z : Ω) : mfderiv I I F z.val = ContinuousLinearMap.id ℝ E := by
    have hval (w : M) (hw : w ∈ Ω) : (F w : M) = w :=
      (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I) Ω ⟨x⟩).right_inv
        ((Ω.openPartialHomeomorphSubtypeCoe_target ⟨x⟩).symm ▸ hw)
    have heq : (fun w => (F w : M)) =ᶠ[𝓝 z.val] id :=
      Filter.eventuallyEq_of_mem (Ω.isOpen.mem_nhds z.property) hval
    rw [← DifferentialGeometry.mfderiv_subtypeVal_comp F z.val, heq.mfderiv_eq, mfderiv_id]
    rfl
  have hclosed : IsClosed (Subtype.val '' K : Set M) :=
    (hK.image continuous_subtype_val).isClosed
  have himagefront : Subtype.val '' frontier K = frontier (Subtype.val '' K : Set M) :=
    DifferentialGeometry.Topology.Embedding.image_frontier_of_isOpenEmbedding_of_isCompact
      Ω.isOpenEmbedding' hK
  have hbound := riemannianEDistOf_map_le_mul_add_of_frontier_bound g h F hclosed hB D
    (by rintro z ⟨w, _, rfl⟩; rw [hsource]; exact w.property)
    (by
      rintro z ⟨w, hw, rfl⟩ v
      rw [hder]
      change h.inner (F w.val) v v ≤ B ^ 2 * g.inner w.val v v
      rw [hF]
      exact hupper w hw v)
    (by
      intro u hu v hv
      rw [← himagefront] at hu hv
      obtain ⟨u', hu', rfl⟩ := hu
      obtain ⟨v', hv', rfl⟩ := hv
      simpa only [hF] using hfront u' hu' v' hv')
    (show x.val ∈ Subtype.val '' K from ⟨x, hx, rfl⟩)
    (show y.val ∈ Subtype.val '' K from ⟨y, hy, rfl⟩)
  simpa only [hF] using hbound


end DifferentialGeometry.Geometry.Metric
