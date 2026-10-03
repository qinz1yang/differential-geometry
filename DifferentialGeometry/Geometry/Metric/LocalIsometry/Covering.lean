import DifferentialGeometry.Geometry.Metric.LocalIsometry.Sheets
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section

open Bundle Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Riemannian

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold J ∞ N]
  [T2Space M] [SigmaCompactSpace M] [T2Space N]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem isEvenlyCovered_of_complete_of_starConvex
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hg : RiemannianMetricComplete (I := I) g)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w))
    (φ : PartialDiffeomorph 𝓘(ℝ, F) J F N ∞)
    (z₀ : F) (hz₀ : z₀ ∈ φ.source) (hstar : StarConvex ℝ z₀ φ.source) :
    IsEvenlyCovered f (φ z₀) (f ⁻¹' {φ z₀}) := by
  classical
  let A := f ⁻¹' ({φ z₀} : Set N)
  let y₀ : φ.target := ⟨φ z₀, φ.map_source hz₀⟩
  have hsections (i : A) : ∃ σ : C(φ.target, M), σ y₀ = i.val ∧
      (∀ y : φ.target, f (σ y) = (y : N)) ∧ Topology.IsOpenEmbedding σ :=
    exists_openEmbedding_section_of_complete_of_starConvex g h hf hg hmetric
      φ z₀ hz₀ hstar i.val i.property
  choose σ hσ0 hσf hσopen using hsections
  let U : A → Set M := fun i => range (σ i)
  let γ (y : φ.target) (t : ℝ) : N := φ ((1 - t) • z₀ + t • φ.symm y)
  have hmem (y : φ.target) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (1 - t) • z₀ + t • φ.symm y ∈ φ.source :=
    hstar (φ.map_target y.property) (sub_nonneg.mpr ht.2) ht.1 (sub_add_cancel _ _)
  have hγ (y : φ.target) : ContMDiffOn 𝓘(ℝ) J 1 (γ y) (Icc (0 : ℝ) 1) := by
    have hc : ContMDiff 𝓘(ℝ) 𝓘(ℝ, F) 1
        (fun t : ℝ => (1 - t) • z₀ + t • φ.symm y) :=
      ((contMDiff_const.sub contMDiff_id).smul contMDiff_const).add
        (contMDiff_id.smul contMDiff_const)
    exact (φ.contMDiffOn_toFun.of_le (by simp)).comp hc.contMDiffOn (hmem y)
  have hγ0 (y : φ.target) : γ y 0 = φ z₀ := by simp [γ]
  have hγ1 (y : φ.target) : γ y 1 = y := by
    simp only [γ, sub_self, zero_smul, one_smul, zero_add]
    exact φ.right_inv y.property
  let τ (y : φ.target) : C(unitInterval, φ.target) :=
    ⟨fun t => ⟨γ y t, φ.map_source (hmem y t t.property)⟩,
      (hγ y).continuousOn.domRestrict.subtype_mk _⟩
  have hτ0 (y : φ.target) : τ y 0 = y₀ := Subtype.ext (hγ0 y)
  have hτ1 (y : φ.target) : τ y 1 = y := Subtype.ext (hγ1 y)
  have hexhaust (z : M) (hz : f z ∈ φ.target) : ∃ i : A, z ∈ U i := by
    let y : φ.target := ⟨f z, hz⟩
    let δ : ℝ → N := fun t => γ y (1 - t)
    have hrev (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 1 - t ∈ Icc (0 : ℝ) 1 :=
      ⟨sub_nonneg.mpr ht.2, by linarith [ht.1]⟩
    have hδ : ContMDiffOn 𝓘(ℝ) J 1 δ (Icc (0 : ℝ) 1) :=
      (hγ y).comp (contMDiff_const.sub contMDiff_id).contMDiffOn hrev
    obtain ⟨η, hη, hη0, hηf, _⟩ := exists_contMDiffOn_lift_of_complete
      g h hf hg hmetric zero_le_one hδ z (by
        change f z = γ y (1 - 0)
        rw [sub_zero, hγ1])
    have hη1 : f (η 1) = φ z₀ := by
      have h := hηf (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
      simpa only [Function.comp_apply, δ, sub_self, hγ0] using h
    let i : A := ⟨η 1, hη1⟩
    have hleft : Continuous (fun t : unitInterval => σ i (τ y t)) :=
      (σ i).continuous.comp (τ y).continuous
    have hright : Continuous (fun t : unitInterval => η (1 - (t : ℝ))) :=
      hη.continuousOn.comp_continuous (continuous_const.sub continuous_subtype_val)
        (fun t => hrev t t.property)
    have hcomp : (fun t : unitInterval => f (σ i (τ y t))) =
        fun t : unitInterval => f (η (1 - (t : ℝ))) := by
      funext t
      rw [hσf]
      have h := hηf (hrev t t.property)
      change f (η (1 - (t : ℝ))) = γ y (1 - (1 - (t : ℝ))) at h
      rw [show (1 : ℝ) - (1 - (t : ℝ)) = t by ring] at h
      exact h.symm
    have hstart : σ i (τ y 0) = η (1 - (0 : ℝ)) := by
      rw [hτ0, hσ0, sub_zero]
    have heq : (fun t : unitInterval => σ i (τ y t)) =
        fun t : unitInterval => η (1 - (t : ℝ)) :=
      (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective
        hleft hright hcomp 0 hstart
    refine ⟨i, y, ?_⟩
    have h := congrFun heq 1
    change σ i (τ y 1) = η (1 - 1) at h
    simpa only [hτ1, sub_self, hη0] using h
  have hdisjoint : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    change Disjoint (U i) (U j)
    rw [Set.disjoint_left]
    intro z hzi hzj
    obtain ⟨u, hu⟩ := hzi
    obtain ⟨v, hv⟩ := hzj
    have huv : u = v := by
      apply Subtype.ext
      exact (hσf i u).symm.trans ((congrArg f (hu.trans hv.symm)).trans (hσf j v))
    subst v
    have hcomp : (fun t : unitInterval => f (σ i (τ u t))) =
        fun t : unitInterval => f (σ j (τ u t)) := by
      funext t
      rw [hσf, hσf]
    have hend : σ i (τ u 1) = σ j (τ u 1) := by
      rw [hτ1]
      exact hu.trans hv.symm
    have heq : (fun t : unitInterval => σ i (τ u t)) = fun t : unitInterval => σ j (τ u t) :=
      (T2Space.isSeparatedMap f).eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective
        ((σ i).continuous.comp (τ u).continuous) ((σ j).continuous.comp (τ u).continuous)
        hcomp 1 hend
    apply hij
    apply Subtype.ext
    have h := congrFun heq 0
    simpa only [hτ0, hσ0] using h
  cases isEmpty_or_nonempty A with
  | inl hA =>
    let : IsEmpty A := hA
    apply IsEvenlyCovered.of_preimage_eq_empty A (φ.open_target.mem_nhds (φ.map_source hz₀))
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨i, _⟩ := hexhaust z hz
    exact isEmptyElim i
  | inr hA =>
    let : Nonempty A := hA
    let : Nonempty (N → M) := ⟨fun _ => (Classical.arbitrary A).val⟩
    let : DiscreteTopology A :=
      (IsDiscrete.of_openPartialHomeomorph f subset_rfl (fun z _ => by
        obtain ⟨e, hz, he⟩ := hf.isLocalHomeomorph z
        exact ⟨e, hz, he.symm⟩)).1
    have hopen (i : A) : IsOpen (U i) := (hσopen i).isOpen_range
    have hinj (i : A) : InjOn f (U i) := by
      rintro z ⟨u, rfl⟩ w ⟨v, rfl⟩ heq
      have huv : u = v := Subtype.ext ((hσf i u).symm.trans (heq.trans (hσf i v)))
      exact congrArg (σ i) huv
    have hsurj (i : A) : SurjOn f (U i) φ.target := by
      intro y hy
      exact ⟨σ i ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hσf i ⟨y, hy⟩⟩
    have hopen_iff (i : A) {W : Set N} (hW : W ⊆ φ.target) :
        IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i) := by
      constructor
      · intro h
        exact (h.preimage hf.contMDiff.continuous).inter (hopen i)
      · intro h
        have himage : f '' (f ⁻¹' W ∩ U i) = W := by
          apply Set.Subset.antisymm
          · rintro _ ⟨z, ⟨hz, _⟩, rfl⟩
            exact hz
          · intro y hy
            obtain ⟨z, hzi, hfz⟩ := hsurj i (hW hy)
            exact ⟨z, ⟨show f z ∈ W from hfz.symm ▸ hy, hzi⟩, hfz⟩
        rw [← himage]
        exact hf.isOpenMap _ h
    have hexhaust' : f ⁻¹' φ.target ⊆ ⋃ i, U i := by
      intro z hz
      obtain ⟨i, hi⟩ := hexhaust z hz
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    exact IsEvenlyCovered.of_trivialization
      (t := φ.open_target.trivializationDiscrete U φ.target hopen_iff hinj hsurj
        hdisjoint hexhaust') (by
          simpa only [IsOpen.trivializationDiscrete_baseSet] using φ.map_source hz₀)

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem isCoveringMap_of_complete [J.Boundaryless]
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f)
    (hg : RiemannianMetricComplete (I := I) g)
    (hmetric : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w = h.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w)) :
    IsCoveringMap f := by
  intro y
  let e := DifferentialGeometry.Topology.PartialDiffeomorph.extendedChart (I := J) y
  have hy : y ∈ e.source := mem_extChartAt_source (I := J) y
  let z₀ := e y
  have hz₀ : z₀ ∈ e.target := e.map_source hy
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target z₀ hz₀
  let φ := DifferentialGeometry.Topology.PartialDiffeomorph.restrict e.symm
    (Metric.ball z₀ r) Metric.isOpen_ball
  have hsource : φ.source = Metric.ball z₀ r := by
    change e.target ∩ Metric.ball z₀ r = Metric.ball z₀ r
    exact inter_eq_right.mpr hball
  have hz : z₀ ∈ φ.source := by rw [hsource]; exact Metric.mem_ball_self hr
  have hstar : StarConvex ℝ z₀ φ.source := by
    rw [hsource]
    exact (convex_ball z₀ r).starConvex (Metric.mem_ball_self hr)
  have hφ : φ.toPartialEquiv z₀ = y := e.left_inv hy
  have h := isEvenlyCovered_of_complete_of_starConvex g h hf hg hmetric φ z₀ hz hstar
  change IsEvenlyCovered f (φ.toPartialEquiv z₀) (f ⁻¹' {φ.toPartialEquiv z₀}) at h
  rwa [hφ] at h

end DifferentialGeometry.Geometry.Riemannian
