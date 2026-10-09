import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import DifferentialGeometry.Geometry.Hyperbolic.TruncationVolume
import DifferentialGeometry.Geometry.Metric.Comparison.ScalarBarrier
import DifferentialGeometry.Geometry.Metric.Distance.Ball
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

set_option autoImplicit false

noncomputable section

open Set Manifold Filter GC.Endpoint
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation

private theorem cusp_radial_mvfderiv_bound
    (C : HyperbolicCusp) (p : CuspHalfSpace)
    (v : TangentSpace halfCollarModel p) :
    |mvfderiv halfCollarModel (fun q : CuspHalfSpace => q.2.val 0) p v| ≤
      Real.sqrt (C.metric.inner p v v) := by
  have hd : mvfderiv halfCollarModel (fun q : CuspHalfSpace => q.2.val 0) p v =
      v.2 0 := by
    rw [mvfderiv_real_eq_mfderiv]
    change mfderiv halfCollarModel 𝓘(ℝ) ((fun t : EuclideanHalfSpace 1 => t.val 0) ∘
      (Prod.snd : CuspHalfSpace → EuclideanHalfSpace 1)) p v = v.2 0
    rw [mfderiv_comp_apply p
      (Topology.Manifold.hasMFDerivAt_halfSpaceOneCoordinate p.2).mdifferentiableAt
      mdifferentiableAt_snd]
    rw [mfderiv_snd, (Topology.Manifold.hasMFDerivAt_halfSpaceOneCoordinate p.2).mfderiv]
    rfl
  rw [hd, C.metric_formula]
  have hn := metric_inner_self_nonneg C.torusMetric p.1 v.1
  have he := mul_nonneg (Real.exp_pos (-p.2.val 0)).le hn
  calc
    |v.2 0| = Real.sqrt ((v.2 0) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (v.2 0 * v.2 0 +
        Real.exp (-p.2.val 0) * C.torusMetric.inner p.1 v.1 v.1) :=
      Real.sqrt_le_sqrt (by nlinarith)

universe u

theorem riemannianBallOf_cuspMap_subset_tail {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (p : CuspHalfSpace)
    {r : ℝ} (hr : 0 < r) (hrs : r < p.2.val 0) :
    riemannianBallOf H.metric (Tr.cuspMap i p) r ⊆
      Tr.cuspMap i '' {q : CuspHalfSpace | p.2.val 0 - r < q.2.val 0} := by
  let ρ : CuspHalfSpace → ℝ := fun q => q.2.val 0
  let a : ℝ := ρ p - r
  have ha : 0 < a := sub_pos.mpr hrs
  have hp : 0 < ρ p := hr.trans hrs
  have hρ : ContMDiff halfCollarModel 𝓘(ℝ) ∞ ρ :=
    Topology.Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd
  have hpositive : IsOpen {q : CuspHalfSpace | 0 < ρ q} :=
    isOpen_lt continuous_const hρ.continuous
  have hlocal : IsLocalDiffeomorphOn halfCollarModel (𝓡 3) ∞ (Tr.cuspMap i)
      {q : CuspHalfSpace | 0 < ρ q} := by
    intro q
    apply Topology.Manifold.isLocalDiffeomorphAt_of_isInteriorPoint_of_isImmersion
      (Tr.cuspEmbedding i).isImmersion
    · change (q : CuspHalfSpace) ∈ halfCollarModel.interior CuspHalfSpace
      rw [ModelWithCorners.interior_prod]
      change torusModel.IsInteriorPoint q.val.1 ∧ (𝓡∂ 1).IsInteriorPoint q.val.2
      refine ⟨BoundarylessManifold.isInteriorPoint, ?_⟩
      change q.val.2.val ∈ interior (range (𝓡∂ 1))
      rw [interior_range_modelWithCornersEuclideanHalfSpace]
      exact q.property
    · simp
  obtain ⟨Φ, hΦs, hΦt, hΦf⟩ :=
    DifferentialGeometry.IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      hlocal hpositive ⟨p, hp⟩ (Tr.cuspEmbedding i).isEmbedding.injective.injOn
  have hΦcoe : (Φ : CuspHalfSpace → H.Carrier) = Tr.cuspMap i := hΦf
  let A : Set H.Carrier := Tr.cuspMap i '' {q : CuspHalfSpace | a < ρ q}
  have htail_source : {q : CuspHalfSpace | a < ρ q} ⊆ Φ.source := by
    rw [hΦs]
    exact fun _ hq => ha.trans hq
  have hAopen : IsOpen A := by
    have h := Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_lt continuous_const hρ.continuous) htail_source
    change IsOpen ((Φ : CuspHalfSpace → H.Carrier) '' {q : CuspHalfSpace | a < ρ q}) at h
    simpa only [hΦcoe] using h
  have hAclosed : IsClosed (Tr.cuspMap i '' {q : CuspHalfSpace | a ≤ ρ q}) :=
    (Tr.cuspMap_isClosedEmbedding i).isClosedMap _
      (isClosed_le continuous_const hρ.continuous)
  have hclosure : closure A ⊆ Tr.cuspMap i '' {q : CuspHalfSpace | a ≤ ρ q} :=
    closure_minimal (image_mono (fun q (hq : a < ρ q) => le_of_lt hq)) hAclosed
  have hAV : closure A ⊆ Φ.target := by
    rintro q hq
    obtain ⟨z, hz, rfl⟩ := hclosure hq
    rw [hΦt]
    exact ⟨z, ha.trans_le hz, rfl⟩
  let f : H.Carrier → ℝ := ρ ∘ Φ.symm
  have hf : ContMDiffOn (𝓡 3) 𝓘(ℝ) 1 f Φ.target :=
    (hρ.comp_contMDiffOn Φ.contMDiffOn_invFun).of_le (by norm_num)
  have hfp : f (Tr.cuspMap i p) = ρ p := by
    change ρ (Φ.symm (Tr.cuspMap i p)) = ρ p
    rw [← hΦcoe]
    exact congrArg ρ (Φ.left_inv (by rw [hΦs]; exact hp))
  have hpA : Tr.cuspMap i p ∈ interior A := by
    rw [hAopen.interior_eq]
    exact ⟨p, by change ρ p - r < ρ p; linarith, rfl⟩
  have hdf : ∀ q ∈ interior A, ∀ v : TangentSpace (𝓡 3) q,
      |mvfderiv (𝓡 3) f q v| ≤ (1 : ℝ) * Real.sqrt (H.metric.inner q v v) := by
    intro q hq v
    have hqT : q ∈ Φ.target := hAV (subset_closure (interior_subset hq))
    let w : TangentSpace halfCollarModel (Φ.symm q) :=
      mfderiv (𝓡 3) halfCollarModel (Φ.symm : H.Carrier → CuspHalfSpace) q v
    have heq : (Φ : CuspHalfSpace → H.Carrier) ∘ (Φ.symm : H.Carrier → CuspHalfSpace)
        =ᶠ[𝓝 q] id := by
      filter_upwards [Φ.open_target.mem_nhds hqT] with z hz
      exact Φ.right_inv hz
    have hchain : mfderiv halfCollarModel (𝓡 3) (Tr.cuspMap i) (Φ.symm q) w = v := by
      rw [← hΦcoe]
      have hh := (mfderiv_comp q
        (Φ.mdifferentiableAt (by simp) (Φ.map_target' hqT))
        (Φ.symm.mdifferentiableAt (by simp) hqT)).symm.trans heq.mfderiv_eq
      have hv := DFunLike.congr_fun hh v
      simp only [mfderiv_id] at hv
      exact hv
    have hpoint : Tr.cuspMap i (Φ.symm q) = q := by
      rw [← hΦcoe]
      exact Φ.right_inv hqT
    have hmetric : (Tr.cusp i).metric.inner (Φ.symm q) w w = H.metric.inner q v v := by
      have h := (Tr.cuspIsometry i (Φ.symm q) w w).symm
      rw [hchain] at h
      exact h.trans (congrArg (fun z : H.Carrier =>
        H.metric.inner z (show EuclideanSpace ℝ (Fin 3) from v)
          (show EuclideanSpace ℝ (Fin 3) from v)) hpoint)
    have hb := cusp_radial_mvfderiv_bound (Tr.cusp i) (Φ.symm q) w
    change |mvfderiv (𝓡 3) (ρ ∘ Φ.symm) q v| ≤
      (1 : ℝ) * Real.sqrt (H.metric.inner q v v)
    rw [mvfderiv_comp_apply q (hρ.mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hqT)]
    simpa only [hmetric, one_mul] using hb
  have hfront : ∀ q ∈ frontier A, r ≤ |f q - f (Tr.cuspMap i p)| := by
    intro q hq
    obtain ⟨z, hz, rfl⟩ := hclosure (frontier_subset_closure hq)
    have hzle : ρ z ≤ a := by
      by_contra h
      have hmem : Tr.cuspMap i z ∈ A := ⟨z, lt_of_not_ge h, rfl⟩
      exact ((hAopen.frontier_eq ▸ hq).2) hmem
    have hza : ρ z = a := le_antisymm hzle hz
    have hzS : z ∈ Φ.source := by
      rw [hΦs]
      exact ha.trans_le hz
    have hfrep : f (Tr.cuspMap i z) = ρ z := by
      change ρ (Φ.symm (Tr.cuspMap i z)) = ρ z
      rw [← hΦcoe]
      exact congrArg ρ (Φ.left_inv hzS)
    rw [hfrep, hfp, hza]
    change r ≤ |ρ p - r - ρ p|
    have he : ρ p - r - ρ p = -r := by ring
    rw [he, abs_neg, abs_of_pos hr]
  have hbarrier := DifferentialGeometry.Geometry.Metric.riemannianEDistOf_ball_subset_of_frontier_gap
    H.metric Φ.open_target hAV f hf 1 hdf hpA (d := r) (r := r) hr hfront (by simp)
  simpa only [hAopen.interior_eq, riemannianBallOf, A, a, ρ] using hbarrier

theorem isCompact_image_cusp_band {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (a b : ℝ) :
    IsCompact (Tr.cuspMap i '' {q : CuspHalfSpace | q.2.val 0 ∈ Icc a b}) := by
  have hheight : _root_.Topology.IsClosedEmbedding
      (fun t : EuclideanHalfSpace 1 => t.val 0) :=
    (_root_.Topology.IsClosedEmbedding.subtypeVal isClosed_Ici).comp
      Topology.Manifold.halfSpaceOneHomeomorph.isClosedEmbedding
  have hhalf : IsCompact {t : EuclideanHalfSpace 1 | t.val 0 ∈ Icc a b} :=
    hheight.isCompact_preimage isCompact_Icc
  have hband : IsCompact {q : CuspHalfSpace | q.2.val 0 ∈ Icc a b} := by
    convert (isCompact_univ : IsCompact (univ : Set Torus)).prod hhalf using 1
    ext q
    simp
  exact hband.image (Tr.cuspEmbedding i).contMDiff.continuous

theorem riemannianClosedBallOf_cuspMap_subset_band {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (p : CuspHalfSpace)
    {r : ℝ} (hr : 0 ≤ r) (hrs : r < p.2.val 0) :
    riemannianClosedBallOf H.metric (Tr.cuspMap i p) r ⊆
      Tr.cuspMap i ''
        {q : CuspHalfSpace | q.2.val 0 ∈ Icc (p.2.val 0 - r) (p.2.val 0 + r)} := by
  intro y hy
  have hp : 0 < p.2.val 0 := hr.trans_lt hrs
  have hm0 : 0 < (r + p.2.val 0) / 2 := by linarith
  have hrm : r < (r + p.2.val 0) / 2 := by linarith
  have hms : (r + p.2.val 0) / 2 < p.2.val 0 := by linarith
  have hyopen : y ∈ riemannianBallOf H.metric (Tr.cuspMap i p)
      ((r + p.2.val 0) / 2) :=
    hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hm0).mpr hrm)
  obtain ⟨q, _, rfl⟩ := Tr.riemannianBallOf_cuspMap_subset_tail i p hm0 hms hyopen
  refine ⟨q, ⟨?_, ?_⟩, rfl⟩
  · by_contra h
    have hlow : q.2.val 0 < p.2.val 0 - r := lt_of_not_ge h
    let δ : ℝ := (r + (p.2.val 0 - q.2.val 0)) / 2
    have hrδ : r < δ := by dsimp [δ]; linarith
    have hδ0 : 0 < δ := hr.trans_lt hrδ
    have hδs : δ < p.2.val 0 := by
      have hq0 := q.2.property
      dsimp [δ]
      linarith
    have hyδ : Tr.cuspMap i q ∈ riemannianBallOf H.metric (Tr.cuspMap i p) δ :=
      hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ0).mpr hrδ)
    obtain ⟨z, hz, hzq⟩ := Tr.riemannianBallOf_cuspMap_subset_tail i p hδ0 hδs hyδ
    have hzq' : z = q := (Tr.cuspEmbedding i).isEmbedding.injective hzq
    rw [hzq'] at hz
    change p.2.val 0 - δ < q.2.val 0 at hz
    dsimp [δ] at hz
    linarith
  · by_contra h
    have hhigh : p.2.val 0 + r < q.2.val 0 := lt_of_not_ge h
    let δ : ℝ := (r + (q.2.val 0 - p.2.val 0)) / 2
    have hrδ : r < δ := by dsimp [δ]; linarith
    have hδ0 : 0 < δ := hr.trans_lt hrδ
    have hδq : δ < q.2.val 0 := by dsimp [δ]; linarith
    have hxδ : Tr.cuspMap i p ∈ riemannianBallOf H.metric (Tr.cuspMap i q) δ := by
      change riemannianEDistOf H.metric (Tr.cuspMap i q) (Tr.cuspMap i p) <
        ENNReal.ofReal δ
      rw [riemannianEDistOf_comm]
      exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ0).mpr hrδ)
    obtain ⟨z, hz, hzp⟩ := Tr.riemannianBallOf_cuspMap_subset_tail i q hδ0 hδq hxδ
    have hzp' : z = p := (Tr.cuspEmbedding i).isEmbedding.injective hzp
    rw [hzp'] at hz
    change q.2.val 0 - δ < p.2.val 0 at hz
    dsimp [δ] at hz
    linarith

theorem volume_riemannianBallOf_cuspMap_le {H : FiniteVolumeHyperbolicModel.{u}}
    (Tr : HyperbolicTruncation H) (i : Fin Tr.count) (p : CuspHalfSpace)
    {r : ℝ} (hr : 0 < r) (hrs : r < p.2.val 0) :
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric
        (riemannianBallOf H.metric (Tr.cuspMap i p) r) ≤
      Integral.Measure.riemannianVolumeMeasure torusModel Torus
        (Tr.cusp i).torusMetric univ *
          ENNReal.ofReal (Real.exp (r - p.2.val 0)) := by
  have h := MeasureTheory.measure_mono (μ :=
    Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric)
      (Tr.riemannianBallOf_cuspMap_subset_tail i p hr hrs)
  rw [Tr.volume_image_cusp_tail i (sub_nonneg.mpr hrs.le), neg_sub] at h
  exact h

end DifferentialGeometry.Geometry.Hyperbolic.HyperbolicTruncation
