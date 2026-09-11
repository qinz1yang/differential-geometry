import DifferentialGeometry.Geometry.Comparison.Nonnegative.FocalJacobi
import DifferentialGeometry.Geometry.Comparison.ConvexTangentSpace

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow

namespace DifferentialGeometry.Geometry.Topology

section Deepest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M]

def boundaryDistanceMax (I : ModelWithCorners ℝ E H) (C : Set M) : ℝ :=
  sSup ((fun x => Metric.infDist x (relBoundary I C)) '' C)

def deepest (I : ModelWithCorners ℝ E H) (C : Set M) : Set M :=
  {z ∈ C | boundaryDistanceMax I C ≤ Metric.infDist z (relBoundary I C)}

theorem mem_deepest_iff {C : Set M} {z : M} :
    z ∈ deepest I C ↔
      z ∈ C ∧ boundaryDistanceMax I C ≤ Metric.infDist z (relBoundary I C) := Iff.rfl

theorem deepest_eq_superlevel (I : ModelWithCorners ℝ E H) (C : Set M) :
    deepest I C =
      {z ∈ C | boundaryDistanceMax I C ≤ Metric.infDist z (relBoundary I C)} := rfl

theorem deepest_subset {C : Set M} : deepest I C ⊆ C := fun _ hz => hz.1


theorem continuous_infDist_relBoundary (I : ModelWithCorners ℝ E H) (C : Set M) :
    Continuous fun x : M => Metric.infDist x (relBoundary I C) :=
  Metric.continuous_infDist_pt _

theorem bddAbove_infDist_relBoundary_image {C : Set M} (hC : IsCompact C) :
    BddAbove ((fun x => Metric.infDist x (relBoundary I C)) '' C) :=
  (hC.image (continuous_infDist_relBoundary I C)).bddAbove

theorem infDist_le_boundaryDistanceMax {C : Set M} (hC : IsCompact C) {x : M}
    (hx : x ∈ C) : Metric.infDist x (relBoundary I C) ≤ boundaryDistanceMax I C :=
  le_csSup (bddAbove_infDist_relBoundary_image hC) ⟨x, hx, rfl⟩


theorem infDist_eq_boundaryDistanceMax_of_mem_deepest {C : Set M} (hC : IsCompact C)
    {x : M} (hx : x ∈ deepest I C) :
    Metric.infDist x (relBoundary I C) = boundaryDistanceMax I C :=
  le_antisymm (infDist_le_boundaryDistanceMax hC hx.1) hx.2

theorem deepest_eq_setOf_eq {C : Set M} (hC : IsCompact C) :
    deepest I C =
      {z ∈ C | Metric.infDist z (relBoundary I C) = boundaryDistanceMax I C} := by
  refine Subset.antisymm (fun z hz => ⟨hz.1, infDist_eq_boundaryDistanceMax_of_mem_deepest hC hz⟩)
    (fun z hz => ⟨hz.1, hz.2.ge⟩)

theorem deepest_nonempty {C : Set M} (hC : IsCompact C) (hne : C.Nonempty) :
    (deepest I C).Nonempty := by
  obtain ⟨x, hxC, hmax⟩ :=
    hC.exists_isMaxOn hne (continuous_infDist_relBoundary I C).continuousOn
  refine ⟨x, hxC, csSup_le (hne.image _) ?_⟩
  rintro r ⟨y, hy, rfl⟩
  exact hmax hy

theorem isClosed_deepest {C : Set M} (hC : IsCompact C) : IsClosed (deepest I C) :=
  hC.isClosed.inter (isClosed_le continuous_const (continuous_infDist_relBoundary I C))

theorem isCompact_deepest {C : Set M} (hC : IsCompact C) : IsCompact (deepest I C) :=
  hC.of_isClosed_subset (isClosed_deepest hC) deepest_subset

end Deepest

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [ConnectedSpace M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
private theorem shave_toReal_eq_dist (p q : M) :
    (riemannianEDist I p q).toReal = dist p q := by
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg]

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem shave_dist_intrinsicGeodesic_le (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (p : M) (v : TangentSpace I p) {s t : ℝ}
    (hst : s ≤ t) :
    dist (intrinsicGeodesic (I := I) g hEnorm p v s)
        (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ Real.sqrt (g.inner p v v) * (t - s) := by
  have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p v hst
  rw [← shave_toReal_eq_dist (I := I)]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans ?_
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (by linarith))]



theorem boundaryDistanceMax_pos (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hBne : (relBoundary I C).Nonempty) : 0 < boundaryDistanceMax I C := by
  obtain ⟨q, hq⟩ := maxSliceLocus_nonempty (I := I) hCne
  exact lt_of_lt_of_le (infDist_relBoundary_pos hEnorm hconv hCcomp.isClosed hBne hq)
    (infDist_le_boundaryDistanceMax hCcomp (maxSliceLocus_subset hq))

theorem exists_mem_isOpen_infDist_lt (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hBne : (relBoundary I C).Nonempty) {x : M} (hxC : x ∈ C)
    (hpos : 0 < Metric.infDist x (relBoundary I C))
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ y ∈ U ∩ C,
      Metric.infDist y (relBoundary I C) < Metric.infDist x (relBoundary I C) := by
  obtain ⟨z, hzB, hzdist⟩ := exists_nearest_relBoundary (I := I) hEnorm hconv hCcomp hBne x
  have hzC : z ∈ C := relBoundary_subset hzB
  have hfin : riemannianEDist I x z ≠ ⊤ := by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x z
  obtain ⟨v, hv, hvlen⟩ := minExp_of_ne_top (I := I) g hEnorm x z hfin
  have hτ0 : intrinsicGeodesic (I := I) g hEnorm x v 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hτ1 : intrinsicGeodesic (I := I) g hEnorm x v 1 = z := by
    rw [← expMapIntrinsic_smul_eq_intrinsicGeodesic g hEnorm x v 1, one_smul, hv]
  have hspeed : Real.sqrt (g.inner x v v) = Metric.infDist x (relBoundary I C) := by
    rw [hvlen, shave_toReal_eq_dist (I := I) x z, hzdist]
  have hmaps : MapsTo (intrinsicGeodesic (I := I) g hEnorm x v) (Icc (0 : ℝ) 1) C :=
    hconv zero_le_one
      ((intrinsicGeodesic_isGeodesic (I := I) g hEnorm x v).isGeodesicOn _)
      (intrinsicGeodesic_continuous g hEnorm x v).continuousOn
      (by rw [hτ0]; exact hxC) (by rw [hτ1]; exact hzC)
  have hopen : IsOpen (intrinsicGeodesic (I := I) g hEnorm x v ⁻¹' U) :=
    hU.preimage (intrinsicGeodesic_continuous g hEnorm x v)
  have hmem : (0 : ℝ) ∈ intrinsicGeodesic (I := I) g hEnorm x v ⁻¹' U := by
    rw [mem_preimage, hτ0]
    exact hxU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen 0 hmem
  have hs0 : 0 < min (δ / 2) 1 := lt_min (by linarith) zero_lt_one
  have hs1 : min (δ / 2) 1 ≤ 1 := min_le_right _ _
  have hsδ : min (δ / 2) 1 < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hsU : intrinsicGeodesic (I := I) g hEnorm x v (min (δ / 2) 1) ∈ U := by
    have hmemball : min (δ / 2) 1 ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs0]
      exact hsδ
    exact hball hmemball
  refine ⟨intrinsicGeodesic (I := I) g hEnorm x v (min (δ / 2) 1),
    ⟨hsU, hmaps ⟨hs0.le, hs1⟩⟩, ?_⟩
  have hd := shave_dist_intrinsicGeodesic_le g hEnorm x v hs1
  rw [hτ1, hspeed] at hd
  have h1 : Metric.infDist (intrinsicGeodesic (I := I) g hEnorm x v (min (δ / 2) 1))
      (relBoundary I C)
      ≤ dist (intrinsicGeodesic (I := I) g hEnorm x v (min (δ / 2) 1)) z :=
    Metric.infDist_le_dist_of_mem hzB
  have hexp : Metric.infDist x (relBoundary I C) * (1 - min (δ / 2) 1)
      = Metric.infDist x (relBoundary I C)
        - Metric.infDist x (relBoundary I C) * min (δ / 2) 1 := by ring
  have hprod : 0 < Metric.infDist x (relBoundary I C) * min (δ / 2) 1 := mul_pos hpos hs0
  linarith

theorem maxSliceDim_deepest_lt (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hBne : (relBoundary I C).Nonempty) :
    maxSliceDim I (deepest I C) < maxSliceDim I C := by
  have hle : maxSliceDim I (deepest I C) ≤ maxSliceDim I C :=
    maxSliceDim_mono (I := I) (C := deepest I C) (D := C) deepest_subset
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  obtain ⟨S, ⟨x, hxS⟩, hSD, hS⟩ :=
    exists_maxSlice (I := I) (deepest_nonempty (I := I) hCcomp hCne)
  rw [heq] at hS
  obtain ⟨U, hU, hxU, hUeq⟩ :=
    maxSlice_eq_near (I := I) hEnorm hconv hS (hSD.trans deepest_subset) hxS
  have hxD : x ∈ deepest I C := hSD hxS
  have hxdist : Metric.infDist x (relBoundary I C) = boundaryDistanceMax I C :=
    infDist_eq_boundaryDistanceMax_of_mem_deepest hCcomp hxD
  have hpos : 0 < Metric.infDist x (relBoundary I C) := by
    rw [hxdist]
    exact boundaryDistanceMax_pos g hEnorm hconv hCcomp hCne hBne
  obtain ⟨y, ⟨hyU, hyC⟩, hylt⟩ :=
    exists_mem_isOpen_infDist_lt g hEnorm hconv hCcomp hBne hxD.1 hpos hU hxU
  have hyS : y ∈ S := by
    have : y ∈ U ∩ S := by rw [← hUeq]; exact ⟨hyU, hyC⟩
    exact this.2
  have hydist : Metric.infDist y (relBoundary I C) = boundaryDistanceMax I C :=
    infDist_eq_boundaryDistanceMax_of_mem_deepest hCcomp (hSD hyS)
  rw [hydist, hxdist] at hylt
  exact lt_irrefl _ hylt



def ShavingConcavity (g : SmoothRiemannianMetric I M) : Prop :=
  ∀ C : Set M, IsCompact C → C.Nonempty → IsTotallyConvex (I := I) g C →
    (relBoundary I C).Nonempty → ∀ t : ℝ,
      IsTotallyConvex (I := I) g {z ∈ C | t ≤ Metric.infDist z (relBoundary I C)}

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem ShavingConcavity.isTotallyConvex_deepest {g : SmoothRiemannianMetric I M}
    (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvex (I := I) g C) (hBne : (relBoundary I C).Nonempty) :
    IsTotallyConvex (I := I) g (deepest I C) :=
  hconc C hCcomp hCne hconv hBne (boundaryDistanceMax I C)

theorem exists_deepest_of_shavingConcavity (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvex (I := I) g C) (hBne : (relBoundary I C).Nonempty) :
    deepest I C ⊆ C ∧ (deepest I C).Nonempty ∧ IsCompact (deepest I C) ∧
      IsTotallyConvex (I := I) g (deepest I C) ∧
      maxSliceDim I (deepest I C) < maxSliceDim I C :=
  ⟨deepest_subset, deepest_nonempty hCcomp hCne, isCompact_deepest hCcomp,
    hconc.isTotallyConvex_deepest hCcomp hCne hconv hBne,
    maxSliceDim_deepest_lt g hEnorm hconv hCcomp hCne hBne⟩

theorem exists_soul_set_of_shavingConcavity (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hconv : IsTotallyConvex (I := I) g C) :
    ∃ S ⊆ C, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧
      ((relBoundary I C).Nonempty → maxSliceDim I S < maxSliceDim I C) := by
  suffices H : ∀ n : ℕ, ∀ D : Set M, maxSliceDim I D = n → IsCompact D → D.Nonempty →
      IsTotallyConvex (I := I) g D →
      ∃ S ⊆ D, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
        relBoundary I S = ∅ ∧
        ((relBoundary I D).Nonempty → maxSliceDim I S < maxSliceDim I D) by
    exact H (maxSliceDim I C) C rfl hCcomp hCne hconv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hDdim hDcomp hDne hDconv
    rcases eq_empty_or_nonempty (relBoundary I D) with hB | hB
    · exact ⟨D, Subset.rfl, hDne, hDcomp, hDconv, hB, fun h => absurd hB h.ne_empty⟩
    obtain ⟨hsub, hne, hcomp, hconv', hlt⟩ :=
      exists_deepest_of_shavingConcavity g hEnorm hconc hDcomp hDne hDconv hB
    obtain ⟨S, hSsub, hSne, hScomp, hSconv, hSB, -⟩ :=
      ih (maxSliceDim I (deepest I D)) (by rw [← hDdim]; exact hlt) (deepest I D) rfl
        hcomp hne hconv'
    exact ⟨S, hSsub.trans hsub, hSne, hScomp, hSconv, hSB,
      fun _ => lt_of_le_of_lt
        (maxSliceDim_mono (I := I) (C := S) (D := deepest I D) hSsub) hlt⟩



omit [T2Space (TangentBundle I M)] in
theorem isTotallyConvex_deepest_of_sec_nonneg (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hconv : IsTotallyConvex (I := I) g C) (hCclosed : IsClosed C)
    (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C)) :
    IsTotallyConvex (I := I) g (deepest I C) :=
  isTotallyConvex_superlevel_infDist_relBoundary_of_sec_nonneg (I := I) g hEnorm hsec
    hconv hCclosed hdim hBne hsupp (boundaryDistanceMax I C)

theorem exists_deepest_lower_dim_of_sec_nonneg (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    {C : Set M} (hconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) (hdim : maxSliceDim I C = Module.finrank ℝ E)
    (hBne : (relBoundary I C).Nonempty)
    (hsupp : HasSupportingHalfSpaces (I := I) g hEnorm C (relBoundary I C)) :
    deepest I C ⊆ C ∧ (deepest I C).Nonempty ∧ IsCompact (deepest I C) ∧
      IsTotallyConvex (I := I) g (deepest I C) ∧
      maxSliceDim I (deepest I C) < maxSliceDim I C :=
  ⟨deepest_subset, deepest_nonempty hCcomp hCne, isCompact_deepest hCcomp,
    isTotallyConvex_deepest_of_sec_nonneg g hEnorm hsec hconv hCcomp.isClosed hdim hBne hsupp,
    maxSliceDim_deepest_lt g hEnorm hconv hCcomp hCne hBne⟩



omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem maxSliceDim_rayBusemannSublevel (p : M) {t : ℝ} (ht : 0 < t) :
    maxSliceDim I (rayBusemannSublevel p t) = Module.finrank ℝ E :=
  maxSliceDim_eq_finrank_of_interior_nonempty (I := I)
    ⟨p, rayBusemannSublevel_subset_interior p ht (self_mem_rayBusemannSublevel p le_rfl)⟩

theorem relBoundary_rayBusemannSublevel_nonempty [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p : M) {t : ℝ} (ht : 0 < t) :
    (relBoundary I (rayBusemannSublevel p t)).Nonempty := by
  rcases eq_empty_or_nonempty (relBoundary I (rayBusemannSublevel p t)) with hB | hB
  · exfalso
    have hloc : maxSliceLocus I (rayBusemannSublevel p t) = rayBusemannSublevel p t :=
      relBoundary_eq_empty_iff.mp hB
    have hopen : IsOpen (rayBusemannSublevel p t) := by
      rw [← hloc]
      exact isOpen_maxSliceLocus_of_maxSliceDim (I := I) hEnorm
        (isTotallyConvex_rayBusemannSublevel g hEnorm hsec p t)
        (maxSliceDim_rayBusemannSublevel p ht)
    have hclopen : IsClopen (rayBusemannSublevel p t) :=
      ⟨isClosed_rayBusemannSublevel p t, hopen⟩
    have huniv : rayBusemannSublevel p t = univ :=
      hclopen.eq_univ ⟨p, self_mem_rayBusemannSublevel p ht.le⟩
    have hcomp := isCompact_rayBusemannSublevel g hEnorm hsec p t
    rw [huniv] at hcomp
    exact absurd hcomp (noncompact_univ M)
  · exact hB



theorem exists_soul_set [NoncompactSpace M] (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hconc : ShavingConcavity (I := I) g) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E := by
  obtain ⟨S, -, hSne, hScomp, hSconv, hSB, hSdim⟩ :=
    exists_soul_set_of_shavingConcavity g hEnorm hconc
      (isCompact_rayBusemannSublevel g hEnorm hsec p 1)
      ⟨p, self_mem_rayBusemannSublevel p zero_le_one⟩
      (isTotallyConvex_rayBusemannSublevel g hEnorm hsec p 1)
  refine ⟨S, hSne, hScomp, hSconv, hSB, ?_⟩
  have hlt := hSdim (relBoundary_rayBusemannSublevel_nonempty g hEnorm hsec p one_pos)
  rwa [maxSliceDim_rayBusemannSublevel (I := I) p one_pos] at hlt



theorem isEmbeddedSlice_of_relBoundary_eq_empty {g : SmoothRiemannianMetric I M}
    (hEnorm : IsMetricNorm (I := I) g) {S : Set M}
    (hSconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    IsEmbeddedSlice I (maxSliceDim I S) S := by
  have h := isEmbeddedSlice_maxSliceLocus (I := I) hEnorm hSconv
  rwa [relBoundary_eq_empty_iff.mp hB] at h

theorem isInnerDirection_iff_mem_sliceTangent_of_relBoundary_eq_empty
    {g : SmoothRiemannianMetric I M} (hEnorm : IsMetricNorm (I := I) g) {S : Set M}
    (hSconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) {x : M}
    (hx : x ∈ S) {v : TangentSpace I x} :
    IsInnerDirection (I := I) g hEnorm S x v ↔ v ∈ sliceTangent I S x := by
  have hloc : maxSliceLocus I S = S := relBoundary_eq_empty_iff.mp hB
  have hxloc : x ∈ maxSliceLocus I S := by rw [hloc]; exact hx
  have h := isInnerDirection_iff_mem_sliceTangent (I := I) hEnorm hSconv hxloc (v := v)
  rwa [hloc] at h

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem relBoundary_singleton (x : M) : relBoundary I ({x} : Set M) = ∅ := by
  rw [relBoundary_eq_empty_iff]
  obtain ⟨S, ⟨y, hyS⟩, hSsub, hS⟩ := exists_maxSlice (I := I) (singleton_nonempty x)
  have hyx : y = x := hSsub hyS
  refine Subset.antisymm maxSliceLocus_subset (fun z hz => ?_)
  rw [mem_singleton_iff] at hz
  refine ⟨S, ?_, hSsub, hS⟩
  rw [hz, ← hyx]
  exact hyS

theorem eq_singleton_of_maxSliceDim_eq_zero (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {S : Set M}
    (hSconv : IsTotallyConvex (I := I) g S) (hSne : S.Nonempty)
    (hB : relBoundary I S = ∅) (hdim : maxSliceDim I S = 0) :
    ∃ x : M, S = {x} := by
  obtain ⟨x, hx⟩ := hSne
  have hslice : IsEmbeddedSlice I 0 S := by
    have h := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hSconv hB
    rwa [hdim] at h
  obtain ⟨c, A, hA, hxc, hAdim, himg⟩ := hslice x hx
  have hdirbot : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hAdim
  have hxA : c x ∈ (A : Set E) := (himg hxc).2 hx
  have hkey : ∀ y ∈ S, y ∈ c.source → y = x := by
    intro y hyS hyc
    have hyA : c y ∈ (A : Set E) := (himg hyc).2 hyS
    have hvsub : c y -ᵥ c x ∈ A.direction := AffineSubspace.vsub_mem_direction hyA hxA
    rw [hdirbot, Submodule.mem_bot, vsub_eq_zero_iff_eq] at hvsub
    exact c.toPartialEquiv.injOn hyc hxc hvsub
  refine ⟨x, Subset.antisymm (fun y hyS => ?_) (singleton_subset_iff.2 hx)⟩
  rw [mem_singleton_iff]
  by_contra hyx
  have hpre : IsPreconnected S :=
    (hSconv.isPathConnected g hEnorm ⟨x, hx⟩).isConnected.isPreconnected
  have hcover : S ⊆ c.source ∪ ({x} : Set M)ᶜ := by
    intro w hwS
    by_cases hwx : w = x
    · exact Or.inl (hwx ▸ hxc)
    · exact Or.inr hwx
  obtain ⟨w, hwS, hwc, hwx⟩ :=
    hpre c.source ({x} : Set M)ᶜ c.open_source isOpen_compl_singleton hcover
      ⟨x, hx, hxc⟩ ⟨y, hyS, hyx⟩
  exact hwx (hkey w hwS hwc)

theorem exists_soul_set_isEmbeddedSlice [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) (M := M) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (hconc : ShavingConcavity (I := I) g) (p : M) :
    ∃ S : Set M, S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
      relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E ∧
      IsEmbeddedSlice I (maxSliceDim I S) S := by
  obtain ⟨S, hSne, hScomp, hSconv, hSB, hSdim⟩ := exists_soul_set g hEnorm hsec hconc p
  exact ⟨S, hSne, hScomp, hSconv, hSB, hSdim,
    isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hSconv hSB⟩

end Geometry

end DifferentialGeometry.Geometry.Topology

end
