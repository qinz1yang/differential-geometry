import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.MetricCurvatureDifference
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Endpoint.Basic
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.Local
import DifferentialGeometry.Geometry.Curvature.Metric.SectionalCone
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Continuity
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.SectionalRicci
import DifferentialGeometry.Topology.SigmaCompactOpen

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

section Restriction

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local instance pointedSectionalRestrictionOne : IsManifold I 1 M :=
  IsManifold.of_le (I := I) (M := M) (n := ∞) (by decide)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem riemannOp_restrictOpen_eq
    (g : SmoothRiemannianMetric I M) (U : TopologicalSpace.Opens M)
    (x : U) (v w u : TangentSpace I x) :
    riemannOp (cov := LeviCivita (I := I) (g.restrictOpen (I := I) U)) x v w u =
      riemannOp (cov := LeviCivita (I := I) g) (x : M) v w u := by
  let A : TangentSpace I (x : M) :=
    riemannOp (cov := LeviCivita (I := I) (g.restrictOpen (I := I) U)) x v w u
  let B := riemannOp (cov := LeviCivita (I := I) g) (x : M) v w u
  have hp (z : TangentSpace I (x : M)) : g.inner (x : M) z A = g.inner (x : M) z B := by
    calc
      _ = metricRm04StandardAt (I := I) (g.restrictOpen (I := I) U) x v w u z :=
        (rm04_eq_inner_riem (g.restrictOpen (I := I) U) x v w u z).symm
      _ = metricRm04StandardAt (I := I) g (x : M) v w u z := by
        have hr := metricRm04StandardAt_restrictOpen g U x v w u z
        erw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
          mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at hr
        exact hr
      _ = _ := rm04_eq_inner_riem g (x : M) v w u z
  change A = B
  apply sub_eq_zero.mp
  by_contra hne
  have hpos := g.pos (x : M) (A - B) hne
  have hz : g.inner (x : M) (A - B) (A - B) = 0 := by
    rw [map_sub, hp]
    ring
  exact (ne_of_gt hpos) hz

end Restriction

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedSectionalLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedSectionalLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedSectionalLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedSectionalLimitOne : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
local instance pointedSectionalLimitT2 : T2Space L.M := L.t2
local instance pointedSectionalLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedSectionalApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedSectionalApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedSectionalApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedSectionalApproxOne (k : ℕ) :
    IsManifold I 1 (X.obj k).M :=
  IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
local instance pointedSectionalApproxT2 (k : ℕ) :
    T2Space (X.obj k).M := (X.obj k).t2
local instance pointedSectionalApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedSectionalSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Φ k) := metricSourceDomainTopology Φ k
local instance pointedSectionalSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Φ k) := metricSourceDomainChartedSpace Φ k
local instance pointedSectionalSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := metric_source_domain_smooth Φ k
local instance pointedSectionalSourceOne (k : ℕ) :
    IsManifold I 1 (MetricSourceDomain (I := I) Φ k) :=
  IsManifold.of_le (I := I) (M := MetricSourceDomain (I := I) Φ k) (n := ∞) (by decide)
local instance pointedSectionalSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Φ k) := metric_source_domain_t2 Φ k
local instance pointedSectionalSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
  metric_source_domain_sigma_compact Φ k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Φ k)

local instance pointedSectionalTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Φ k) := metricTargetDomainTopology Φ k
local instance pointedSectionalTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Φ k) := metricTargetDomainChartedSpace Φ k
local instance pointedSectionalTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) := metric_target_domain_smooth Φ k
local instance pointedSectionalTargetOne (k : ℕ) :
    IsManifold I 1 (MetricTargetDomain (I := I) Φ k) :=
  IsManifold.of_le (I := I) (M := MetricTargetDomain (I := I) Φ k) (n := ∞) (by decide)
local instance pointedSectionalTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Φ k) := metric_target_domain_t2 Φ k
local instance pointedSectionalTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
  metric_target_domain_sigma_compact Φ k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Φ k)

variable {Φ}

omit [NeZero (Module.finrank ℝ E)] in
theorem pointedRm04_tendsto_of_canonical_metric_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Φ (CanonicalMetricCompactness.canonicalSourceData Φ) K 2)
    (x : L.M) (v w u z : TangentSpace I x) :
    Tendsto (fun k => metricRm04StandardAt (I := I) (X.obj (subseq k)).metric (Φ.map k x)
        (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x w)
        (mfderiv I I (Φ.map k) x u) (mfderiv I I (Φ.map k) x z)) atTop
      (𝓝 (metricRm04StandardAt (I := I) L.metric x v w u z)) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon hepsilon
  let n : ℝ := Module.finrank ℝ E
  let R := riemannOp (cov := LeviCivita (I := I) L.metric) x v w u
  let A : ℝ := Real.sqrt (L.metric.inner x z z) * Real.sqrt (L.metric.inner x R R) +
    864 * Real.sqrt (L.metric.inner x v v) * Real.sqrt (L.metric.inner x w w) *
      Real.sqrt (L.metric.inner x u u) * Real.sqrt (L.metric.inner x z z)
  have hn : 0 ≤ n := by dsimp only [n]; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let delta : ℝ := min (1 / (2 * (n + 1))) (min 1 (epsilon / (A + 1)))
  have hd0 : 0 < delta := by dsimp only [delta]; positivity
  have hd1 : delta ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hdn : n * delta ≤ 1 / 2 := by
    have ht : delta ≤ 1 / (2 * (n + 1)) := min_le_left _ _
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (n + 1))).mp ht
    nlinarith [hd0.le]
  have hdA : delta * A < epsilon := by
    have ht : delta ≤ epsilon / (A + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ (by positivity : 0 < A + 1)).mp ht
    nlinarith
  obtain ⟨k0, hk0⟩ := hconv {x} isCompact_singleton delta hd0
  refine ⟨k0, fun k hk => ?_⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain (I := I) Φ k := ⟨x, hsource (Set.mem_singleton x)⟩
  let gU := L.metric.restrictOpen (I := I) (metricSourceOpenSubset Φ k)
  let hU := Diffeomorph.pullbackMetric (I := I)
    ((X.obj (subseq k)).metric.restrictOpen (I := I) (metricTargetOpenSubset Φ k))
    (metricSourceTargetDiffeomorph Φ k)
  have hcompact : IsCompact (metricSourceCompactSet (I := I) Φ k {x}) :=
    metric_source_compact_set_is_compact (I := I) Φ k isCompact_singleton hsource
  change metricDerivNormSupOn (I := I)
    (metricSourceCompactSet (I := I) Φ k {x}) 2 hU gU gU < delta at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm (I := I) a hU gU gU xu ≤ delta := by
    have ht := derivNorm_le_sup (I := I) hcompact ha
      hU gU gU (x := xu) (Set.mem_singleton x)
    exact ht.trans hsup.le
  have hb := metricRm04_difference_le_of_metricDerivNorm_le gU hU xu hd0.le hd1 hdn
    hjet v w u z
  have hlim : metricRm04StandardAt (I := I) gU xu v w u z =
      metricRm04StandardAt (I := I) L.metric x v w u z := by
    have hr := metricRm04StandardAt_restrictOpen L.metric (metricSourceOpenSubset Φ k) xu v w u z
    erw [mfderiv_subtype_val_apply, mfderiv_subtype_val_apply,
      mfderiv_subtype_val_apply, mfderiv_subtype_val_apply] at hr
    exact hr
  have hpull : metricRm04StandardAt (I := I) hU xu v w u z =
      metricRm04StandardAt (I := I) (X.obj (subseq k)).metric (Φ.map k x)
        (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x w)
        (mfderiv I I (Φ.map k) x u) (mfderiv I I (Φ.map k) x z) := by
    have ht := metricRm04StandardAt_pullback_localDiffeo
      (X.obj (subseq k)).metric (metricTargetOpenSubset Φ k) (metricSourceOpenSubset Φ k)
      (metricSourceTargetDiffeomorph Φ k) xu v w u z
    erw [metric_source_target_diffeomorph_apply, metric_source_target_diffeomorph_mfderiv,
      metric_source_target_diffeomorph_mfderiv, metric_source_target_diffeomorph_mfderiv,
      metric_source_target_diffeomorph_mfderiv] at ht
    exact ht
  have hR : riemannOp (cov := LeviCivita (I := I) gU) xu v w u = R :=
    riemannOp_restrictOpen_eq L.metric (metricSourceOpenSubset Φ k) xu v w u
  rw [hpull, hlim] at hb
  simp only [hR] at hb
  change |metricRm04StandardAt (I := I) (X.obj (subseq k)).metric (Φ.map k x)
      (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x w)
      (mfderiv I I (Φ.map k) x u) (mfderiv I I (Φ.map k) x z) -
      metricRm04StandardAt (I := I) L.metric x v w u z| ≤ delta * A at hb
  rw [Real.dist_eq]
  exact hb.trans_lt hdA

omit [NeZero (Module.finrank ℝ E)] in
theorem sectional_nonnegative_of_pointed_canonical_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Φ (CanonicalMetricCompactness.canonicalSourceData Φ) K 2)
    (hsec : ∀ᶠ k in atTop, ∀ y : L.M, y ∈ Φ.source k →
      metricRm04At (I := I) (X.obj (subseq k)).metric (Φ.map k y) ∈
        tensor04SectionalNonnegativeCone (I := I)) :
    ∀ x : L.M, metricRm04At (I := I) L.metric x ∈
      tensor04SectionalNonnegativeCone (I := I) := by
  intro x
  apply (metricRm04At_mem_tensor04SectionalNonnegativeCone_iff L.metric x).mpr
  intro v w
  have hc := pointedRm04_tendsto_of_canonical_metric_convergence hconv x v w w v
  obtain ⟨k0, hk0⟩ := Φ.source_subset (K := {x}) isCompact_singleton
  have hs : ∀ᶠ k in atTop, x ∈ Φ.source k := by
    filter_upwards [eventually_ge_atTop k0] with k hk
    exact hk0 k hk (Set.mem_singleton x)
  apply ge_of_tendsto hc
  filter_upwards [hsec, hs] with k hk hx
  exact ((metricRm04At_mem_tensor04SectionalNonnegativeCone_iff
    (X.obj (subseq k)).metric (Φ.map k x)).mp (hk x hx))
    (mfderiv I I (Φ.map k) x v) (mfderiv I I (Φ.map k) x w)

omit [NeZero (Module.finrank ℝ E)] in
theorem ricci_nonnegative_of_pointed_canonical_convergence
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn (I := I) Φ (CanonicalMetricCompactness.canonicalSourceData Φ) K 2)
    (hsec : ∀ᶠ k in atTop, ∀ y : L.M, y ∈ Φ.source k →
      metricRm04At (I := I) (X.obj (subseq k)).metric (Φ.map k y) ∈
        tensor04SectionalNonnegativeCone (I := I)) :
    ∀ x : L.M, ∀ v : TangentSpace I x, 0 ≤ ricciTensor (I := I) L.metric x v v := by
  intro x v
  exact Geometry.Riemannian.BonnetMyers.ricci_nonneg_of_sec L.metric x
    (sectional_nonnegative_of_pointed_canonical_convergence hconv hsec x) v

omit [NeZero (Module.finrank ℝ E)] in
theorem sectional_nonnegative_in_canonicalMetricCompactness
    (C : CanonicalMetricCompactness (I := I) X)
    (hsec : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let _ : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let _ : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let _ : T2Space (X.obj k).M := (X.obj k).t2
      let _ : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      ∀ y : (X.obj k).M, metricRm04At (I := I) (X.obj k).metric y ∈
        tensor04SectionalNonnegativeCone (I := I)) :
    let P := C.compactness.limit
    let _ : TopologicalSpace P.M := P.topology
    let _ : ChartedSpace H P.M := P.charted
    let _ : IsManifold I ∞ P.M := P.smooth
    let _ : T2Space P.M := P.t2
    let _ : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ x : P.M, metricRm04At (I := I) P.metric x ∈
      tensor04SectionalNonnegativeCone (I := I) := by
  let P := C.compactness.limit
  let _ : TopologicalSpace P.M := P.topology
  let _ : ChartedSpace H P.M := P.charted
  let _ : IsManifold I ∞ P.M := P.smooth
  let _ : T2Space P.M := P.t2
  let _ : SigmaCompactSpace P.M := P.sigmaCompact
  have hD : C.compactness.convergence.metrics.domain =
      CanonicalMetricCompactness.canonicalSourceData C.compactness.maps :=
    funext C.domain_eq_canonical
  have hc : ∀ K : Set P.M, IsCompact K →
      metricSourceConvergesOn (I := I) C.compactness.maps
        (CanonicalMetricCompactness.canonicalSourceData C.compactness.maps) K 2 := by
    intro K hK
    have ht := C.compactness.convergence.metrics.converges K hK 2
    rw [hD] at ht
    exact ht
  apply sectional_nonnegative_of_pointed_canonical_convergence hc
  exact Filter.Eventually.of_forall
    (fun k y _hy => hsec (C.compactness.subseq k) (C.compactness.maps.map k y))

theorem sectional_nonnegative_in_metricCompactness
    (inp : MetricCompactnessAssumptions (I := I) X)
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      ConnectedSpace (X.obj k).M)
    (hsec : ∀ k : ℕ,
      let _ : TopologicalSpace (X.obj k).M := (X.obj k).topology
      let _ : ChartedSpace H (X.obj k).M := (X.obj k).charted
      let _ : IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
      let _ : T2Space (X.obj k).M := (X.obj k).t2
      let _ : SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact
      ∀ y : (X.obj k).M, metricRm04At (I := I) (X.obj k).metric y ∈
        tensor04SectionalNonnegativeCone (I := I)) :
    let C := inp.metricCompactness hcomplete hconn
    let _ : TopologicalSpace C.limit.M := C.limit.topology
    let _ : ChartedSpace H C.limit.M := C.limit.charted
    let _ : IsManifold I ∞ C.limit.M := C.limit.smooth
    let _ : T2Space C.limit.M := C.limit.t2
    let _ : SigmaCompactSpace C.limit.M := C.limit.sigmaCompact
    ∀ x : C.limit.M, metricRm04At (I := I) C.limit.metric x ∈
      tensor04SectionalNonnegativeCone (I := I) :=
  sectional_nonnegative_in_canonicalMetricCompactness
    (inp.canonicalMetricCompactness hcomplete hconn) hsec

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
