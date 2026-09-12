import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedSectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedInverseDistanceControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenRestrictionVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.VolumeNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Geometry.Metric.TensorInner.FiberMetric.Tensor0SMetricIneq
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Filter Set MeasureTheory TopologicalSpace
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open CanonicalNeighborhood
open scoped Manifold ContDiff ENNReal Topology BigOperators

universe u uE uH

section LocalVolume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance pointedNCLocalMMeasurable : MeasurableSpace M := borel M
private local instance pointedNCLocalMBorel : BorelSpace M := ⟨rfl⟩
private local instance pointedNCLocalNMeasurable : MeasurableSpace N := borel N
private local instance pointedNCLocalNBorel : BorelSpace N := ⟨rfl⟩

omit [CompleteSpace E] in
private theorem pointedNC_image_volume_le
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (F : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    {A : Set M} (hA : MeasurableSet A) (hsource : A ⊆ F.source)
    {Q : ℝ} (hQ : 0 < Q)
    (hmetric : ∀ x ∈ A, ∀ v : TangentSpace I x,
      h.inner (F x) (mfderiv I I (F : M → N) x v)
        (mfderiv I I (F : M → N) x v) ≤ Q * g.inner x v v) :
    riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) ≤
      ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g A := by
  let U : Opens M := ⟨F.source, F.open_source⟩
  have hU : (U : Set M) ⊆ F.source := subset_rfl
  let V : Opens N := ⟨(F : M → N) '' (U : Set M), image_opens_isOpen F hU⟩
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I U.isOpen)
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let _ : MeasurableSpace U := borel U
  let _ : BorelSpace U := ⟨rfl⟩
  let _ : MeasurableSpace V := borel V
  let _ : BorelSpace V := ⟨rfl⟩
  let e : U ≃ₘ⟮I, I⟯ V := PartialDiffeomorph.toOpensDiffeo F hU
  let B : Set U := (Subtype.val : U → M) ⁻¹' A
  let gU := g.restrictOpen U
  let hV := h.restrictOpen V
  let gP := Diffeomorph.pullbackMetric hV e
  have hB : MeasurableSet B := hA.preimage continuous_subtype_val.measurable
  have hvalB : (Subtype.val : U → M) '' B = A := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hsource hx⟩, hx, rfl⟩
  have himage : (Subtype.val : V → N) '' ((e : U → V) '' B) =
      (F : M → N) '' A := by
    rw [Set.image_image]
    change (fun x : U => F (x : M)) '' B = (F : M → N) '' A
    rw [← Set.image_image, hvalB]
  have he : MeasurableEmbedding (e : U → V) :=
    e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  have hpres := (volumeMeasurePreserving_pullbackMetric hV e).measure_preimage_emb he
    ((e : U → V) '' B)
  rw [he.injective.preimage_image] at hpres
  have hcomp : ∀ x ∈ B, ∀ v : TangentSpace I x,
      gP.inner x v v ≤ Q * gU.inner x v v := by
    intro x hx v
    dsimp only [gP, gU, hV]
    rw [Diffeomorph.pullbackMetric_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner]
    dsimp only [e]
    rw [PartialDiffeomorph.mfderiv_toOpensDiffeo]
    exact hmetric (x : M) hx v
  calc
    riemannianVolumeMeasure (I := I) (M := N) h ((F : M → N) '' A) =
        riemannianVolumeMeasure (I := I) (M := V) hV ((e : U → V) '' B) := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, himage]
    _ = riemannianVolumeMeasure (I := I) (M := U) gP B := hpres.symm
    _ ≤ ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := U) gU B :=
      riemannianVolumeMeasure_le_on gU gP hB hQ hcomp
    _ = ENNReal.ofReal (Real.sqrt (Q ^ Module.finrank ℝ E)) *
        riemannianVolumeMeasure (I := I) (M := M) g A := by
      rw [riemannianVolumeMeasure_restrictOpen_apply, hvalB]

end LocalVolume

section CurvatureEstimate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance pointedNCCurvatureOne : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

theorem metricRmNorm_le_of_relative_two_jets
    (g h : SmoothRiemannianMetric I M) (x : M) {delta K : ℝ}
    (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1)
    (hsmall : (Module.finrank ℝ E : ℝ) * delta ≤ 1 / 2)
    (hK : normSq0S g x 4 (metricRm04At g x) ≤ K)
    (hjet : ∀ a : ℕ, a ≤ 2 → metricDerivNorm a h g g x ≤ delta) :
    Real.sqrt (normSq0S h x 4 (metricRm04At h x)) ≤
      ((1 - (Module.finrank ℝ E : ℝ) * delta)⁻¹) ^ 2 *
        (Real.sqrt K + (Module.finrank ℝ E : ℝ) ^ 2 * delta * (Real.sqrt K + 864)) := by
  classical
  let n : ℝ := Module.finrank ℝ E
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis g x
  have hinv := metricInverseInBasis_of_orthonormal g basis hON
  let A := metricRm04At h x - metricRm04At g x
  let B := delta * (Real.sqrt K + 864)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hunit (i) : g.inner x (basis i) (basis i) = 1 := by simp [hON]
  have hcomponent (slots : Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x))) :
      |component0S basis A slots| ≤ B := by
    have hR := riemannOp_normSq_le_of_rmNormSq_le g x hK
      (basis (slots 0)) (basis (slots 1)) (basis (slots 2))
    simp only [hunit, mul_one] at hR
    have hRroot := Real.sqrt_le_sqrt hR
    have hd := metricRm04_difference_le_of_metricDerivNorm_le g h x hd0 hd1 hsmall
      hjet (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3))
    simp only [hunit, Real.sqrt_one, one_mul, mul_one] at hd
    have heval : component0S basis A slots =
        metricRm04StandardAt h x (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) -
        metricRm04StandardAt g x (basis (slots 0)) (basis (slots 1))
          (basis (slots 2)) (basis (slots 3)) := by
      change A (fun i => basis (slots i)) = _
      have hs : (fun i : Fin 4 => basis (slots i)) =
          vec4 (basis (slots 0)) (basis (slots 1)) (basis (slots 2)) (basis (slots 3)) := by
        funext i
        fin_cases i <;> rfl
      rw [hs]
      rfl
    rw [heval]
    exact hd.trans (mul_le_mul_of_nonneg_left (add_le_add_left hRroot 864) hd0)
  have hdiff := normSq0S_le_card_of_component_bound g x 4 basis hinv A B hB hcomponent
  have hdim : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have hcard : (Fintype.card (Fin 4 → Fin (Module.finrank ℝ (TangentSpace I x))) : ℝ) =
      n ^ 4 := by simp [n, hdim]
  rw [hcard] at hdiff
  have hdiffroot : Real.sqrt (normSq0S g x 4 A) ≤ n ^ 2 * B := by
    have hs : n ^ 4 * B ^ 2 = (n ^ 2 * B) ^ 2 := by ring
    rw [hs] at hdiff
    exact (Real.sqrt_le_sqrt hdiff).trans_eq (Real.sqrt_sq (by positivity))
  have hsum := Tensor0SBundle.sqrt_normSq0S_add_le g x 4 A (metricRm04At g x)
  have hadd : A + metricRm04At g x = metricRm04At h x := sub_add_cancel _ _
  rw [hadd] at hsum
  have hfixed : Real.sqrt (normSq0S g x 4 (metricRm04At h x)) ≤
      Real.sqrt K + n ^ 2 * B := by
    have ht := hsum.trans (add_le_add hdiffroot (Real.sqrt_le_sqrt hK))
    linarith
  have hquad (v : TangentSpace I x) :
      |h.inner x v v - g.inner x v v| ≤ (n * delta) * g.inner x v v := by
    have ht := metricQuadFormDiff_le_metricDerivNorm h g g x v
    have hc := mul_le_mul_of_nonneg_left (hjet 0 (by norm_num)) hn
    exact ht.trans (mul_le_mul_of_nonneg_right hc
      (DifferentialGeometry.metric_inner_self_nonneg g x v))
  have heq := metricUniformEquivalentOn_of_quadFormDiff (I := I)
    (K := {x}) (g := g) (h := h) (mul_nonneg hn hd0)
    (by change n * delta < 1; linarith)
    (fun y hy v => by rcases Set.mem_singleton_iff.mp hy with rfl; exact hquad v)
  have hnrm := sqrt_normSq0S_le_of_metric_equiv g h x 4 heq.1
    (heq.2 x (Set.mem_singleton x)) (metricRm04At h x)
  have hsquare : Real.sqrt (((1 - n * delta)⁻¹) ^ 4) =
      ((1 - n * delta)⁻¹) ^ 2 := by
    have hp : ((1 - n * delta)⁻¹) ^ 4 = (((1 - n * delta)⁻¹) ^ 2) ^ 2 := by ring
    rw [hp, Real.sqrt_sq (sq_nonneg _)]
  calc
    _ ≤ ((1 - n * delta)⁻¹) ^ 2 *
        Real.sqrt (normSq0S g x 4 (metricRm04At h x)) := by
      simpa only [hsquare] using hnrm
    _ ≤ ((1 - n * delta)⁻¹) ^ 2 * (Real.sqrt K + n ^ 2 * B) :=
      mul_le_mul_of_nonneg_left hfixed (sq_nonneg _)
    _ = _ := by dsimp only [B, n]; ring

omit [I.Boundaryless] in
private theorem pointedNC_rmNormSq_pullback
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
    (g : SmoothRiemannianMetric I N) (e : M ≃ₘ⟮I, I⟯ N) (x : M) :
    normSq0S (Diffeomorph.pullbackMetric g e) x 4
        (metricRm04At (Diffeomorph.pullbackMetric g e) x) =
      normSq0S g (e x) 4 (metricRm04At g (e x)) := by
  classical
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis (Diffeomorph.pullbackMetric g e) x
  apply normSq0S_pullback_eval_of_orthonormal g e x 4 basis hON
  intro slots
  have hs : slots = vec4 (slots 0) (slots 1) (slots 2) (slots 3) := by
    funext i
    fin_cases i <;> rfl
  have ht : (fun i : Fin 4 => mfderiv I I (e : M → N) x (slots i)) =
      vec4 (mfderiv I I (e : M → N) x (slots 0))
        (mfderiv I I (e : M → N) x (slots 1))
        (mfderiv I I (e : M → N) x (slots 2))
        (mfderiv I I (e : M → N) x (slots 3)) := by
    funext i
    fin_cases i <;> rfl
  rw [ht, hs]
  exact metricRm04Standard_pullback g e x (slots 0) (slots 1) (slots 2) (slots 3)

end CurvatureEstimate
section Pointed

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {L : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}
  (Φ : PointedRiemannianConvergenceMaps (I := I) X L subseq)

local instance pointedNCLimitTopology : TopologicalSpace L.M := L.topology
local instance pointedNCLimitCharted : ChartedSpace H L.M := L.charted
local instance pointedNCLimitSmooth : IsManifold I ∞ L.M := L.smooth
local instance pointedNCLimitOne : IsManifold I 1 L.M :=
  IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
local instance pointedNCLimitT2 : T2Space L.M := L.t2
local instance pointedNCLimitSigma : SigmaCompactSpace L.M := L.sigmaCompact

local instance pointedNCApproxTopology (k : ℕ) :
    TopologicalSpace (X.obj k).M := (X.obj k).topology
local instance pointedNCApproxCharted (k : ℕ) :
    ChartedSpace H (X.obj k).M := (X.obj k).charted
local instance pointedNCApproxSmooth (k : ℕ) :
    IsManifold I ∞ (X.obj k).M := (X.obj k).smooth
local instance pointedNCApproxOne (k : ℕ) :
    IsManifold I 1 (X.obj k).M :=
  IsManifold.of_le (I := I) (M := (X.obj k).M) (n := ∞) (by decide)
local instance pointedNCApproxT2 (k : ℕ) :
    T2Space (X.obj k).M := (X.obj k).t2
local instance pointedNCApproxSigma (k : ℕ) :
    SigmaCompactSpace (X.obj k).M := (X.obj k).sigmaCompact

local instance pointedNCSourceTopology (k : ℕ) :
    TopologicalSpace (MetricSourceDomain (I := I) Φ k) := metricSourceDomainTopology Φ k
local instance pointedNCSourceCharted (k : ℕ) :
    ChartedSpace H (MetricSourceDomain (I := I) Φ k) := metricSourceDomainChartedSpace Φ k
local instance pointedNCSourceSmooth (k : ℕ) :
    IsManifold I ∞ (MetricSourceDomain (I := I) Φ k) := metric_source_domain_smooth Φ k
local instance pointedNCSourceOne (k : ℕ) :
    IsManifold I 1 (MetricSourceDomain (I := I) Φ k) :=
  IsManifold.of_le (I := I) (M := MetricSourceDomain (I := I) Φ k) (n := ∞) (by decide)
local instance pointedNCSourceT2 (k : ℕ) :
    T2Space (MetricSourceDomain (I := I) Φ k) := metric_source_domain_t2 Φ k
local instance pointedNCSourceSigma (k : ℕ) :
    SigmaCompactSpace (MetricSourceDomain (I := I) Φ k) :=
  metric_source_domain_sigma_compact Φ k (PointedRiemannianConvergenceMaps.isSigmaCompact_source Φ k)

local instance pointedNCTargetTopology (k : ℕ) :
    TopologicalSpace (MetricTargetDomain (I := I) Φ k) := metricTargetDomainTopology Φ k
local instance pointedNCTargetCharted (k : ℕ) :
    ChartedSpace H (MetricTargetDomain (I := I) Φ k) := metricTargetDomainChartedSpace Φ k
local instance pointedNCTargetSmooth (k : ℕ) :
    IsManifold I ∞ (MetricTargetDomain (I := I) Φ k) := metric_target_domain_smooth Φ k
local instance pointedNCTargetOne (k : ℕ) :
    IsManifold I 1 (MetricTargetDomain (I := I) Φ k) :=
  IsManifold.of_le (I := I) (M := MetricTargetDomain (I := I) Φ k) (n := ∞) (by decide)
local instance pointedNCTargetT2 (k : ℕ) :
    T2Space (MetricTargetDomain (I := I) Φ k) := metric_target_domain_t2 Φ k
local instance pointedNCTargetSigma (k : ℕ) :
    SigmaCompactSpace (MetricTargetDomain (I := I) Φ k) :=
  metric_target_domain_sigma_compact Φ k (PointedRiemannianConvergenceMaps.isSigmaCompact_target Φ k)

variable {Φ}

private local instance pointedNCLimitTangentT2 : T2Space (TangentBundle I L.M) :=
  L.t2TangentBundle
private local instance pointedNCLimitMeasurable : MeasurableSpace L.M := borel L.M
private local instance pointedNCLimitBorel : BorelSpace L.M := ⟨rfl⟩
private local instance pointedNCApproxMeasurable (k : ℕ) : MeasurableSpace (X.obj k).M :=
  borel (X.obj k).M
private local instance pointedNCApproxBorel (k : ℕ) : BorelSpace (X.obj k).M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem exists_pointed_compact_rmNorm_lt
    (hconv : ∀ K : Set L.M, IsCompact K →
      metricSourceConvergesOn Φ (CanonicalMetricCompactness.canonicalSourceData Φ) K 2)
    (A : Set L.M) (hA : IsCompact A) {K B : ℝ}
    (hK : ∀ x ∈ A, normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ K)
    (hB : Real.sqrt K < B) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → A ⊆ Φ.source k ∧
      ∀ x ∈ A, Real.sqrt (normSq0S (X.obj (subseq k)).metric (Φ.map k x) 4
        (metricRm04At (X.obj (subseq k)).metric (Φ.map k x))) < B := by
  let n : ℝ := Module.finrank ℝ E
  let d : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hnd : Tendsto (fun j => n * d j) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => n) atTop (𝓝 n)).mul hd
  have hfac : Tendsto (fun j => ((1 - n * d j)⁻¹) ^ 2) atTop (𝓝 (1 : ℝ)) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hnd
    simpa only [sub_zero, inv_one, one_pow] using
      (ht.inv₀ (by norm_num : (1 - 0 : ℝ) ≠ 0)).pow 2
  have hadd : Tendsto (fun j => Real.sqrt K + n ^ 2 * d j * (Real.sqrt K + 864))
      atTop (𝓝 (Real.sqrt K)) := by
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => n ^ 2) atTop (𝓝 (n ^ 2))).mul hd
    have hu := ht.mul (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.sqrt K + 864) atTop (𝓝 (Real.sqrt K + 864)))
    simpa only [mul_zero, zero_mul, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.sqrt K) atTop (𝓝 (Real.sqrt K))).add hu
  have he : Tendsto (fun j => ((1 - n * d j)⁻¹) ^ 2 *
      (Real.sqrt K + n ^ 2 * d j * (Real.sqrt K + 864))) atTop (𝓝 (Real.sqrt K)) := by
    simpa only [one_mul] using hfac.mul hadd
  have hevent : ∀ᶠ j in atTop, ((1 - n * d j)⁻¹) ^ 2 *
      (Real.sqrt K + n ^ 2 * d j * (Real.sqrt K + 864)) < B :=
    he.eventually (gt_mem_nhds hB)
  have hsmall : ∀ᶠ j in atTop, n * d j < 1 / 2 :=
    hnd.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨j, hj, hjsmall⟩ := (hevent.and hsmall).exists
  have hd0 : 0 < d j := by dsimp only [d]; positivity
  have hd1 : d j ≤ 1 := by
    dsimp only [d]
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    simpa only [div_one] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ (j : ℝ) + 1))
  obtain ⟨k0, hk0⟩ := hconv A hA (d j) hd0
  refine ⟨k0, fun k hk => ⟨(hk0 k hk).1, fun x hx => ?_⟩⟩
  obtain ⟨hsource, hsup⟩ := hk0 k hk
  let xu : MetricSourceDomain Φ k := ⟨x, hsource hx⟩
  let gU := L.metric.restrictOpen (metricSourceOpenSubset Φ k)
  let hU := Diffeomorph.pullbackMetric
    ((X.obj (subseq k)).metric.restrictOpen (metricTargetOpenSubset Φ k))
    (metricSourceTargetDiffeomorph Φ k)
  have hcompact := metric_source_compact_set_is_compact Φ k hA hsource
  change metricDerivNormSupOn (metricSourceCompactSet Φ k A) 2 hU gU gU < d j at hsup
  have hjet (a : ℕ) (ha : a ≤ 2) : metricDerivNorm a hU gU gU xu ≤ d j :=
    (derivNorm_le_sup hcompact ha hU gU gU (x := xu) hx).trans hsup.le
  have hlim : normSq0S gU xu 4 (metricRm04At gU xu) =
      normSq0S L.metric x 4 (metricRm04At L.metric x) :=
    rmNormSq_restrictOpen L.metric (metricSourceOpenSubset Φ k) xu
  have hpull : normSq0S hU xu 4 (metricRm04At hU xu) =
      normSq0S (X.obj (subseq k)).metric (Φ.map k x) 4
        (metricRm04At (X.obj (subseq k)).metric (Φ.map k x)) := by
    rw [pointedNC_rmNormSq_pullback, rmNormSq_restrictOpen]
    rfl
  have hnorm := metricRmNorm_le_of_relative_two_jets gU hU xu hd0.le hd1 hjsmall.le
    (hlim.trans_le (hK x hx)) hjet
  rw [hpull] at hnorm
  exact hnorm.trans_lt hj
private theorem pointedNC_quadratic_comparison
    {a b epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hepsilon : 0 < epsilon)
    (herror : |b - a| ≤ epsilon / (1 + epsilon) * a) :
    b ≤ (1 + epsilon) ^ 2 * a ∧ a ≤ (1 + epsilon) ^ 2 * b := by
  have hL : 0 < 1 + epsilon := by linarith
  have hcoef : epsilon / (1 + epsilon) ≤ epsilon :=
    div_le_self hepsilon.le (by linarith)
  have hsq : 1 + epsilon ≤ (1 + epsilon) ^ 2 := by nlinarith
  have hupper : b ≤ (1 + epsilon) * a := by
    have hmul := mul_le_mul_of_nonneg_right hcoef ha
    have habs := (abs_le.mp herror).2
    nlinarith
  have hdivision : a / (1 + epsilon) = a - epsilon / (1 + epsilon) * a := by
    field_simp [ne_of_gt hL]
    ring
  have hlower : a ≤ (1 + epsilon) * b := by
    have hdiv : a / (1 + epsilon) ≤ b := by
      rw [hdivision]
      have habs := (abs_le.mp herror).1
      linarith
    simpa only [mul_comm] using (div_le_iff₀ hL).1 hdiv
  exact ⟨hupper.trans (mul_le_mul_of_nonneg_right hsq ha),
    hlower.trans (mul_le_mul_of_nonneg_right hsq hb)⟩

theorem exists_pointed_inverse_capture_at
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (z : L.M)
    {s epsilon : ℝ} (hs : 0 ≤ s) (hepsilon : 0 < epsilon) :
    IsCompact (riemannianClosedBallOf L.metric z ((1 + epsilon) * s)) ∧
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ y ∈ riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) s,
        y ∈ (Φ.partialDiffeomorph k).target ∧
          (Φ.partialDiffeomorph k).symm y ∈
            riemannianClosedBallOf L.metric z ((1 + epsilon) * s) := by
  have hc : RiemannianMetricComplete (I := I) L.metric :=
    ⟨MetricComplete.complete (I := I) L hcomplete⟩
  have hcpt (r : ℝ) : IsCompact (riemannianClosedBallOf L.metric z r) :=
    RiemannianMetricComplete.closedEBall_isCompact hc z r
  refine ⟨hcpt _, ?_⟩
  let K := riemannianClosedBallOf L.metric z ((1 + epsilon) * (3 * s + 2))
  obtain ⟨k0, hk0⟩ := exists_pointed_full_ambient_quadratic_control
    C hreference K (hcpt _) (epsilon / (1 + epsilon)) (by positivity)
  refine ⟨k0, fun k hk => ?_⟩
  let F := Φ.partialDiffeomorph k
  have hquad (x : L.M) (hx : x ∈ K) (v : TangentSpace I x) :
      (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) ≤
        (1 + epsilon) ^ 2 * L.metric.inner x v v ∧
      L.metric.inner x v v ≤ (1 + epsilon) ^ 2 *
        (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) :=
    pointedNC_quadratic_comparison
      (DifferentialGeometry.metric_inner_self_nonneg L.metric x v)
      (DifferentialGeometry.metric_inner_self_nonneg
        (X.obj (subseq k)).metric (F x) _) hepsilon ((hk0 k hk).2 x hx v)
  exact (inverse_distance_control_on_buffered_metric_ball
    L.metric (X.obj (subseq k)).metric F z (by linarith : 1 ≤ 1 + epsilon) hs
    (hcpt _) (hk0 k hk).1 (fun x hx v => (hquad x hx v).1)
    (fun x hx v => (hquad x hx v).2)).1

theorem exists_pointed_buffered_ball_volume_le_at
    (C : MetricConvergenceData Φ)
    (hreference : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (hcomplete : MetricComplete (I := I) L) (z : L.M)
    {s r epsilon delta : ℝ} (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hbuffer : (1 + epsilon) * s < r) (hdelta : 0 < delta) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      riemannianVolumeMeasure (I := I) (M := (X.obj (subseq k)).M) (X.obj (subseq k)).metric
          (riemannianBallOf (X.obj (subseq k)).metric (Φ.map k z) s) ≤
        ENNReal.ofReal (Real.sqrt ((1 + delta) ^ Module.finrank ℝ E)) *
          riemannianVolumeMeasure (I := I) (M := L.M) L.metric (riemannianBallOf L.metric z r) := by
  obtain ⟨hKcompact, kcap, hkcap⟩ := exists_pointed_inverse_capture_at
    C hreference hcomplete z hs.le hepsilon
  let K := riemannianClosedBallOf L.metric z ((1 + epsilon) * s)
  obtain ⟨kmetric, hkmetric⟩ :=
    exists_pointed_full_ambient_quadratic_control C hreference K hKcompact delta hdelta
  refine ⟨max kcap kmetric, fun k hk => ?_⟩
  let F := Φ.partialDiffeomorph k
  let B := riemannianBallOf (X.obj (subseq k)).metric (Φ.map k z) s
  let A : Set L.M := F.source ∩ (F : L.M → (X.obj (subseq k)).M) ⁻¹' B
  have hcap := hkcap k ((Nat.le_max_left _ _).trans hk)
  have hmetric := (hkmetric k ((Nat.le_max_right _ _).trans hk)).2
  have hBopen : IsOpen B :=
    isOpen_lt (DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist
      (X.obj (subseq k)).metric (Φ.map k z))
      continuous_const
  have hA : MeasurableSet A :=
    (F.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage F.open_source hBopen).measurableSet
  have hAK : A ⊆ K := by
    intro x hx
    have hxclosed : F x ∈
        riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) s := by
      change riemannianEDistOf (X.obj (subseq k)).metric (Φ.map k z) (F x) ≤
        ENNReal.ofReal s
      exact hx.2.le
    have hc := (hcap (F x) hxclosed).2
    have hleft : F.symm (F x) = x := F.left_inv' hx.1
    change F.symm (F x) ∈ K at hc
    rwa [hleft] at hc
  have hr : 0 < r := (mul_pos (by linarith : 0 < 1 + epsilon) hs).trans hbuffer
  have hAr : A ⊆ riemannianBallOf L.metric z r := fun x hx =>
    (hAK hx).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hbuffer)
  have himage : (F : L.M → (X.obj (subseq k)).M) '' A = B := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have hyclosed : y ∈
          riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) s := by
        change riemannianEDistOf (X.obj (subseq k)).metric (Φ.map k z) y ≤
          ENNReal.ofReal s
        exact hy.le
      have hyt : y ∈ F.target := (hcap y hyclosed).1
      have hright : F (F.symm y) = y := F.right_inv' hyt
      refine ⟨F.symm y, ⟨F.toPartialEquiv.map_target hyt, ?_⟩, hright⟩
      change F (F.symm y) ∈ B
      simpa only [hright] using hy
  have hquad : ∀ x ∈ A, ∀ v : TangentSpace I x,
      (X.obj (subseq k)).metric.inner (F x)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
          (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) ≤
        (1 + delta) * L.metric.inner x v v := by
    intro x hx v
    have herr := (abs_le.mp (hmetric x (hAK hx) v)).2
    change (X.obj (subseq k)).metric.inner (F x)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v)
        (mfderiv I I (F : L.M → (X.obj (subseq k)).M) x v) -
      L.metric.inner x v v ≤ delta * L.metric.inner x v v at herr
    linarith
  have hv := pointedNC_image_volume_le L.metric (X.obj (subseq k)).metric F
    hA inter_subset_left (by linarith : 0 < 1 + delta) hquad
  rw [himage] at hv
  exact hv.trans (mul_le_mul_right (measure_mono hAr) _)

private theorem pointedNC_sqrt_inverse_fourth {r : ℝ} :
    Real.sqrt (1 / r ^ 4) = 1 / r ^ 2 := by
  have hp : r ^ 4 = (r ^ 2) ^ 2 := by ring
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, hp, Real.sqrt_sq (sq_nonneg r)]

theorem exists_pointed_ball_curvature_control
    (C : MetricConvergenceData Φ)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (hcomplete : MetricComplete (I := I) L) (z : L.M)
    {s r epsilon : ℝ} (hs : 0 < s) (hepsilon : 0 < epsilon)
    (hbuffer : (1 + epsilon) * s < r)
    (hcurvature : ∀ x ∈ riemannianBallOf L.metric z r,
      r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ 1) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∀ y ∈ riemannianBallOf (X.obj (subseq k)).metric (Φ.map k z) s,
        s ^ 4 * normSq0S (X.obj (subseq k)).metric y 4
          (metricRm04At (X.obj (subseq k)).metric y) ≤ 1 := by
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  have hconv (A : Set L.M) (hA : IsCompact A) :
      metricSourceConvergesOn Φ (CanonicalMetricCompactness.canonicalSourceData Φ) A 2 := by
    have ht := C.converges A hA 2
    rw [funext hcanonical] at ht
    exact ht
  have hsr : s < r := by nlinarith [mul_pos hepsilon hs]
  have hr : 0 < r := hs.trans hsr
  obtain ⟨hKcompact, kcap, hkcap⟩ := exists_pointed_inverse_capture_at
    C hreference hcomplete z hs.le hepsilon
  let K := riemannianClosedBallOf L.metric z ((1 + epsilon) * s)
  have hKr : K ⊆ riemannianBallOf L.metric z r := fun x hx =>
    hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).2 hbuffer)
  have hK (x : L.M) (hx : x ∈ K) :
      normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ 1 / r ^ 4 := by
    apply (le_div_iff₀ (pow_pos hr 4)).2
    simpa only [mul_comm] using hcurvature x (hKr hx)
  have hB : Real.sqrt (1 / r ^ 4) < 1 / s ^ 2 := by
    rw [pointedNC_sqrt_inverse_fourth]
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos hs) ((sq_lt_sq₀ hs.le hr.le).2 hsr)
  obtain ⟨kcurv, hkcurv⟩ := exists_pointed_compact_rmNorm_lt hconv K hKcompact hK hB
  refine ⟨max kcap kcurv, fun k hk y hy => ?_⟩
  let F := Φ.partialDiffeomorph k
  have hyclosed : y ∈
      riemannianClosedBallOf (X.obj (subseq k)).metric (Φ.map k z) s := by
    change riemannianEDistOf (X.obj (subseq k)).metric (Φ.map k z) y ≤
      ENNReal.ofReal s
    exact hy.le
  obtain ⟨hyt, hyK⟩ := hkcap k ((Nat.le_max_left _ _).trans hk) y hyclosed
  have hnorm := (hkcurv k ((Nat.le_max_right _ _).trans hk)).2 (F.symm y) hyK
  change Real.sqrt (normSq0S (X.obj (subseq k)).metric (F (F.symm y)) 4
    (metricRm04At (X.obj (subseq k)).metric (F (F.symm y)))) < 1 / s ^ 2 at hnorm
  have hright : F (F.symm y) = y := F.right_inv' hyt
  rw [hright] at hnorm
  let N := normSq0S (X.obj (subseq k)).metric y 4
    (metricRm04At (X.obj (subseq k)).metric y)
  have hN : 0 ≤ N := normSq0S_nonneg _ _ _ _
  have hprod : s ^ 2 * Real.sqrt N < 1 := by
    have ht := mul_lt_mul_of_pos_left hnorm (sq_pos_of_pos hs)
    simpa only [mul_one_div_cancel (ne_of_gt (sq_pos_of_pos hs))] using ht
  have hsq : (s ^ 2 * Real.sqrt N) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ (by positivity) zero_le_one).2 hprod.le
  rw [mul_pow, Real.sq_sqrt hN, one_pow] at hsq
  convert hsq using 1
  ring

theorem tensor_noncollapsed_of_pointed_canonical_convergence
    (C : MetricConvergenceData Φ)
    (hcanonical : ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData Φ k)
    (hcomplete : MetricComplete (I := I) L) (kappa : ℝ)
    (hsource : ∀ (i : ℕ) (p : (X.obj i).M) (r : ℝ), 0 < r →
      (∀ y ∈ riemannianBallOf (X.obj i).metric p r,
        r ^ 4 * normSq0S (X.obj i).metric y 4 (metricRm04At (X.obj i).metric y) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := (X.obj i).M) (X.obj i).metric
          (riemannianBallOf (X.obj i).metric p r)) :
    ∀ (z : L.M) (r : ℝ), 0 < r →
      (∀ x ∈ riemannianBallOf L.metric z r,
        r ^ 4 * normSq0S L.metric x 4 (metricRm04At L.metric x) ≤ 1) →
      ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric (riemannianBallOf L.metric z r) := by
  intro z r hr hcurvature
  have hreference (k : ℕ) : (C.domain k).referenceMetric = (C.domain k).limitMetric := by
    rw [hcanonical k]
    rfl
  let n := Module.finrank ℝ E
  let epsilon : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let s : ℕ → ℝ := fun j => r / (1 + epsilon j) ^ 2
  have hepsilon : Tendsto epsilon atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone : Tendsto (fun j => 1 + epsilon j) atTop (𝓝 (1 : ℝ)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hepsilon
  have hs : Tendsto s atTop (𝓝 r) := by
    simpa only [s, Pi.div_def, one_pow, div_one] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).div
        (hone.pow 2) (by norm_num : (1 : ℝ) ^ 2 ≠ 0)
  have hreal : Tendsto (fun j => ENNReal.ofReal (s j)) atTop (𝓝 (ENNReal.ofReal r)) := by
    simpa only [Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hs
  have hleft := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal kappa)
    (ENNReal.Tendsto.pow (n := n) hreal)
    (Or.inr ENNReal.ofReal_ne_top)
  have hsqrt : Tendsto (fun j => Real.sqrt ((1 + epsilon j) ^ n)) atTop
      (𝓝 (1 : ℝ)) := by
    simpa only [one_pow, Real.sqrt_one, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (hone.pow n)
  have hcoef : Tendsto (fun j => ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hsqrt
  have hright : Tendsto (fun j =>
      ENNReal.ofReal (Real.sqrt ((1 + epsilon j) ^ n)) *
        riemannianVolumeMeasure (I := I) (M := L.M) L.metric (riemannianBallOf L.metric z r))
      atTop (𝓝 (riemannianVolumeMeasure (I := I) (M := L.M) L.metric
        (riemannianBallOf L.metric z r))) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hcoef (Or.inl one_ne_zero)
  apply le_of_tendsto_of_tendsto' hleft hright
  intro j
  have he : 0 < epsilon j := by dsimp only [epsilon]; positivity
  have h1 : 0 < 1 + epsilon j := by linarith
  have hsj : 0 < s j := div_pos hr (sq_pos_of_pos h1)
  have hbuffer : (1 + epsilon j) * s j < r := by
    calc
      (1 + epsilon j) * s j = r / (1 + epsilon j) := by
        dsimp only [s]
        field_simp [ne_of_gt h1]
      _ < r := (div_lt_self hr (by linarith))
  obtain ⟨kv, hkv⟩ := exists_pointed_buffered_ball_volume_le_at
    C hreference hcomplete z hsj he hbuffer he
  obtain ⟨kc, hkc⟩ := exists_pointed_ball_curvature_control
    C hcanonical hcomplete z hsj he hbuffer hcurvature
  let k := max kv kc
  exact (hsource (subseq k) (Φ.map k z) (s j) hsj
    (hkc k (Nat.le_max_right _ _))).trans (hkv k (Nat.le_max_left _ _))

end Pointed

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
