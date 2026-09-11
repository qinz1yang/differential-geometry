import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompactDomainTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.LocalVolumeOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.OpenRestrictionVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CrossVolumeNaturality
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Scaling


set_option autoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {P : Type v} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]

private local instance volumeTransportMeasurable : MeasurableSpace M := borel M
private local instance volumeTransportBorel : BorelSpace M := ⟨rfl⟩
private local instance volumeTransportOpensMeasurable (W : Opens M) :
    MeasurableSpace W := borel W
private local instance volumeTransportOpensBorel (W : Opens M) : BorelSpace W := ⟨rfl⟩

omit [T2Space M] [SigmaCompactSpace M] in
theorem MetricComparisonOn.inner_image_bounds
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [CompleteSpace E'] {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [T2Space N] [SigmaCompactSpace N]
    {h : ℝ → SmoothRiemannianMetric J N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {f : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g f U times order eps)
    {s : ℝ} (hs : s ∈ times) {y : N} (hy : y ∈ U) (v : TangentSpace J y) :
    (1 - eps) * (h s).inner y v v ≤
        (g s).inner (f y) (mfderiv J I3 f y v) (mfderiv J I3 f y v) ∧
      (g s).inner (f y) (mfderiv J I3 f y v) (mfderiv J I3 f y v) ≤
        (1 + eps) * (h s).inner y v v := by
  have hp := C.pullback_eq s y hy (fun _ => v)
  have he := C.equivalence s hs y hy v
  rw [hp] at he
  exact he

omit [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P] in
private theorem exists_opensDiffeo_of_subset_source
    (F : PartialDiffeomorph I3 I3 P M ∞) {U : Set P} (hU : IsOpen U)
    (hsrc : U ⊆ F.source) :
    ∃ (V : Opens P) (W : Opens M) (Phi : Diffeomorph I3 I3 V W ∞),
      (V : Set P) = U ∧ (W : Set M) = (F : P → M) '' U ∧
      (∀ p : V, ((Phi p : W) : M) = (F : P → M) (p : P)) ∧
      (∀ (p : V) (v : TangentSpace I3 p),
        mfderiv I3 I3 (Phi : V → W) p v = mfderiv I3 I3 (F : P → M) (p : P) v) :=
  ⟨⟨U, hU⟩, ⟨(F : P → M) '' U, image_opens_isOpen F (U := ⟨U, hU⟩) hsrc⟩,
    PartialDiffeomorph.toOpensDiffeo F (U := ⟨U, hU⟩) hsrc, rfl, rfl, fun _ => rfl,
    fun p v => PartialDiffeomorph.mfderiv_toOpensDiffeo F hsrc p v⟩


theorem riemannianVolumeMeasure_image_sandwich
    (k : SmoothRiemannianMetric I3 P) (g : SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I3 I3 P M ∞) {U : Set P} (hU : IsOpen U)
    (hsrc : U ⊆ F.source) {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlower : ∀ y ∈ U, ∀ v : TangentSpace I3 y,
      k.inner y v v ≤ a * g.inner ((F : P → M) y)
        (mfderiv I3 I3 (F : P → M) y v) (mfderiv I3 I3 (F : P → M) y v))
    (hupper : ∀ y ∈ U, ∀ v : TangentSpace I3 y,
      g.inner ((F : P → M) y)
          (mfderiv I3 I3 (F : P → M) y v) (mfderiv I3 I3 (F : P → M) y v) ≤
        b * k.inner y v v) :
    riemannianVolumeMeasure I3 P k K ≤
        ENNReal.ofReal (Real.sqrt (a ^ 3)) *
          riemannianVolumeMeasure I3 M g ((F : P → M) '' K) ∧
      riemannianVolumeMeasure I3 M g ((F : P → M) '' K) ≤
        ENNReal.ofReal (Real.sqrt (b ^ 3)) * riemannianVolumeMeasure I3 P k K := by
  classical
  have : SecondCountableTopology P :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace M
  have : LocallyCompactSpace P := Manifold.locallyCompact_of_finiteDimensional I3
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I3
  obtain ⟨V, W, Phi, hVU, hWU, hPhi, hdPhi⟩ :=
    exists_opensDiffeo_of_subset_source F hU hsrc
  have : LocallyCompactSpace V := V.2.locallyCompactSpace
  have : LocallyCompactSpace W := W.2.locallyCompactSpace
  have : SigmaCompactSpace V := inferInstance
  have : SigmaCompactSpace W := inferInstance
  have hmemV : ∀ p : V, (p : P) ∈ U := by
    intro p
    rw [← hVU]
    exact p.2
  have hGinner : ∀ (p : V) (v : TangentSpace I3 p),
      (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi).inner p v v =
        g.inner ((F : P → M) (p : P))
          (mfderiv I3 I3 (F : P → M) (p : P) v)
          (mfderiv I3 I3 (F : P → M) (p : P) v) := by
    intro p v
    rw [Diffeomorph.pullbackMetricCross_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hdPhi p v, hPhi p]
  have hvalB : (Subtype.val : V → P) '' ((Subtype.val : V → P) ⁻¹' K) = K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨p, hp, rfl⟩
      exact hp
    · intro y hy
      have hyV : y ∈ (V : Set P) := by
        rw [hVU]
        exact hKU hy
      exact ⟨⟨y, hyV⟩, hy, rfl⟩
  have hvalA : (Subtype.val : W → M) ''
      ((Subtype.val : W → M) ⁻¹' ((F : P → M) '' K)) = (F : P → M) '' K := by
    apply Set.Subset.antisymm
    · rintro _ ⟨q, hq, rfl⟩
      exact hq
    · rintro _ ⟨y, hyK, rfl⟩
      have hyW : (F : P → M) y ∈ (W : Set M) := by
        rw [hWU]
        exact ⟨y, hKU hyK, rfl⟩
      exact ⟨⟨(F : P → M) y, hyW⟩, ⟨y, hyK, rfl⟩, rfl⟩
  have hpre : (Phi : V → W) ⁻¹' ((Subtype.val : W → M) ⁻¹' ((F : P → M) '' K))
      = (Subtype.val : V → P) ⁻¹' K := by
    ext p
    constructor
    · intro hp
      have hq : ((Phi p : W) : M) ∈ (F : P → M) '' K := hp
      rw [hPhi p] at hq
      obtain ⟨y, hyK, hy⟩ := hq
      have hle : F.symm ((F : P → M) y) = y := F.left_inv' (hsrc (hKU hyK))
      have hlp : F.symm ((F : P → M) (p : P)) = (p : P) := F.left_inv' (hsrc (hmemV p))
      have hpy : (p : P) = y := by rw [← hlp, ← hy, hle]
      change (p : P) ∈ K
      rw [hpy]
      exact hyK
    · intro hp
      have hpK : (p : P) ∈ K := hp
      change ((Phi p : W) : M) ∈ (F : P → M) '' K
      rw [hPhi p]
      exact Set.mem_image_of_mem _ hpK
  have hBmeas : MeasurableSet ((Subtype.val : V → P) ⁻¹' K) :=
    (hK.isClosed.preimage continuous_subtype_val).measurableSet
  have h1 : riemannianVolumeMeasure I3 V (k.restrictOpen V)
      ((Subtype.val : V → P) ⁻¹' K) = riemannianVolumeMeasure I3 P k K := by
    rw [riemannianVolumeMeasure_restrictOpen_apply, hvalB]
  have h2 : riemannianVolumeMeasure I3 V
        (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi)
        ((Subtype.val : V → P) ⁻¹' K)
      = riemannianVolumeMeasure I3 M g ((F : P → M) '' K) := by
    have hemb : MeasurableEmbedding (Phi : V → W) :=
      Phi.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    have hmp := (volumeMeasurePreserving_pullbackMetricCross
      (g.restrictOpen W) Phi).measure_preimage_emb hemb
      ((Subtype.val : W → M) ⁻¹' ((F : P → M) '' K))
    rw [hpre] at hmp
    rw [hmp, riemannianVolumeMeasure_restrictOpen_apply, hvalA]
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  constructor
  · have hcomp : ∀ p ∈ (Subtype.val : V → P) ⁻¹' K, ∀ v : TangentSpace I3 p,
        (k.restrictOpen V).inner p v v ≤
          a * (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi).inner p v v := by
      intro p _ v
      rw [SmoothRiemannianMetric.restrictOpen_inner, hGinner p v]
      exact hlower (p : P) (hmemV p) v
    have hres := riemannianVolumeMeasure_le_on
      (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi)
      (k.restrictOpen V) hBmeas ha hcomp
    rw [hdim, h1, h2] at hres
    exact hres
  · have hcomp : ∀ p ∈ (Subtype.val : V → P) ⁻¹' K, ∀ v : TangentSpace I3 p,
        (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi).inner p v v ≤
          b * (k.restrictOpen V).inner p v v := by
      intro p _ v
      rw [SmoothRiemannianMetric.restrictOpen_inner, hGinner p v]
      exact hupper (p : P) (hmemV p) v
    have hres := riemannianVolumeMeasure_le_on (k.restrictOpen V)
      (Diffeomorph.pullbackMetricCross (g.restrictOpen W) Phi) hBmeas hb hcomp
    rw [hdim, h1, h2] at hres
    exact hres

private theorem comparison_volume_bounds
    {h : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M}
    (F : PartialDiffeomorph I3 I3 P M ∞)
    {U : Set P} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g (F : P → M) U times order eps)
    {s : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    {V : Set P} (hV : IsOpen V) (hVU : V ⊆ U) (hVsrc : V ⊆ F.source)
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) :
    riemannianVolumeMeasure I3 P (h s) K ≤
        ENNReal.ofReal (Real.sqrt (((1 - eps)⁻¹) ^ 3)) *
          riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K) ∧
      riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K) ≤
        ENNReal.ofReal (Real.sqrt ((1 + eps) ^ 3)) *
          riemannianVolumeMeasure I3 P (h s) K := by
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  refine riemannianVolumeMeasure_image_sandwich (h s) (g s) F hV hVsrc hK hKV
    (inv_pos.mpr h1e) (by linarith) ?_ ?_
  · intro y hy v
    rw [inv_mul_eq_div, le_div_iff₀ h1e]
    linarith [(C.inner_image_bounds hs (hVU hy) v).1]
  · intro y hy v
    exact (C.inner_image_bounds hs (hVU hy) v).2


theorem MetricComparisonOn.volume_image_ge
    {h : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M}
    (F : PartialDiffeomorph I3 I3 P M ∞)
    {U : Set P} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g (F : P → M) U times order eps)
    {s : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    {V : Set P} (hV : IsOpen V) (hVU : V ⊆ U) (hVsrc : V ⊆ F.source)
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) :
    ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
        riemannianVolumeMeasure I3 P (h s) K ≤
      riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K) := by
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hb := (comparison_volume_bounds F C hs heps heps1 hV hVU hVsrc hK hKV).1
  have hinv : ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
      ENNReal.ofReal (Real.sqrt (((1 - eps)⁻¹) ^ 3)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
      ← Real.sqrt_mul (pow_nonneg h1e.le 3), ← mul_pow,
      mul_inv_cancel₀ (ne_of_gt h1e), one_pow, Real.sqrt_one, ENNReal.ofReal_one]
  calc ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
        riemannianVolumeMeasure I3 P (h s) K
      ≤ ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
          (ENNReal.ofReal (Real.sqrt (((1 - eps)⁻¹) ^ 3)) *
            riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K)) :=
        mul_le_mul' le_rfl hb
    _ = riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K) := by
        rw [← mul_assoc, hinv, one_mul]


theorem MetricComparisonOn.volume_image_le
    {h : ℝ → SmoothRiemannianMetric I3 P} {g : ℝ → SmoothRiemannianMetric I3 M}
    (F : PartialDiffeomorph I3 I3 P M ∞)
    {U : Set P} {times : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g (F : P → M) U times order eps)
    {s : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    {V : Set P} (hV : IsOpen V) (hVU : V ⊆ U) (hVsrc : V ⊆ F.source)
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) :
    riemannianVolumeMeasure I3 M (g s) ((F : P → M) '' K) ≤
      ENNReal.ofReal (Real.sqrt ((1 + eps) ^ 3)) *
        riemannianVolumeMeasure I3 P (h s) K :=
  (comparison_volume_bounds F C hs heps heps1 hV hVU hVsrc hK hKV).2


theorem volume_reserve_constant_pos {R Cm eps : ℝ} (hR : 0 < R) (hCm : 0 < Cm)
    (heps1 : eps < 1) :
    0 < Cm * (R * Real.sqrt R) / Real.sqrt ((1 - eps) ^ 3) := by
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  exact div_pos (mul_pos hCm (mul_pos hR (Real.sqrt_pos.mpr hR)))
    (Real.sqrt_pos.mpr (pow_pos h1e 3))


theorem volume_reserve_image_of_scaled_comparison
    {k : SmoothRiemannianMetric I3 P} {gt : SmoothRiemannianMetric I3 M}
    (F : PartialDiffeomorph I3 I3 P M ∞)
    {U : Set P} {times : Set ℝ} {order : ℕ} {eps Q : ℝ} (hQ : 0 < Q)
    (C : MetricComparisonOn (fun _ => k) (fun _ => scaleMetric Q hQ gt)
      (F : P → M) U times order eps)
    {s : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    {V : Set P} (hV : IsOpen V) (hVU : V ⊆ U) (hVsrc : V ⊆ F.source)
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) {R Cm : ℝ}
    (hmodel : ENNReal.ofReal (Cm⁻¹ / (R * Real.sqrt R)) ≤
      riemannianVolumeMeasure I3 P k K) :
    ENNReal.ofReal
        ((Cm * (R * Real.sqrt R) / Real.sqrt ((1 - eps) ^ 3))⁻¹ / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure I3 M gt ((F : P → M) '' K) := by
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hsQ : (0 : ℝ) < Q * Real.sqrt Q := mul_pos hQ (Real.sqrt_pos.mpr hQ)
  have hge : ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
      riemannianVolumeMeasure I3 P k K ≤
      riemannianVolumeMeasure I3 M (scaleMetric Q hQ gt) ((F : P → M) '' K) :=
    MetricComparisonOn.volume_image_ge F C hs heps heps1 hV hVU hVsrc hK hKV
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hscale := volume_scale_apply Q hQ gt ((F : P → M) '' K)
  rw [hdim] at hscale
  have hpow : (ENNReal.ofReal (Real.sqrt Q)) ^ 3 = ENNReal.ofReal (Q * Real.sqrt Q) := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg Q)]
    congr 1
    have hcube : Real.sqrt Q ^ 3 = Real.sqrt Q ^ 2 * Real.sqrt Q := by ring
    rw [hcube, Real.sq_sqrt hQ.le]
  have hchain : ENNReal.ofReal
        (Real.sqrt ((1 - eps) ^ 3) * (Cm⁻¹ / (R * Real.sqrt R))) ≤
      riemannianVolumeMeasure I3 M gt ((F : P → M) '' K) *
        ENNReal.ofReal (Q * Real.sqrt Q) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    calc ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
          ENNReal.ofReal (Cm⁻¹ / (R * Real.sqrt R))
        ≤ ENNReal.ofReal (Real.sqrt ((1 - eps) ^ 3)) *
            riemannianVolumeMeasure I3 P k K := mul_le_mul' le_rfl hmodel
      _ ≤ riemannianVolumeMeasure I3 M (scaleMetric Q hQ gt) ((F : P → M) '' K) := hge
      _ = riemannianVolumeMeasure I3 M gt ((F : P → M) '' K) *
            ENNReal.ofReal (Q * Real.sqrt Q) := by
          rw [hscale, hpow, mul_comm]
  have hconst : (Cm * (R * Real.sqrt R) / Real.sqrt ((1 - eps) ^ 3))⁻¹ =
      Real.sqrt ((1 - eps) ^ 3) * (Cm⁻¹ / (R * Real.sqrt R)) := by
    rw [inv_div, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  have hne : ENNReal.ofReal (Q * Real.sqrt Q) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hsQ
  rw [hconst, ENNReal.ofReal_div_of_pos hsQ,
    ENNReal.div_le_iff hne ENNReal.ofReal_ne_top]
  exact hchain


theorem CompactDomain.map_volume_reserve
    (Dom : CompactDomain P) {k : SmoothRiemannianMetric I3 P}
    {gt : SmoothRiemannianMetric I3 M} (F : PartialDiffeomorph I3 I3 P M ∞)
    (hDsrc : Dom.carrier ⊆ F.source)
    {U : Set P} {times : Set ℝ} {order : ℕ} {eps Q : ℝ} (hQ : 0 < Q)
    (C : MetricComparisonOn (fun _ => k) (fun _ => scaleMetric Q hQ gt)
      (F : P → M) U times order eps)
    {s : ℝ} (hs : s ∈ times) (heps : 0 ≤ eps) (heps1 : eps < 1)
    {V : Set P} (hV : IsOpen V) (hVU : V ⊆ U) (hVsrc : V ⊆ F.source)
    (hDV : Dom.carrier ⊆ V) {R Cm : ℝ}
    (hmodel : ENNReal.ofReal (Cm⁻¹ / (R * Real.sqrt R)) ≤
      riemannianVolumeMeasure I3 P k Dom.carrier) :
    ENNReal.ofReal
        ((Cm * (R * Real.sqrt R) / Real.sqrt ((1 - eps) ^ 3))⁻¹ / (Q * Real.sqrt Q)) ≤
      riemannianVolumeMeasure I3 M gt (Dom.map F hDsrc).carrier := by
  rw [CompactDomain.map_carrier]
  exact volume_reserve_image_of_scaled_comparison F hQ C hs heps heps1 hV hVU hVsrc
    Dom.compact hDV hmodel

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
