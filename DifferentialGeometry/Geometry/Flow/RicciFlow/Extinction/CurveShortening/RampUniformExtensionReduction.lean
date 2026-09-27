import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampFamilySatisfiability

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

def RampUniformLocalTime (B : RicciBackground (I := I) (M := M) D a b) (lambda δ : ℝ) : Prop :=
  0 < δ ∧ ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ c : ProductCurve M,
      c.IsSolutionOn B.family.metric lambda (Icc a (a + δ)) ∧
      c.IsRampOn B.family.metric lambda (Icc a (a + δ)) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      ∀ x t, t ∈ Icc a (min b (a + δ)) →
        c.curvature B.family.metric lambda x t ≤
          c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

def RampUniformContinuation (B : RicciBackground (I := I) (M := M) D a b)
    (lambda δ : ℝ) : Prop :=
  ∀ (T : ℝ) (c c₀ : ProductCurve M),
    a ≤ T → T < b → c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    (∀ z, c.map z a = c₀.map z a) →
    c.IsSolutionOn B.family.metric lambda (Icc a T) →
    c.IsRampOn B.family.metric lambda (Icc a T) →
    (∀ x t, t ∈ Icc a T →
      c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t) →
    ∃ c' : ProductCurve M,
      c'.IsSolutionOn B.family.metric lambda (Icc a (T + δ)) ∧
      c'.IsRampOn B.family.metric lambda (Icc a (T + δ)) ∧
      (∀ z t, t ∈ Icc a T → c'.map z t = c.map z t) ∧
      ∀ x t, t ∈ Icc a (min b (T + δ)) →
        c'.curvature B.family.metric lambda x t ≤
          c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

def RampUniformLocalData (B : RicciBackground (I := I) (M := M) D a b) (lambda δ : ℝ)
    {P : Type*} (initial : P → ProductCurve M) : Prop :=
  ∀ p : P, ∃ c : ProductCurve M,
    c.IsSolutionOn B.family.metric lambda (Icc a (a + δ)) ∧
    c.IsRampOn B.family.metric lambda (Icc a (a + δ)) ∧
    (∀ z, c.map z a = (initial p).map z a) ∧
    ∀ x t, t ∈ Icc a (min b (a + δ)) →
      c.curvature B.family.metric lambda x t ≤
        (initial p).curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

def RampLocalExistenceCore (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) : Prop :=
  ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set (ProductCurve M),
      @IsOpen (ProductCurve M) (smoothProductInitialTopology e a) U ∧ c₀ ∈ U ∧
      ∀ q ∈ U, q.SmoothOn (I := I) {a} → q.IsRampOn B.family.metric lambda {a} →
        ∃ c : ProductCurve M,
          c.IsSolutionOn B.family.metric lambda (Icc a (a + δ)) ∧
          c.IsRampOn B.family.metric lambda (Icc a (a + δ)) ∧
          (∀ z, c.map z a = q.map z a)

def RampLocalCurvatureEnvelope (B : RicciBackground (I := I) (M := M) D a b)
    (lambda : ℝ) : Prop :=
  ∀ (δ : ℝ) (q : ProductCurve M), 0 < δ → q.SmoothOn (I := I) {a} →
    q.IsRampOn B.family.metric lambda {a} →
    ∀ c : ProductCurve M, (∀ z, c.map z a = q.map z a) →
      c.IsSolutionOn B.family.metric lambda (Icc a (a + δ)) →
      c.IsRampOn B.family.metric lambda {a} →
      ∀ x t, t ∈ Icc a (min b (a + δ)) →
        c.curvature B.family.metric lambda x t ≤
          q.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

def RampLocalExistence (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) : Prop :=
  ∀ c₀ : ProductCurve M, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ δ : ℝ, 0 < δ ∧ ∃ U : Set (ProductCurve M),
      @IsOpen (ProductCurve M) (smoothProductInitialTopology e a) U ∧ c₀ ∈ U ∧
      ∀ q ∈ U, q.SmoothOn (I := I) {a} → q.IsRampOn B.family.metric lambda {a} →
        ∃ c : ProductCurve M,
          c.IsSolutionOn B.family.metric lambda (Icc a (a + δ)) ∧
          c.IsRampOn B.family.metric lambda (Icc a (a + δ)) ∧
          (∀ z, c.map z a = q.map z a) ∧
          ∀ x t, t ∈ Icc a (min b (a + δ)) →
            c.curvature B.family.metric lambda x t ≤
              q.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampUniformExtension_exists_localTime_and_continuation
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (H : RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    ∃ δ : ℝ, RampUniformLocalTime B lambda δ ∧ RampUniformContinuation B lambda δ :=
  ⟨H.local_time, ⟨H.local_time_pos, H.exists_from_start⟩, H.extend⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
def rampUniformExtensionOfLocalTimeAndContinuation
    (B : RicciBackground (I := I) (M := M) D a b) (lambda δ : ℝ)
    (hloc : RampUniformLocalTime B lambda δ) (hcont : RampUniformContinuation B lambda δ) :
    RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B lambda :=
  ⟨δ, hloc.1, hloc.2, hcont⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalExistenceCore_of_localExistence
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (H : RampLocalExistence B lambda e) : RampLocalExistenceCore B lambda e := by
  intro c₀ hs hr
  obtain ⟨δ, hδ, U, hUo, hmem, hprop⟩ := H c₀ hs hr
  exact ⟨δ, hδ, U, hUo, hmem, fun q hq hqs hqr => by
    obtain ⟨c, hsol, hramp, hagree, _⟩ := hprop q hq hqs hqr
    exact ⟨c, hsol, hramp, hagree⟩⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalExistence_of_core_and_curvatureEnvelope
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (hcore : RampLocalExistenceCore B lambda e)
    (hcurv : RampLocalCurvatureEnvelope B lambda) : RampLocalExistence B lambda e := by
  intro c₀ hs hr
  obtain ⟨δ, hδpos, U, hUo, hmem, hprop⟩ := hcore c₀ hs hr
  refine ⟨δ, hδpos, U, hUo, hmem, fun q hq hqs hqr => ?_⟩
  obtain ⟨c, hsol, hramp, hagree⟩ := hprop q hq hqs hqr
  have hrampA : c.IsRampOn B.family.metric lambda {a} :=
    hramp.mono (by rw [← Set.Icc_self a]; exact Icc_subset_Icc le_rfl (by linarith))
  exact ⟨c, hsol, hramp, hagree,
    fun x t ht => hcurv δ q hδpos hqs hqr c hagree hsol hrampA x t ht⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalExistence_of_uniformExtension
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (H : RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    RampLocalExistence B lambda e := by
  intro c₀ hs hr
  refine ⟨H.local_time, H.local_time_pos, univ,
    @isOpen_univ (ProductCurve M) (smoothProductInitialTopology e a), mem_univ c₀, ?_⟩
  intro q _ hqs hqr
  exact H.exists_from_start q hqs hqr

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem exists_uniform_localData_of_localExistence
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (initial : P → ProductCurve M)
    (hcont : @Continuous P (ProductCurve M) inferInstance
      (smoothProductInitialTopology e a) initial)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a})
    (H : RampLocalExistence B lambda e) :
    ∃ δ : ℝ, 0 < δ ∧ RampUniformLocalData B lambda δ initial := by
  classical
  choose δ hδ using fun p => H (initial p) (hsmooth p) (hramp p)
  choose U hU using fun p => (hδ p).2
  let V : P → Set P := fun p => initial ⁻¹' U p
  have hVopen : ∀ p, IsOpen (V p) := fun p =>
    letI : TopologicalSpace (ProductCurve M) := smoothProductInitialTopology e a
    (hU p).1.preimage hcont
  have hcover : (univ : Set P) ⊆ ⋃ p, V p :=
    fun p _ => Set.mem_iUnion.mpr ⟨p, (hU p).2.1⟩
  obtain ⟨t, ht⟩ := (@isCompact_univ P _ _).elim_finite_subcover V hVopen hcover
  by_cases hne : t.Nonempty
  · have hminpos : 0 < (t.image δ).min' (hne.image δ) := by
      rw [Finset.lt_min'_iff]
      intro c hc
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hc
      exact (hδ p).1
    refine ⟨(t.image δ).min' (hne.image δ), hminpos, ?_⟩
    intro p
    obtain ⟨i, hit, hpi⟩ := Set.mem_iUnion₂.mp (ht (mem_univ p))
    obtain ⟨c, hsol, hramp', hagree, hcurv⟩ :=
      (hU i).2.2 (initial p) hpi (hsmooth p) (hramp p)
    have hle : (t.image δ).min' (hne.image δ) ≤ δ i :=
      Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
    refine ⟨c, ProductCurve.IsSolutionOn.mono_Icc le_rfl (by linarith)
        (by linarith [hminpos]) hsol,
      hramp'.mono (Icc_subset_Icc le_rfl (by linarith)), hagree, fun x t' ht' => ?_⟩
    exact hcurv x t' ⟨ht'.1, le_trans ht'.2 (min_le_min le_rfl (by linarith))⟩
  · have hempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, one_pos, fun p => ?_⟩
    obtain ⟨i, hit, _⟩ := Set.mem_iUnion₂.mp (ht (mem_univ p))
    rw [hempty] at hit
    exact absurd hit (by simp)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem exists_uniform_localData_of_uniformExtension
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    {P : Type*} (initial : P → ProductCurve M)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a})
    (H : RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    ∃ δ : ℝ, 0 < δ ∧ RampUniformLocalData B lambda δ initial :=
  ⟨H.local_time, H.local_time_pos,
    fun p => H.exists_from_start (initial p) (hsmooth p) (hramp p)⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampUniformLocalTime_zero (B : RicciBackground (I := I) (M := M) D a b) :
    RampUniformLocalTime B 0 1 := by
  refine ⟨one_pos, fun c₀ _ hr => ?_⟩
  exact absurd hr (ProductCurve.not_isRampOn_zero (a := a) c₀ B.family.metric)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampUniformContinuation_zero (B : RicciBackground (I := I) (M := M) D a b) :
    RampUniformContinuation B 0 1 := by
  intro T c c₀ _ _ _ hr _ _ _ _
  exact absurd hr (ProductCurve.not_isRampOn_zero (a := a) c₀ B.family.metric)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem nonempty_rampUniformExtension_zero (B : RicciBackground (I := I) (M := M) D a b) :
    Nonempty (RampUniformExtension (I := I) (M := M) (D := D) (a := a) (b := b) B 0) :=
  ⟨{ local_time := 1
     local_time_pos := one_pos
     exists_from_start := (rampUniformLocalTime_zero B).2
     extend := rampUniformContinuation_zero B }⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalExistenceCore_zero (B : RicciBackground (I := I) (M := M) D a b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    RampLocalExistenceCore B 0 e := by
  intro c₀ _ hr
  exact absurd hr (ProductCurve.not_isRampOn_zero (a := a) c₀ B.family.metric)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalCurvatureEnvelope_zero (B : RicciBackground (I := I) (M := M) D a b) :
    RampLocalCurvatureEnvelope B 0 := by
  intro δ q _ _ hr
  exact absurd hr (ProductCurve.not_isRampOn_zero (a := a) q B.family.metric)

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem rampLocalExistence_zero (B : RicciBackground (I := I) (M := M) D a b)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    RampLocalExistence B 0 e := by
  intro c₀ _ hr
  exact absurd hr (ProductCurve.not_isRampOn_zero (a := a) c₀ B.family.metric)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
