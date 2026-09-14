import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampFamilySatisfiability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampDifferenceEquation

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width CurveShortening

section ProductRamp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem productCurve_angle_eq_mul_deriv (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) (lambda x t : ℝ) :
    c.angle g lambda x t = lambda * (c.speed g lambda x t)⁻¹ * deriv (fun z => c.y z t) x := by
  rw [ProductCurve.angle, ProductCurve.inner, ProductCurve.unitTangent, ProductCurve.verticalUnit]
  simp only [ProductCurve.X, Prod.smul_fst, Prod.smul_snd, map_zero, smul_eq_mul]
  rcases eq_or_ne lambda 0 with h | h
  · rw [h]; simp
  · field_simp
    ring

theorem productCurve_inner_X_self (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) (lambda x t : ℝ) :
    c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) =
      (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) +
        lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by
  rw [ProductCurve.inner]
  simp only [ProductCurve.X]
  ring

theorem productCurve_inner_X_self_pos_iff (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) (lambda x t : ℝ) (hlambda : lambda ≠ 0) :
    0 < c.inner g lambda x t (c.X (I := I) x t) (c.X (I := I) x t) ↔
      c.X (I := I) x t ≠ 0 := by
  rw [productCurve_inner_X_self]
  constructor
  · intro h hzero
    have h1 : c.projection.X (I := I) x t = 0 := congrArg Prod.fst hzero
    have h2 : deriv (fun z => c.y z t) x = 0 := congrArg Prod.snd hzero
    rw [h1, h2] at h
    simp at h
  · intro hne
    have hcases : (c.X (I := I) x t).1 ≠ 0 ∨ (c.X (I := I) x t).2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (Prod.ext hc.1 hc.2)
    rcases hcases with h1 | h2
    · have h1' : c.projection.X (I := I) x t ≠ 0 := h1
      have hpos := (g t).pos (c.projection.lift x t) (c.projection.X (I := I) x t) h1'
      have hnn : 0 ≤ lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 := by positivity
      linarith
    · have h2' : deriv (fun z => c.y z t) x ≠ 0 := h2
      have hsq : 0 < lambda ^ 2 * (deriv (fun z => c.y z t) x) ^ 2 :=
        mul_pos (sq_pos_of_ne_zero hlambda) (sq_pos_of_ne_zero h2')
      have hnn : 0 ≤ (g t).inner (c.projection.lift x t) (c.projection.X (I := I) x t)
          (c.projection.X (I := I) x t) := by
        rcases eq_or_ne (c.projection.X (I := I) x t) 0 with h | h
        · rw [h]; simp
        · exact ((g t).pos (c.projection.lift x t) _ h).le
      linarith

theorem productCurve_speed_pos_iff (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) (lambda x t : ℝ) (hlambda : lambda ≠ 0) :
    0 < c.speed g lambda x t ↔ c.X (I := I) x t ≠ 0 := by
  rw [ProductCurve.speed, Real.sqrt_pos]
  exact productCurve_inner_X_self_pos_iff c g lambda x t hlambda

theorem productCurve_isRampOn_iff_pos_deriv (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) {lambda : ℝ} (hlambda : 0 < lambda) (J : Set ℝ) :
    c.IsRampOn g lambda J ↔ ∀ x t, t ∈ J → 0 < deriv (fun z => c.y z t) x := by
  constructor
  · intro h x t ht
    have hang := h.2 x t ht
    have hsp : 0 < c.speed g lambda x t :=
      (productCurve_speed_pos_iff c g lambda x t hlambda.ne').mpr (h.1 x t ht)
    rw [productCurve_angle_eq_mul_deriv c g lambda x t] at hang
    by_contra hle
    have hneg : lambda * (c.speed g lambda x t)⁻¹ * deriv (fun z => c.y z t) x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_pos hlambda (inv_pos.mpr hsp)).le (le_of_not_gt hle)
    linarith
  · intro h
    refine ⟨fun x t ht => ?_, fun x t ht => ?_⟩
    · intro hzero
      have hd : deriv (fun z => c.y z t) x = 0 := congrArg Prod.snd hzero
      linarith [h x t ht]
    · have hsp : 0 < c.speed g lambda x t := by
        rw [productCurve_speed_pos_iff c g lambda x t hlambda.ne']
        intro hzero
        have hd : deriv (fun z => c.y z t) x = 0 := congrArg Prod.snd hzero
        linarith [h x t ht]
      rw [productCurve_angle_eq_mul_deriv]
      exact mul_pos (mul_pos hlambda (inv_pos.mpr hsp)) (h x t ht)

theorem productCurve_isRampOn_congr_of_pos (c : ProductCurve Q)
    (g : ℝ → SmoothRiemannianMetric I Q) {lambda lambda' : ℝ} (J : Set ℝ)
    (h : 0 < lambda) (h' : 0 < lambda') :
    c.IsRampOn g lambda J ↔ c.IsRampOn g lambda' J :=
  (productCurve_isRampOn_iff_pos_deriv c g h J).trans
    (productCurve_isRampOn_iff_pos_deriv c g h' J).symm

theorem rampInitialData_congr_of_pos (g : ℝ → SmoothRiemannianMetric I Q) (a : ℝ)
    {lambda lambda' : ℝ} (h : 0 < lambda) (h' : 0 < lambda') :
    (∃ c : ProductCurve Q, c.SmoothOn (I := I) {a} ∧ c.IsRampOn g lambda {a}) ↔
      ∃ c : ProductCurve Q, c.SmoothOn (I := I) {a} ∧ c.IsRampOn g lambda' {a} :=
  ⟨fun ⟨c, hsm, hr⟩ =>
      ⟨c, hsm, (productCurve_isRampOn_congr_of_pos c g {a} h h').mp hr⟩,
    fun ⟨c, hsm, hr⟩ =>
      ⟨c, hsm, (productCurve_isRampOn_congr_of_pos c g {a} h h').mpr hr⟩⟩

end ProductRamp

private theorem rampMin_eq_right_of_lt (b x : ℝ) (h : min b x < b) : min b x = x := by
  rcases le_total b x with hbx | hxb
  · rw [min_eq_left hbx] at h
    exact absurd h (lt_irrefl b)
  · exact min_eq_right hxb

section RampExistenceReduction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
    [SigmaCompactSpace Q] [hT2 : T2Space Q] [hCompact : CompactSpace Q]
    [hConnected : ConnectedSpace Q] [hBoundary : I.Boundaryless]
    {D : RealTimeInterval} {a b : ℝ}

def RampSolutionExistence (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ) : Prop :=
  ∀ c₀ : ProductCurve Q, c₀.SmoothOn (I := I) {a} →
    c₀.IsRampOn B.family.metric lambda {a} →
    ∃ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      (∀ x t, t ∈ Icc a b → c.curvature B.family.metric lambda x t ≤
        c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t)

def RampSolutionUniqueness (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ) : Prop :=
  ∀ (c₀ c d : ProductCurve Q),
    c.IsSolutionOn B.family.metric lambda (Icc a b) →
    d.IsSolutionOn B.family.metric lambda (Icc a b) →
    (∀ z, c.map z a = c₀.map z a) → (∀ z, d.map z a = c₀.map z a) →
    ∀ z t, t ∈ Icc a b → d.map z t = c.map z t

theorem rampExistenceInput_iff_solutionExistence_and_uniqueness
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ) :
    RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda ↔
      RampSolutionExistence (I := I) (D := D) (a := a) (b := b) B lambda ∧
        RampSolutionUniqueness (I := I) (D := D) (a := a) (b := b) B lambda :=
  ⟨fun h => ⟨h.exists_solution, h.unique⟩, fun h => ⟨h.1, h.2⟩⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem RampSolutionUniqueness.of_localUniqueness
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    (U : RampLocalUniqueness (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) :
    RampSolutionUniqueness (I := I) (D := D) (a := a) (b := b) B lambda := by
  intro c₀ c d hc hd hc₀ hd₀ z t ht
  exact (U a b b le_rfl B.lt B.lt le_rfl le_rfl c d hc hd
    (fun z => by rw [hc₀ z, hd₀ z]) z t (by simpa using ht)).symm

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem RampSolutionUniqueness.of_shortTime
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    (H : RampShortTimeUniqueness (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) :
    RampSolutionUniqueness (I := I) (D := D) (a := a) (b := b) B lambda :=
  RampSolutionUniqueness.of_localUniqueness B lambda
    (RampLocalUniqueness.of_shortTime (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda H)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem RampSolutionUniqueness.of_differenceSubsolution
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ) (hlambda : 0 < lambda)
    (h : ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b → ∀ c₁ c₂ : ProductCurve Q,
      c₁.IsSolutionOn B.family.metric lambda (Icc s T) →
      c₂.IsSolutionOn B.family.metric lambda (Icc s T) →
      (∀ z, c₁.map z s = c₂.map z s) →
      c₁.DifferenceSubsolution (I := I) B.family.metric lambda s T c₂) :
    RampSolutionUniqueness (I := I) (D := D) (a := a) (b := b) B lambda :=
  RampSolutionUniqueness.of_localUniqueness B lambda
    (rampLocalUniqueness_of_differenceSubsolution (I := I) (M := Q) B lambda hlambda h)

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem RampSolutionExistence.of_uniformExtension
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    (H : RampUniformExtension (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) :
    RampSolutionExistence (I := I) (D := D) (a := a) (b := b) B lambda := by
  intro c₀ hsmooth hramp₀
  have hτ : 0 < H.local_time := H.local_time_pos
  have key : ∀ n : ℕ, 1 ≤ n → ∃ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a (min b (a + (n : ℝ) * H.local_time))) ∧
      c.IsRampOn B.family.metric lambda (Icc a (min b (a + (n : ℝ) * H.local_time))) ∧
      (∀ z, c.map z a = c₀.map z a) ∧
      ∀ x t, t ∈ Icc a (min b (a + (n : ℝ) * H.local_time)) →
        c.curvature B.family.metric lambda x t ≤
          c₀.curvatureEnvelope B.family.metric lambda B.B₀ B.C a b t := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      obtain ⟨c, hsol, hramp, hdat, hcurv⟩ :=
        H.exists_from_start (I := I) (M := Q) (D := D) (a := a) (b := b) c₀ hsmooth hramp₀
      have hgoal : min b (a + ((1 : ℕ) : ℝ) * H.local_time) = min b (a + H.local_time) := by
        norm_num
      rw [hgoal]
      exact ⟨c,
        ProductCurve.IsSolutionOn.mono_Icc le_rfl (min_le_right _ _)
          (lt_min B.lt (by linarith)) hsol,
        hramp.mono (Icc_subset_Icc le_rfl (min_le_right _ _)),
        hdat,
        hcurv⟩
    | succ n hn ih =>
      obtain ⟨c, hsol, hramp, hdat, hcurv⟩ := ih
      by_cases hb : min b (a + (n : ℝ) * H.local_time) = b
      · have hnext : min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) =
            min b (a + (n : ℝ) * H.local_time) := by
          have hge : b ≤ a + (n : ℝ) * H.local_time := min_eq_left_iff.mp hb
          have hcast : a + (((n + 1 : ℕ) : ℝ)) * H.local_time =
              a + (n : ℝ) * H.local_time + H.local_time := by
            push_cast
            ring
          rw [hcast, min_eq_left (by linarith), hb]
        refine ⟨c, ?_, ?_, hdat, ?_⟩
        · rw [hnext]; exact hsol
        · rw [hnext]; exact hramp
        · intro x t ht
          rw [hnext] at ht
          exact hcurv x t ht
      · have hlt : min b (a + (n : ℝ) * H.local_time) < b :=
          lt_of_le_of_ne (min_le_left _ _) hb
        have hnonneg : (0 : ℝ) ≤ (n : ℝ) * H.local_time :=
          mul_nonneg (Nat.cast_nonneg n) hτ.le
        have hle : a ≤ min b (a + (n : ℝ) * H.local_time) := le_min B.lt.le (by linarith)
        have heq : min b (a + (n : ℝ) * H.local_time) = a + (n : ℝ) * H.local_time :=
          rampMin_eq_right_of_lt b _ hlt
        obtain ⟨c', hsol', hramp', hagree, hcurv'⟩ :=
          H.extend (I := I) (M := Q) (D := D) (a := a) (b := b)
            (min b (a + (n : ℝ) * H.local_time)) c c₀ hle hlt hsmooth hramp₀
            hdat hsol hramp hcurv
        have hnext : min b (min b (a + (n : ℝ) * H.local_time) + H.local_time) =
            min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) := by
          rw [heq]
          congr 1
          push_cast
          ring
        have hle' : min b (a + (((n + 1 : ℕ) : ℝ)) * H.local_time) ≤
            min b (a + (n : ℝ) * H.local_time) + H.local_time := by
          rw [← hnext]
          exact min_le_right _ _
        have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) * H.local_time :=
          mul_pos (Nat.cast_pos.mpr (Nat.succ_pos n)) hτ
        refine ⟨c',
          ProductCurve.IsSolutionOn.mono_Icc le_rfl hle' (lt_min B.lt (by linarith)) hsol',
          hramp'.mono (Icc_subset_Icc le_rfl hle'), ?_, ?_⟩
        · intro z
          rw [hagree z a ⟨le_rfl, hle⟩]
          exact hdat z
        · intro x t ht
          rw [← hnext] at ht
          exact hcurv' x t ht
  obtain ⟨c, hsol, hramp, hdat, hcurv⟩ :=
    key (Nat.ceil ((b - a) / H.local_time))
      (Nat.succ_le_of_lt (Nat.ceil_pos.mpr (div_pos (sub_pos.mpr B.lt) hτ)))
  have hmul : (b - a) / H.local_time ≤ (Nat.ceil ((b - a) / H.local_time) : ℝ) :=
    Nat.le_ceil _
  rw [div_le_iff₀ hτ] at hmul
  have hmin : min b (a + (Nat.ceil ((b - a) / H.local_time) : ℝ) * H.local_time) = b :=
    min_eq_left (by linarith [hmul])
  rw [hmin] at hsol hramp hcurv
  exact ⟨c, hsol, hramp, hdat, hcurv⟩

omit [SigmaCompactSpace Q] hCompact hConnected hBoundary in
theorem rampSolutionExistence_zero (B : RicciBackground (I := I) (M := Q) D a b) :
    RampSolutionExistence (I := I) (D := D) (a := a) (b := b) B 0 := by
  intro c₀ _ hramp
  exact absurd hramp (ProductCurve.not_isRampOn_zero c₀ B.family.metric)

omit [SigmaCompactSpace Q] hCompact hBoundary in
theorem rampInitialData_nonempty (B : RicciBackground (I := I) (M := Q) D a b) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    ∃ c : ProductCurve Q, c.SmoothOn (I := I) {a} ∧
      c.IsRampOn B.family.metric lambda {a} :=
  exists_smoothOn_and_isRampOn (Classical.arbitrary Q) B.family.metric a lambda hlambda

def RampExistenceOn (B : RicciBackground (I := I) (M := Q) D a b) (S : Set ℝ) : Prop :=
  ∀ lambda ∈ S, RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda

theorem rampExistenceOn_mono (B : RicciBackground (I := I) (M := Q) D a b) {S T : Set ℝ}
    (hTS : T ⊆ S) (h : RampExistenceOn (I := I) (D := D) (a := a) (b := b) B S) :
    RampExistenceOn (I := I) (D := D) (a := a) (b := b) B T :=
  fun lambda hl => h lambda (hTS hl)

theorem rampExistenceOn_iff_pointwise (B : RicciBackground (I := I) (M := Q) D a b)
    (S : Set ℝ) :
    RampExistenceOn (I := I) (D := D) (a := a) (b := b) B S ↔
      (∀ lambda ∈ S, RampSolutionExistence (I := I) (D := D) (a := a) (b := b) B lambda) ∧
        (∀ lambda ∈ S,
          RampSolutionUniqueness (I := I) (D := D) (a := a) (b := b) B lambda) := by
  constructor
  · intro h
    exact ⟨fun lambda hl =>
        ((rampExistenceInput_iff_solutionExistence_and_uniqueness B lambda).mp
          (h lambda hl)).1,
      fun lambda hl =>
        ((rampExistenceInput_iff_solutionExistence_and_uniqueness B lambda).mp
          (h lambda hl)).2⟩
  · rintro ⟨h1, h2⟩ lambda hl
    exact (rampExistenceInput_iff_solutionExistence_and_uniqueness B lambda).mpr
      ⟨h1 lambda hl, h2 lambda hl⟩

theorem rfs_csf_ramp_family_of_discreteTopology
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N) {P : Type*} [TopologicalSpace P]
    [DiscreteTopology P] (initial : P → ProductCurve Q)
    (hsmooth : ∀ p, (initial p).SmoothOn (I := I) {a})
    (hramp : ∀ p, (initial p).IsRampOn B.family.metric lambda {a})
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) :
    ∃ solutions : P → ProductCurve Q,
      (@Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions) ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a := by
  classical
  have h : ∀ p : P, ∃ c : ProductCurve Q,
      c.IsSolutionOn B.family.metric lambda (Icc a b) ∧
      c.IsRampOn B.family.metric lambda (Icc a b) ∧
      ∀ z, c.map z a = (initial p).map z a := by
    intro p
    obtain ⟨c, h1, h2, h3, -⟩ := K.exists_solution (initial p) (hsmooth p) (hramp p)
    exact ⟨c, h1, h2, h3⟩
  have hcont : @Continuous P (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) (fun p => Classical.choose (h p)) :=
    @Continuous.mk P (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) (fun p => Classical.choose (h p))
      (fun s _ => isOpen_discrete _)
  exact ⟨fun p => Classical.choose (h p), hcont, fun p => Classical.choose_spec (h p)⟩

theorem rfs_csf_ramp_family_of_const_initial
    (B : RicciBackground (I := I) (M := Q) D a b) (lambda : ℝ)
    {N : ℕ} (e : SmoothLoopEmbedding (I := I) (Q := Q) N) {P : Type*} [TopologicalSpace P]
    (c₀ : ProductCurve Q) (initial : P → ProductCurve Q) (hconst : ∀ p, initial p = c₀)
    (hsmooth : c₀.SmoothOn (I := I) {a}) (hramp : c₀.IsRampOn B.family.metric lambda {a})
    (K : RampExistenceInput (I := I) (M := Q) (D := D) (a := a) (b := b) B lambda) :
    ∃ solutions : P → ProductCurve Q,
      (@Continuous P (ProductCurve Q) inferInstance
        (smoothProductCylinderTopology e (Icc a b)) solutions) ∧
      ∀ p, (solutions p).IsSolutionOn B.family.metric lambda (Icc a b) ∧
        (solutions p).IsRampOn B.family.metric lambda (Icc a b) ∧
        ∀ z, (solutions p).map z a = (initial p).map z a := by
  obtain ⟨c, h1, h2, h3, -⟩ := K.exists_solution c₀ hsmooth hramp
  have hcont : @Continuous P (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) (fun _ => c) :=
    @Continuous.mk P (ProductCurve Q) inferInstance
      (smoothProductCylinderTopology e (Icc a b)) (fun _ => c)
      (fun s _ => by
        by_cases hmem : c ∈ s
        · rw [Set.preimage_const_of_mem hmem]; exact isOpen_univ
        · rw [Set.preimage_const_of_notMem hmem]; exact isOpen_empty)
  exact ⟨fun _ => c, hcont, fun p => ⟨h1, h2, fun z => by rw [hconst p]; exact h3 z⟩⟩

end RampExistenceReduction

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
