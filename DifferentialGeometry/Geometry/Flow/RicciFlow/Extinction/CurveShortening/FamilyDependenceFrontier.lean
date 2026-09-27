import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary

variable {D : RealTimeInterval} {a b : ℝ}

def curveShorteningLoopFamilyExtension
    (B : SmoothMetricWindow (I := I) (M := M) D a b) (d : ℝ) (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) : Prop :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  ∃ window : ℝ, 0 < window ∧ window ≤ d - a ∧
    (∀ (c : CurveMap M) (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Icc a d)),
      ∃ U : Set (SmoothImmersion (I := I) (M := M)),
        IsOpen U ∧
          SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
          ∃ solutions : U → CurveMap M,
            (@Continuous U (CurveMap M) inferInstance
              (smoothCylinderTopology e (Icc a (min d (a + window)))) solutions) ∧
            ∀ p : U,
              (solutions p).IsSolutionOn B.family.metric (Icc a (min d (a + window))) ∧
                ∀ z, solutions p z a = p.1.map z) ∧
    (∀ (T : ℝ), a ≤ T → T < d → ∀ (c : CurveMap M)
      (hc : CurveMap.IsSolutionOn (I := I) c B.family.metric (Icc a d)),
      ∀ (U : Set (SmoothImmersion (I := I) (M := M))), IsOpen U →
        ∀ solutions : U → CurveMap M,
          (@Continuous U (CurveMap M) inferInstance
            (smoothCylinderTopology e (Icc a T)) solutions) →
          (∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a T)) →
          SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U →
          ∃ V : Set (SmoothImmersion (I := I) (M := M)),
            IsOpen V ∧
              SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ V ∧
              V ⊆ U ∧
              ∃ solutions' : V → CurveMap M,
                (@Continuous V (CurveMap M) inferInstance
                  (smoothCylinderTopology e (Icc a (min d (T + window)))) solutions') ∧
                ∀ p : V,
                  (solutions' p).IsSolutionOn B.family.metric (Icc a (min d (T + window))) ∧
                    ∀ z, solutions' p z a = p.1.map z)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
private theorem min_add_window_min {w x d : ℝ} (hw : 0 ≤ w) :
    min d (min d x + w) = min d (x + w) := by
  rcases le_total x d with h | h
  · rw [min_eq_right h]
  · rw [min_eq_left h]
    rcases le_total (x + w) d with h2 | h2
    · rw [min_eq_left (le_add_of_nonneg_right hw), min_eq_right h2]
      linarith
    · rw [min_eq_left (le_add_of_nonneg_right hw), min_eq_left h2]

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem rfs_csf_family_dependence_of_familyExtension
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    {d : ℝ} (had : a < d)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc a d))
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (H : curveShorteningLoopFamilyExtension (I := I) (M := M) B d had e) :
    letI := smoothImmersionTopology e
    ∃ U : Set (SmoothImmersion (I := I) (M := M)),
      IsOpen U ∧ SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
      ∃ solutions : U → CurveMap M,
        (@Continuous U (CurveMap M) inferInstance
          (smoothCylinderTopology e (Icc a d)) solutions) ∧
        ∀ p : U, (solutions p).IsSolutionOn B.family.metric (Icc a d) ∧
          ∀ z, solutions p z a = p.1.map z :=
  letI : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  by
    obtain ⟨window, hwpos, hwle, hseed, hext⟩ := H
    have key : ∀ n : ℕ, ∃ (T : ℝ) (U : Set (SmoothImmersion (I := I) (M := M)))
        (sols : U → CurveMap M),
        IsOpen U ∧
        SmoothImmersion.slice c hc.smooth hc.immersed a ⟨le_rfl, had.le⟩ ∈ U ∧
        (@Continuous U (CurveMap M) inferInstance (smoothCylinderTopology e (Icc a T)) sols) ∧
        (∀ p : U, (sols p).IsSolutionOn B.family.metric (Icc a T)) ∧
        (∀ p : U, ∀ z, sols p z a = p.1.map z) ∧
        T = min d (a + (n : ℝ) * window + window) := by
      intro n
      induction n with
      | zero =>
        obtain ⟨U, hU, hp, sols, hcont, hsol⟩ := hseed c hc
        refine ⟨min d (a + window), U, sols, hU, hp, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.cast_zero, zero_mul, zero_add] using hcont
        · intro p
          simpa only [Nat.cast_zero, zero_mul, zero_add] using (hsol p).1
        · intro p z
          simpa only [Nat.cast_zero, zero_mul, zero_add] using (hsol p).2 z
        · congr 1
          ring
      | succ n ih =>
        obtain ⟨T, U, sols, hU, hp, hcont, hsol, hinit, hTeq⟩ := ih
        have hTle : T ≤ d := by rw [hTeq]; exact min_le_left _ _
        have hTa : a ≤ T := by
          rw [hTeq]
          refine le_min had.le ?_
          have hnn : (0 : ℝ) ≤ (n : ℝ) * window := mul_nonneg (Nat.cast_nonneg n) hwpos.le
          linarith
        by_cases hTd : T < d
        · obtain ⟨V, hV, hpV, -, sols', hcont', hsol'⟩ :=
            hext T hTa hTd c hc U hU sols hcont hsol hp
          have hstep : min d (T + window) = min d (a + ((n : ℝ) + 1) * window + window) := by
            have hrw : a + ((n : ℝ) + 1) * window + window =
                a + (n : ℝ) * window + window + window := by ring
            rw [hrw, hTeq]
            exact min_add_window_min hwpos.le
          have hgoal : min d (a + ((n : ℝ) + 1) * window + window) =
              min d (a + ((n + 1 : ℕ) : ℝ) * window + window) := by
            congr 1
            push_cast
            ring
          refine ⟨min d (T + window), V, sols', hV, hpV, ?_, ?_, ?_, ?_⟩
          · simpa only [hstep] using hcont'
          · intro p
            simpa only [hstep] using (hsol' p).1
          · intro p z
            simpa only [hstep] using (hsol' p).2 z
          · rw [hstep, hgoal]
        · have hTd' : d ≤ T := not_lt.mp hTd
          have hTeqd : T = d := le_antisymm hTle hTd'
          have hbase : d ≤ a + (n : ℝ) * window + window := by
            rw [← hTeqd, hTeq]
            exact min_le_right _ _
          have hge : d ≤ a + ((n + 1 : ℕ) : ℝ) * window + window := by
            have hrw : a + ((n + 1 : ℕ) : ℝ) * window + window =
                a + (n : ℝ) * window + window + window := by push_cast; ring
            rw [hrw]
            linarith [hbase, hwpos]
          refine ⟨T, U, sols, hU, hp, hcont, hsol, hinit, ?_⟩
          rw [hTeqd, min_eq_left hge]
    obtain ⟨T, U, sols, hU, hp, hcont, hsol, hinit, hTeq⟩ :=
      key (Nat.ceil ((d - a) / window))
    have hceil : (d - a) / window ≤ ((Nat.ceil ((d - a) / window) : ℕ) : ℝ) := Nat.le_ceil _
    have hmul : d - a ≤ ((Nat.ceil ((d - a) / window) : ℕ) : ℝ) * window :=
      (div_le_iff₀ hwpos).mp hceil
    have hTd : T = d := by
      rw [hTeq, min_eq_left (by linarith [hmul, hwpos])]
    refine ⟨U, hU, hp, sols, ?_, ?_⟩
    · rw [hTd] at hcont
      exact hcont
    · intro p
      refine ⟨?_, hinit p⟩
      rw [hTd] at hsol
      exact hsol p

omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningLoopFamilyExtension_of_isEmpty [IsEmpty M]
    (B : SmoothMetricWindow (I := I) (M := M) D a b) {d : ℝ} (had : a < d)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    curveShorteningLoopFamilyExtension (I := I) (M := M) B d had e := by
  refine ⟨(d - a) / 2, by linarith, by linarith, ?_, ?_⟩
  · intro c hc
    exact (IsEmpty.false (c 0 0)).elim
  · intro T hTa hTd c hc U hU sols hcont hsol hp
    exact (IsEmpty.false (c 0 0)).elim

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
