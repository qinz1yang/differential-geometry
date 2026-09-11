import DifferentialGeometry.Geometry.Comparison.Soul.SoulExists

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

section Sequence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [MetricSpace M] [ChartedSpace H M]


def shavingSequence (C : Set M) : ℕ → Set M
  | 0 => C
  | n + 1 => deepest I (shavingSequence C n)


@[simp] theorem shavingSequence_zero (C : Set M) : shavingSequence I C 0 = C := rfl


@[simp] theorem shavingSequence_succ (C : Set M) (n : ℕ) :
    shavingSequence I C (n + 1) = deepest I (shavingSequence I C n) := rfl


theorem shavingSequence_deepest (C : Set M) (n : ℕ) :
    shavingSequence I (deepest I C) n = shavingSequence I C (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [shavingSequence_succ, ih]


theorem shavingSequence_succ_subset (C : Set M) (n : ℕ) :
    shavingSequence I C (n + 1) ⊆ shavingSequence I C n := deepest_subset


theorem shavingSequence_antitone (C : Set M) : Antitone (shavingSequence I C) :=
  antitone_nat_of_succ_le (shavingSequence_succ_subset I C)


theorem shavingSequence_subset (C : Set M) (n : ℕ) : shavingSequence I C n ⊆ C :=
  shavingSequence_antitone I C (Nat.zero_le n)

variable {I}


theorem deepest_eq_self_of_relBoundary_eq_empty {C : Set M}
    (hne : C.Nonempty) (hB : relBoundary I C = ∅) : deepest I C = C := by
  have hmax : boundaryDistanceMax I C = 0 := by
    unfold boundaryDistanceMax
    simp only [hB, Metric.infDist_empty]
    have himage : (fun _ : M => (0 : ℝ)) '' C = {0} := by
      ext a
      constructor
      · rintro ⟨x, hx, rfl⟩
        rfl
      · intro ha
        obtain ⟨x, hx⟩ := hne
        exact ⟨x, hx, ha.symm⟩
    rw [himage, csSup_singleton]
  ext x
  simp only [mem_deepest_iff, hmax, hB, Metric.infDist_empty, le_refl, and_true]


theorem exists_shavingSequence_exit {C : Set M} {r : M} (hr : r ∈ C)
    {n : ℕ} (hn : r ∉ shavingSequence I C n) :
    ∃ k < n, r ∈ shavingSequence I C k ∧ r ∉ deepest I (shavingSequence I C k) := by
  induction n with
  | zero => exact (hn hr).elim
  | succ n ih =>
    by_cases hmem : r ∈ shavingSequence I C n
    · exact ⟨n, Nat.lt_succ_self n, hmem, hn⟩
    · obtain ⟨k, hk, hkin, hkout⟩ := ih hmem
      exact ⟨k, hk.trans (Nat.lt_succ_self n), hkin, hkout⟩


def shavingSuperlevel (C : Set M) (t : ℝ) : Set M :=
  {z ∈ C | t ≤ Metric.infDist z (relBoundary I C)}

end Sequence

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
  [ConnectedSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem shavingSequence_spec {g : SmoothRiemannianMetric I M}
    (hconc : ShavingConcavity (I := I) g) {C : Set M}
    (hCcomp : IsCompact C) (hCne : C.Nonempty) (hCconv : IsTotallyConvex (I := I) g C)
    (n : ℕ) : IsCompact (shavingSequence I C n) ∧ (shavingSequence I C n).Nonempty ∧
      IsTotallyConvex (I := I) g (shavingSequence I C n) := by
  induction n with
  | zero => exact ⟨hCcomp, hCne, hCconv⟩
  | succ n ih =>
    rw [shavingSequence_succ]
    refine ⟨isCompact_deepest ih.1, deepest_nonempty ih.1 ih.2.1, ?_⟩
    rcases eq_empty_or_nonempty (relBoundary I (shavingSequence I C n)) with hB | hB
    · rw [deepest_eq_self_of_relBoundary_eq_empty ih.2.1 hB]
      exact ih.2.2
    · exact hconc.isTotallyConvex_deepest ih.1 ih.2.1 ih.2.2 hB

theorem exists_shavingSequence_terminal (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hCconv : IsTotallyConvex (I := I) g C) :
    ∃ n ≤ maxSliceDim I C, relBoundary I (shavingSequence I C n) = ∅ := by
  suffices H : ∀ d : ℕ, ∀ D : Set M, maxSliceDim I D = d → IsCompact D → D.Nonempty →
      IsTotallyConvex (I := I) g D →
      ∃ n ≤ d, relBoundary I (shavingSequence I D n) = ∅ by
    exact H _ C rfl hCcomp hCne hCconv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro D hdim hcomp hne hconv
    rcases eq_empty_or_nonempty (relBoundary I D) with hB | hB
    · exact ⟨0, Nat.zero_le d, hB⟩
    obtain ⟨_, hDne, hDcomp, hDconv, hlt⟩ :=
      exists_deepest_of_shavingConcavity g hEnorm hconc hcomp hne hconv hB
    obtain ⟨n, hn, hterm⟩ := ih (maxSliceDim I (deepest I D)) (by rwa [hdim] at hlt)
      (deepest I D) rfl hDcomp hDne hDconv
    refine ⟨n + 1, Nat.succ_le_of_lt (hn.trans_lt (by rwa [hdim] at hlt)), ?_⟩
    rwa [shavingSequence_deepest] at hterm

theorem deepest_subset_maxSliceLocus (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hCconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) (hBne : (relBoundary I C).Nonempty) :
    deepest I C ⊆ maxSliceLocus I C := by
  intro x hx
  by_contra hxN
  have hzero := Metric.infDist_zero_of_mem (show x ∈ relBoundary I C from ⟨hx.1, hxN⟩)
  have hpos := boundaryDistanceMax_pos g hEnorm hCconv hCcomp hCne hBne
  exact (not_le_of_gt hpos) (by simpa only [hzero] using hx.2)

theorem shavingSuperlevel_dim_and_deepest (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hCconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) (hBne : (relBoundary I C).Nonempty)
    {t : ℝ} (ht : t < boundaryDistanceMax I C) :
    maxSliceDim I (shavingSuperlevel (I := I) C t) = maxSliceDim I C ∧
      deepest I C ⊆ maxSliceLocus I (shavingSuperlevel (I := I) C t) := by
  let O : Set M := {x | t < Metric.infDist x (relBoundary I C)}
  have hO : IsOpen O := isOpen_lt continuous_const (Metric.continuous_infDist_pt _)
  let N := maxSliceLocus I C ∩ O
  have hN : IsEmbeddedSlice I (maxSliceDim I C) N :=
    (isEmbeddedSlice_maxSliceLocus hEnorm hCconv).inter_open hO
  have hdeepN : deepest I C ⊆ N := by
    intro x hx
    refine ⟨deepest_subset_maxSliceLocus g hEnorm hCconv hCcomp hCne hBne hx, ?_⟩
    exact ht.trans_le hx.2
  have hNsub : N ⊆ shavingSuperlevel (I := I) C t := by
    rintro x ⟨hxN, hxO⟩
    exact ⟨maxSliceLocus_subset hxN, hxO.le⟩
  have hdim : maxSliceDim I (shavingSuperlevel (I := I) C t) = maxSliceDim I C := by
    apply le_antisymm (maxSliceDim_mono (I := I) (fun _ hx => hx.1))
    exact le_maxSliceDim (I := I)
      ⟨N, (deepest_nonempty hCcomp hCne).mono hdeepN, hNsub, hN⟩
  refine ⟨hdim, ?_⟩
  intro x hx
  exact ⟨N, hdeepN hx, hNsub, by rwa [hdim]⟩

theorem mem_relBoundary_shavingSuperlevel (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {C : Set M}
    (hCconv : IsTotallyConvex (I := I) g C) (hCcomp : IsCompact C)
    (hCne : C.Nonempty) (hBne : (relBoundary I C).Nonempty)
    {r : M} (hr : r ∈ C) (hrout : r ∉ deepest I C) :
    r ∈ relBoundary I (shavingSuperlevel (I := I) C (Metric.infDist r (relBoundary I C))) := by
  let t := Metric.infDist r (relBoundary I C)
  have htmax : t < boundaryDistanceMax I C := by
    by_contra h
    exact hrout ⟨hr, le_of_not_gt h⟩
  have hdim := (shavingSuperlevel_dim_and_deepest g hEnorm hCconv hCcomp hCne hBne htmax).1
  rcases eq_or_lt_of_le (Metric.infDist_nonneg : 0 ≤ t) with ht0 | htpos
  · have hzero : t = 0 := ht0.symm
    have heq : shavingSuperlevel (I := I) C t = C := by
      ext x
      simp only [shavingSuperlevel, hzero, mem_ofPred_eq, Metric.infDist_nonneg, and_true]
    rw [heq]
    exact ((isClosed_relBoundary hEnorm hCconv hCcomp.isClosed).mem_iff_infDist_zero hBne).2 hzero
  · refine ⟨⟨hr, le_rfl⟩, ?_⟩
    rintro ⟨N, hrN, hNsub, hN⟩
    have hNC : N ⊆ C := fun x hx => (hNsub hx).1
    have hNmax : IsEmbeddedSlice I (maxSliceDim I C) N := by rwa [hdim] at hN
    obtain ⟨U, hU, hrU, hUCN⟩ := maxSlice_eq_near hEnorm hCconv hNmax hNC hrN
    obtain ⟨y, hyU, hylt⟩ := exists_mem_isOpen_infDist_lt g hEnorm hCconv hCcomp hBne hr htpos hU hrU
    have hyN : y ∈ U ∩ N := by rwa [← hUCN]
    exact (not_le_of_gt hylt) (hNsub hyN.2).2

theorem shavingSuperlevel_separator (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hCconv : IsTotallyConvex (I := I) g C) {r : M} (hr : r ∈ C)
    (hrout : r ∉ deepest I C) :
    let D := shavingSuperlevel (I := I) C (Metric.infDist r (relBoundary I C))
    IsCompact D ∧ IsTotallyConvex (I := I) g D ∧ r ∈ relBoundary I D ∧
      deepest I C ⊆ maxSliceLocus I D := by
  have hBne : (relBoundary I C).Nonempty := by
    rcases eq_empty_or_nonempty (relBoundary I C) with hB | hB
    · exact (hrout (by rwa [deepest_eq_self_of_relBoundary_eq_empty hCne hB])).elim
    · exact hB
  have htmax : Metric.infDist r (relBoundary I C) < boundaryDistanceMax I C := by
    by_contra h
    exact hrout ⟨hr, le_of_not_gt h⟩
  refine ⟨?_, hconc C hCcomp hCne hCconv hBne _,
    mem_relBoundary_shavingSuperlevel g hEnorm hCconv hCcomp hCne hBne hr hrout,
    (shavingSuperlevel_dim_and_deepest g hEnorm hCconv hCcomp hCne hBne htmax).2⟩
  exact hCcomp.inter_right (isClosed_le continuous_const (Metric.continuous_infDist_pt _))

theorem shavingSequence_separator (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) (hconc : ShavingConcavity (I := I) g)
    {C : Set M} (hCcomp : IsCompact C) (hCne : C.Nonempty)
    (hCconv : IsTotallyConvex (I := I) g C) {r : M} (hr : r ∈ C)
    {n : ℕ} (hrout : r ∉ shavingSequence I C n) :
    ∃ k < n,
      let D := shavingSuperlevel (I := I) (shavingSequence I C k)
        (Metric.infDist r (relBoundary I (shavingSequence I C k)))
      IsCompact D ∧ IsTotallyConvex (I := I) g D ∧ r ∈ relBoundary I D ∧
        shavingSequence I C n ⊆ maxSliceLocus I D := by
  obtain ⟨k, hkn, hrk, hrkout⟩ := exists_shavingSequence_exit hr hrout
  have hk := shavingSequence_spec hconc hCcomp hCne hCconv k
  obtain ⟨hcomp, hconv, hrB, hdeep⟩ :=
    shavingSuperlevel_separator g hEnorm hconc hk.1 hk.2.1 hk.2.2 hrk hrkout
  exact ⟨k, hkn, hcomp, hconv, hrB,
    (shavingSequence_antitone I C (Nat.succ_le_of_lt hkn)).trans hdeep⟩

theorem exists_soul_shavingSequence [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M)) (p : M) :
    ∃ n ≤ Module.finrank ℝ E,
      let S := shavingSequence I (rayBusemannSublevel p 1) n
      S.Nonempty ∧ IsCompact S ∧ IsTotallyConvex (I := I) g S ∧
        relBoundary I S = ∅ ∧ maxSliceDim I S < Module.finrank ℝ E := by
  let C := rayBusemannSublevel p 1
  have hcomp : IsCompact C := isCompact_rayBusemannSublevel g hEnorm hsec p 1
  have hne : C.Nonempty := ⟨p, self_mem_rayBusemannSublevel p zero_le_one⟩
  have hconv : IsTotallyConvex (I := I) g C := isTotallyConvex_rayBusemannSublevel g hEnorm hsec p 1
  have hconc := shavingConcavity_of_sec_nonneg' g hEnorm hsec
  obtain ⟨n, hn, hterm⟩ := exists_shavingSequence_terminal g hEnorm hconc hcomp hne hconv
  have hBne : (relBoundary I C).Nonempty := relBoundary_rayBusemannSublevel_nonempty g hEnorm hsec p one_pos
  have hnpos : 1 ≤ n := by
    apply Nat.one_le_iff_ne_zero.2
    intro hnzero
    subst n
    exact hBne.ne_empty hterm
  have hspec := shavingSequence_spec hconc hcomp hne hconv n
  have hdim : maxSliceDim I C = Module.finrank ℝ E := maxSliceDim_rayBusemannSublevel p one_pos
  refine ⟨n, by rwa [hdim] at hn, hspec.2.1, hspec.1, hspec.2.2, hterm, ?_⟩
  have hlt := (maxSliceDim_mono (I := I) (shavingSequence_antitone I C hnpos)).trans_lt
    (maxSliceDim_deepest_lt g hEnorm hconv hcomp hne hBne)
  simpa only [shavingSequence_zero, hdim] using hlt

end Geometry

end DifferentialGeometry.Geometry.Topology
