import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.FiniteTime.Solution
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.MaximalTime

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]
variable [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]

structure FlowTo (g0 : SmoothRiemannianMetric I M) (T : Real) where
  hT : 0 < T
  S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT)
  isSol : IsSolutionOn (I := I) S
  start : S.family.metric 0 = g0
  joint : ∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
    ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
      (fun p : Real × M =>
        Integral.Measure.chartGramMatrix (I := I) (S.family.metric p.1) x0 p.2 i j)
      (Ico 0 T ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet)
  pde : ∀ t ∈ Ico 0 T, ∀ x : M, ∀ v w : TangentSpace I x,
    HasDerivWithinAt (fun s : Real => (S.family.metric s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I) (S.family.metric t) x v w) (Ici 0) t

private structure FlowCover
    (g0 : SmoothRiemannianMetric I M) (t : Real) where
  T : Real
  flow : FlowTo (I := I) (M := M) g0 T
  lt_end : t < T

omit [SigmaCompactSpace M] in
theorem flow_to_seed (g0 : SmoothRiemannianMetric I M) :
    ∃ T : Real, Nonempty (FlowTo (I := I) (M := M) g0 T) := by
  rcases ricci_flow_short_time_existence (I := I) (M := M) g0 with
    ⟨T, hT, g, hstart, hjoint, hpde⟩
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen 0 T hT) :=
    { base := { metric := g } }
  have hS : IsSolutionOn (I := I) S :=
    solutionOn_of_joint (I := I) (M := M) hT g hjoint hpde
  refine ⟨T, ⟨⟨hT, S, hS, ?_, ?_, ?_⟩⟩⟩
  · simpa [S] using hstart
  · simpa [S] using hjoint
  · simpa [S] using hpde

omit [SigmaCompactSpace M] in
theorem flow_to_agree
    {g0 : SmoothRiemannianMetric I M} {T U : Real}
    (P : FlowTo (I := I) (M := M) g0 T)
    (Q : FlowTo (I := I) (M := M) g0 U) :
    ∀ t ∈ Ico 0 (min T U), P.S.family.metric t = Q.S.family.metric t := by
  have hTU : 0 < min T U := lt_min P.hT Q.hT
  apply ricci_flow_forward_unique (I := I) (M := M)
    P.S.family.metric Q.S.family.metric hTU
  · intro x0 i j
    exact (P.joint x0 i j).mono fun p hp =>
      ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 (min_le_left T U)⟩, hp.2⟩
  · intro x0 i j
    exact (Q.joint x0 i j).mono fun p hp =>
      ⟨⟨hp.1.1, lt_of_lt_of_le hp.1.2 (min_le_right T U)⟩, hp.2⟩
  · intro t ht x v w
    exact P.pde t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left T U)⟩ x v w
  · intro t ht x v w
    exact Q.pde t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right T U)⟩ x v w
  · exact P.start.trans Q.start.symm

omit [SigmaCompactSpace M] in
theorem flow_to_eq
    {g0 : SmoothRiemannianMetric I M} {T U t : Real}
    (P : FlowTo (I := I) (M := M) g0 T)
    (Q : FlowTo (I := I) (M := M) g0 U)
    (h0 : 0 ≤ t) (hT : t < T) (hU : t < U) :
    P.S.family.metric t = Q.S.family.metric t :=
  flow_to_agree (I := I) (M := M) P Q t ⟨h0, lt_min hT hU⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless] in
theorem flow_to_extend
    {g0 : SmoothRiemannianMetric I M} {T : Real}
    (P : FlowTo (I := I) (M := M) g0 T)
    (hext : ExtendsPastEndpoint (I := I) P.hT P.S) :
    ∃ eps : Real, 0 < eps ∧
      Nonempty (FlowTo (I := I) (M := M) g0 (T + eps)) := by
  rcases hext with ⟨eps, heps, hwide, Shat, hShat, hagree⟩
  have hmetric : ∀ t ∈ Ico 0 T,
      P.S.family.metric t = Shat.family.metric t := by
    intro t ht
    exact (hagree t ht).1
  have hstart : Shat.family.metric 0 = g0 := by
    exact (hmetric 0 ⟨le_rfl, P.hT⟩).symm.trans P.start
  have hjoint : ∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I)
            (Shat.family.metric p.1) x0 p.2 i j)
        (Ico 0 (T + eps) ×ˢ
          (trivializationAt E (TangentSpace I) x0).baseSet) := by
    intro x0 i j
    apply contMDiffOn_of_locally_contMDiffOn
    intro p hp
    by_cases hpt : p.1 < T
    · refine ⟨Iio T ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet,
        isOpen_Iio.prod (trivializationAt E (TangentSpace I) x0).open_baseSet,
        ⟨hpt, hp.2⟩, ?_⟩
      refine ((P.joint x0 i j).mono ?_).congr ?_
      · intro q hq
        exact ⟨⟨hq.1.1.1, hq.2.1⟩, hq.2.2⟩
      · intro q hq
        rw [hmetric q.1 ⟨hq.1.1.1, hq.2.1⟩]
    · have hTp : T ≤ p.1 := le_of_not_gt hpt
      refine ⟨Ioo 0 (T + eps) ×ˢ
          (trivializationAt E (TangentSpace I) x0).baseSet,
        isOpen_Ioo.prod (trivializationAt E (TangentSpace I) x0).open_baseSet,
        ⟨⟨lt_of_lt_of_le P.hT hTp, hp.1.2⟩, hp.2⟩, ?_⟩
      simpa using
        ((chartGram_smooth_of_soln (I := I) (M := M) hShat x0 i j).mono
          Set.inter_subset_right)
  have hpde : ∀ t ∈ Ico 0 (T + eps), ∀ x : M,
      ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (Shat.family.metric s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (Shat.family.metric t) x v w)
        (Ici 0) t := by
    intro t ht x v w
    by_cases htT : t < T
    · have ht_old : t ∈ Ico 0 T := ⟨ht.1, htT⟩
      have heq :
          (fun s : Real => (Shat.family.metric s).inner x v w) =ᶠ[nhdsWithin t (Ici 0)]
            (fun s : Real => (P.S.family.metric s).inner x v w) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT)] with s hs0 hsT
        exact congrArg (fun g : SmoothRiemannianMetric I M => g.inner x v w)
          (hmetric s ⟨hs0, hsT⟩).symm
      have heq_t : (Shat.family.metric t).inner x v w =
          (P.S.family.metric t).inner x v w :=
        congrArg (fun g : SmoothRiemannianMetric I M => g.inner x v w)
          (hmetric t ht_old).symm
      have htransport :=
        (P.pde t ht_old x v w).congr_of_eventuallyEq heq heq_t
      rw [hmetric t ht_old] at htransport
      exact htransport
    · have ht_pos : 0 < t := lt_of_lt_of_le P.hT (le_of_not_gt htT)
      simpa using
        ricciFlowPDE_Ici_of_soln (I := I) (M := M) hShat t
          ⟨le_of_lt ht_pos, ht.2⟩ x v w
  refine ⟨eps, heps, ⟨⟨hwide, Shat, hShat, hstart, hjoint, hpde⟩⟩⟩

omit [SigmaCompactSpace M] in
theorem exists_max_flow
    [Nonempty M]
    (g0 : SmoothRiemannianMetric I M)
    (hdim : Module.finrank Real E = 3)
    (hscalar_pos : ∀ x : M,
      0 < metricScalarAt (I := I) (M := M) g0 x) :
    ∃ omega : Real, ∃ h0omega : 0 < omega,
      ∃ Smax : SolutionOn (I := I) (M := M)
          (RealTimeInterval.closedOpen 0 omega h0omega),
        IsSolutionOn (I := I) Smax ∧
          Smax.family.metric 0 = g0 ∧
          IsMaximalAtEndpoint (I := I) h0omega Smax := by
  classical
  let ends : Set Real :=
    {T : Real | Nonempty (FlowTo (I := I) (M := M) g0 T)}
  rcases flow_to_seed (I := I) (M := M) g0 with ⟨T0, hseed⟩
  let P0 : FlowTo (I := I) (M := M) g0 T0 := Classical.choice hseed
  have hT0_mem : T0 ∈ ends := by
    change Nonempty (FlowTo (I := I) (M := M) g0 T0)
    exact hseed
  have hends_nonempty : ends.Nonempty := ⟨T0, hT0_mem⟩
  have hscalar_cont : Continuous (fun x : M =>
      metricScalarAt (I := I) (M := M) g0 x) := by
    simpa using (metricScalar_smooth (I := I) (M := M) g0).continuous
  rcases exists_initialScalarMinimum_of_continuous
      (M := M) (fun _t x => metricScalarAt (I := I) (M := M) g0 x)
      (by simpa using hscalar_cont) with
    ⟨c0, hc0⟩
  have hends_bdd : BddAbove ends := by
    refine ⟨3 / (2 * c0), ?_⟩
    intro T hT
    change Nonempty (FlowTo (I := I) (M := M) g0 T) at hT
    let P : FlowTo (I := I) (M := M) g0 T := Classical.choice hT
    exact flow_end_le (I := I) (M := M) g0 hdim hscalar_pos P.hT hc0
      P.S P.isSol P.start
  let omega : Real := sSup ends
  have hT0_le : T0 ≤ omega := by
    dsimp [omega]
    exact le_csSup hends_bdd hT0_mem
  have h0omega : 0 < omega := lt_of_lt_of_le P0.hT hT0_le
  have hcover : ∀ t : Real, t ∈ Ico 0 omega →
      Nonempty (FlowCover (I := I) (M := M) g0 t) := by
    intro t ht
    have ht_sup : t < sSup ends := by simpa [omega] using ht.2
    rcases exists_lt_of_lt_csSup hends_nonempty ht_sup with ⟨T, hT, htT⟩
    change Nonempty (FlowTo (I := I) (M := M) g0 T) at hT
    rcases hT with ⟨P⟩
    exact ⟨⟨T, P, htT⟩⟩
  let cover (t : Real) (ht : t ∈ Ico 0 omega) :
      FlowCover (I := I) (M := M) g0 t :=
    Classical.choice (hcover t ht)
  let gmax : Real → SmoothRiemannianMetric I M := fun t =>
    if ht : t ∈ Ico 0 omega then
      (cover t ht).flow.S.family.metric t
    else g0
  have hmax_eq : ∀ (t : Real) (ht : t ∈ Ico 0 omega),
      ∀ {U : Real} (Q : FlowTo (I := I) (M := M) g0 U), t < U →
        gmax t = Q.S.family.metric t := by
    intro t ht U Q htU
    simp only [gmax, dif_pos ht]
    exact flow_to_eq (I := I) (M := M) (cover t ht).flow Q ht.1
      (cover t ht).lt_end htU
  have hstart : gmax 0 = g0 := by
    have hzero : (0 : Real) ∈ Ico 0 omega := ⟨le_rfl, h0omega⟩
    simp only [gmax, dif_pos hzero]
    exact (cover 0 hzero).flow.start
  have hjoint : ∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          Integral.Measure.chartGramMatrix (I := I) (gmax p.1) x0 p.2 i j)
        (Ico 0 omega ×ˢ
          (trivializationAt E (TangentSpace I) x0).baseSet) := by
    intro x0 i j
    apply contMDiffOn_of_locally_contMDiffOn
    intro p hp
    let C : FlowCover (I := I) (M := M) g0 p.1 := cover p.1 hp.1
    refine ⟨Iio C.T ×ˢ (trivializationAt E (TangentSpace I) x0).baseSet,
      isOpen_Iio.prod (trivializationAt E (TangentSpace I) x0).open_baseSet,
      ⟨C.lt_end, hp.2⟩, ?_⟩
    refine ((C.flow.joint x0 i j).mono ?_).congr ?_
    · intro q hq
      exact ⟨⟨hq.1.1.1, hq.2.1⟩, hq.2.2⟩
    · intro q hq
      rw [hmax_eq q.1 hq.1.1 C.flow hq.2.1]
  have hpde : ∀ t ∈ Ico 0 omega, ∀ x : M,
      ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (gmax s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (gmax t) x v w)
        (Ici 0) t := by
    intro t ht x v w
    let C : FlowCover (I := I) (M := M) g0 t := cover t ht
    have ht_bound : t < min omega C.T := lt_min ht.2 C.lt_end
    have heq : (fun s : Real => (gmax s).inner x v w) =ᶠ[nhdsWithin t (Ici 0)]
        (fun s : Real => (C.flow.S.family.metric s).inner x v w) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht_bound)] with s hs0 hs_bound
      have hs_omega : s < omega :=
        lt_of_lt_of_le hs_bound (min_le_left omega C.T)
      have hs_C : s < C.T :=
        lt_of_lt_of_le hs_bound (min_le_right omega C.T)
      exact congrArg (fun g : SmoothRiemannianMetric I M => g.inner x v w)
        (hmax_eq s ⟨hs0, hs_omega⟩ C.flow hs_C)
    have heq_t : (gmax t).inner x v w =
        (C.flow.S.family.metric t).inner x v w :=
      congrArg (fun g : SmoothRiemannianMetric I M => g.inner x v w)
        (hmax_eq t ht C.flow C.lt_end)
    have htransport :=
      (C.flow.pde t ⟨ht.1, C.lt_end⟩ x v w).congr_of_eventuallyEq heq heq_t
    rw [← hmax_eq t ht C.flow C.lt_end] at htransport
    exact htransport
  let Smax : SolutionOn (I := I) (M := M)
      (RealTimeInterval.closedOpen 0 omega h0omega) :=
    { base := { metric := gmax } }
  have hSmax : IsSolutionOn (I := I) Smax := by
    simpa [Smax] using
      solutionOn_of_joint (I := I) (M := M) h0omega gmax hjoint hpde
  have hstart_max : Smax.family.metric 0 = g0 := by
    simpa [Smax] using hstart
  have hjoint_max : ∀ (x0 : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M => Integral.Measure.chartGramMatrix (I := I)
          (Smax.family.metric p.1) x0 p.2 i j)
        (Ico 0 omega ×ˢ
          (trivializationAt E (TangentSpace I) x0).baseSet) := by
    simpa [Smax] using hjoint
  have hpde_max : ∀ t ∈ Ico 0 omega, ∀ x : M,
      ∀ v w : TangentSpace I x,
      HasDerivWithinAt (fun s : Real => (Smax.family.metric s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (Smax.family.metric t) x v w)
        (Ici 0) t := by
    simpa [Smax] using hpde
  let Pmax : FlowTo (I := I) (M := M) g0 omega :=
    ⟨h0omega, Smax, hSmax, hstart_max, hjoint_max, hpde_max⟩
  have hmaximal : IsMaximalAtEndpoint (I := I) h0omega Smax := by
    intro hext
    have hext_P : ExtendsPastEndpoint (I := I) Pmax.hT Pmax.S := by
      simpa [Pmax] using hext
    rcases flow_to_extend (I := I) (M := M) Pmax hext_P with
      ⟨eps, heps, hlong⟩
    have hlong_mem : omega + eps ∈ ends := by
      change Nonempty (FlowTo (I := I) (M := M) g0 (omega + eps))
      exact hlong
    have hle : omega + eps ≤ omega := by
      simpa [omega] using le_csSup hends_bdd hlong_mem
    linarith
  exact ⟨omega, h0omega, Smax, hSmax, hstart_max, hmaximal⟩

end DifferentialGeometry.PDE.RicciFlow
