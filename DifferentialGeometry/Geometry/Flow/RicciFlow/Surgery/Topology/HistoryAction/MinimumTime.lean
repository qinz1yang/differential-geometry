import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryAction.Density
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Minimum.Continuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.TimeExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.WeakBarrier
import DifferentialGeometry.Analysis.Calculus.UpperSupport.Monotonicity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.TimeRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Constant
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryPartition

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal NNReal Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_lipschitz_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
    (last : Fin (H.eventCount + 1)) (first : ℝ → Fin (H.eventCount + 1))
    (hle : ∀ b, first b ≤ last)
    (f : ∀ b, (j : H.StageInterval (first b) last) → X → (H.stage j.val).Carrier)
    (hf : ∀ b j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f b j))
    (hinj : ∀ b j, Function.Injective (f b j))
    (hcross : ∀ b (i : Fin H.eventCount) (hi : first b ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f b ⟨i.castSucc,hi,i.castSucc_le_succ.trans hl⟩ z)
        (f b ⟨i.succ,hi.trans i.castSucc_le_succ,hl⟩ z))
    {T b₀ b₁ : ℝ} (hb₀ : 0 < b₀)
    (hupper : T ∈ H.stageDomain last)
    (hlower : ∀ b ∈ Icc b₀ b₁, T-b^2 ∈ H.stageDomain (first b))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 b₁, T-t^2 ∈ J)
    (hreg : ∀ t ∈ Ioo 0 b₁, T-t^2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (K : Set X) (hK : IsCompact K) (g : SmoothRiemannianMetric ThreeModel X)
    {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ b ∈ Icc b₀ b₁, ∀ j : H.StageInterval (first b) last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f b j) (hf b j))
    (hcompare : ∀ t ∈ Ioo 0 b₁, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ*g.inner z w w ≤ (S.base.metric (T-t^2)).inner z w w)
    (hscalar : ∀ b ∈ Icc b₀ b₁, ∀ j : H.StageInterval (first b) last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (p : (H.stage last).Carrier) (hpoint : ∀ b ∈ Icc b₀ b₁, f b ⟨last,hle b,le_rfl⟩ x = p)
    (hx : x ∈ interior K) (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (γ : ℝ → ℝ → X) (hγ : ∀ b ∈ Icc b₀ b₁, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (γ b))
    (hstart : ∀ b ∈ Icc b₀ b₁, γ b 0 = x)
    (hact : ∀ b ∈ Icc b₀ b₁, lRegularizedAction S T (γ b) 0 b <
      μ*r^2/(2*b)-(2*B/3)*b^3) :
    ∃ m : ℝ → ℝ, (∃ C : ℝ≥0, LipschitzOnWith C m (Icc b₀ b₁)) ∧
      ContinuousOn (fun b => 2*b*m b-6*b^2) (Icc b₀ b₁) ∧
      ∀ b ∈ Icc b₀ b₁, ∃ η : ℝ → X,
        ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧ MapsTo η (Icc 0 b) K ∧
        m b = lRegularizedAction S T η 0 b ∧
        m b ≤ lRegularizedAction S T (γ b) 0 b ∧
        (m b : WithTop ℝ) ∈ H.regularizedActionValues (first b) last (hle b) T B 0 b p
          (f b ⟨first b,le_rfl,hle b⟩ (η b)) ∧
        H.regularizedCost (first b) last (hle b) T B 0 b p
          (f b ⟨first b,le_rfl,hle b⟩ (η b)) = (m b : WithTop ℝ) ∧
        ∀ q : (H.stage (first b)).Carrier,
          (m b : WithTop ℝ) ≤ H.regularizedCost (first b) last (hle b) T B 0 b p q := by
  classical
  have hfamily (b : ℝ) (hb : b ∈ Icc b₀ b₁) :=
    H.exists_regularizedCost_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
      (first b) last (hle b) (f b) (hf b) (hinj b) K hK (hcross b)
      le_rfl (hb₀.trans_le hb.1) (by simpa only [zero_pow two_ne_zero,sub_zero] using hupper)
      (hlower b hb) S hS J hJ (fun t ht => hclock t ⟨ht.1,ht.2.trans hb.2⟩)
      (fun t ht => hreg t ⟨ht.1,ht.2.trans_le hb.2⟩) hsmooth g hμ hr (hmetric b hb)
      (fun t ht => hcompare t ⟨ht.1,ht.2.trans_le hb.2⟩) (hscalar b hb) x hx hfront
      (γ b) (hγ b hb) (hstart b hb) (by simpa only [sub_zero,zero_pow (by norm_num : 3≠0)] using hact b hb)
  choose η hη hη0 hηK hηact hηmem hηcost hηmin using hfamily
  let ηall : ℝ → ℝ → X := fun b => if hb : b ∈ Icc b₀ b₁ then η b hb else fun _ => x
  have heta (b : ℝ) (hb : b ∈ Icc b₀ b₁) : ηall b = η b hb := dif_pos hb
  let m := fun b => lRegularizedAction S T (ηall b) 0 b
  have hminall : ∀ b ∈ Icc b₀ b₁, ∀ δ : ℝ → X,
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 δ → δ 0 = x →
      lRegularizedAction S T (ηall b) 0 b ≤ lRegularizedAction S T δ 0 b := by
    intro b hb δ hδ hδ0
    have hm := H.action_mem_regularizedC1ActionValues_of_common_curve (first b) last (hle b)
      (f b) (hf b) (hcross b) S hS T le_rfl (hb₀.trans_le hb.1).le
      (by simpa only [zero_pow two_ne_zero,sub_zero] using
        (show T ∈ Icc (H.time last) (H.stageEndTime last) from
          ⟨H.time_le_of_mem_stageDomain hupper,H.le_stageEndTime_of_mem_stageDomain hupper⟩))
      (hlower b hb) (fun t ht => hJ (hclock t ⟨ht.1,ht.2.trans hb.2⟩)) (hmetric b hb) δ hδ
    have hmAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
      (first b) last (hle b) (hscalar b hb) _ _ hm
    have hlecost := H.regularizedCost_le_of_competitor (first b) last (hle b) T B 0 b
      _ _ hmAC
    have hbound := (hηmin b hb (f b ⟨first b,le_rfl,hle b⟩ (δ b))).trans
      (by simpa only [hδ0] using hlecost)
    rw [hηcost b hb] at hbound
    rw [heta b hb]
    exact WithTop.coe_le_coe.mp hbound
  let jlast : H.StageInterval (first b₀) last := ⟨last,hle b₀,le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f b₀ jlast) :=
    .of_continuous_injective_isOpenMap (hf b₀ jlast).contMDiff.continuous (hinj b₀ jlast) (hf b₀ jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  obtain ⟨C,hC⟩ := exists_lipschitzOnWith_action_of_compact_free_endpoint_minimizers S hS T hb₀
    (fun t ht => hJ (hclock t ht)) x ηall K hK
    (fun b hb => by rw [heta b hb]; exact hη b hb)
    (fun b hb => by rw [heta b hb]; exact hη0 b hb)
    (fun b hb => by rw [heta b hb]; exact hηK b hb) hminall
  refine ⟨m,⟨C,hC⟩,?_,?_⟩
  · exact ((continuousOn_const.mul continuousOn_id).mul hC.continuousOn).sub
      (continuousOn_const.mul (continuousOn_id.pow 2))
  · intro b hb
    refine ⟨η b hb,hη b hb,hη0 b hb,hηK b hb,?_,?_,?_,?_,?_⟩
    · simp only [m,heta b hb]
    · simpa only [m,heta b hb] using hηact b hb
    · simpa only [m,heta b hb,hpoint b hb] using hηmem b hb
    · simpa only [m,heta b hb,hpoint b hb] using hηcost b hb
    · intro q
      have hbound := hηmin b hb q
      rw [hηcost b hb] at hbound
      simpa only [m,heta b hb,hpoint b hb] using hbound


private theorem exists_initial_stages_of_backward_clock
    (H : ObservedHistory.{u}) (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    {T bmax : ℝ} (hupper : T ∈ H.stageDomain last)
    (hlower : T - bmax ^ 2 ∈ H.stageDomain first₀) :
    ∃ first : ℝ → Fin (H.eventCount + 1),
      (∀ b, first₀ ≤ first b) ∧ (∀ b, first b ≤ last) ∧
      ∀ b ∈ Icc 0 bmax, T - b ^ 2 ∈ H.stageDomain (first b) := by
  have hTrange := H.stageDomain_subset last hupper
  have hlrange := H.stageDomain_subset first₀ hlower
  have hclock (b : ℝ) (hb : b ∈ Icc 0 bmax) : T - b ^ 2 ∈ Icc 0 H.horizon := by
    have hsq := pow_le_pow_left₀ hb.1 hb.2 2
    exact ⟨by linarith [hlrange.1],(sub_le_self _ (sq_nonneg b)).trans hTrange.2⟩
  let point := fun b hb => (⟨T - b ^ 2,hclock b hb⟩ : Icc (0 : ℝ) H.horizon)
  let first := fun b => if hb : b ∈ Icc 0 bmax then H.activeStage (point b hb) else last
  refine ⟨first,?_,?_,?_⟩
  · intro b
    dsimp only [first]
    split_ifs with hb
    · exact H.le_activeStage (point b hb) first₀
        ((H.time_le_of_mem_stageDomain hlower).trans (sub_le_sub_left
          (pow_le_pow_left₀ hb.1 hb.2 2) T))
    · exact hle
  · intro b
    dsimp only [first]
    split_ifs with hb
    · have hpoint : point b hb ≤ (⟨T,hTrange⟩ : Icc (0 : ℝ) H.horizon) :=
        sub_le_self _ (sq_nonneg b)
      have hh := H.activeStage_mono hpoint
      rwa [(H.mem_stageDomain_iff ⟨T,hTrange⟩ last).mp hupper] at hh
    · exact le_rfl
  · intro b hb
    change T - b ^ 2 ∈ H.stageDomain (if h : b ∈ Icc 0 bmax then H.activeStage (point b h) else last)
    rw [dif_pos hb]
    exact H.activeStage_mem (point b hb)


theorem exists_short_negative_continuous_spatial_minimum_of_joint_history_metric
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc,hi,i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ,hi.trans i.castSucc_le_succ,hl⟩ z))
    {T bmax : ℝ} (hbmax : 0 < bmax)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - bmax ^ 2 ∈ H.stageDomain first₀)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 bmax, T-t^2 ∈ J)
    (hreg : ∀ t ∈ Ioo 0 bmax, T-t^2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (K : Set X) (hK : IsCompact K) (B : ℝ)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (hx : x ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bmax ∧ ∀ b₀ : ℝ, 0 < b₀ → b₀ ≤ δ →
      ∃ (first : ℝ → Fin (H.eventCount+1)) (hfirst : ∀ b, first₀ ≤ first b) (hlast : ∀ b, first b ≤ last)
        (m : ℝ → ℝ),
        (∀ b ∈ Icc 0 bmax, T-b^2 ∈ H.stageDomain (first b)) ∧
        (∃ C : ℝ≥0, LipschitzOnWith C m (Icc b₀ δ)) ∧
        ContinuousOn (fun b => 2*b*m b-6*b^2) (Icc b₀ δ) ∧
        ∀ b ∈ Icc b₀ δ, 2*b*m b-6*b^2 < 0 ∧
          ∃ η : ℝ → X, ContMDiff 𝓘(ℝ,ℝ) ThreeModel 1 η ∧ η 0=x ∧ MapsTo η (Icc 0 b) K ∧
            m b = lRegularizedAction S T η 0 b ∧
            (m b : WithTop ℝ) ∈ H.regularizedActionValues (first b) last (hlast b) T B 0 b
              (f ⟨last,hle,le_rfl⟩ x)
              (f ⟨first b,hfirst b,hlast b⟩ (η b)) ∧
            H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last,hle,le_rfl⟩ x)
              (f ⟨first b,hfirst b,hlast b⟩ (η b)) = (m b : WithTop ℝ) ∧
            ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
              H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last,hle,le_rfl⟩ x) q := by
  obtain ⟨μ,r,δ,hμ,hr,hδ,hδmax,hcompare,hfront,hseed⟩ :=
    exists_lRegularizedAction_const_lt_compact_barrier S hS T B hbmax
      (fun t ht => hJ (hclock t ht)) x K hK hx
  refine ⟨δ,hδ,hδmax,?_⟩
  intro b₀ hb₀ hb₀δ
  obtain ⟨first,hfirst,hlast,hfirstclock⟩ := exists_initial_stages_of_backward_clock H first₀ last hle hupper hlower
  let fb := fun b (j : H.StageInterval (first b) last) =>
    f ⟨j.val,(hfirst b).trans j.property.1,j.property.2⟩
  let hfb := fun b (j : H.StageInterval (first b) last) =>
    hf ⟨j.val,(hfirst b).trans j.property.1,j.property.2⟩
  have hend (b : ℝ) (hb : b ∈ Icc b₀ δ) (j : Fin (H.eventCount+1)) :
      H.regularizedStageEnd T b j ≤ H.regularizedStageEnd T bmax j := by
    apply Real.sqrt_le_sqrt
    exact sub_le_sub_left (max_le_max_right (H.time j)
      (sub_le_sub_left (pow_le_pow_left₀ (hb₀.trans_le hb.1).le (hb.2.trans hδmax) 2) T)) T
  have hmet : ∀ b ∈ Icc b₀ δ, ∀ j : H.StageInterval (first b) last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (fb b j) (hfb b j) := by
    intro b hb j t ht
    exact hmetric ⟨j.val,(hfirst b).trans j.property.1,j.property.2⟩ t
      ⟨ht.1,ht.2.trans_le (hend b hb j.val)⟩
  obtain ⟨m,hLip,hCont,hm⟩ := H.exists_lipschitz_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
    last first hlast fb hfb (fun b j => hinj _)
    (fun b i hi hl z => hcross i ((hfirst b).trans hi) hl z) hb₀ hupper
    (fun b hb => hfirstclock b ⟨(hb₀.trans_le hb.1).le,hb.2.trans hδmax⟩)
    S hS J hJ (fun t ht => hclock t ⟨ht.1,ht.2.trans hδmax⟩)
    (fun t ht => hreg t ⟨ht.1,ht.2.trans_le hδmax⟩) hsmooth K hK (S.base.metric T) hμ.le hr hmet
    (fun t ht => hcompare t ⟨ht.1.le,ht.2.le.trans hδmax⟩)
    (fun b hb j t ht => hscalar ⟨j.val,(hfirst b).trans j.property.1,j.property.2⟩ t
      ⟨ht.1,ht.2.trans_le (hend b hb j.val)⟩)
    x (f ⟨last,hle,le_rfl⟩ x) (fun _ _ => rfl) hx hfront
    (fun _ _ => x) (fun _ _ => contMDiff_const) (fun _ _ => rfl)
    (fun b hb => (hseed b ⟨hb₀.trans_le hb.1,hb.2⟩).1)
  refine ⟨first,hfirst,hlast,m,hfirstclock,hLip,hCont,?_⟩
  intro b hb
  obtain ⟨η,hη,hη0,hηK,hval,hseedle,hmem,hcost,hmin⟩ := hm b hb
  refine ⟨?_,η,hη,hη0,hηK,hval,hmem,hcost,hmin⟩
  have hbp : 0 < b := hb₀.trans_le hb.1
  have hh := mul_le_mul_of_nonneg_left hseedle (by positivity : 0 ≤ 2*b)
  have hn := (hseed b ⟨hb₀.trans_le hb.1,hb.2⟩).2
  linarith


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal NNReal Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private theorem spatial_cost_minimum_value_eq
    (H : ObservedHistory.{u}) {j k last : Fin (H.eventCount + 1)}
    (heq : j = k) (hj : j ≤ last) (hk : k ≤ last) (T B v : ℝ) (p : (H.stage last).Carrier)
    {A C : ℝ}
    (hA : ∃ q : (H.stage j).Carrier, H.regularizedCost j last hj T B 0 v p q = (A : WithTop ℝ))
    (hAmin : ∀ q : (H.stage j).Carrier, (A : WithTop ℝ) ≤ H.regularizedCost j last hj T B 0 v p q)
    (hC : ∃ q : (H.stage k).Carrier, H.regularizedCost k last hk T B 0 v p q = (C : WithTop ℝ))
    (hCmin : ∀ q : (H.stage k).Carrier, (C : WithTop ℝ) ≤ H.regularizedCost k last hk T B 0 v p q) : A = C := by
  subst k
  obtain ⟨q, hq⟩ := hA
  obtain ⟨z, hz⟩ := hC
  have hac := hAmin z
  have hca := hCmin q
  rw [hz] at hac
  rw [hq] at hca
  exact le_antisymm (WithTop.coe_le_coe.mp hac) (WithTop.coe_le_coe.mp hca)

private theorem spatial_cost_infimum_eq
    (H : ObservedHistory.{u}) {j last : Fin (H.eventCount + 1)}
    (hj : j ≤ last) (T B v : ℝ) (p : (H.stage last).Carrier) {A : ℝ}
    (hA : ∃ q : (H.stage j).Carrier, H.regularizedCost j last hj T B 0 v p q = (A : WithTop ℝ))
    (hAmin : ∀ q : (H.stage j).Carrier, (A : WithTop ℝ) ≤ H.regularizedCost j last hj T B 0 v p q) :
    sInf (Set.range (H.regularizedCost j last hj T B 0 v p)) = (A : WithTop ℝ) := by
  obtain ⟨q, hq⟩ := hA
  have hmem : (A : WithTop ℝ) ∈ Set.range (H.regularizedCost j last hj T B 0 v p) := ⟨q, hq⟩
  have hbdd : BddBelow (Set.range (H.regularizedCost j last hj T B 0 v p)) := by
    refine ⟨(A : WithTop ℝ), ?_⟩
    rintro c ⟨z, rfl⟩
    exact hAmin z
  apply le_antisymm (csInf_le hbdd hmem)
  exact le_csInf ⟨A, hmem⟩ (by rintro c ⟨z, rfl⟩; exact hAmin z)

private theorem spatial_minimum_endpoint_transfer
    (H : ObservedHistory.{u}) {X : Type u} {first₀ last j k : Fin (H.eventCount + 1)}
    (hle : first₀ ≤ last) (heq : j = k) (hj₀ : first₀ ≤ j) (hjl : j ≤ last)
    (hk₀ : first₀ ≤ k) (hkl : k ≤ last)
    (f : (i : H.StageInterval first₀ last) → X → (H.stage i.val).Carrier)
    (T B b c : ℝ) (x y : X)
    (hmem : (c : WithTop ℝ) ∈ H.regularizedActionValues j last hjl T B 0 b
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨j, hj₀, hjl⟩ y))
    (hcost : H.regularizedCost j last hjl T B 0 b
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨j, hj₀, hjl⟩ y) = (c : WithTop ℝ))
    (hmin : ∀ q : (H.stage j).Carrier, (c : WithTop ℝ) ≤
      H.regularizedCost j last hjl T B 0 b (f ⟨last, hle, le_rfl⟩ x) q) :
    (c : WithTop ℝ) ∈ H.regularizedActionValues k last hkl T B 0 b
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨k, hk₀, hkl⟩ y) ∧
    H.regularizedCost k last hkl T B 0 b
      (f ⟨last, hle, le_rfl⟩ x) (f ⟨k, hk₀, hkl⟩ y) = (c : WithTop ℝ) ∧
    ∀ q : (H.stage k).Carrier, (c : WithTop ℝ) ≤
      H.regularizedCost k last hkl T B 0 b (f ⟨last, hle, le_rfl⟩ x) q := by
  subst k
  exact ⟨hmem, hcost, hmin⟩

variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]
theorem exists_continuous_spatial_cost_minimum_near_pole
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T bmax : ℝ} (hbmax : 0 < bmax)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - bmax ^ 2 ∈ H.stageDomain first₀)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 bmax, T-t^2 ∈ J)
    (hreg : ∀ t ∈ Ioo 0 bmax, T-t^2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (K : Set X) (hK : IsCompact K) (B : ℝ)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (hx : x ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bmax ∧
      ∃ (first : ℝ → Fin (H.eventCount + 1)) (hfirst : ∀ b, first₀ ≤ first b)
        (hlast : ∀ b, first b ≤ last) (m : ℝ → ℝ),
        (∀ b ∈ Icc 0 bmax, T-b^2 ∈ H.stageDomain (first b)) ∧
        ContinuousOn m (Ioc 0 δ) ∧
        ContinuousOn (fun b => 2*b*m b-6*b^2) (Ioc 0 δ) ∧
        ∀ b ∈ Ioc 0 δ,
          2*b*m b-6*b^2 < 0 ∧
          sInf (Set.range (H.regularizedCost (first b) last (hlast b) T B 0 b
            (f ⟨last, hle, le_rfl⟩ x))) = (m b : WithTop ℝ) ∧
          ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0=x ∧ MapsTo η (Icc 0 b) K ∧
            m b = lRegularizedAction S T η 0 b ∧
            (m b : WithTop ℝ) ∈ H.regularizedActionValues (first b) last (hlast b) T B 0 b
              (f ⟨last, hle, le_rfl⟩ x) (f ⟨first b, hfirst b, hlast b⟩ (η b)) ∧
            H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x)
              (f ⟨first b, hfirst b, hlast b⟩ (η b)) = (m b : WithTop ℝ) ∧
            ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
              H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x) q := by
  classical
  obtain ⟨δ, hδ, hδmax, hrows⟩ := H.exists_short_negative_continuous_spatial_minimum_of_joint_history_metric
    first₀ last hle f hf hinj hcross hbmax hupper hlower S hS J hJ hclock hreg hsmooth
      K hK B hmetric hscalar x hx
  choose firstRow hfirstRow hlastRow value hclockRow hLipRow hContRow hdata using hrows
  let a₀ := δ/2
  have ha₀ : 0 < a₀ := half_pos hδ
  have ha₀δ : a₀ ≤ δ := by dsimp [a₀]; linarith
  let first := firstRow a₀ ha₀ ha₀δ
  let hfirst := hfirstRow a₀ ha₀ ha₀δ
  let hlast := hlastRow a₀ ha₀ ha₀δ
  have hfirstclock : ∀ b ∈ Icc 0 bmax, T-b^2 ∈ H.stageDomain (first b) :=
    hclockRow a₀ ha₀ ha₀δ
  let m := fun b => if hb : b ∈ Ioc 0 δ then value (b/2) (half_pos hb.1) (by linarith [hb.2]) b else 0
  have hroweq (a b : ℝ) (ha : 0 < a) (haδ : a ≤ δ) (hb : b ∈ Icc a δ) :
      firstRow a ha haδ b = first b := by
    have hleft := hclockRow a ha haδ b ⟨ha.le.trans hb.1, hb.2.trans hδmax⟩
    have hright := hfirstclock b ⟨ha.le.trans hb.1, hb.2.trans hδmax⟩
    exact H.pairwise_disjoint_stageDomain.eq (Set.not_disjoint_iff.mpr ⟨T-b^2, hleft, hright⟩)
  have hvaluesEq (a c b : ℝ) (ha : 0 < a) (haδ : a ≤ δ) (hc : 0 < c) (hcδ : c ≤ δ)
      (hbA : b ∈ Icc a δ) (hbC : b ∈ Icc c δ) : value a ha haδ b = value c hc hcδ b := by
    obtain ⟨_, ηA, _, _, _, _, _, hcostA, hminA⟩ := hdata a ha haδ b hbA
    obtain ⟨_, ηC, _, _, _, _, _, hcostC, hminC⟩ := hdata c hc hcδ b hbC
    exact spatial_cost_minimum_value_eq H ((hroweq a b ha haδ hbA).trans (hroweq c b hc hcδ hbC).symm)
      _ _ T B b (f ⟨last, hle, le_rfl⟩ x) ⟨_, hcostA⟩ hminA ⟨_, hcostC⟩ hminC
  have hmrow (a b : ℝ) (ha : 0 < a) (haδ : a ≤ δ) (hb : b ∈ Icc a δ) :
      m b = value a ha haδ b := by
    have hb0 : 0 < b := ha.trans_le hb.1
    dsimp only [m]
    rw [dif_pos ⟨hb0, hb.2⟩]
    exact hvaluesEq (b/2) a b (half_pos hb0) (by linarith [hb.2]) ha haδ
      ⟨by linarith, hb.2⟩ hb
  have hmcont : ContinuousOn m (Ioc 0 δ) := by
    intro b hb
    let a := b/2
    have ha : 0 < a := half_pos hb.1
    have haδ : a ≤ δ := by dsimp [a]; linarith [hb.2]
    obtain ⟨C, hC⟩ := hLipRow a ha haδ
    have hbA : b ∈ Icc a δ := ⟨by dsimp [a]; linarith [hb.1], hb.2⟩
    have hnb : Icc a δ ∈ 𝓝[Ioc 0 δ] b := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (Ioi_mem_nhds (show a < b by dsimp [a]; linarith [hb.1]))] with c hc hca
      exact ⟨hca.le, hc.2⟩
    apply ((hC.continuousOn b hbA).mono_of_mem_nhdsWithin hnb).congr_of_eventuallyEq ?_
      (hmrow a b ha haδ hbA)
    filter_upwards [hnb] with c hc
    exact hmrow a c ha haδ hc
  refine ⟨δ, hδ, hδmax, first, hfirst, hlast, m, hfirstclock, hmcont, ?_, ?_⟩
  · exact ((continuousOn_const.mul continuousOn_id).mul hmcont).sub
      (continuousOn_const.mul (continuousOn_id.pow 2))
  · intro b hb
    let a := b/2
    have ha : 0 < a := half_pos hb.1
    have haδ : a ≤ δ := by dsimp [a]; linarith [hb.2]
    have hbA : b ∈ Icc a δ := ⟨by dsimp [a]; linarith [hb.1], hb.2⟩
    have heq := hroweq a b ha haδ hbA
    obtain ⟨hneg, η, hη, hη0, hηK, hval, hmem, hcost, hmin⟩ := hdata a ha haδ b hbA
    have hmval := hmrow a b ha haδ hbA
    obtain ⟨hmem', hcost', hmin'⟩ := spatial_minimum_endpoint_transfer H hle heq
      (hfirstRow a ha haδ b) (hlastRow a ha haδ b) (hfirst b) (hlast b)
      f T B b (value a ha haδ b) x (η b) hmem hcost hmin
    rw [← hmval] at hmem' hcost' hmin'
    have hval' : m b = lRegularizedAction S T η 0 b := hmval.trans hval
    exact ⟨by simpa only [hmval] using hneg,
      spatial_cost_infimum_eq H (hlast b) T B b _ ⟨_, hcost'⟩ hmin',
      η, hη, hη0, hηK, hval', hmem', hcost', hmin'⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal NNReal Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

private theorem action_le_of_spatial_cost_lower_bound
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    {T B b c : ℝ} (hb : 0 ≤ b)
    (hupper : T ∈ H.stageDomain last) (hlower : T-b^2 ∈ H.stageDomain first)
    (hclock : ∀ t ∈ Icc 0 b, T-t^2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T b j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X)
    (hmin : ∀ q : (H.stage first).Carrier, (c : WithTop ℝ) ≤
      H.regularizedCost first last hle T B 0 b (f ⟨last, hle, le_rfl⟩ x) q)
    (γ : ℝ → X) (hγ : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ) (hγ0 : γ 0 = x) :
    c ≤ lRegularizedAction S T γ 0 b := by
  have hm := H.action_mem_regularizedC1ActionValues_of_common_curve first last hle f hf hcross
    S hS T le_rfl hb (by simpa only [zero_pow two_ne_zero, sub_zero] using
      (show T ∈ Icc (H.time last) (H.stageEndTime last) from
        ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩))
    hlower hclock hmetric γ hγ
  have hmAC := H.coe_mem_regularizedActionValues_of_mem_regularizedC1ActionValues
    first last hle hscalar _ _ hm
  have hlecost := H.regularizedCost_le_of_competitor first last hle T B 0 b _ _ hmAC
  have hbound := (hmin (f ⟨first, le_rfl, hle⟩ (γ b))).trans
    (by simpa only [hγ0] using hlecost)
  exact WithTop.coe_le_coe.mp hbound


private theorem exists_free_endpoint_minimizers_of_spatial_cost_minima
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    (first : ℝ → Fin (H.eventCount + 1)) (hfirst : ∀ b, first₀ ≤ first b)
    (hlast : ∀ b, first b ≤ last)
    {T B δ : ℝ} (hupper : T ∈ H.stageDomain last)
    (hlower : ∀ b ∈ Ioc 0 δ, T-b^2 ∈ H.stageDomain (first b))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hclock : ∀ t ∈ Icc 0 δ, T-t^2 ∈ D.carrier)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (m : ℝ → ℝ)
    (hm : ∀ b ∈ Ioc 0 δ, ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      m b = lRegularizedAction S T η 0 b ∧
      ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
        H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x) q) :
    ∃ η : ℝ → ℝ → X,
      (∀ b ∈ Ioc 0 δ, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (η b)) ∧
      (∀ b ∈ Ioc 0 δ, η b 0 = x) ∧
      (∀ b ∈ Ioc 0 δ, m b = lRegularizedAction S T (η b) 0 b) ∧
      ∀ b ∈ Ioc 0 δ, ∀ γ : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 γ → γ 0 = x →
        lRegularizedAction S T (η b) 0 b ≤ lRegularizedAction S T γ 0 b := by
  classical
  choose η hη hη0 hηact hηmin using hm
  let allη := fun b => if hb : b ∈ Ioc 0 δ then η b hb else fun _ => x
  have hall (b : ℝ) (hb : b ∈ Ioc 0 δ) : allη b = η b hb := dif_pos hb
  refine ⟨allη, ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [hall b hb]
    exact hη b hb
  · intro b hb
    rw [hall b hb]
    exact hη0 b hb
  · intro b hb
    rw [hall b hb]
    exact hηact b hb
  · intro b hb γ hγ hγ0
    rw [hall b hb, ← hηact b hb]
    let fb := fun (j : H.StageInterval (first b) last) =>
      f ⟨j.val, (hfirst b).trans j.property.1, j.property.2⟩
    let hfb := fun (j : H.StageInterval (first b) last) =>
      hf ⟨j.val, (hfirst b).trans j.property.1, j.property.2⟩
    have hend (j : Fin (H.eventCount + 1)) :
        H.regularizedStageEnd T b j ≤ H.regularizedStageEnd T δ j :=
      H.regularizedStageEnd_monotoneOn T j hb.1.le (hb.1.le.trans hb.2) hb.2
    exact action_le_of_spatial_cost_lower_bound H (first b) last (hlast b) fb hfb
      (fun i hi hl z => hcross i ((hfirst b).trans hi) hl z) S hS hb.1.le hupper
      (hlower b hb) (fun t ht => hclock t ⟨ht.1, ht.2.trans hb.2⟩)
      (fun j t ht => hmetric ⟨j.val, (hfirst b).trans j.property.1, j.property.2⟩ t
        ⟨ht.1, ht.2.trans_le (hend j.val)⟩)
      (fun j t ht => hscalar ⟨j.val, (hfirst b).trans j.property.1, j.property.2⟩ t
        ⟨ht.1, ht.2.trans_le (hend j.val)⟩)
      x (hηmin b hb) γ hγ hγ0

theorem exists_time_upper_support_of_spatial_cost_minima
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : Function.Injective (f ⟨last, hle, le_rfl⟩))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    (first : ℝ → Fin (H.eventCount + 1)) (hfirst : ∀ b, first₀ ≤ first b)
    (hlast : ∀ b, first b ≤ last)
    {T B δ : ℝ} (hδ : 0 < δ) (hupper : T ∈ H.stageDomain last)
    (hlower : ∀ b ∈ Ioc 0 δ, T-b^2 ∈ H.stageDomain (first b))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hreg : ∀ t ∈ Icc 0 δ, T-t^2 ∈ D.regular)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (m : ℝ → ℝ)
    (hm : ∀ b ∈ Ioc 0 δ, ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      m b = lRegularizedAction S T η 0 b ∧
      ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
        H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x) q)
    {tau eps : ℝ} (htau : tau ∈ Ioo 0 (δ^2)) (heps : 0 < eps) :
    ∃ (phi : ℝ → ℝ) (d : ℝ),
      (∀ᶠ rho in 𝓝 tau, 2 * Real.sqrt rho * m (Real.sqrt rho) - 6*rho ≤ phi rho) ∧
      phi tau = 2 * Real.sqrt tau * m (Real.sqrt tau) - 6*tau ∧
      HasDerivAt phi d tau ∧ d ≤ eps := by
  obtain ⟨η, hη, hη0, hηact, hηmin⟩ := exists_free_endpoint_minimizers_of_spatial_cost_minima
    H first₀ last hle f hf hcross first hfirst hlast hupper hlower S hS
    (fun t ht => D.regular_subset (hreg t ht)) hmetric hscalar x m hm
  let jlast : H.StageInterval first₀ last := ⟨last, hle, le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jlast) :=
    .of_continuous_injective_isOpenMap (hf jlast).contMDiff.continuous hinj (hf jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let : PseudoMetricSpace X := _root_.TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have hsqrt (rho : ℝ) (hrho : rho ∈ Ioo 0 (δ^2)) : Real.sqrt rho ∈ Ioc 0 δ := by
    exact ⟨Real.sqrt_pos.mpr hrho.1, ((Real.sqrt_lt hrho.1.le hδ.le).mpr hrho.2).le⟩
  have hslab : Icc (T - δ^2) T ⊆ D.regular := by
    intro t ht
    have hnonneg : 0 ≤ T-t := sub_nonneg.mpr ht.2
    have hs : Real.sqrt (T-t) ∈ Icc 0 δ :=
      ⟨Real.sqrt_nonneg _, (Real.sqrt_le_left hδ.le).mpr (by linarith [ht.1])⟩
    have hh := hreg (Real.sqrt (T-t)) hs
    simpa only [Real.sq_sqrt hnonneg, sub_sub_cancel] using hh
  obtain ⟨phi, d, hbound, hcontact, hd, hde⟩ :=
    exists_time_upper_support_of_free_endpoint_minimizers S hS T (δ^2) tau htau.1 htau.2 hslab x
      (fun rho => η (Real.sqrt rho))
      (fun rho hrho => hη _ (hsqrt rho hrho))
      (fun rho hrho => hη0 _ (hsqrt rho hrho))
      (fun rho hrho => hηmin _ (hsqrt rho hrho)) eps heps
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by norm_num [ThreeSpace]
  refine ⟨phi, d, ?_, ?_, hd, hde⟩
  · filter_upwards [hbound, isOpen_Ioo.mem_nhds htau] with rho hrho hrt
    simpa only [← hηact _ (hsqrt rho hrt), hdim, show (2:ℝ)*3=6 by norm_num] using hrho
  · simpa only [← hηact _ (hsqrt tau htau), hdim, show (2:ℝ)*3=6 by norm_num] using hcontact

theorem antitoneOn_scaled_spatial_cost_minimum
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : Function.Injective (f ⟨last, hle, le_rfl⟩))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    (first : ℝ → Fin (H.eventCount + 1)) (hfirst : ∀ b, first₀ ≤ first b)
    (hlast : ∀ b, first b ≤ last)
    {T B δ : ℝ} (hδ : 0 < δ) (hupper : T ∈ H.stageDomain last)
    (hlower : ∀ b ∈ Ioc 0 δ, T-b^2 ∈ H.stageDomain (first b))
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (hreg : ∀ t ∈ Icc 0 δ, T-t^2 ∈ D.regular)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T δ j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (m : ℝ → ℝ)
    (hm : ∀ b ∈ Ioc 0 δ, ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      m b = lRegularizedAction S T η 0 b ∧
      ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
        H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x) q)
    (hcont : ContinuousOn (fun b => 2*b*m b-6*b^2) (Ioc 0 δ)) :
    AntitoneOn (fun b => 2*b*m b-6*b^2) (Ioc 0 δ) := by
  have hsqrt (rho : ℝ) (hrho : rho ∈ Ioc 0 (δ^2)) : Real.sqrt rho ∈ Ioc 0 δ :=
    ⟨Real.sqrt_pos.mpr hrho.1, (Real.sqrt_le_left hδ.le).mpr hrho.2⟩
  have hc : ContinuousOn (fun rho => 2 * Real.sqrt rho * m (Real.sqrt rho) - 6*rho)
      (Ioc 0 (δ^2)) := by
    have hh := hcont.comp Real.continuous_sqrt.continuousOn hsqrt
    apply hh.congr
    intro rho hrho
    dsimp only [Function.comp_def]
    rw [Real.sq_sqrt hrho.1.le]
  have ha : AntitoneOn (fun rho => 2 * Real.sqrt rho * m (Real.sqrt rho) - 6*rho)
      (Ioc 0 (δ^2)) := by
    apply DifferentialGeometry.antitoneOn_Ioc_of_deriv_upper_support_le_pos hc
    intro tau htau eps heps
    obtain ⟨phi, d, hbound, hcontact, hd, hde⟩ :=
      H.exists_time_upper_support_of_spatial_cost_minima first₀ last hle f hf hinj hcross
        first hfirst hlast hδ hupper hlower S hS hreg hmetric hscalar x m hm htau heps
    exact ⟨phi, d, hcontact, hbound.filter_mono nhdsWithin_le_nhds, hd.hasDerivWithinAt, hde⟩
  intro a ha₀ b hb hab
  have hasq : a^2 ∈ Ioc 0 (δ^2) := ⟨sq_pos_of_pos ha₀.1, pow_le_pow_left₀ ha₀.1.le ha₀.2 2⟩
  have hbsq : b^2 ∈ Ioc 0 (δ^2) := ⟨sq_pos_of_pos hb.1, pow_le_pow_left₀ hb.1.le hb.2 2⟩
  simpa only [Real.sqrt_sq ha₀.1.le, Real.sqrt_sq hb.1.le] using
    ha hasq hbsq (pow_le_pow_left₀ ha₀.1.le hab 2)

theorem exists_antitone_spatial_cost_minimum_near_pole
    (first₀ last : Fin (H.eventCount + 1)) (hle : first₀ ≤ last)
    (f : (j : H.StageInterval first₀ last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j))
    (hcross : ∀ (i : Fin H.eventCount) (hi : first₀ ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T bmax : ℝ} (hbmax : 0 < bmax)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - bmax ^ 2 ∈ H.stageDomain first₀)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 bmax, T-t^2 ∈ J)
    (hreg : ∀ t ∈ Icc 0 bmax, T-t^2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (K : Set X) (hK : IsCompact K) (B : ℝ)
    (hmetric : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      S.base.metric (T-t^2) = localPullMetric (H.stageMetric j.val (T-t^2)) (f j) (hf j))
    (hscalar : ∀ j : H.StageInterval first₀ last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T bmax j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T-t^2)) z)
    (x : X) (hx : x ∈ interior K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ bmax ∧
      ∃ (first : ℝ → Fin (H.eventCount + 1)) (hfirst : ∀ b, first₀ ≤ first b)
        (hlast : ∀ b, first b ≤ last) (m : ℝ → ℝ),
        (∀ b ∈ Icc 0 bmax, T-b^2 ∈ H.stageDomain (first b)) ∧
        ContinuousOn m (Ioc 0 δ) ∧
        ContinuousOn (fun b => 2*b*m b-6*b^2) (Ioc 0 δ) ∧
        AntitoneOn (fun b => 2*b*m b-6*b^2) (Ioc 0 δ) ∧
        ∀ b ∈ Ioc 0 δ,
          2*b*m b-6*b^2 < 0 ∧
          sInf (Set.range (H.regularizedCost (first b) last (hlast b) T B 0 b
            (f ⟨last, hle, le_rfl⟩ x))) = (m b : WithTop ℝ) ∧
          ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0=x ∧ MapsTo η (Icc 0 b) K ∧
            m b = lRegularizedAction S T η 0 b ∧
            (m b : WithTop ℝ) ∈ H.regularizedActionValues (first b) last (hlast b) T B 0 b
              (f ⟨last, hle, le_rfl⟩ x) (f ⟨first b, hfirst b, hlast b⟩ (η b)) ∧
            H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x)
              (f ⟨first b, hfirst b, hlast b⟩ (η b)) = (m b : WithTop ℝ) ∧
            ∀ q : (H.stage (first b)).Carrier, (m b : WithTop ℝ) ≤
              H.regularizedCost (first b) last (hlast b) T B 0 b (f ⟨last, hle, le_rfl⟩ x) q := by
  obtain ⟨δ, hδ, hδmax, first, hfirst, hlast, m, hfirstclock, hmcont, hcont, hm⟩ :=
    H.exists_continuous_spatial_cost_minimum_near_pole first₀ last hle f hf hinj hcross
      hbmax hupper hlower S hS J hJ hclock (fun t ht => hreg t ⟨ht.1.le, ht.2.le⟩)
      hsmooth K hK B hmetric hscalar x hx
  refine ⟨δ, hδ, hδmax, first, hfirst, hlast, m, hfirstclock, hmcont, hcont, ?_, hm⟩
  apply H.antitoneOn_scaled_spatial_cost_minimum first₀ last hle f hf
    (hinj ⟨last, hle, le_rfl⟩) hcross first hfirst hlast hδ hupper
    (fun b hb => hfirstclock b ⟨hb.1.le, hb.2.trans hδmax⟩) S hS
    (fun t ht => hreg t ⟨ht.1, ht.2.trans hδmax⟩)
    (fun j t ht => hmetric j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val hδ.le hbmax.le hδmax)⟩)
    (fun j t ht => hscalar j t ⟨ht.1, ht.2.trans_le
      (H.regularizedStageEnd_monotoneOn T j.val hδ.le hbmax.le hδmax)⟩) x m ?_ hcont
  intro b hb
  obtain ⟨_, _, η, hη, hη0, _, hval, _, _, hmin⟩ := hm b hb
  exact ⟨η, hη, hη0, hval, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal NNReal Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_regularizedCost_spatial_minimum_of_tendsto_time_of_compact_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ J)
    (hreg : ∀ t ∈ Ioo 0 v, T - t ^ 2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (time : ℕ → ℝ) (htime : ∀ n, time n ∈ Icc 0 v) (hlim : Tendsto time atTop (𝓝 v))
    (α : ℕ → ℝ → X) (hα : ∀ n, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (α n))
    (hstart : ∀ n, α n 0 = x) (hend : ∀ n, α n (time n) ∈ K)
    {A L : ℝ} (hAL : A < L) (hact : ∀ n, lRegularizedAction S T (α n) 0 (time n) ≤ A)
    (hbarrier : L ≤ μ * r ^ 2 / (2 * v) - (2 * B / 3) * v ^ 3) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      MapsTo η (Icc 0 v) K ∧ lRegularizedAction S T η 0 v < L ∧
      (lRegularizedAction S T η 0 v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ∧
      H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η 0 v : WithTop ℝ) ∧
      ∀ q : (H.stage first).Carrier, H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ≤
          H.regularizedCost first last hle T B 0 v (f ⟨last, hle, le_rfl⟩ x) q := by
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jlast) :=
    .of_continuous_injective_isOpenMap (hf jlast).contMDiff.continuous (hinj jlast) (hf jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  let : PseudoMetricSpace X := _root_.TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  obtain ⟨_, γ, hγ, hγ0, _, hγact⟩ := exists_lRegularizedAction_lt_of_tendsto_time S
    hS.smoothMetric ⟨hS.scalarCont⟩ T v K hK (fun t ht => hJ (hclock t ht))
    time htime hlim α hα x hstart hend hAL hact
  obtain ⟨η, hη, hη0, hηK, hηact, hmem, hcost, hmin⟩ :=
    H.exists_regularizedCost_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
      first last hle f hf hinj K hK hcross le_rfl hv
      (by simpa only [zero_pow two_ne_zero, sub_zero] using hupper) hlower S hS
      J hJ hclock hreg hsmooth g hμ hr hmetric hcompare hscalar x hx hfront γ hγ hγ0
      (by simpa only [sub_zero, zero_pow (by norm_num : 3 ≠ 0)] using hγact.trans_le hbarrier)
  exact ⟨η, hη, hη0, hηK, hηact.trans_lt hγact, hmem, hcost, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end

noncomputable section
open Set Filter Manifold MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff ENNReal NNReal Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u
private theorem linear_le_inverse_cubic_barrier {c B C v b : ℝ}
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hb : 0 < b) (hbv : b ≤ v)
    (hguard : 2 * c * v ^ 2 + (4 * B / 3) * v ^ 4 ≤ C) :
    c * b ≤ C / (2 * b) - (2 * B / 3) * b ^ 3 := by
  have h2 := pow_le_pow_left₀ hb.le hbv 2
  have h4 := pow_le_pow_left₀ hb.le hbv 4
  have hpoly : 2 * c * b ^ 2 + (4 * B / 3) * b ^ 4 ≤ C := by
    have hh2 := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * c)
    have hh4 := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 4 * B / 3)
    linarith
  apply (le_sub_iff_add_le).mpr
  apply (le_div_iff₀ (by positivity : 0 < 2 * b)).mpr
  nlinarith

variable (H : ObservedHistory.{u}) {X : Type u} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
  [IsManifold ThreeModel ∞ X] [T2Space X]

theorem exists_regularizedCost_spatial_minimum_of_uniform_history_escape_barrier
    (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    (f : (j : H.StageInterval first last) → X → (H.stage j.val).Carrier)
    (hf : ∀ j, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j))
    (hinj : ∀ j, Function.Injective (f j)) (K : Set X) (hK : IsCompact K)
    (hcross : ∀ (i : Fin H.eventCount) (hi : first ≤ i.castSucc) (hl : i.succ ≤ last), ∀ z : X,
      (H.event i).RegularCrossing (f ⟨i.castSucc, hi, i.castSucc_le_succ.trans hl⟩ z)
        (f ⟨i.succ, hi.trans i.castSucc_le_succ, hl⟩ z))
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ H.stageDomain last)
    (hlower : T - v ^ 2 ∈ H.stageDomain first)
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (J : Set ℝ) (hJ : J ⊆ D.carrier)
    (hclock : ∀ t ∈ Icc 0 v, T - t ^ 2 ∈ J)
    (hreg : ∀ t ∈ Ico 0 v, T - t ^ 2 ∈ D.regular)
    (hsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel)
      (ThreeModel.prod 𝓘(ℝ, ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)) ∞
      (fun z : ℝ × X => (⟨z.2, (S.base.metric z.1).inner z.2⟩ :
        Bundle.TotalSpace (ThreeSpace →L[ℝ] ThreeSpace →L[ℝ] ℝ)
          (fun x => TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel x →L[ℝ] ℝ)))
      (J ×ˢ (univ : Set X)))
    (g : SmoothRiemannianMetric ThreeModel X) {μ B r : ℝ} (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 < r)
    (hmetric : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      S.base.metric (T - t ^ 2) = localPullMetric (H.stageMetric j.val (T - t ^ 2)) (f j) (hf j))
    (hcompare : ∀ t ∈ Ioo 0 v, ∀ z ∈ K, ∀ w : TangentSpace ThreeModel z,
      μ * g.inner z w w ≤ (S.base.metric (T - t ^ 2)).inner z w w)
    (hscalar : ∀ j : H.StageInterval first last,
      ∀ t ∈ Ioo (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val),
      ∀ z : (H.stage j.val).Carrier, -B ≤ metricScalarAt (H.stageMetric j.val (T - t ^ 2)) z)
    (x : X) (hx : x ∈ interior K)
    (hfront : ∀ z ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g x z)
    (hguard : 6 * v ^ 2 + (4 * B / 3) * v ^ 4 ≤ μ * r ^ 2) :
    ∃ η : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 η ∧ η 0 = x ∧
      MapsTo η (Icc 0 v) K ∧ lRegularizedAction S T η 0 v < 3 * v ∧
      (lRegularizedAction S T η 0 v : WithTop ℝ) ∈ H.regularizedActionValues first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ∧
      H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) = (lRegularizedAction S T η 0 v : WithTop ℝ) ∧
      ∀ q : (H.stage first).Carrier, H.regularizedCost first last hle T B 0 v
        (f ⟨last, hle, le_rfl⟩ x) (f ⟨first, le_rfl, hle⟩ (η v)) ≤
          H.regularizedCost first last hle T B 0 v (f ⟨last, hle, le_rfl⟩ x) q := by
  classical
  obtain ⟨δ, hδ, hδv, firstTime, hfirstTime, hlastTime, m, hfirstClock, _, _, hm⟩ :=
    H.exists_continuous_spatial_cost_minimum_near_pole first last hle f hf hinj hcross hv
      hupper hlower S hS J hJ hclock (fun t ht => hreg t ⟨ht.1.le, ht.2⟩) hsmooth
      K hK B hmetric hscalar x hx
  let b₀ := δ / 2
  have hb₀ : 0 < b₀ := half_pos hδ
  have hb₀δ : b₀ ≤ δ := by dsimp only [b₀]; linarith
  have hb₀v : b₀ < v := by dsimp only [b₀]; linarith
  obtain ⟨hneg, _, α₀, hα₀, hα₀start, _, hα₀val, _, _, _⟩ := hm b₀ ⟨hb₀, hb₀δ⟩
  have hα₀act : lRegularizedAction S T α₀ 0 b₀ < 3 * b₀ := by
    rw [hα₀val] at hneg
    nlinarith
  let jlast : H.StageInterval first last := ⟨last, hle, le_rfl⟩
  have hemb : _root_.Topology.IsOpenEmbedding (f jlast) :=
    .of_continuous_injective_isOpenMap (hf jlast).contMDiff.continuous (hinj jlast) (hf jlast).isOpenMap
  let : SecondCountableTopology (H.stage last).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (H.stage last).Carrier
  let : SecondCountableTopology X := hemb.toIsEmbedding.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ThreeSpace X
  let : SigmaCompactSpace X := inferInstance
  let : _root_.TopologicalSpace.MetrizableSpace X := Manifold.metrizableSpace ThreeModel X
  have hbarrier (b : ℝ) (hb : b ∈ Ioc 0 v) :
      3 * b ≤ μ * r ^ 2 / (2 * b) - (2 * B / 3) * b ^ 3 := by
    apply linear_le_inverse_cubic_barrier (by norm_num : (0 : ℝ) ≤ 3) hB hb.1 hb.2
    simpa only [show (2:ℝ)*3=6 by norm_num] using hguard
  have hconf : ∀ b ∈ Ico b₀ v, ∀ α : ℝ → X, ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 α →
      α 0 = x → lRegularizedAction S T α 0 b < 3 * b → MapsTo α (Icc 0 b) K := by
    intro b hb α hα hα0 hαact
    have hb0 : 0 < b := hb₀.trans_le hb.1
    let fb := fun (j : H.StageInterval (firstTime b) last) =>
      f ⟨j.val, (hfirstTime b).trans j.property.1, j.property.2⟩
    let hfb := fun (j : H.StageInterval (firstTime b) last) =>
      hf ⟨j.val, (hfirstTime b).trans j.property.1, j.property.2⟩
    have hend (j : Fin (H.eventCount + 1)) :
        H.regularizedStageEnd T b j ≤ H.regularizedStageEnd T v j :=
      H.regularizedStageEnd_monotoneOn T j hb0.le hv.le hb.2.le
    apply H.mapsTo_of_lRegularizedAction_lt_history_escape_barrier
      (firstTime b) last (hlastTime b) fb hfb (fun j => hinj _) K hK
      (fun i hi hl z => hcross i ((hfirstTime b).trans hi) hl z) le_rfl hb0.le
      (by simpa only [zero_pow two_ne_zero, sub_zero] using
        (show T ∈ Icc (H.time last) (H.stageEndTime last) from
          ⟨H.time_le_of_mem_stageDomain hupper, H.le_stageEndTime_of_mem_stageDomain hupper⟩))
      (hfirstClock b ⟨hb0.le, hb.2.le⟩) S hS
      (fun t ht => hJ (hclock t ⟨ht.1, ht.2.trans hb.2.le⟩)) g hμ hr
      (fun j t ht => hmetric ⟨j.val, (hfirstTime b).trans j.property.1, j.property.2⟩ t
        ⟨ht.1, ht.2.trans_le (hend j.val)⟩)
      (fun t ht => hcompare t ⟨ht.1, ht.2.trans hb.2⟩)
      (fun j t ht z => hscalar ⟨j.val, (hfirstTime b).trans j.property.1, j.property.2⟩ t
        ⟨ht.1, ht.2.trans_le (hend j.val)⟩ (fb j z)) x hx hfront α hα hα0
    simpa only [sub_zero, zero_pow (by norm_num : 3 ≠ 0)] using
      hαact.trans_le (hbarrier b ⟨hb0, hb.2.le⟩)
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) = 3 := by norm_num [ThreeSpace]
  obtain ⟨_, _, _, _, _, _, _, _, γ, hγ, hγ0, _, hγact⟩ :=
    exists_lRegularizedAction_lt_linear_at_carrier_endpoint_of_compact_action_sublevels
      S hS T hb₀ hb₀v (fun t ht => hJ (hclock t ht)) hreg x K hK α₀ hα₀ hα₀start
      (by simpa only [hdim] using hα₀act) (by simpa only [hdim] using hconf)
  have hγact' : lRegularizedAction S T γ 0 v < 3 * v := by simpa only [hdim] using hγact
  obtain ⟨η, hη, hη0, hηK, hηact, hmem, hcost, hmin⟩ :=
    H.exists_regularizedCost_spatial_minimum_of_joint_metric_of_action_lt_compact_barrier
      first last hle f hf hinj K hK hcross le_rfl hv
      (by simpa only [zero_pow two_ne_zero, sub_zero] using hupper) hlower S hS J hJ hclock
      (fun t ht => hreg t ⟨ht.1.le, ht.2⟩) hsmooth g hμ hr hmetric hcompare hscalar
      x hx hfront γ hγ hγ0
      (by simpa only [sub_zero, zero_pow (by norm_num : 3 ≠ 0)] using
        hγact'.trans_le (hbarrier v ⟨hv, le_rfl⟩))
  exact ⟨η, hη, hη0, hηK, hηact.trans_lt hγact', hmem, hcost, hmin⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

end
