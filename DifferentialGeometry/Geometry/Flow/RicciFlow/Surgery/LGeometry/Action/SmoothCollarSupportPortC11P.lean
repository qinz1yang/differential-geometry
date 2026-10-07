import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Action.SmoothCollarContact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.JointRegularity
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.FiniteParameterGraph

/-!
# S-CH11-FIX4 port of `Surgery.LGeometry.Action.SmoothCollarSupport` (`PortC11P`)

Source: donor file of the same relative path in the chapter-11 branch (ch11 HEAD a73e4bdbfd).
Verbatim it does not elaborate against this tree (1 error at donor line 135, in the proof of the
local-inverse support lemma).  One elaboration-level repair:
* `hpsi` (donor line 135): the implicit target set `s` of `contMDiff_fst.contMDiffOn` is given
  explicitly, `(contMDiff_fst.contMDiffOn (s := univ)).comp hInv (fun _ _ => mem_univ _)`, so the
  `mem_univ _` argument is checked against `x ∈ f ⁻¹' univ` instead of an unassigned `?s`.
No statement, definition or proof idea is altered.  The module
`Surgery.LGeometry.Action.SmoothCollarSupport` is a shim re-exporting this file.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open Set Filter _root_.MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped _root_.Manifold ContDiff _root_.Topology BigOperators Interval

universe u uP uX

private theorem exists_admissible_endpoint_clock_neighborhood
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first))
    (lo hi : H.StageInterval first last → ℝ)
    (hbounds : ∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
      hi j ≤ H.regularizedStageEnd T v j.val)
    (hiv : hi ⟨first, le_rfl, hle⟩ < v)
    {K : Set ℝ} (hK : IsOpen K) (hvK : v ∈ K) :
    ∃ J : Set ℝ, IsOpen J ∧ v ∈ J ∧ J ⊆ K ∧
      ∀ w ∈ J, 0 < w ∧ hi ⟨first, le_rfl, hle⟩ < w ∧
        T - w ^ 2 ∈ H.stageDomain first ∧
        ∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
          hi j ≤ H.regularizedStageEnd T w j.val := by
  let J := (K ∩ (Ioi 0 ∩ Ioi (hi ⟨first, le_rfl, hle⟩))) ∩
    (fun w : ℝ => T - w ^ 2) ⁻¹' Ioo (H.time first) (H.stageEndTime first)
  have hJ : IsOpen J :=
    (hK.inter (isOpen_Ioi.inter isOpen_Ioi)).inter
      (isOpen_Ioo.preimage (continuous_const.sub (continuous_id.pow 2)))
  refine ⟨J, hJ, ⟨⟨hvK, hv, hiv⟩, hpast⟩, fun _ hw => hw.1.1, ?_⟩
  intro w hw
  have hpastW := H.mem_stageDomain_of_mem_Ioo hw.2
  have hpastV := H.mem_stageDomain_of_mem_Ioo hpast
  refine ⟨hw.1.2.1, hw.1.2.2, hpastW, fun j =>
    ⟨(hbounds j).1, (hbounds j).2.1, ?_⟩⟩
  by_cases hj : j.val = first
  · have hje : j = ⟨first, le_rfl, hle⟩ := Subtype.ext hj
    rw [hje]
    change hi ⟨first, le_rfl, hle⟩ ≤ H.regularizedStageEnd T w first
    rw [H.regularizedStageEnd_eq_of_mem_stageDomain hw.1.2.1.le hpastW]
    exact hw.1.2.2.le
  · have hneq : first.val ≠ j.val.val := fun he => hj (Fin.ext he.symm)
    have hjpos : 0 < j.val.val := by
      have hle0 := j.property.1
      change first.val ≤ j.val.val at hle0
      omega
    let i : Fin H.eventCount := ⟨j.val.val - 1, by
      have hlt := j.val.isLt
      omega⟩
    have hij : i.succ = j.val := by
      apply Fin.ext
      change j.val.val - 1 + 1 = j.val.val
      omega
    have hfi : first ≤ i.castSucc := by
      change first.val ≤ j.val.val - 1
      have hle0 := j.property.1
      change first.val ≤ j.val.val at hle0
      omega
    have hend : H.regularizedStageEnd T w j.val = H.regularizedStageEnd T v j.val := by
      rw [← hij, H.regularizedStageEnd_succ_eq_event_clock hpastW i hfi,
        H.regularizedStageEnd_succ_eq_event_clock hpastV i hfi]
    rw [hend]
    exact (hbounds j).2.2

private theorem contDiffOn_fixed_clock_action
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {X : Type uX} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X] {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := X) D) (hS : IsSolutionOn S)
    (T a b : ℝ) (f : P × ℝ → X)
    (hf : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 f)
    {V : Set P} (hV : IsOpen V) {K : Set ℝ} (hK : IsOpen K)
    (hKconn : IsPreconnected K) (ha : a ∈ K) (hb : b ∈ K)
    (hreg : ∀ r ∈ K, T - r ^ 2 ∈ D.regular) (Kout : Set ℝ) :
    ContDiffOn ℝ 2
      (fun z : P × ℝ => lRegularizedAction S T (fun r => f (z.1, r)) a b)
      (V ×ˢ Kout) := by
  have hh := contDiffOn_lRegularizedAction_joint S hS T a hV hK hKconn ha
    hf.contMDiffOn hreg
  exact hh.comp (contDiffOn_fst.prodMk contDiffOn_const)
    (fun _ hz => ⟨hz.1, hb⟩)

private theorem exists_joint_action_endpoint_branch
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {X : Type uX} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (tail : P × ℝ → X)
    (htail : ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 tail)
    (g : SmoothRiemannianMetric ThreeModel X) (q : X) (v : ℝ)
    (Bframe : P ≃L[ℝ] ThreeSpace)
    (hexp : (fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
      (fun z => expMap g q (show TangentSpace ThreeModel q from Bframe z)))
    (A : P × ℝ → ℝ) {V : Set P} (hV : IsOpen V) (h0 : (0 : P) ∈ V)
    {K J : Set ℝ} (hJ : IsOpen J) (hvJ : v ∈ J) (hJK : J ⊆ K)
    (hA : ContDiffOn ℝ 2 A (V ×ˢ K)) :
    ∃ (U : Set (X × ℝ)) (psi : X × ℝ → P) (F : X × ℝ → ℝ),
      IsOpen U ∧ (q, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (q, v) = 0 ∧ F (q, v) = A (0, v) ∧
      ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ J ∧
        tail (psi x, x.2) = x.1 ∧ F x = A (psi x, x.2) := by
  have htail2 : ContMDiffAt (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 2 tail (0, v) :=
    htail.contMDiffAt.of_le (by norm_num)
  obtain ⟨hcenter, hloc⟩ :=
    DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_parameter_graph_of_exponential_germ_two
      g q Bframe htail2 hexp
  let W : Set (P × ℝ) := V ×ˢ J
  let U : Set (X × ℝ) := hloc.localInverse.source ∩ hloc.localInverse ⁻¹' W
  have hWopen : IsOpen W := hV.prod hJ
  have hUopen : IsOpen U :=
    hloc.contMDiffOn_localInverse.continuousOn.isOpen_inter_preimage
      hloc.localInverse_open_source hWopen
  have hinv : hloc.localInverse (q, v) = (0, v) := by
    simpa only [hcenter] using hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hqU : (q, v) ∈ U := by
    refine ⟨?_, ?_⟩
    · simpa only [hcenter] using hloc.localInverse_mem_source
    · change hloc.localInverse (q, v) ∈ W
      rw [hinv]
      exact ⟨h0, hvJ⟩
  let psi : X × ℝ → P := fun x => (hloc.localInverse x).1
  let F : X × ℝ → ℝ := fun x => A (hloc.localInverse x)
  have hInv := hloc.contMDiffOn_localInverse.mono
    (inter_subset_left : U ⊆ hloc.localInverse.source)
  have hpsi : ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U :=
    (contMDiff_fst.contMDiffOn (s := univ)).comp hInv (fun _ _ => mem_univ _)
  have hact : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 A W := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiffOn_iff_contDiffOn.mpr
      (hA.mono (fun _ hx => ⟨hx.1, hJK hx.2⟩))
  have hF : ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U :=
    hact.comp hInv (fun _ hx => hx.2)
  refine ⟨U, psi, F, hUopen, hqU, hpsi, hF, ?_, ?_, ?_⟩
  · change (hloc.localInverse (q, v)).1 = 0
    rw [hinv]
  · change A (hloc.localInverse (q, v)) = _
    rw [hinv]
  · intro x hx
    have hright := hloc.localInverse_right_inv hx.1
    change (tail (hloc.localInverse x), (hloc.localInverse x).2) = x at hright
    have hclock : (hloc.localInverse x).2 = x.2 := congrArg Prod.snd hright
    have hpair : hloc.localInverse x = (psi x, x.2) := Prod.ext rfl hclock
    refine ⟨hx.2.1, ?_, ?_, ?_⟩
    · rw [← hclock]
      exact hx.2.2
    · have hp := congrArg Prod.fst hright
      rwa [hpair] at hp
    · change A (hloc.localInverse x) = _
      rw [hpair]

/-- A single C2 upper support for the actual history cost, formed from the same
joint collar family and its genuine physical terminal exponential germ. The
original prefix remains AC and unchanged. This theorem covers a positive pole
stage and a strictly interior regular past endpoint; event-boundary continuation
is a separate receiving step. -/
theorem exists_smooth_collar_cost_support
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {T v : ℝ} (hv : 0 < v)
    (hupper : T ∈ Ioc (H.time last) (H.stageEndTime last))
    (hpast : T - v ^ 2 ∈ Ioo (H.time first) (H.stageEndTime first)) (Bfloor : ℝ)
    (hscalar : ∀ j (t : ℝ), t ∈ H.stageDomain j →
      ∀ x : (H.stage j).Carrier, -Bfloor ≤ metricScalarAt (H.stageMetric j t) x) :
    let Jstage := H.StageInterval first last;
    let Eevent := {i : Fin H.eventCount // first ≤ i.castSucc ∧ i.succ ≤ last};
    let jo (i : Eevent) : Jstage := ⟨i.val.castSucc, i.property.1,
      i.val.castSucc_le_succ.trans i.property.2⟩;
    let jn (i : Eevent) : Jstage := ⟨i.val.succ,
      i.property.1.trans i.val.castSucc_le_succ, i.property.2⟩;
    let jf : Jstage := ⟨first, le_rfl, hle⟩;
    let jl : Jstage := ⟨last, hle, le_rfl⟩;
    ∀ (gamma : (j : Jstage) → ℝ → (H.stage j.val).Carrier) (lo hi : Jstage → ℝ),
      (∀ j, H.regularizedStageStart T 0 j.val ≤ lo j ∧ lo j ≤ hi j ∧
        hi j ≤ H.regularizedStageEnd T v j.val) →
      hi jf < v →
      Manifold.absolutelyContinuousOnInterval ThreeModel (gamma jl) 0 (lo jl) →
      (∀ j, IntervalIntegrable (H.stageRegularizedLagrangian j.val T (gamma j)) volume
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val)) →
      H.regularizedExtendedAction first last T Bfloor 0 v gamma =
        H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) →
    ∀ (W : (i : Eevent) → TopologicalSpace.Opens (H.event i.val).incoming.terminalRegularOpen)
      (FC : (i : Eevent) → PartialDiffeomorph ThreeModel ThreeModel
        (H.event i.val).incoming.terminalRegularOpen (H.stage i.val.succ).Carrier ∞)
      (DO : Jstage → RealTimeInterval) (DS : Eevent → RealTimeInterval) (DT : RealTimeInterval)
      (SO : (j : Jstage) → SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) (DO j))
      (SS : (i : Eevent) → SolutionOn (I := ThreeModel) (M := W i) (DS i))
      (ST : SolutionOn (I := ThreeModel) (M := (H.stage first).Carrier) DT)
      (hold : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => z.val.val))
      (hnew : ∀ i, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (fun z : W i => FC i z.val))
      (ordinary : (j : Jstage) → P × ℝ → (H.stage j.val).Carrier)
      (survivor : (i : Eevent) → P × ℝ → W i) (tail : P × ℝ → (H.stage first).Carrier),
      (∀ j, IsSolutionOn (SO j)) → (∀ i, IsSolutionOn (SS i)) → IsSolutionOn ST →
      (∀ j t, (SO j).base.metric t = H.stageMetric j.val t) →
      (∀ t, ST.base.metric t = H.stageMetric first t) →
      (∀ i z, (H.event i.val).RegularCrossing (z : W i).val.val (FC i z.val)) →
      (∀ i, ∀ r ∈ Ioo (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.castSucc (T - r ^ 2))
            (fun z : W i => z.val.val) (hold i)) →
      (∀ i, ∀ r ∈ Ioo (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)),
        (SS i).base.metric (T - r ^ 2) =
          localPullMetric (H.stageMetric i.val.succ (T - r ^ 2))
            (fun z : W i => FC i z.val) (hnew i)) →
      (∀ j, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (ordinary j)) →
      (∀ i, ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 (survivor i)) →
      ContMDiff (𝓘(ℝ, P).prod 𝓘(ℝ, ℝ)) ThreeModel 8 tail →
    ∀ (V : Set P), IsOpen V → (0 : P) ∈ V →
    ∀ (KO : Jstage → Set ℝ) (KS : Eevent → Set ℝ) (KT : Set ℝ),
      (∀ j, IsOpen (KO j) ∧ IsPreconnected (KO j) ∧ lo j ∈ KO j ∧ hi j ∈ KO j) →
      (∀ i, IsOpen (KS i) ∧ IsPreconnected (KS i) ∧ hi (jn i) ∈ KS i ∧ lo (jo i) ∈ KS i) →
      IsOpen KT ∧ IsPreconnected KT ∧ hi jf ∈ KT ∧ v ∈ KT →
      (∀ j r, r ∈ KO j → T - r ^ 2 ∈ (DO j).regular) →
      (∀ i r, r ∈ KS i → T - r ^ 2 ∈ (DS i).regular) →
      (∀ r ∈ KT, T - r ^ 2 ∈ DT.regular) →
      (∀ z ∈ V, ordinary jl (z, lo jl) = gamma jl (lo jl)) →
      (∀ z ∈ V, ∀ i, ordinary (jo i) (z, lo (jo i)) =
        (survivor i (z, lo (jo i))).val.val) →
      (∀ z ∈ V, ∀ i, ordinary (jn i) (z, hi (jn i)) =
        FC i (survivor i (z, hi (jn i))).val) →
      (∀ z ∈ V, ordinary jf (z, hi jf) = tail (z, hi jf)) →
      (∀ j, EqOn (fun r => ordinary j (0, r)) (gamma j) (Icc (lo j) (hi j))) →
      (∀ i, EqOn (fun r => (survivor i (0, r)).val.val) (gamma (jo i))
        (Icc (Real.sqrt (T - H.time i.val.succ)) (lo (jo i)))) →
      (∀ i, EqOn (fun r => FC i (survivor i (0, r)).val) (gamma (jn i))
        (Icc (hi (jn i)) (Real.sqrt (T - H.time i.val.succ)))) →
      EqOn (fun r => tail (0, r)) (gamma jf) (Icc (hi jf) v) →
    ∀ (Bframe : P ≃L[ℝ] ThreeSpace),
      (fun z => tail (z, v)) =ᶠ[𝓝 (0 : P)]
        (fun z => expMap (ST.base.metric (T - v ^ 2)) (gamma jf v)
          (show TangentSpace ThreeModel (gamma jf v) from Bframe z)) →
    let action : P × ℝ → ℝ := fun z =>
      H.stageRegularizedAction last T (gamma jl) 0 (lo jl) +
      (∑ j : Jstage, lRegularizedAction (SO j) T (fun r => ordinary j (z.1, r)) (lo j) (hi j)) +
      (∑ i : Eevent, lRegularizedAction (SS i) T (fun r => survivor i (z.1, r))
        (hi (jn i)) (lo (jo i))) +
      lRegularizedAction ST T (fun r => tail (z.1, r)) (hi jf) z.2;
    ∃ (Jclock : Set ℝ) (U : Set ((H.stage first).Carrier × ℝ))
      (psi : (H.stage first).Carrier × ℝ → P) (F : (H.stage first).Carrier × ℝ → ℝ),
      IsOpen Jclock ∧ v ∈ Jclock ∧ Jclock ⊆ KT ∧
      (∀ w ∈ Jclock, 0 < w ∧ hi jf < w ∧ T - w ^ 2 ∈ H.stageDomain first) ∧
      ContDiffOn ℝ 2 action (V ×ˢ KT) ∧
      IsOpen U ∧ (gamma jf v, v) ∈ U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P) 2 psi U ∧
      ContMDiffOn (ThreeModel.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 F U ∧
      psi (gamma jf v, v) = 0 ∧
      F (gamma jf v, v) = ∑ j : Jstage, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) ∧
      H.regularizedCost first last hle T Bfloor 0 v (gamma jl 0) (gamma jf v) =
        (F (gamma jf v, v) : WithTop ℝ) ∧
      ∀ x ∈ U, psi x ∈ V ∧ x.2 ∈ Jclock ∧
        tail (psi x, x.2) = x.1 ∧ F x = action (psi x, x.2) ∧
        H.regularizedCost first last hle T Bfloor 0 x.2 (gamma jl 0) x.1 ≤
          (F x : WithTop ℝ) := by
  classical
  intro Jstage Eevent jo jn jf jl gamma lo hi hbounds hiv hprefixAC hInt hattain
    W FC DO DS DT SO SS ST hold hnew ordinary survivor tail hSO hSS hST
    hmetricO hmetricT hcross hmetricOld hmetricNew hOrd hSurv hTail
    V hV h0 KO KS KT hKO hKS hKT hregO hregS hregT
    hfix hjoinOld hjoinNew hjoinTail hcenterO hcenterOld hcenterNew hcenterTail Bframe hexp action
  have hupperClosed : T ∈ Icc (H.time last) (H.stageEndTime last) :=
    ⟨hupper.1.le, hupper.2⟩
  have hupper0 : T - (0 : ℝ) ^ 2 ∈ Icc (H.time last) (H.stageEndTime last) := by
    simpa only [zero_pow two_ne_zero, sub_zero] using hupperClosed
  have hpastD := H.mem_stageDomain_of_mem_Ioo hpast
  obtain ⟨Jclock, hJclock, hvJclock, hJKT, hJdomain⟩ :=
    H.exists_admissible_endpoint_clock_neighborhood first last hle hv hpast lo hi
      hbounds hiv hKT.1 hKT.2.2.2
  have hstart : H.regularizedStageStart T 0 last = 0 :=
    H.regularizedStageStart_eq_of_mem_Icc le_rfl hupper0
  have hlo0 : 0 ≤ lo jl := by simpa only [jl, hstart] using (hbounds jl).1
  have hloEnd : lo jl ≤ H.regularizedStageEnd T v last :=
    (hbounds jl).2.1.trans (hbounds jl).2.2
  have hlastInt : IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume
      0 (H.regularizedStageEnd T v last) := by
    simpa only [jl, hstart] using hInt jl
  have hprefixInt : IntervalIntegrable (H.stageRegularizedLagrangian last T (gamma jl)) volume
      0 (lo jl) := hlastInt.mono_set (by
    rw [uIcc_of_le hlo0, uIcc_of_le (hlo0.trans hloEnd)]
    exact Icc_subset_Icc le_rfl hloEnd)
  have hOrd1 (z : P) (j : Jstage) :
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (fun r => ordinary j (z, r)) :=
    ((hOrd j).comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
  have hSurv1 (z : P) (i : Eevent) :
      ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (fun r => survivor i (z, r)) :=
    ((hSurv i).comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
  have hTail1 (z : P) : ContMDiff 𝓘(ℝ, ℝ) ThreeModel 1 (fun r => tail (z, r)) :=
    (hTail.comp (contMDiff_const.prodMk contMDiff_id)).of_le (by norm_num)
  have hclockO (j : Jstage) (r : ℝ) (hr : r ∈ Icc (lo j) (hi j)) :
      T - r ^ 2 ∈ (DO j).carrier :=
    (DO j).regular_subset (hregO j r
      ((hKO j).2.1.ordConnected.out (hKO j).2.2.1 (hKO j).2.2.2 hr))
  have hclockS (i : Eevent) (r : ℝ) (hr : r ∈ Icc (hi (jn i)) (lo (jo i))) :
      T - r ^ 2 ∈ (DS i).carrier :=
    (DS i).regular_subset (hregS i r
      ((hKS i).2.1.ordConnected.out (hKS i).2.2.1 (hKS i).2.2.2 hr))
  have hclockT (w : ℝ) (hw : w ∈ KT) (r : ℝ) (hr : r ∈ Icc (hi jf) w) :
      T - r ^ 2 ∈ DT.carrier :=
    DT.regular_subset (hregT r (hKT.2.1.ordConnected.out hKT.2.2.1 hw hr))
  have hAO (j : Jstage) := contDiffOn_fixed_clock_action (SO j) (hSO j) T (lo j) (hi j)
    (ordinary j) (hOrd j) hV (hKO j).1 (hKO j).2.1 (hKO j).2.2.1 (hKO j).2.2.2
    (hregO j) KT
  have hAS (i : Eevent) := contDiffOn_fixed_clock_action (SS i) (hSS i) T
    (hi (jn i)) (lo (jo i)) (survivor i) (hSurv i) hV
    (hKS i).1 (hKS i).2.1 (hKS i).2.2.1 (hKS i).2.2.2 (hregS i) KT
  have hAT := contDiffOn_lRegularizedAction_joint ST hST T (hi jf) hV hKT.1 hKT.2.1
    hKT.2.2.1 hTail.contMDiffOn hregT
  have hAction : ContDiffOn ℝ 2 action (V ×ˢ KT) :=
    ((contDiffOn_const.add (ContDiffOn.sum (s := Finset.univ) (fun j _ => hAO j))).add
      (ContDiffOn.sum (s := Finset.univ) (fun i _ => hAS i))).add hAT
  have hbound (z : P) (hz : z ∈ V) (w : ℝ) (hw : w ∈ Jclock) :
      H.regularizedCost first last hle T Bfloor 0 w (gamma jl 0) (tail (z, w)) ≤
        (action (z, w) : WithTop ℝ) := by
    obtain ⟨hw0, _hwi, hpastW, hboundsW⟩ := hJdomain w hw
    exact H.regularizedCost_le_smooth_collar_action first last hle hw0.le hupperClosed hpastW
      Bfloor hscalar gamma lo hi hboundsW hprefixAC hprefixInt
      W FC DO DS DT SO SS ST hold hnew
      (fun j r => ordinary j (z, r)) (fun i r => survivor i (z, r)) (fun r => tail (z, r))
      hSO hSS hST hmetricO hmetricT hclockO (hclockT w (hJKT hw)) hcross hclockS
      hmetricOld hmetricNew (hOrd1 z) (hSurv1 z) (hTail1 z)
      (hfix z hz) (hjoinOld z hz) (hjoinNew z hz) (hjoinTail z hz)
  have hcontact : action (0, v) =
      ∑ j : Jstage, H.stageRegularizedAction j.val T (gamma j)
        (H.regularizedStageStart T 0 j.val) (H.regularizedStageEnd T v j.val) :=
    H.smooth_collar_action_eq_sum_stage_action first last hle hv.le hupperClosed hpastD
      gamma lo hi hbounds hInt W FC DO DS DT SO SS ST hold hnew
      (fun j r => ordinary j (0, r)) (fun i r => survivor i (0, r)) (fun r => tail (0, r))
      hSS hmetricO hmetricT hcross hclockS hmetricOld hmetricNew (hSurv1 0)
      hcenterO hcenterOld hcenterNew hcenterTail
  have hfull := H.regularizedExtendedAction_eq_sum_action first last le_rfl hv.le hupper0 hpastD
    gamma hInt (fun j => by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      exact hscalar j.val (T - r ^ 2) (H.mapsTo_regularizedStage_Ioo T 0 v j.val hr)
        (gamma j r))
  obtain ⟨U, psi, F, hU, hqU, hpsi, hF, hpsi0, hF0, hbranch⟩ :=
    exists_joint_action_endpoint_branch tail hTail (ST.base.metric (T - v ^ 2))
      (gamma jf v) v Bframe hexp action hV h0 hJclock hvJclock hJKT hAction
  have hFcontact := hF0.trans hcontact
  have hcostContact : H.regularizedCost first last hle T Bfloor 0 v
      (gamma jl 0) (gamma jf v) = (F (gamma jf v, v) : WithTop ℝ) :=
    hattain.symm.trans (hfull.trans
      (congrArg (fun L : ℝ => (L : WithTop ℝ)) hFcontact).symm)
  refine ⟨Jclock, U, psi, F, hJclock, hvJclock, hJKT,
    fun w hw => ⟨(hJdomain w hw).1, (hJdomain w hw).2.1, (hJdomain w hw).2.2.1⟩,
    hAction, hU, hqU, hpsi, hF, hpsi0, hFcontact, hcostContact, ?_⟩
  intro x hx
  obtain ⟨hz, hw, hend, hvalue⟩ := hbranch x hx
  refine ⟨hz, hw, hend, hvalue, ?_⟩
  have hh := hbound (psi x) hz x.2 hw
  rwa [hend, ← hvalue] at hh

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
