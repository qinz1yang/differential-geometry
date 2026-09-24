import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorIncoming
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ X] [T2Space X]
  [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ Y] [T2Space Y] [SigmaCompactSpace Y]

private theorem exists_normalized_closed_localPullback
    {a b q : ℝ} (hab : a < b) (hq : 0 < q)
    (S : SolutionOn (I := 𝓡 3) (M := Y) (RealTimeInterval.closed a b hab.le))
    (hS : IsSolutionOn S)
    (hgram : ∀ (y : Y) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
        (fun z : ℝ × Y => chartGramMatrix (S.base.metric z.1) y z.2 i j)
        (Icc a b ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) y).baseSet))
    (Φ : X → Y) (hΦ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ Φ) :
    ∃ L : SolutionOn (I := 𝓡 3) (M := X)
        (RealTimeInterval.closed 0 (q * (b - a)) (by positivity)),
      IsSolutionOn L ∧
      (∀ t, L.base.metric t = localPullMetric (scaleMetric q hq (S.base.metric (a + t / q))) Φ hΦ) ∧
      ∀ (x : X) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
          (fun z : ℝ × X => chartGramMatrix (L.base.metric z.1) x z.2 i j)
          (Icc 0 (q * (b - a)) ×ˢ
            (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x).baseSet) := by
  have ha : a ∈ (RealTimeInterval.closed a b hab.le).carrier := ⟨le_rfl, hab.le⟩
  let P := parabolicSolution S a q hq ha
  have hP := parabolicSolution_isSolutionOn S hS a q hq ha
  have htime : ∀ t ∈ Icc 0 (q * (b - a)), a + t / q ∈ Icc a b := by
    intro t ht
    refine ⟨by linarith [div_nonneg ht.1 hq.le], ?_⟩
    have hh : t / q ≤ b - a := (div_le_iff₀ hq).mpr (by nlinarith [ht.2])
    linarith
  let R := (P.localPullback Φ hΦ).timeRestrict
    (RealTimeInterval.closed 0 (q * (b - a)) (by positivity))
  have hsol : IsSolutionOn R := by
    apply isSolutionOn_timeRestrict (hP.localPullback Φ hΦ)
    · intro t ht
      exact htime t ht
    · intro t ht
      change a < a + t / q ∧ a + t / q < b
      constructor
      · linarith [div_pos ht.1 hq]
      · have hh : t / q < b - a := (div_lt_iff₀ hq).mpr (by nlinarith [ht.2])
        linarith
  have hpgram : ∀ (y : Y) (i j : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
        (fun z : ℝ × Y => chartGramMatrix (P.base.metric z.1) y z.2 i j)
        (Icc 0 (q * (b - a)) ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) y).baseSet) := by
    intro y i j
    have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun z : ℝ × Y => (a + z.1 / q, z.2)) :=
      (contMDiff_const.add (contMDiff_fst.div_const q)).prodMk contMDiff_snd
    have hmaps : MapsTo (fun z : ℝ × Y => (a + z.1 / q, z.2))
        (Icc 0 (q * (b - a)) ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) y).baseSet)
        (Icc a b ×ˢ
          (trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) y).baseSet) :=
      fun z hz => ⟨htime z.1 hz.1, hz.2⟩
    have hh := (contMDiffOn_const (c := q)).mul ((hgram y i j).comp hmap.contMDiffOn hmaps)
    convert! hh using 1
  refine ⟨R, hsol, ?_, ?_⟩
  · intro t
    rfl
  · exact P.localPullback_chartGramMatrix_joint_contMDiffOn Φ hΦ
      (Icc 0 (q * (b - a))) hpgram

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first i.castSucc hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first i.castSucc hle).isOpen)
private local instance : SigmaCompactSpace (H.backwardSurvivorTerminalFace first i hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorTerminalFace first i hle).isOpen)

private theorem survivor_terminal_metric_initial
    (G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
          (H.backwardSurvivorTerminalFace first i hle))
    (hlast : ∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
      G t = H.backwardSurvivorTerminalFaceMetric first i hle t) :
    G (H.time first) =
      (H.backwardSurvivorInitialMetric first i.castSucc hle first le_rfl hle).restrictOpen
        (H.backwardSurvivorTerminalFace first i hle) := by
  rcases eq_or_lt_of_le hle with he | hlt
  · subst first
    rw [hlast _ ⟨le_rfl, (H.time_strictMono i.castSucc_lt_succ).le⟩,
      H.backwardSurvivorTerminalFaceMetric_initial]
  · let j : Fin H.eventCount := ⟨first.val, by omega⟩
    have hj : j.castSucc = first := Fin.ext rfl
    have hji : j.succ ≤ i.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      change first.val + 1 ≤ i.val
      exact Nat.succ_le_iff.mpr hlt
    have hf : first ≤ j.castSucc := by rw [hj]
    have hh := hslabs j hf hji (H.time j.castSucc)
      ⟨le_rfl, (H.time_strictMono j.castSucc_lt_succ).le⟩
    rw [H.backwardSurvivorSlabMetric_initial] at hh
    simpa only [hj] using hh

theorem exists_normalized_backwardSurvivor_chart_solution
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (Ξ : X → H.backwardSurvivorTerminalFace first i hle)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first i.castSucc hle first le_rfl hle
      (Ξ x).val = J x)
    (q : ℝ) (hq : 0 < q) (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) :
    ∃ G : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorTerminalFace first i hle),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ i.castSucc),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          G t = (H.backwardSurvivorSlabMetric first i.castSucc hle j hf hl t).restrictOpen
            (H.backwardSurvivorTerminalFace first i hle)) ∧
      (∀ t ∈ Icc (H.time i.castSucc) (H.time i.succ),
        G t = H.backwardSurvivorTerminalFaceMetric first i hle t) ∧
      ∃ L : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q * (H.time i.succ - H.time first))
            (by have ht := H.time_strictMono (hle.trans_lt i.castSucc_lt_succ); positivity)),
        IsSolutionOn L ∧ L.base.metric 0 = g₀ ∧
        (∀ t, L.base.metric t =
          localPullMetric (scaleMetric q hq (G (H.time first + t / q))) Ξ hΞ) ∧
        ∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => chartGramMatrix (L.base.metric z.1) x z.2 k l)
            (Icc 0 (q * (H.time i.succ - H.time first)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet) := by
  obtain ⟨G, hslabs, hlast, hjoint, hG⟩ :=
    H.exists_backwardSurvivorTerminal_isSolutionOn first i hle
  have hab : H.time first < H.time i.succ := H.time_strictMono (hle.trans_lt i.castSucc_lt_succ)
  let S : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorTerminalFace first i hle)
      (RealTimeInterval.closed (H.time first) (H.time i.succ) hab.le) :=
    { base := { metric := G } }
  obtain ⟨L, hL, hmetric, hgram⟩ := exists_normalized_closed_localPullback hab hq S hG
    (chartGramMatrix_joint_contMDiffOn G _ hjoint) Ξ hΞ
  refine ⟨G, hslabs, hlast, L, hL, ?_, hmetric, hgram⟩
  rw [hmetric, zero_div, add_zero]
  change localPullMetric (scaleMetric q hq (G (H.time first))) Ξ hΞ = g₀
  rw [H.survivor_terminal_metric_initial first i hle G hslabs hlast]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
  unfold backwardSurvivorInitialMetric
  erw [localPullMetric_inner]
  rw [hzero]
  have hcomp : (H.backwardSurvivorMap first i.castSucc hle first le_rfl hle) ∘
      (fun x => (Ξ x).val) = J := funext hbirth
  have hmap : ContMDiff ThreeModel ThreeModel ∞ (fun x => (Ξ x).val) :=
    contMDiff_subtype_val.comp hΞ.contMDiff
  have hder := mfderiv_comp x
    ((H.backwardSurvivorMap_isLocalDiffeomorph first i.castSucc hle first le_rfl hle).contMDiff.mdifferentiableAt (by simp))
    (hmap.mdifferentiableAt (by simp))
  rw [hcomp] at hder
  have hinc := mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel) Ξ x
  rw [hinc] at hder
  rw [hbirth x, hder]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {s : ℝ} (G : (H.stage last).IncomingSlab (H.time last) s) (L : G.TerminalLimitMetric)

private local instance : SigmaCompactSpace (H.backwardSurvivorDomain first last hle) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorDomain first last hle).isOpen)
private local instance : SigmaCompactSpace (H.backwardSurvivorIncomingDomain first last hle G) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen ThreeModel (H.backwardSurvivorIncomingDomain first last hle G).isOpen)

private theorem survivor_incoming_metric_initial
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    (gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G))
    (hslabs : ∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
      ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
        gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
          (H.backwardSurvivorIncomingDomain first last hle G))
    (hlast : ∀ t ∈ Icc (H.time last) s,
      gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) :
    gflow (H.time first) =
      (H.backwardSurvivorInitialMetric first last hle first le_rfl hle).restrictOpen
        (H.backwardSurvivorIncomingDomain first last hle G) := by
  rcases eq_or_lt_of_le hle with he | hlt
  · subst first
    rw [hlast _ ⟨le_rfl, G.lt.le⟩, H.backwardSurvivorIncomingMetric_initial _ _ _ G L hinit]
  · let j : Fin H.eventCount := ⟨first.val, by have hh := last.isLt; omega⟩
    have hj : j.castSucc = first := Fin.ext rfl
    have hjlast : j.succ ≤ last := by
      apply Fin.le_iff_val_le_val.mpr
      change first.val + 1 ≤ last.val
      exact Nat.succ_le_iff.mpr hlt
    have hf : first ≤ j.castSucc := by rw [hj]
    have hh := hslabs j hf hjlast (H.time j.castSucc)
      ⟨le_rfl, (H.time_strictMono j.castSucc_lt_succ).le⟩
    rw [H.backwardSurvivorSlabMetric_initial] at hh
    simpa only [hj] using hh

theorem exists_normalized_backwardSurvivorIncoming_chart_solution
    (hinit : G.flow.base.metric (H.time last) = H.initialMetric last)
    {X : Type*} [TopologicalSpace X] [ChartedSpace ThreeSpace X]
    [IsManifold ThreeModel ∞ X] [T2Space X]
    (Ξ : X → H.backwardSurvivorIncomingDomain first last hle G)
    (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (J : X → (H.stage first).Carrier)
    (hbirth : ∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x).val = J x)
    (q : ℝ) (hq : 0 < q) (g₀ : SmoothRiemannianMetric ThreeModel X)
    (hzero : ∀ x (v w : TangentSpace ThreeModel x),
      g₀.inner x v w = q * (H.initialMetric first).inner (J x)
        (mfderiv ThreeModel ThreeModel J x v) (mfderiv ThreeModel ThreeModel J x w)) :
    ∃ gflow : ℝ → SmoothRiemannianMetric ThreeModel (H.backwardSurvivorIncomingDomain first last hle G),
      (∀ (j : Fin H.eventCount) (hf : first ≤ j.castSucc) (hl : j.succ ≤ last),
        ∀ t ∈ Icc (H.time j.castSucc) (H.time j.succ),
          gflow t = (H.backwardSurvivorSlabMetric first last hle j hf hl t).restrictOpen
            (H.backwardSurvivorIncomingDomain first last hle G)) ∧
      (∀ t ∈ Icc (H.time last) s,
        gflow t = H.backwardSurvivorIncomingMetric first last hle G L t) ∧
      ∃ S : SolutionOn (I := ThreeModel) (M := X)
          (RealTimeInterval.closed 0 (q * (s - H.time first))
            (by have ht := (H.time_strictMono.monotone hle).trans_lt G.lt; positivity)),
        IsSolutionOn S ∧ S.base.metric 0 = g₀ ∧
        (∀ t, S.base.metric t =
          localPullMetric (scaleMetric q hq (gflow (H.time first + t / q))) Ξ hΞ) ∧
        ∀ (x : X) (k l : Fin (Module.finrank ℝ ThreeSpace)),
          ContMDiffOn (𝓘(ℝ, ℝ).prod ThreeModel) 𝓘(ℝ) ∞
            (fun z : ℝ × X => chartGramMatrix (S.base.metric z.1) x z.2 k l)
            (Icc 0 (q * (s - H.time first)) ×ˢ
              (trivializationAt ThreeSpace (TangentSpace ThreeModel) x).baseSet) := by
  obtain ⟨gflow, hslabs, hlast, hjoint, hG⟩ :=
    H.exists_backwardSurvivorIncoming_isSolutionOn first last hle G L hinit
  have hab : H.time first < s := (H.time_strictMono.monotone hle).trans_lt G.lt
  let R : SolutionOn (I := ThreeModel) (M := H.backwardSurvivorIncomingDomain first last hle G)
      (RealTimeInterval.closed (H.time first) s hab.le) :=
    { base := { metric := gflow } }
  obtain ⟨S, hS, hmetric, hgram⟩ := exists_normalized_closed_localPullback hab hq R hG
    (chartGramMatrix_joint_contMDiffOn gflow _ hjoint) Ξ hΞ
  refine ⟨gflow, hslabs, hlast, S, hS, ?_, hmetric, hgram⟩
  rw [hmetric, zero_div, add_zero]
  change localPullMetric (scaleMetric q hq (gflow (H.time first))) Ξ hΞ = g₀
  rw [H.survivor_incoming_metric_initial first last hle G L hinit gflow hslabs hlast]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, scaleMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
  unfold backwardSurvivorInitialMetric
  erw [localPullMetric_inner]
  rw [hzero]
  have hcomp : (H.backwardSurvivorMap first last hle first le_rfl hle) ∘
      (fun x => (Ξ x).val) = J := funext hbirth
  have hmap : ContMDiff ThreeModel ThreeModel ∞ (fun x => (Ξ x).val) :=
    contMDiff_subtype_val.comp hΞ.contMDiff
  have hder := mfderiv_comp x
    ((H.backwardSurvivorMap_isLocalDiffeomorph first last hle first le_rfl hle).contMDiff.mdifferentiableAt (by simp))
    (hmap.mdifferentiableAt (by simp))
  rw [hcomp] at hder
  have hinc := mfderiv_subtypeVal_comp (I := ThreeModel) (J := ThreeModel) Ξ x
  rw [hinc] at hder
  rw [hbirth x, hder]
  rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
