import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceLocalChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Embedding
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

set_option autoImplicit false
noncomputable section
open Set Filter Manifold TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace BackwardPointTrace

variable {H : ObservedHistory.{u}} {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
  {x y : (H.stage last).Carrier}

theorem endpoint_eq_of_point_first_eq
    (A : BackwardPointTrace H first last hle x) (B : BackwardPointTrace H first last hle y)
    (hfirst : A.point first le_rfl hle = B.point first le_rfl hle) : x = y := by
  have hall : ∀ j (hj : first ≤ j) (hl : j ≤ last), A.point j hj hl = B.point j hj hl := by
    intro j
    induction j using Fin.induction with
    | zero =>
      intro hj hl
      have he : first = 0 := le_antisymm hj (Fin.zero_le _)
      subst first
      exact hfirst
    | succ i ih =>
      intro hj hl
      by_cases he : first = i.succ
      · subst first
        exact hfirst
      · have hf : first ≤ i.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          have hlt : first < i.succ := lt_of_le_of_ne hj he
          change first.val ≤ i.val
          exact Nat.le_of_lt_succ hlt
        have hp := ih hf (i.castSucc_lt_succ.le.trans hl)
        have ha := A.crossing i hf hl
        have hb := B.crossing i hf hl
        rw [hp] at ha
        exact (H.event i).regularCrossing_right_unique ha hb
  exact A.endpoint_eq.symm.trans ((hall last hle le_rfl).trans B.endpoint_eq)

end BackwardPointTrace

namespace ObservedHistory

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)

def backwardSurvivorDomain : Opens (H.stage last).Carrier :=
  ⟨{q | Nonempty (BackwardPointTrace H first last hle q)},
    BackwardPointTrace.isOpen_setOf_nonempty first last hle⟩

def backwardSurvivorMap (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    H.backwardSurvivorDomain first last hle → (H.stage j).Carrier := fun x =>
  (Classical.choice x.property).point j hj hl

theorem backwardSurvivorMap_eq_point
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last)
    (x : H.backwardSurvivorDomain first last hle)
    (A : BackwardPointTrace H first last hle x.val) :
    H.backwardSurvivorMap first last hle j hj hl x = A.point j hj hl := by
  exact congrArg (fun B => B.point j hj hl) (Subsingleton.elim (Classical.choice x.property) A)

@[simp] theorem backwardSurvivorMap_last (x : H.backwardSurvivorDomain first last hle) :
    H.backwardSurvivorMap first last hle last hle le_rfl x = x.val :=
  (Classical.choice x.property).endpoint_eq

theorem backwardSurvivorMap_crossing
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (x : H.backwardSurvivorDomain first last hle) :
    (H.event i).RegularCrossing
      (H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl) x)
      (H.backwardSurvivorMap first last hle i.succ (hf.trans i.castSucc_lt_succ.le) hl x) :=
  (Classical.choice x.property).crossing i hf hl

theorem backwardSurvivorMap_injective
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    Function.Injective (H.backwardSurvivorMap first last hle j hj hl) := by
  intro x y hxy
  apply Subtype.ext
  let A := (Classical.choice x.property).restrictFirst hj hl
  let B := (Classical.choice y.property).restrictFirst hj hl
  exact A.endpoint_eq_of_point_first_eq B hxy

theorem backwardSurvivorMap_isLocalDiffeomorph
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    IsLocalDiffeomorph ThreeModel ThreeModel ∞ (H.backwardSurvivorMap first last hle j hj hl) := by
  let U := H.backwardSurvivorDomain first last hle
  let f := H.backwardSurvivorMap first last hle j hj hl
  have hlocal (x : U) : ∃ F : PartialDiffeomorph ThreeModel ThreeModel
      (H.stage last).Carrier (H.stage j).Carrier ∞,
      x.val ∈ F.source ∧ f =ᶠ[𝓝 x] (fun y : U => F y.val) := by
    let A := (Classical.choice x.property).restrictFirst hj hl
    obtain ⟨F, hxF, _, htrace⟩ :=
      BackwardPointTrace.exists_partialDiffeomorph_point_traces last j hl x.val A
    refine ⟨F, hxF, ?_⟩
    filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
      (F.open_source.mem_nhds hxF)] with y hy
    obtain ⟨B, hB⟩ := htrace y.val hy
    have he : (Classical.choice y.property).restrictFirst hj hl = B := Subsingleton.elim _ _
    exact (congrArg (fun C => C.point j le_rfl hl) he).trans hB
  have hfd : ContMDiff ThreeModel ThreeModel ∞ f := by
    intro x
    obtain ⟨F, hxF, heq⟩ := hlocal x
    have hf := (F.contMDiffOn.contMDiffAt (F.open_source.mem_nhds hxF)).comp x
      contMDiff_subtype_val.contMDiffAt
    exact hf.congr_of_eventuallyEq heq
  apply DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv f hfd _ rfl
  intro x
  obtain ⟨F, hxF, heq⟩ := hlocal x
  rw [heq.mfderiv_eq]
  have hh := (DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := ThreeModel) U x).comp ThreeModel (H.stage j).Carrier
    (F.isLocalDiffeomorphAt ThreeModel ThreeModel ∞ hxF)
  exact (hh.mfderivToContinuousLinearEquiv (by decide)).injective

theorem backwardSurvivorMap_isSmoothEmbedding
    (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
    IsSmoothEmbedding ThreeModel ThreeModel ∞ (H.backwardSurvivorMap first last hle j hj hl) :=
  localDiffeomorph_isSmoothEmbedding_of_injective
    (H.backwardSurvivorMap_isLocalDiffeomorph first last hle j hj hl)
    (H.backwardSurvivorMap_injective first last hle j hj hl)

def backwardSurvivorTerminalMap
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    H.backwardSurvivorDomain first last hle → (H.event i).incoming.terminalRegularOpen := fun x =>
  ⟨H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl) x,
    (H.backwardSurvivorMap_crossing first last hle i hf hl x).mem_terminalRegularRegion (H.event i)⟩

@[simp] theorem backwardSurvivorTerminalMap_val
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (x : H.backwardSurvivorDomain first last hle) :
    (H.backwardSurvivorTerminalMap first last hle i hf hl x).val =
      H.backwardSurvivorMap first last hle i.castSucc hf (i.castSucc_lt_succ.le.trans hl) x := rfl

theorem backwardSurvivorTerminalMap_isSmoothEmbedding
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last) :
    IsSmoothEmbedding ThreeModel ThreeModel ∞
      (H.backwardSurvivorTerminalMap first last hle i hf hl) :=
  DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_intoOpen ThreeModel ThreeModel
    (H.event i).incoming.terminalRegularOpen _
    (H.backwardSurvivorMap_isSmoothEmbedding first last hle i.castSucc hf
      (i.castSucc_lt_succ.le.trans hl))

theorem backwardSurvivorMap_metric_crossing
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (x : H.backwardSurvivorDomain first last hle) (v w : TangentSpace ThreeModel x) :
    (H.initialMetric i.succ).inner
        (H.backwardSurvivorMap first last hle i.succ (hf.trans i.castSucc_lt_succ.le) hl x)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorMap first last hle i.succ (hf.trans i.castSucc_lt_succ.le) hl) x v)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorMap first last hle i.succ (hf.trans i.castSucc_lt_succ.le) hl) x w) =
      (H.event i).terminal.metric.inner
        (H.backwardSurvivorTerminalMap first last hle i hf hl x)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorTerminalMap first last hle i hf hl) x v)
        (mfderiv ThreeModel ThreeModel
          (H.backwardSurvivorTerminalMap first last hle i hf hl) x w) := by
  rw [← H.event_output i]
  exact (H.event i).regularCrossing_chart_metric_inner
    (H.backwardSurvivorTerminalMap first last hle i hf hl)
    (H.backwardSurvivorMap first last hle i.succ (hf.trans i.castSucc_lt_succ.le) hl)
    (H.backwardSurvivorTerminalMap_isSmoothEmbedding first last hle i hf hl) rfl
    (H.backwardSurvivorMap_crossing first last hle i hf hl) x v w

theorem subset_backwardSurvivorDomain_iff {F : Set (H.stage last).Carrier} :
    F ⊆ H.backwardSurvivorDomain first last hle ↔
      ∀ x ∈ F, Nonempty (BackwardPointTrace H first last hle x) := Iff.rfl


end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
