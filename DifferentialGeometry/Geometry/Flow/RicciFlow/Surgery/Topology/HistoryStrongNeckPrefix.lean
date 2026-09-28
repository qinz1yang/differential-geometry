import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryStrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreHistoryPrefix

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace ObservedHistory

private def neckBody (K : ObservedHistory.{u}) (k : Fin (K.eventCount + 1)) {s : ℝ}
    (G : (K.stage k).IncomingSlab (K.time k) s) (eps : ℝ) (y : (K.stage k).Carrier) (t : ℝ)
    (first : Fin (K.eventCount + 1)) (O : Opens (K.stage k).Carrier)
    (f : ∀ (j : Fin K.eventCount), first ≤ j.castSucc → j.succ ≤ k →
      O → (K.event j).incoming.terminalRegularOpen)
    (hf : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f j hj hl)) : Prop :=
  ∃ (hts : K.time first < s) (gflow : ℝ → SmoothRiemannianMetric ThreeModel O),
    K.time first ≤ t - 1 / 5 * (G.flow.scalar t y)⁻¹ ∧
    (∀ (j : Fin K.eventCount) (hj : first ≤ j.castSucc) (hl : j.succ ≤ k),
      ∀ τ ∈ Icc (K.time j.castSucc) (K.time j.succ),
        gflow τ = localPullMetric ((K.event j).terminal.extendedMetric τ) (f j hj hl)
          (hf j hj hl)) ∧
    (∀ τ ∈ Ico (K.time k) s, gflow τ = (G.flow.base.metric τ).restrictOpen O) ∧
    IsSolutionOn ({ base := { metric := gflow } } :
      SolutionOn (I := ThreeModel) (M := O) (RealTimeInterval.closedOpen (K.time first) s hts)) ∧
    ∃ z : O, z.val = y ∧
      Nonempty (TruncatedNeck ({ base := { metric := gflow } } :
        SolutionOn (I := ThreeModel) (M := O)
          (RealTimeInterval.closedOpen (K.time first) s hts)) eps (1 / 5) z t)

end ObservedHistory

namespace RetainedCoreHistory

variable (H : RetainedCoreHistory.{u}) (k : Fin (H.eventCount + 1))

private def backwardPointTraceToPrefix {first : Fin ((H.prefixAt k).eventCount + 1)}
    (hle : first ≤ Fin.last (H.prefixAt k).eventCount) {x : (H.stage k).Carrier}
    (A : BackwardPointTrace H.toHistory
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) k
      (Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)) x) :
    BackwardPointTrace (H.prefixAt k).toHistory first (Fin.last (H.prefixAt k).eventCount) hle x
    where
  point m hm1 hm2 := A.point (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) m) hm1 hm2
  endpoint_eq := (fun (_ : first ≤ Fin.last (H.prefixAt k).eventCount) => A.endpoint_eq) hle
  crossing i hf hl := A.crossing (Fin.castLE (Nat.le_of_lt_succ k.isLt) i) hf hl

private theorem neckBody_prefix_transfer {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    (eps : ℝ) (y : (H.stage k).Carrier) (t : ℝ)
    (first : Fin ((H.prefixAt k).eventCount + 1))
    {O₁ O₂ : Opens (H.stage k).Carrier} (hO : O₁ = O₂)
    (f₁ : ∀ (j : Fin (H.prefixAt k).eventCount), first ≤ j.castSucc →
      j.succ ≤ Fin.last (H.prefixAt k).eventCount →
      O₁ → ((H.prefixAt k).toHistory.event j).incoming.terminalRegularOpen)
    (hf₁ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₁ j hj hl))
    (f₂ : ∀ (j : Fin H.eventCount),
      Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ j.castSucc → j.succ ≤ k →
      O₂ → (H.toHistory.event j).incoming.terminalRegularOpen)
    (hf₂ : ∀ j hj hl, IsLocalDiffeomorph ThreeModel ThreeModel ∞ (f₂ j hj hl))
    (hf : ∀ (j : Fin H.eventCount)
      (hj : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ j.castSucc)
      (hl : j.succ ≤ k) (x : O₁),
      f₂ j hj hl ⟨x.val, hO ▸ x.2⟩ = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl x)
    (hb : (H.prefixAt k).toHistory.neckBody (Fin.last (H.prefixAt k).eventCount) G eps y t first
      O₁ f₁ hf₁) :
    H.toHistory.neckBody k G eps y t
      (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) O₂ f₂ hf₂ := by
  subst hO
  obtain ⟨hts, gflow, hwin, hslabs, hcur, hsol, z, hz, hnk⟩ := hb
  refine ⟨hts, gflow, hwin, ?_, hcur, hsol, z, hz, hnk⟩
  intro j hj hl τ hτ
  rw [hslabs ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl τ hτ]
  have hfe : f₂ j hj hl = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl := funext fun x => hf j hj hl x
  have key : ∀ (ψ : O₁ → (H.toHistory.event j).incoming.terminalRegularOpen)
      (hψ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ψ),
      ψ = f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl →
      localPullMetric ((H.toHistory.event j).terminal.extendedMetric τ)
        (f₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl) (hf₁ ⟨j.val, Nat.lt_of_succ_le hl⟩ hj hl) =
        localPullMetric ((H.toHistory.event j).terminal.extendedMetric τ) ψ hψ := by
    intro ψ hψ h
    subst h
    rfl
  exact key _ _ hfe

theorem historyStrongNeck_of_prefixAt {s : ℝ} (G : (H.stage k).IncomingSlab (H.time k) s)
    {eps t : ℝ} {y : (H.stage k).Carrier}
    (h : (H.prefixAt k).toHistory.HistoryStrongNeck (Fin.last (H.prefixAt k).eventCount) G eps
      y t) :
    H.toHistory.HistoryStrongNeck k G eps y t := by
  obtain ⟨first, hle, hb⟩ := h
  have hleH : Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first ≤ k :=
    Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp hle)
  have hO : (H.prefixAt k).toHistory.backwardSurvivorDomain first
      (Fin.last (H.prefixAt k).eventCount) hle =
      H.toHistory.backwardSurvivorDomain
        (Fin.castLE (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt)) first) k hleH := by
    ext q
    exact ⟨fun ⟨A⟩ => ⟨H.backwardPointTraceOfPrefix k A⟩,
      fun ⟨A⟩ => ⟨backwardPointTraceToPrefix H k hle A⟩⟩
  refine ⟨_, hleH, neckBody_prefix_transfer H k G eps y t first hO _ _ _ _ ?_ hb⟩
  intro j hj hl x
  apply Subtype.ext
  let A := Classical.choice x.property
  exact (H.toHistory.backwardSurvivorMap_eq_point _ k hleH j.castSucc hj
    (j.castSucc_lt_succ.le.trans hl) ⟨x.val, hO ▸ x.2⟩ (H.backwardPointTraceOfPrefix k A)).trans
    ((H.prefixAt k).toHistory.backwardSurvivorMap_eq_point first _ hle
      (⟨j.val, Nat.lt_of_succ_le hl⟩ : Fin (H.prefixAt k).eventCount).castSucc hj
      (Fin.castSucc_lt_succ.le.trans hl) x A).symm

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

end
