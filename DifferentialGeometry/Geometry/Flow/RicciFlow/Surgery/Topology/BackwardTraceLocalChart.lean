import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Backward
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SurvivorChartMetric
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

set_option autoImplicit false
noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {last : Fin (H.eventCount + 1)}
  {hle : i.succ ≤ last} {endpoint : (H.stage last).Carrier}

def restrictFirst {first next : Fin (H.eventCount + 1)} {hfirst : first ≤ last}
    (A : BackwardPointTrace H first last hfirst endpoint) (hfn : first ≤ next)
    (hnl : next ≤ last) : BackwardPointTrace H next last hnl endpoint where
  point j hj hl := A.point j (hfn.trans hj) hl
  endpoint_eq := A.endpoint_eq
  crossing j hj hl := A.crossing j (hfn.trans hj) hl

def restrictLast {first next : Fin (H.eventCount + 1)} {hfirst : first ≤ last}
    (A : BackwardPointTrace H first last hfirst endpoint) (hfn : first ≤ next) (hnl : next ≤ last) :
    BackwardPointTrace H first next hfn (A.point next hfn hnl) where
  point j hf hj := A.point j hf (hj.trans hnl)
  endpoint_eq := rfl
  crossing j hf hj := A.crossing j hf (hj.trans hnl)

@[simp] theorem restrictLast_point {first next : Fin (H.eventCount + 1)} {hfirst : first ≤ last}
    (A : BackwardPointTrace H first last hfirst endpoint) (hfn : first ≤ next) (hnl : next ≤ last)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hj : j ≤ next) :
    (A.restrictLast hfn hnl).point j hf hj = A.point j hf (hj.trans hnl) := rfl


def prepend (A : BackwardPointTrace H i.succ last hle endpoint)
    (p : (H.stage i.castSucc).Carrier)
    (hcross : (H.event i).RegularCrossing p (A.point i.succ le_rfl hle)) :
    BackwardPointTrace H i.castSucc last (i.castSucc_lt_succ.le.trans hle) endpoint where
  point k hk hl := if hki : k = i.castSucc then hki ▸ p else
    A.point k (by
      apply Fin.le_iff_val_le_val.mpr
      have hlt : i.castSucc < k := lt_of_le_of_ne hk (Ne.symm hki)
      exact Nat.succ_le_iff.mpr hlt) hl
  endpoint_eq := by
    have hne : last ≠ i.castSucc := by
      intro h
      have := i.castSucc_lt_succ
      rw [h] at hle
      exact (not_le_of_gt this) hle
    simp only [dite_eq_right hne]
    exact A.endpoint_eq
  crossing j hf hl := by
    by_cases hji : j = i
    · subst j
      have hsne : i.succ ≠ i.castSucc := ne_of_gt i.castSucc_lt_succ
      simpa only [dite_eq_left True.intro, dite_eq_right hsne] using hcross
    · have hcast : j.castSucc ≠ i.castSucc := by
        intro h
        exact hji (Fin.castSucc_injective _ h)
      have hsne : j.succ ≠ i.castSucc := by
        intro h
        have hlt := j.castSucc_lt_succ
        rw [h] at hlt
        exact (not_lt_of_ge hf) hlt
      have hfirst : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : i.castSucc < j.castSucc := lt_of_le_of_ne hf (Ne.symm hcast)
        exact Nat.succ_le_iff.mpr hlt
      simpa only [dite_eq_right hcast, dite_eq_right hsne] using A.crossing j hfirst hl

@[simp] theorem prepend_point_first (A : BackwardPointTrace H i.succ last hle endpoint)
    (p : (H.stage i.castSucc).Carrier)
    (hcross : (H.event i).RegularCrossing p (A.point i.succ le_rfl hle)) :
    (A.prepend p hcross).point i.castSucc le_rfl (i.castSucc_lt_succ.le.trans hle) = p := by
  simp [prepend]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

set_option autoImplicit false
noncomputable section

open Set Manifold
open DifferentialGeometry
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

universe u
variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)

theorem RegularCrossing.exists_ambient_partialDiffeomorph
    {p : P.Carrier} {q : Q.Carrier} (h : E.RegularCrossing p q) :
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel P.Carrier Q.Carrier ∞,
      p ∈ F.source ∧ F p = q ∧
      ∀ x ∈ F.source, E.RegularCrossing x (F x) := by
  obtain ⟨z, hz, hp, hq⟩ := h
  let p₀ : E.incoming.terminalRegularOpen := E.oldTerminal z
  have hp₀ : p₀.val = p := (E.oldTerminal_eq z).trans hp
  have hc : E.RegularCrossing p₀.val q := ⟨z, hz, (E.oldTerminal_eq z).symm, hq⟩
  obtain ⟨F, _, hsrc, heq, _, hcross, _⟩ := hc.exists_survivor_partialDiffeomorph E
  let inc := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph
    ThreeModel E.incoming.terminalRegularOpen ⟨p₀⟩
  let C := inc.symm.trans F
  have hinc : inc p₀ = p := by
    change p₀.val = p
    exact hp₀
  have hpinc : p ∈ inc.target := by
    rw [← hinc]
    exact inc.map_source (by trivial)
  have hinv : inc.symm p = p₀ := by rw [← hinc]; exact inc.left_inv (by trivial)
  have hCsrc : p ∈ C.source := by
    change p ∈ inc.target ∧ inc.symm p ∈ F.source
    exact ⟨hpinc, hinv ▸ hsrc⟩
  refine ⟨C, hCsrc, ?_, ?_⟩
  · change F (inc.symm p) = q
    rw [hinv, heq]
  · intro x hx
    change x ∈ inc.target ∧ inc.symm x ∈ F.source at hx
    have h := hcross (inc.symm x) hx.2
    have hincl : (inc.symm x).val = x := inc.right_inv hx.1
    change E.RegularCrossing x (F (inc.symm x))
    rwa [hincl] at h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.MetricCutCapEvent

set_option autoImplicit false
noncomputable section

open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem exists_partialDiffeomorph_point_traces (last first : Fin (H.eventCount + 1)) :
    ∀ (hle : first ≤ last) (endpoint : (H.stage last).Carrier)
      (A : BackwardPointTrace H first last hle endpoint),
    ∃ F : PartialDiffeomorph ThreeModel ThreeModel (H.stage last).Carrier (H.stage first).Carrier ∞,
      endpoint ∈ F.source ∧ F endpoint = A.point first le_rfl hle ∧
      ∀ q ∈ F.source, ∃ B : BackwardPointTrace H first last hle q,
        B.point first le_rfl hle = F q := by
  induction first using Fin.reverseInduction with
  | last =>
    intro hle endpoint A
    have heq : last = Fin.last H.eventCount := le_antisymm (Fin.le_last _) hle
    subst last
    refine ⟨(Diffeomorph.refl ThreeModel _ ∞).toPartialDiffeomorph,
      by trivial, A.endpoint_eq.symm, ?_⟩
    intro q _
    exact ⟨singleton H _ q, rfl⟩
  | cast i ih =>
    intro hle endpoint A
    by_cases heq : i.castSucc = last
    · subst last
      refine ⟨(Diffeomorph.refl ThreeModel _ ∞).toPartialDiffeomorph,
      by trivial, A.endpoint_eq.symm, ?_⟩
      intro q _
      exact ⟨singleton H _ q, rfl⟩
    · have hsucc : i.succ ≤ last := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : i.castSucc < last := lt_of_le_of_ne hle heq
        exact Nat.succ_le_iff.mpr hlt
      let tail := A.restrictFirst i.castSucc_lt_succ.le hsucc
      obtain ⟨F, hpF, heF, htrace⟩ := ih hsucc endpoint tail
      obtain ⟨G, hpG, heG, hcross⟩ :=
        (A.crossing i le_rfl hsucc).exists_ambient_partialDiffeomorph (H.event i)
      let K := F.trans G.symm
      have hpK : endpoint ∈ K.source := by
        refine ⟨hpF, ?_⟩
        change F endpoint ∈ G.target
        rw [heF]
        exact heG ▸ G.map_source hpG
      refine ⟨K, hpK, ?_, ?_⟩
      · change G.symm (F endpoint) = A.point i.castSucc le_rfl hle
        rw [heF]
        change G.symm (A.point i.succ i.castSucc_lt_succ.le hsucc) = _
        rw [← heG]
        exact G.left_inv hpG
      · intro q hq
        change q ∈ F.source ∧ F q ∈ G.target at hq
        obtain ⟨B, hB⟩ := htrace q hq.1
        have hc := hcross (G.symm (F q)) (G.map_target hq.2)
        have hright : G (G.symm (F q)) = F q := G.right_inv hq.2
        rw [hright] at hc
        have hcB : (H.event i).RegularCrossing (G.symm (F q))
            (B.point i.succ le_rfl hsucc) := hB ▸ hc
        refine ⟨B.prepend (G.symm (F q)) hcB, ?_⟩
        exact prepend_point_first B _ hcB

theorem exists_smooth_stage_charts
    {first last : Fin (H.eventCount + 1)} {hle : first ≤ last}
    {endpoint : (H.stage last).Carrier} (A : BackwardPointTrace H first last hle endpoint) :
    ∃ U : TopologicalSpace.Opens (H.stage last).Carrier, endpoint ∈ U ∧
      ∃ chart : ∀ j, first ≤ j → j ≤ last →
          PartialDiffeomorph ThreeModel ThreeModel (H.stage last).Carrier (H.stage j).Carrier ∞,
        (∀ j hj hl, (U : Set (H.stage last).Carrier) ⊆ (chart j hj hl).source) ∧
        (∀ j hj hl, chart j hj hl endpoint = A.point j hj hl) ∧
        (∀ x ∈ U, chart last hle le_rfl x = x) ∧
        ∀ i : Fin H.eventCount, ∀ hf : first ≤ i.castSucc, ∀ hl : i.succ ≤ last,
          ∀ x ∈ U,
          (H.event i).RegularCrossing
            (chart i.castSucc hf ((Fin.castSucc_lt_succ (i := i)).le.trans hl) x)
            (chart i.succ (hf.trans (Fin.castSucc_lt_succ (i := i)).le) hl x) := by
  classical
  have hex (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :=
    exists_partialDiffeomorph_point_traces last j hl endpoint (A.restrictFirst hj hl)
  choose chart hsource hcenter htrace using hex
  let U : TopologicalSpace.Opens (H.stage last).Carrier :=
    ⟨⋂ (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last), (chart j hj hl).source,
      isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun hj =>
        isOpen_iInter_of_finite fun hl => (chart j hj hl).open_source⟩
  have hpU : endpoint ∈ U := mem_iInter.mpr fun j =>
    mem_iInter.mpr fun hj => mem_iInter.mpr fun hl => hsource j hj hl
  have hsrc (j : Fin (H.eventCount + 1)) (hj : first ≤ j) (hl : j ≤ last) :
      (U : Set (H.stage last).Carrier) ⊆ (chart j hj hl).source := by
    intro x hx
    exact mem_iInter.mp (mem_iInter.mp (mem_iInter.mp hx j) hj) hl
  have heval (x : (H.stage last).Carrier) (hx : x ∈ U) :
      ∃ B : BackwardPointTrace H first last hle x,
        ∀ j hj hl, B.point j hj hl = chart j hj hl x := by
    obtain ⟨B, _⟩ := htrace first le_rfl hle x (hsrc first le_rfl hle hx)
    refine ⟨B, ?_⟩
    intro j hj hl
    obtain ⟨C, hC⟩ := htrace j hj hl x (hsrc j hj hl hx)
    have heq : B.restrictFirst hj hl = C := Subsingleton.elim _ _
    exact (congrArg (fun D => D.point j le_rfl hl) heq).trans hC
  refine ⟨U, hpU, chart, hsrc, hcenter, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB⟩ := heval x hx
    exact (hB last hle le_rfl).symm.trans B.endpoint_eq
  · intro i hf hl x hx
    obtain ⟨B, hB⟩ := heval x hx
    have h := B.crossing i hf hl
    simpa only [hB] using h

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

set_option autoImplicit false
noncomputable section
open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}}

theorem isOpen_setOf_nonempty (first last : Fin (H.eventCount + 1)) (hle : first ≤ last) :
    IsOpen {q : (H.stage last).Carrier | Nonempty (BackwardPointTrace H first last hle q)} := by
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨A⟩
  obtain ⟨F, hq, _, htrace⟩ := exists_partialDiffeomorph_point_traces last first hle q A
  apply Filter.mem_of_superset (F.open_source.mem_nhds hq)
  intro x hx
  obtain ⟨B, _⟩ := htrace x hx
  exact ⟨B⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
