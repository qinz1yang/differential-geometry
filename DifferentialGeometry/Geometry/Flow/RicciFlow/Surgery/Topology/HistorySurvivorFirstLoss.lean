import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorDomain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFlow
import DifferentialGeometry.Topology.Embedding.Lift

noncomputable section
open Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)}
  {i : Fin H.eventCount} {hle : first ≤ i.castSucc}
  {p : (H.stage i.castSucc).Carrier}

def append (A : BackwardPointTrace H first i.castSucc hle p)
    (q : (H.stage i.succ).Carrier) (hcross : (H.event i).RegularCrossing p q) :
    BackwardPointTrace H first i.succ (hle.trans i.castSucc_lt_succ.le) q where
  point k hf hl := if hki : k = i.succ then hki ▸ q else
    A.point k hf (by
      apply Fin.le_iff_val_le_val.mpr
      have hlt : k < i.succ := lt_of_le_of_ne hl hki
      exact Nat.le_of_lt_succ hlt)
  endpoint_eq := by simp only [dite_true]
  crossing j hf hl := by
    by_cases hji : j = i
    · subst j
      have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
      simpa only [dif_neg hne, dif_pos True.intro, A.endpoint_eq] using hcross
    · have hcast : j.castSucc ≠ i.succ := by
        intro he
        have hlt := j.castSucc_lt_succ
        rw [he] at hlt
        exact (not_lt_of_ge hl) hlt
      have hsucc : j.succ ≠ i.succ := fun he => hji (Fin.succ_injective _ he)
      have hlast : j.succ ≤ i.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        have hlt : j.succ < i.succ := lt_of_le_of_ne hl hsucc
        exact Nat.le_of_lt_succ hlt
      simpa only [dif_neg hcast, dif_neg hsucc] using A.crossing j hf hlast

@[simp] theorem append_point_before
    (A : BackwardPointTrace H first i.castSucc hle p)
    (q : (H.stage i.succ).Carrier) (hcross : (H.event i).RegularCrossing p q)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ i.castSucc) :
    (A.append q hcross).point j hf (hl.trans i.castSucc_lt_succ.le) = A.point j hf hl := by
  have hne : j ≠ i.succ := ne_of_lt (hl.trans_lt i.castSucc_lt_succ)
  simp only [append, dif_neg hne]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y}
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X]

theorem exists_backwardSurvivor_chart_of_point_traces
    (J : X → (H.stage first).Carrier) (hJ : ContMDiff I ThreeModel ∞ J)
    (f : X → (H.stage last).Carrier)
    (A : ∀ x, BackwardPointTrace H first last hle (f x))
    (hfirst : ∀ x, (A x).point first le_rfl hle = J x) :
    ∃ Ξ : X → H.backwardSurvivorDomain first last hle,
      ContMDiff I ThreeModel ∞ Ξ ∧
      (∀ x, (Ξ x).val = f x) ∧
      (∀ x, H.backwardSurvivorMap first last hle first le_rfl hle (Ξ x) = J x) ∧
      ∀ (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ last) (x : X),
        H.backwardSurvivorMap first last hle j hf hl (Ξ x) = (A x).point j hf hl := by
  let F := H.backwardSurvivorMap first last hle first le_rfl hle
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first last hle first le_rfl hle
  have hrange : range J ⊆ range F := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨f x, ⟨A x⟩⟩, ?_⟩
    exact (H.backwardSurvivorMap_eq_point first last hle first le_rfl hle
      ⟨f x, ⟨A x⟩⟩ (A x)).trans (hfirst x)
  let Ξ := hF.lift J hrange
  have heq (x : X) : Ξ x = ⟨f x, ⟨A x⟩⟩ := by
    apply hF.isEmbedding.injective
    exact (hF.comp_lift hrange x).trans
      ((hfirst x).symm.trans
        (H.backwardSurvivorMap_eq_point first last hle first le_rfl hle
          ⟨f x, ⟨A x⟩⟩ (A x)).symm)
  refine ⟨Ξ, hF.contMDiff_lift hJ hrange, ?_, hF.comp_lift hrange, ?_⟩
  · intro x
    rw [heq]
  · intro j hf hl x
    rw [heq]
    exact H.backwardSurvivorMap_eq_point first last hle j hf hl ⟨f x, ⟨A x⟩⟩ (A x)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory


namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {X : Type v}

theorem exists_first_event_of_not_subset_backwardSurvivorMap_range
    (J : X → (H.stage first).Carrier)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ¬ range J ⊆ range (H.backwardSurvivorMap first i.succ
        (hf.trans i.castSucc_lt_succ.le) first le_rfl (hf.trans i.castSucc_lt_succ.le)) := by
  classical
  let bad : Finset (Fin (H.eventCount + 1)) := Finset.univ.filter fun k =>
    ∃ hk : first ≤ k, k ≤ last ∧
      ¬ range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)
  have hbad : bad.Nonempty := ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle, le_rfl, hnot⟩⟩
  obtain ⟨k, hkbad, hminimal⟩ := Finset.exists_min_image bad id hbad
  obtain ⟨hfk, hkl, hkn⟩ := (Finset.mem_filter.mp hkbad).2
  have hself : range J ⊆ range (H.backwardSurvivorMap first first le_rfl first le_rfl le_rfl) := by
    rintro _ ⟨x, rfl⟩
    let z : H.backwardSurvivorDomain first first le_rfl :=
      ⟨J x, ⟨BackwardPointTrace.singleton H first (J x)⟩⟩
    exact ⟨z, H.backwardSurvivorMap_last first first le_rfl z⟩
  have hne : first ≠ k := by
    intro he
    apply hkn
    subst k
    exact hself
  have hlt : first < k := lt_of_le_of_ne hfk hne
  obtain ⟨i, hi⟩ := Fin.eq_succ_of_ne_zero (ne_of_gt ((Fin.zero_le first).trans_lt hlt))
  subst k
  have hf : first ≤ i.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    exact Nat.le_of_lt_succ hlt
  refine ⟨i, hf, hkl, ?_, hkn⟩
  intro j hj hji
  by_contra hn
  have hjbad : j ∈ bad := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hj, hji.trans (i.castSucc_lt_succ.le.trans hkl), hn⟩
  have hmin := hminimal j hjbad
  have hjlt : j < i.succ := hji.trans_lt i.castSucc_lt_succ
  exact (not_le_of_gt hjlt) hmin

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Y : Type*} [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless]
  {X : Type v} [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem exists_first_event_without_regularCrossing
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ Ξ : X → H.backwardSurvivorDomain first i.castSucc hf,
        IsSmoothEmbedding I ThreeModel ∞ Ξ ∧
        (∀ x, H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x) = J x) ∧
        ∃ x : X, ∀ q : (H.stage i.succ).Carrier,
          ¬ (H.event i).RegularCrossing (Ξ x).val q := by
  classical
  obtain ⟨i, hf, hl, hpast, hfail⟩ :=
    H.exists_first_event_of_not_subset_backwardSurvivorMap_range first last hle J hnot
  let F := H.backwardSurvivorMap first i.castSucc hf first le_rfl hf
  have hF := H.backwardSurvivorMap_isSmoothEmbedding first i.castSucc hf first le_rfl hf
  have hrange : range J ⊆ range F := hpast i.castSucc hf le_rfl
  let Ξ := hF.lift J hrange
  have hbirth (x : X) : F (Ξ x) = J x := hF.comp_lift hrange x
  refine ⟨i, hf, hl, hpast, Ξ, hF.isSmoothEmbedding_lift hJ (by simp) hrange, hbirth, ?_⟩
  by_contra hcross
  push Not at hcross
  choose q hq using hcross
  apply hfail
  rintro _ ⟨x, rfl⟩
  let A : BackwardPointTrace H first i.castSucc hf (Ξ x).val := Classical.choice (Ξ x).property
  let B := A.append (q x) (hq x)
  refine ⟨⟨q x, ⟨B⟩⟩, ?_⟩
  have hBx := H.backwardSurvivorMap_eq_point first i.succ
    (hf.trans i.castSucc_lt_succ.le) first le_rfl (hf.trans i.castSucc_lt_succ.le)
      ⟨q x, ⟨B⟩⟩ B
  have hAx := H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Ξ x) A
  exact hBx.trans ((BackwardPointTrace.append_point_before A (q x) (hq x)
    first le_rfl hf).trans (hAx.symm.trans (hbirth x)))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
