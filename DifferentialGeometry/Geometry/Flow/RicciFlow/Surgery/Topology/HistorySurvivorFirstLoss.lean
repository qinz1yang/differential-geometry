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
      simpa only [dite_eq_right hne, dite_eq_left True.intro, A.endpoint_eq] using hcross
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
      simpa only [dite_eq_right hcast, dite_eq_right hsucc] using A.crossing j hf hlast

@[simp] theorem append_point_before
    (A : BackwardPointTrace H first i.castSucc hle p)
    (q : (H.stage i.succ).Carrier) (hcross : (H.event i).RegularCrossing p q)
    (j : Fin (H.eventCount + 1)) (hf : first ≤ j) (hl : j ≤ i.castSucc) :
    (A.append q hcross).point j hf (hl.trans i.castSucc_lt_succ.le) = A.point j hf hl := by
  have hne : j ≠ i.succ := ne_of_lt (hl.trans_lt i.castSucc_lt_succ)
  simp only [append, dite_eq_right hne]

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


noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v
variable (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
  {X : Type v}

theorem exists_regularCrossing_of_backwardSurvivor_initial_eq
    (J : X → (H.stage first).Carrier)
    (i : Fin H.eventCount) (hf : first ≤ i.castSucc) (hl : i.succ ≤ last)
    (Ξ : X → H.backwardSurvivorTerminalFace first i hf)
    (hbirth : ∀ x,
      H.backwardSurvivorMap first i.castSucc hf first le_rfl hf (Ξ x).val = J x)
    (x : X) (endpoint : (H.stage last).Carrier)
    (A : BackwardPointTrace H first last hle endpoint)
    (hA : A.point first le_rfl hle = J x) :
    (H.event i).RegularCrossing (H.backwardSurvivorTerminalFaceMap first i hf (Ξ x)).val
      (A.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) := by
  let B := A.restrictLast hf (i.castSucc_lt_succ.le.trans hl)
  let C : BackwardPointTrace H first i.castSucc hf (Ξ x).val.val :=
    Classical.choice (Ξ x).val.property
  have hfirst : B.point first le_rfl hf = C.point first le_rfl hf := by
    exact hA.trans ((hbirth x).symm.trans
      (H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf (Ξ x).val C))
  have he := B.endpoint_eq_of_point_first_eq C hfirst
  have hc := A.crossing i hf hl
  change (H.event i).RegularCrossing (Ξ x).val.val _
  rwa [he] at hc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

set_option autoImplicit false
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
universe u v
variable {H : ObservedHistory.{u}} {first : Fin (H.eventCount + 1)} {i : Fin H.eventCount}
  {hle : first ≤ i.castSucc}
  {E Y X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace Y] {I : ModelWithCorners ℝ E Y} [I.Boundaryless]
  [TopologicalSpace X] [ChartedSpace Y X] [IsManifold I ∞ X]

theorem exists_backwardSurvivor_chart_after_terminal_crossing
    (J : X → (H.stage first).Carrier) (hJ : IsSmoothEmbedding I ThreeModel ∞ J)
    (Ξ : X → H.backwardSurvivorTerminalFace first i hle)
    (hbirth : ∀ x,
      H.backwardSurvivorMap first i.castSucc hle first le_rfl hle (Ξ x).val = J x)
    (ψ : X → (H.stage i.succ).Carrier)
    (hcross : ∀ x, (H.event i).RegularCrossing
      (H.backwardSurvivorTerminalFaceMap first i hle (Ξ x)).val (ψ x)) :
    ∃ Υ : X → H.backwardSurvivorDomain first i.succ (hle.trans i.castSucc_lt_succ.le),
      IsSmoothEmbedding I ThreeModel ∞ Υ ∧
      (∀ x, (Υ x).val = ψ x) ∧
      (∀ x, H.backwardSurvivorMap first i.succ (hle.trans i.castSucc_lt_succ.le)
        first le_rfl (hle.trans i.castSucc_lt_succ.le) (Υ x) = J x) ∧
      ∀ x, H.backwardSurvivorMap first i.succ (hle.trans i.castSucc_lt_succ.le)
        i.castSucc hle i.castSucc_lt_succ.le (Υ x) = (Ξ x).val.val := by
  classical
  have hcross' (x : X) : (H.event i).RegularCrossing (Ξ x).val.val (ψ x) := hcross x
  let A (x : X) : BackwardPointTrace H first i.castSucc hle (Ξ x).val.val :=
    Classical.choice (Ξ x).val.property
  let B (x : X) : BackwardPointTrace H first i.succ (hle.trans i.castSucc_lt_succ.le) (ψ x) :=
    (A x).append (ψ x) (hcross' x)
  have hBfirst (x : X) : (B x).point first le_rfl (hle.trans i.castSucc_lt_succ.le) = J x := by
    exact ((A x).append_point_before (ψ x) (hcross' x) first le_rfl hle).trans
      ((H.backwardSurvivorMap_eq_point first i.castSucc hle first le_rfl hle (Ξ x).val (A x)).symm.trans
        (hbirth x))
  let b := H.backwardSurvivorMap first i.succ (hle.trans i.castSucc_lt_succ.le)
    first le_rfl (hle.trans i.castSucc_lt_succ.le)
  have hb := H.backwardSurvivorMap_isSmoothEmbedding first i.succ (hle.trans i.castSucc_lt_succ.le)
    first le_rfl (hle.trans i.castSucc_lt_succ.le)
  have hrange : range J ⊆ range b := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨ψ x, ⟨B x⟩⟩, ?_⟩
    exact (H.backwardSurvivorMap_eq_point first i.succ (hle.trans i.castSucc_lt_succ.le)
      first le_rfl (hle.trans i.castSucc_lt_succ.le) ⟨ψ x, ⟨B x⟩⟩ (B x)).trans (hBfirst x)
  let Υ := hb.lift J hrange
  have hΥ : IsSmoothEmbedding I ThreeModel ∞ Υ := hb.isSmoothEmbedding_lift hJ (by simp) hrange
  have hΥeq (x : X) : Υ x = ⟨ψ x, ⟨B x⟩⟩ := by
    apply hb.isEmbedding.injective
    exact (hb.comp_lift hrange x).trans
      ((H.backwardSurvivorMap_eq_point first i.succ (hle.trans i.castSucc_lt_succ.le)
        first le_rfl (hle.trans i.castSucc_lt_succ.le) ⟨ψ x, ⟨B x⟩⟩ (B x)).trans (hBfirst x)).symm
  refine ⟨Υ, hΥ, fun x => congrArg Subtype.val (hΥeq x), hb.comp_lift hrange, ?_⟩
  intro x
  rw [hΥeq, H.backwardSurvivorMap_eq_point _ _ _ _ _ _ _ (B x)]
  change ((A x).append (ψ x) (hcross' x)).point i.castSucc hle _ = (Ξ x).val.val
  exact ((A x).append_point_before (ψ x) (hcross' x) i.castSucc hle le_rfl).trans (A x).endpoint_eq

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u v

theorem exists_first_event_trace_without_regularCrossing
    (H : ObservedHistory.{u}) (first last : Fin (H.eventCount + 1)) (hle : first ≤ last)
    {X : Type v} (J : X → (H.stage first).Carrier)
    (hnot : ¬ range J ⊆ range (H.backwardSurvivorMap first last hle first le_rfl hle)) :
    ∃ (i : Fin H.eventCount) (hf : first ≤ i.castSucc), i.succ ≤ last ∧
      (∀ (k : Fin (H.eventCount + 1)) (hk : first ≤ k), k ≤ i.castSucc →
        range J ⊆ range (H.backwardSurvivorMap first k hk first le_rfl hk)) ∧
      ∃ (x : X) (p : (H.stage i.castSucc).Carrier)
        (A : BackwardPointTrace H first i.castSucc hf p),
        A.point first le_rfl hf = J x ∧
        ∀ q : (H.stage i.succ).Carrier, ¬ (H.event i).RegularCrossing p q := by
  classical
  obtain ⟨i, hf, hl, hpast, hfail⟩ :=
    H.exists_first_event_of_not_subset_backwardSurvivorMap_range first last hle J hnot
  obtain ⟨y, hy, hbad⟩ := Set.not_subset.mp hfail
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨z, hz⟩ := hpast i.castSucc hf le_rfl (mem_range_self x)
  let A : BackwardPointTrace H first i.castSucc hf z.val := Classical.choice z.property
  have hbirth : A.point first le_rfl hf = J x :=
    (H.backwardSurvivorMap_eq_point first i.castSucc hf first le_rfl hf z A).symm.trans hz
  refine ⟨i, hf, hl, hpast, x, z.val, A, hbirth, ?_⟩
  intro q hcross
  let B := A.append q hcross
  apply hbad
  refine ⟨⟨q, ⟨B⟩⟩, ?_⟩
  exact (H.backwardSurvivorMap_eq_point first i.succ (hf.trans i.castSucc_lt_succ.le)
    first le_rfl (hf.trans i.castSucc_lt_succ.le) ⟨q, ⟨B⟩⟩ B).trans
    ((A.append_point_before q hcross first le_rfl hf).trans hbirth)


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
