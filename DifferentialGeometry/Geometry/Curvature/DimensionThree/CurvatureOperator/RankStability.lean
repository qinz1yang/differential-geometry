import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Basic

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open scoped Matrix _root_.Topology

theorem matrix_rank_le_eventually_of_tendsto
    {α : Type*} {l : Filter α}
    {A : α → Matrix (Fin 3) (Fin 3) ℝ} {B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : Tendsto A l (𝓝 B)) : ∀ᶠ t in l, B.rank ≤ (A t).rank := by
  classical
  let R := LinearMap.range B.mulVecLin
  let β := Module.finBasis ℝ R
  let v : Fin (Module.finrank ℝ R) → Fin 3 → ℝ :=
    fun i => Classical.choose (β i).property
  have hv (i : Fin (Module.finrank ℝ R)) : B *ᵥ v i = (β i : Fin 3 → ℝ) :=
    Classical.choose_spec (β i).property
  have hLI : LinearIndependent ℝ (fun i => B *ᵥ v i) := by
    have heq : (fun i => B *ᵥ v i) = (fun i => (β i : Fin 3 → ℝ)) := funext hv
    rw [heq]
    exact β.linearIndependent.map' R.subtype
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hlim : Tendsto (fun t => fun i => A t *ᵥ v i) l
      (𝓝 (fun i => B *ᵥ v i)) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have hc : Continuous (fun C : Matrix (Fin 3) (Fin 3) ℝ => C *ᵥ v i) :=
      continuous_id.matrix_mulVec continuous_const
    exact (hc.tendsto B).comp hA
  filter_upwards [hlim.eventually hLI.eventually] with t ht
  have hLIrange : LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ R) =>
        (⟨A t *ᵥ v i, ⟨v i, rfl⟩⟩ : LinearMap.range (A t).mulVecLin)) :=
    LinearIndependent.of_comp (LinearMap.range (A t).mulVecLin).subtype ht
  simpa only [Fintype.card_fin, Matrix.rank, R] using hLIrange.fintype_card_le_finrank

theorem curvatureRank_terminal_constancy_of_spreading
    {X : Type*} (A : X → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    {T : ℝ} (hT : 0 < T) (p : X)
    (hcont : ∀ x, ContinuousWithinAt (A x) (Set.Iio T) T)
    (hspread : ∀ s t, 0 < s → s < t → t ≤ T → ∀ x y,
      (A x s).rank ≤ (A y t).rank) :
    (∀ x, (A x T).rank = (A p T).rank) ∧
      ∃ a ∈ Set.Ioo 0 T, ∀ t ∈ Set.Ioc a T, ∀ x,
        (A x t).rank = (A p T).rank := by
  have hle (x y : X) : (A x T).rank ≤ (A y T).rank := by
    have hpersist := matrix_rank_le_eventually_of_tendsto (hcont x)
    obtain ⟨s, hs, hsIoo⟩ := (hpersist.and (Ioo_mem_nhdsLT hT)).exists
    exact hs.trans (hspread s T hsIoo.1 hsIoo.2 le_rfl x y)
  have hterminal (x : X) : (A x T).rank = (A p T).rank :=
    le_antisymm (hle x p) (hle p x)
  have hpersist := matrix_rank_le_eventually_of_tendsto (hcont p)
  obtain ⟨a, haRank, ha⟩ := (hpersist.and (Ioo_mem_nhdsLT hT)).exists
  refine ⟨hterminal, a, ha, ?_⟩
  intro t ht x
  have hlower : (A p T).rank ≤ (A x t).rank :=
    haRank.trans (hspread a t ha.1 ht.1 ht.2 p x)
  have hupper : (A x t).rank ≤ (A p T).rank := by
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact hspread t T (ha.1.trans ht.1) hlt le_rfl x p
    · exact (hterminal x).le
  exact le_antisymm hupper hlower

theorem curvatureRank_positive_time_constancy_of_spreading
    {X : Type*} (A : X → ℝ → Matrix (Fin 3) (Fin 3) ℝ)
    {T : ℝ} (hT : 0 < T) (p : X)
    (hcont : ∀ t ∈ Set.Ioc 0 T, ∀ x, ContinuousWithinAt (A x) (Set.Iio t) t)
    (hspread : ∀ s t, 0 < s → s < t → t ≤ T → ∀ x y,
      (A x s).rank ≤ (A y t).rank) :
    (∀ t ∈ Set.Ioc 0 T, ∀ x, (A x t).rank = (A p t).rank) ∧
      MonotoneOn (fun t => (A p t).rank) (Set.Ioc 0 T) ∧
      (∀ t ∈ Set.Ioc 0 T, ∃ a ∈ Set.Ioo 0 t, ∀ s ∈ Set.Ioc a t, ∀ x,
        (A x s).rank = (A p t).rank) ∧
      ∃ δ ∈ Set.Ioc 0 T, ∀ t ∈ Set.Ioc 0 δ, ∀ x,
        (A x t).rank = (A p δ).rank := by
  classical
  have hlocal (t : ℝ) (ht : t ∈ Set.Ioc 0 T) :=
    curvatureRank_terminal_constancy_of_spreading A ht.1 p (hcont t ht)
      (fun s u hs hsu hu x y => hspread s u hs hsu (hu.trans ht.2) x y)
  have hspatial : ∀ t ∈ Set.Ioc 0 T, ∀ x, (A x t).rank = (A p t).rank :=
    fun t ht => (hlocal t ht).1
  have hmono : MonotoneOn (fun t => (A p t).rank) (Set.Ioc 0 T) := by
    intro s hs t ht hst
    rcases lt_or_eq_of_le hst with hlt | rfl
    · exact hspread s t hs.1 hlt ht.2 p p
    · exact le_rfl
  have hvalues : ∃ n : ℕ, ∃ t ∈ Set.Ioc 0 T, (A p t).rank = n :=
    ⟨(A p T).rank, T, ⟨hT, le_rfl⟩, rfl⟩
  obtain ⟨δ, hδ, hrδ⟩ := Nat.find_spec hvalues
  refine ⟨hspatial, hmono, fun t ht => (hlocal t ht).2, δ, hδ, ?_⟩
  intro t ht x
  have htT : t ∈ Set.Ioc 0 T := ⟨ht.1, ht.2.trans hδ.2⟩
  rw [hspatial t htT x]
  apply le_antisymm (hmono htT hδ ht.2)
  change (A p δ).rank ≤ (A p t).rank
  rw [hrδ]
  exact Nat.find_min' hvalues ⟨t, htT, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
