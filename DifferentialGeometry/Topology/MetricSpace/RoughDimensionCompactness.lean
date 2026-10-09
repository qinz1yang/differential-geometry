import DifferentialGeometry.Topology.MetricSpace.RoughDimension
import DifferentialGeometry.Topology.MetricSpace.FiniteNets

set_option autoImplicit false

open Set Filter
open scoped Topology ENNReal NNReal

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem eventually_finitePackingNumber_ne_top_of_roughVolume_eq_zero
    {S : Set X} {a : ℝ} (hv : roughVolume a S = 0) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, finitePackingNumber ε S ≠ ⊤ := by
  have hlim : limsup (fun ε : ℝ => ENNReal.ofReal (ε ^ a) *
      (finitePackingNumber ε S : ℝ≥0∞)) (𝓝[>] 0) < 1 := by
    change roughVolume a S < 1
    rw [hv]
    exact zero_lt_one
  have hev := eventually_lt_of_limsup_lt hlim
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos
  change 0 < ε at hpos
  intro htop
  have hp : ENNReal.ofReal (ε ^ a) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hpos a)).ne'
  rw [htop, ENat.toENNReal_top, ENNReal.mul_top hp] at hε
  exact not_top_lt hε

theorem totallyBounded_of_roughDim_lt_top {S : Set X} (hd : roughDim S < ⊤) :
    TotallyBounded S := by
  unfold roughDim at hd
  obtain ⟨a, ha⟩ := iInf_lt_iff.mp hd
  obtain ⟨hv, _⟩ := iInf_lt_iff.mp ha
  have hev := eventually_finitePackingNumber_ne_top_of_roughVolume_eq_zero hv
  rw [Metric.totallyBounded_iff]
  intro ε hε
  have hsmall : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < ε :=
    (gt_mem_nhds hε).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδpos, hδε, hfinite⟩ :=
    (hpositive.and (hsmall.and hev)).exists
  change 0 < δ at hδpos
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hpack (A : Finset X) (hA : (A : Set X) ⊆ S)
      (hsep : (A : Set X).Pairwise (fun x y => δ ≤ dist x y)) : A.card ≤ N := by
    have hb := card_le_finitePackingNumber A hA hsep
    rw [← hN] at hb
    exact_mod_cast hb
  obtain ⟨A, _, _, hnet⟩ := exists_finset_net_card_le_of_packing hδpos N hpack
  refine ⟨A, A.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hnet x hx
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy.trans hδε⟩⟩


theorem exists_compact_closedBall_of_roughDim_lt_top {S : Set X} {p : X}
    (hS : S ∈ 𝓝 p) (hd : roughDim S < ⊤)
    (hcomplete : ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall p R)) :
    ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ S ∧ IsCompact (closedBall p r) := by
  obtain ⟨h, hh, hB⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨R, hR, hRc⟩ := hcomplete
  let r := min (h / 2) R
  have hr : 0 < r := lt_min (half_pos hh) hR
  have hrh : r < h := (min_le_left _ _).trans_lt (half_lt_self hh)
  have hrR : r ≤ R := min_le_right _ _
  have hsub : closedBall p r ⊆ S := (closedBall_subset_ball hrh).trans hB
  have hrc : IsComplete (closedBall p r) := by
    intro f hf hfs
    obtain ⟨x, _, hfx⟩ := hRc f hf
      (hfs.trans (Filter.principal_mono.mpr (closedBall_subset_closedBall hrR)))
    exact ⟨x, isClosed_iff_clusterPt.mp isClosed_closedBall x
      (hf.1.mono (le_inf hfx hfs)), hfx⟩
  exact ⟨r, hr, hsub, ((totallyBounded_of_roughDim_lt_top hd).subset hsub).isCompact_of_isComplete hrc⟩

end Metric

