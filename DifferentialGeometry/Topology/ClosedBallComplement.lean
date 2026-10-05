import DifferentialGeometry.Topology.ConnectedComplement
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.OpenPartialHomeomorph.Basic

set_option autoImplicit false
noncomputable section
open Set Function Metric
open scoped Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isConnected_ball_sdiff_closedBall (hdim : 1 < Module.rank ℝ E)
    {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    IsConnected (Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r) := by
  have hs := (isPathConnected_sphere hdim (0 : E) zero_le_one).isConnected
  have hi := isConnected_Ioo hrR
  have heq : (fun p : E × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : E) 1 ×ˢ Ioo r R) = Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩
      have hz' : ‖z‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      have ht0 : 0 < t := hr.trans_lt ht.1
      rw [mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        norm_smul, Real.norm_of_nonneg ht0.le, hz', mul_one, not_le]
      exact ⟨ht.2, ht.1⟩
    · intro hx
      have hxR : ‖x‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hx.1
      have hxr : r < ‖x‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx.2
      have hxpos := hr.trans_lt hxr
      refine ⟨(‖x‖⁻¹ • x, ‖x‖), ⟨?_, hxr, hxR⟩, ?_⟩
      · rw [Metric.mem_sphere, dist_zero_right, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr hxpos.le), inv_mul_cancel₀ hxpos.ne']
      · change ‖x‖ • (‖x‖⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  rw [← heq]
  exact (hs.prod hi).image _ (by fun_prop)

private theorem exists_connected_collars_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    ∃ V : ι → Set M, (∀ i, IsOpen (V i)) ∧
      (∀ i, e i '' Metric.closedBall 0 (r i) ⊆ V i) ∧
      (∀ i j, i ≠ j → Disjoint (V i) (e j '' Metric.closedBall 0 (r j))) ∧
      ∀ i, IsConnected (V i \ e i '' Metric.closedBall 0 (r i)) := by
  classical
  let K (i : ι) : Set M := e i '' Metric.closedBall 0 (r i)
  have hK (i : ι) : IsCompact (K i) :=
    (isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))
  let L (i : ι) : Set M := ⋃ j : {j : ι // j ≠ i}, K j.val
  have hL (i : ι) : IsClosed (L i) :=
    isClosed_iUnion_of_finite fun j => (hK j.val).isClosed
  have hsub (i : ι) : Metric.closedBall 0 (r i) ⊆
      (e i).source ∩ (e i) ⁻¹' (L i)ᶜ := by
    intro x hx
    refine ⟨hs i hx, ?_⟩
    change e i x ∉ L i
    intro hxL
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxL
    exact Set.disjoint_left.mp (hdisj i j.val (Ne.symm j.property)) ⟨x, hx, rfl⟩ hj
  have hR (i : ι) : ∃ R : ℝ, r i < R ∧
      Metric.ball 0 R ⊆ (e i).source ∩ (e i) ⁻¹' (L i)ᶜ := by
    have ho : IsOpen ((e i).source ∩ (e i) ⁻¹' (L i)ᶜ) :=
      (e i).isOpen_inter_preimage (hL i).isOpen_compl
    obtain ⟨δ, hδ, hδsub⟩ :=
      (isCompact_closedBall (0 : E) (r i)).exists_thickening_subset_open ho (hsub i)
    rw [thickening_closedBall hδ (hr i)] at hδsub
    refine ⟨r i + δ / 2, by linarith only [hδ], ?_⟩
    exact (Metric.ball_subset_ball (by linarith only [hδ] : r i + δ / 2 ≤ δ + r i)).trans hδsub
  choose R hRlt hRs using hR
  let V (i : ι) : Set M := e i '' Metric.ball 0 (R i)
  have hopen (i : ι) : IsOpen (V i) :=
    (e i).isOpen_image_of_subset_source Metric.isOpen_ball (fun x hx => (hRs i hx).1)
  have hKV (i : ι) : K i ⊆ V i :=
    Set.image_mono (Metric.closedBall_subset_ball (hRlt i))
  have hVK (i j : ι) (hij : i ≠ j) : Disjoint (V i) (K j) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    exact (hRs i hx).2 (Set.mem_iUnion.mpr ⟨⟨j, Ne.symm hij⟩, hy⟩)
  have hconn (i : ι) : IsConnected (V i \ K i) := by
    have hinj : Set.InjOn (e i) (Metric.ball 0 (R i)) :=
      (e i).injOn.mono (fun x hx => (hRs i hx).1)
    have heq := hinj.image_sdiff_subset (Metric.closedBall_subset_ball (hRlt i))
    change e i '' (Metric.ball 0 (R i) \ Metric.closedBall 0 (r i)) = V i \ K i at heq
    rw [← heq]
    exact (isConnected_ball_sdiff_closedBall hdim (hr i) (hRlt i)).image _
      ((e i).continuousOn_toFun.mono (fun x hx => (hRs i hx.1).1))
  exact ⟨V, hopen, hKV, hVK, hconn⟩

theorem isPreconnected_compl_iUnion_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    IsPreconnected ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M) := by
  obtain ⟨V, hV, hKV, hVK, hconn⟩ :=
    exists_connected_collars_image_closedBall e r hdim hr hs hdisj
  have hK (i : ι) : IsClosed (e i '' Metric.closedBall 0 (r i)) :=
    ((isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))).isClosed
  exact isPreconnected_compl_iUnion_of_collar
    (fun i => e i '' Metric.closedBall 0 (r i)) V hK hV hKV hVK hconn

theorem isPathConnected_compl_iUnion_image_closedBall
    [ProperSpace E] {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [LocallyPathConnectedSpace M]
    {ι : Type*} [Finite ι] (e : ι → OpenPartialHomeomorph E M) (r : ι → ℝ)
    (hdim : 1 < Module.rank ℝ E) (hr : ∀ i, 0 ≤ r i)
    (hs : ∀ i, Metric.closedBall 0 (r i) ⊆ (e i).source)
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (e i '' Metric.closedBall 0 (r i)) (e j '' Metric.closedBall 0 (r j))) :
    IsPathConnected ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M) := by
  classical
  obtain ⟨V, hV, hKV, hVK, hconn⟩ :=
    exists_connected_collars_image_closedBall e r hdim hr hs hdisj
  have hK (i : ι) : IsClosed (e i '' Metric.closedBall 0 (r i)) :=
    ((isCompact_closedBall (0 : E) (r i)).image_of_continuousOn
      ((e i).continuousOn_toFun.mono (hs i))).isClosed
  have hpre := isPreconnected_compl_iUnion_of_collar
    (fun i => e i '' Metric.closedBall 0 (r i)) V hK hV hKV hVK hconn
  have hne : ((⋃ i, e i '' Metric.closedBall 0 (r i))ᶜ : Set M).Nonempty := by
    rcases isEmpty_or_nonempty ι with hI | hI
    · refine ⟨Classical.arbitrary M, ?_⟩
      simp only [mem_compl_iff, mem_iUnion, not_exists]
      exact fun i => isEmptyElim i
    · obtain ⟨i⟩ := hI
      obtain ⟨x, hx⟩ := (hconn i).nonempty
      refine ⟨x, ?_⟩
      intro hmem
      obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
      by_cases hji : j = i
      · exact hx.2 (hji ▸ hj)
      · exact Set.disjoint_left.mp (hVK i j (Ne.symm hji)) hx.1 hj
  exact (isClosed_iUnion_of_finite hK).isOpen_compl.isConnected_iff_isPathConnected.mp
    ⟨hne, hpre⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M] [PreconnectedSpace M]
  [LocallyPathConnectedSpace M] [ProperSpace E]

theorem isPathConnected_compl_image_closedBall
    (e : OpenPartialHomeomorph E M) (hdim : 1 < Module.rank ℝ E)
    {r : ℝ} (hr : 0 ≤ r) (hs : Metric.closedBall 0 r ⊆ e.source) :
    IsPathConnected ((e '' Metric.closedBall 0 r)ᶜ : Set M) := by
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_closedBall (0 : E) r).exists_thickening_subset_open e.open_source hs
  rw [thickening_closedBall hδ hr] at hδsub
  let R := r + δ / 2
  have hrR : r < R := by dsimp [R]; linarith
  have hRs : Metric.ball (0 : E) R ⊆ e.source :=
    (Metric.ball_subset_ball (by dsimp [R]; linarith : R ≤ δ + r)).trans hδsub
  let K := e '' Metric.closedBall (0 : E) r
  let V := e '' Metric.ball (0 : E) R
  have hK : IsCompact K := (isCompact_closedBall (0 : E) r).image_of_continuousOn
    (e.continuousOn_toFun.mono hs)
  have hV : IsOpen V := e.isOpen_image_of_subset_source Metric.isOpen_ball hRs
  have hKV : K ⊆ V := Set.image_mono (Metric.closedBall_subset_ball hrR)
  have hconn : IsConnected (V \ K) := by
    have hinj : InjOn e (Metric.ball (0 : E) R) := e.injOn.mono hRs
    have himage := hinj.image_sdiff_subset (Metric.closedBall_subset_ball hrR)
    change e '' (Metric.ball (0 : E) R \ Metric.closedBall (0 : E) r) = V \ K at himage
    rw [← himage]
    exact (isConnected_ball_sdiff_closedBall hdim hr hrR).image _
      (e.continuousOn_toFun.mono (fun _ hx => hRs hx.1))
  have hpre := isPreconnected_compl_iUnion_of_collar (X := M)
    (fun _ : Unit => K) (fun _ : Unit => V) (fun _ => hK.isClosed) (fun _ => hV)
    (fun _ => hKV) (fun i j hij => False.elim (hij (Subsingleton.elim i j))) (fun _ => hconn)
  have hpre' : IsPreconnected (Kᶜ : Set M) := by simpa only [iUnion_const] using hpre
  have hne : (Kᶜ : Set M).Nonempty := hconn.nonempty.mono (fun _ hx => hx.2)
  exact hK.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp ⟨hne, hpre'⟩

end DifferentialGeometry.Topology
