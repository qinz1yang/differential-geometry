import DifferentialGeometry.Topology.Cobordism.HomotopySphere

namespace DifferentialGeometry.Topology

open scoped Manifold ContDiff ContinuousMap
open Metric Set _root_.Topology unitInterval

universe u

theorem isChartDisk.exists_push_off_within {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : isChartDisk e) {B : Set M} (hD : range e ⊆ B)
    {F : I × I → M} (hF : Continuous F) (hFB : ∀ z, F z ∈ B) :
    ∃ F' : I × I → M, Continuous F' ∧ (∀ z, F' z ∈ B \ e '' diskInterior n) ∧
      (∀ z, F z ∉ e '' diskInterior n → F' z = F z) := by
  obtain ⟨F', hF', hmem, hfix, hin⟩ := he.exists_push_off hn hF
  refine ⟨F', hF', fun z => ⟨?_, hmem z⟩, hfix⟩
  by_cases hz : F z ∈ e '' diskInterior n
  · exact hD (hin z hz)
  · rw [hfix z hz]
    exact hFB z

theorem isPathConnected_sdiff_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : isChartDisk e) {B : Set M} (hD : range e ⊆ B)
    (hB : IsPathConnected B) : IsPathConnected (B \ e '' diskInterior n) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e w, hD (mem_range_self w), ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_diskInterior] at h
    exact absurd h (by simp [w, hv])
  · obtain ⟨γ, hγ⟩ := hB.joinedIn x hx.1 y hy.1
    obtain ⟨F', hF', hmem, hfix⟩ := he.exists_push_off_within hn hD
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd) (fun z => hγ z.2)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩,
      ?_, ?_⟩, fun t => hmem (0, t)⟩
    · change F' (0, 0) = x
      rw [hfix (0, 0) (by change γ 0 ∉ _; rw [γ.source]; exact hx.2)]
      exact γ.source
    · change F' (0, 1) = y
      rw [hfix (0, 1) (by change γ 1 ∉ _; rw [γ.target]; exact hy.2)]
      exact γ.target

theorem isSimplyConnected_sdiff_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {e : Disk n → M} (he : isChartDisk e) {B : Set M} (hD : range e ⊆ B)
    (hB : IsSimplyConnected B) : IsSimplyConnected (B \ e '' diskInterior n) := by
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem] at hB ⊢
  refine ⟨isPathConnected_sdiff_chartDisk hn he hD hB.1, fun x p hp => ?_⟩
  obtain ⟨G, hG⟩ := hB.2 x p (fun t => (hp t).1)
  obtain ⟨F', hF', hmem, hfix⟩ := he.exists_push_off_within hn hD
    (F := fun z : I × I => G z) G.continuous hG
  have hx : x ∉ e '' diskInterior n := p.source ▸ (hp 0).2
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by rw [G.apply_zero]; exact (hp s).2)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · change F' (t, 0) = p 0
      rw [hfix (t, 0) (by rw [G.source]; exact hx)]
      rw [G.source, p.source]
    · change F' (t, 1) = p 1
      rw [hfix (t, 1) (by rw [G.target]; exact hx)]
      rw [G.target, p.target]

theorem isPathConnected_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [PathConnectedSpace M] {e : Disk n → M} (he : isChartDisk e) :
    IsPathConnected ((e '' diskInterior n)ᶜ : Set M) := by
  rw [isPathConnected_iff]
  refine ⟨?_, fun x hx y hy => ?_⟩
  · let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, by omega⟩ 1
    have hv : ‖v‖ = 1 := by simp [v]
    let w : Disk n := ⟨v, mem_closedBall_zero_iff.2 hv.le⟩
    refine ⟨e w, ?_⟩
    intro h
    rw [he.injective.mem_set_image, mem_diskInterior] at h
    exact absurd h (by simp [w, hv])
  · let γ := PathConnectedSpace.somePath x y
    obtain ⟨F', hF', hmem, hfix, -⟩ := he.exists_push_off hn
      (F := fun z : I × I => γ z.2) (γ.continuous.comp continuous_snd)
    refine ⟨⟨⟨fun s => F' (0, s), hF'.comp (continuous_const.prodMk continuous_id)⟩,
      ?_, ?_⟩, fun t => hmem (0, t)⟩
    · change F' (0, 0) = x
      rw [hfix (0, 0) (by change γ 0 ∉ _; rw [γ.source]; exact hx)]
      exact γ.source
    · change F' (0, 1) = y
      rw [hfix (0, 1) (by change γ 1 ∉ _; rw [γ.target]; exact hy)]
      exact γ.target

theorem exists_homotopy_refl_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e : Disk n → M} (he : isChartDisk e) (x : M) (p : Path x x)
    (hp : ∀ t, p t ∈ (e '' diskInterior n)ᶜ) :
    ∃ F : p.Homotopy (.refl x), ∀ t, F t ∈ (e '' diskInterior n)ᶜ := by
  obtain ⟨G⟩ := SimplyConnectedSpace.paths_homotopic p (Path.refl x)
  obtain ⟨F', hF', hmem, hfix, -⟩ := he.exists_push_off hn
    (F := fun z : I × I => G z) G.continuous
  have hx : x ∈ (e '' diskInterior n)ᶜ := p.source ▸ hp 0
  refine ⟨{ toFun := F'
            continuous_toFun := hF'
            map_zero_left := fun s => ?_
            map_one_left := fun s => ?_
            prop' := fun t s hs => ?_ }, hmem⟩
  · rw [hfix (0, s) (by rw [G.apply_zero]; exact hp s)]
    exact G.apply_zero s
  · rw [hfix (1, s) (by rw [G.apply_one]; exact hx)]
    exact G.apply_one s
  · rcases hs with rfl | rfl
    · change F' (t, 0) = p 0
      rw [hfix (t, 0) (by rw [G.source]; exact hx)]
      rw [G.source, p.source]
    · change F' (t, 1) = p 1
      rw [hfix (t, 1) (by rw [G.target]; exact hx)]
      rw [G.target, p.target]

theorem simplyConnectedSpace_compl_chartDisk {n : ℕ} (hn : 3 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [SimplyConnectedSpace M] {e : Disk n → M} (he : isChartDisk e) :
    SimplyConnectedSpace ((e '' diskInterior n)ᶜ : Set M) := by
  change IsSimplyConnected _
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  exact ⟨isPathConnected_compl_chartDisk hn he,
    exists_homotopy_refl_compl_chartDisk hn he⟩

theorem simplyConnected_acyclic_compl_chartDisk_of_homotopy_sphere {n : ℕ} (hn : 3 ≤ n)
    {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    (e : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    {d : Disk n → M} (hd : isChartDisk d) :
    SimplyConnectedSpace ((d '' diskInterior n)ᶜ : Set M) ∧
      SingularPair.acyclic SingularPair.integerCoefficients.{u} (TopCat.of ((d '' diskInterior n)ᶜ : Set M)) := by
  have : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    simplyConnectedSpace_sphere (by omega)
  have : SimplyConnectedSpace M := e.simplyConnectedSpace
  exact ⟨simplyConnectedSpace_compl_chartDisk hn hd,
    SingularPair.acyclic_compl_image_diskInterior_integerCoefficients (by omega) e hd⟩

end DifferentialGeometry.Topology
