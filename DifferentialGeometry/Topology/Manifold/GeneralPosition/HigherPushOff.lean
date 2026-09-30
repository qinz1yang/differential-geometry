import DifferentialGeometry.Topology.Manifold.GeneralPosition.PushOff
import DifferentialGeometry.Topology.ClosedBall.NullhomotopyExtension

namespace DifferentialGeometry.Topology

open Metric Set unitInterval _root_.Topology Module
open scoped ContinuousMap

variable {m n : ℕ} {K : Set (EuclideanSpace ℝ (Fin m))} [CompactSpace K]

theorem exists_continuous_near_avoiding_on_compact (hmn : m < n)
    {f : K → EuclideanSpace ℝ (Fin n)} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : K → EuclideanSpace ℝ (Fin n)) (d : EuclideanSpace ℝ (Fin n)),
      Continuous g ∧ ‖d‖ < ε ∧ (∀ z, ‖g z - f z‖ < ε) ∧ ∀ z, g z ≠ d := by
  obtain ⟨G, hG, hGf⟩ := exists_differentiable_near_on_compact hf hε
  have hdim : finrank ℝ (EuclideanSpace ℝ (Fin m)) <
      finrank ℝ (EuclideanSpace ℝ (Fin n)) := by simpa using hmn
  obtain ⟨d, hdG, hd⟩ := (hG.dense_compl_range_of_finrank_lt_finrank hdim).exists_mem_open
    isOpen_ball (nonempty_ball.mpr hε : (ball (0 : EuclideanSpace ℝ (Fin n)) ε).Nonempty)
  exact ⟨fun z => G z.1, d, hG.continuous.comp continuous_subtype_val,
    mem_ball_zero_iff.mp hd, hGf, fun z hz => hdG ⟨z.1, hz⟩⟩

variable {M : Type*} [TopologicalSpace M]

theorem exists_push_off_center_on_compact [T2Space M] (hmn : m < n)
    (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))) {c : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ φ.target) {F : K → M}
    (hF : Continuous F) :
    ∃ F' : K → M, Continuous F' ∧ (∀ z, F' z ≠ φ.symm c) ∧
      (∀ z, ¬ (F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R) → F' z = F z) ∧
      (∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → F' z ∈ φ.source ∧ ‖φ (F' z) - c‖ < R) := by
  classical
  have h14 : R / 4 < R / 2 := by linarith
  have h24 : R / 2 < 3 * R / 4 := by linarith
  have hsub2 : closedBall c (R / 2) ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  have hsub3 : closedBall c (3 * R / 4) ⊆ φ.target :=
    (closedBall_subset_closedBall (by linarith)).trans hsub
  have hball : ball c R ⊆ φ.target := ball_subset_closedBall.trans hsub
  have hc : c ∈ φ.target := hsub (mem_closedBall_self hR.le)
  set κ : M → ℝ := chartCutoff φ c (R / 4) (R / 2) with hκ
  set μ : M → ℝ := chartCutoff φ c (R / 2) (3 * R / 4) with hμ
  have hf : Continuous fun z : K => μ (F z) • (φ (F z) - c) :=
    (continuous_chartCutoff_smul h24 hsub3).comp hF
  obtain ⟨g, d, hg, hd, hgf, hgd⟩ :=
    exists_continuous_near_avoiding_on_compact hmn hf (ε := R / 8) (by linarith)
  set f : K → EuclideanSpace ℝ (Fin n) := fun z => μ (F z) • (φ (F z) - c) with hf_def
  set lam : K → ℝ := fun z => κ (F z) with hlam
  have hlamc : Continuous lam := (chartCutoff_continuous h14 hsub2).comp hF
  set H : K → EuclideanSpace ℝ (Fin n) :=
    fun z => (1 - lam z) • φ (F z) + lam z • (c + g z - d) with hH
  have hHz : ∀ z, H z = (1 - lam z) • φ (F z) + lam z • (c + g z - d) := fun z => rfl
  have hlam01 : ∀ z, lam z ∈ Icc (0 : ℝ) 1 := fun z => chartCutoff_mem_Icc (F z)
  have hlam_pos : ∀ z, 0 < lam z → F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R / 2 :=
    fun z h => lt_of_chartCutoff_pos h14 h
  have hf_eq : ∀ z, 0 < lam z → f z = φ (F z) - c := by
    intro z h
    have hμ1 : μ (F z) = 1 := chartCutoff_eq_one h24 (hlam_pos z h).1 (hlam_pos z h).2.le
    change μ (F z) • (φ (F z) - c) = φ (F z) - c
    rw [hμ1, one_smul]
  have hH_zero : ∀ z, lam z = 0 → H z = φ (F z) := by
    intro z h
    rw [hHz, h]; simp
  have hH_one : ∀ z, lam z = 1 → H z - c = g z - d := by
    intro z h
    rw [hHz, h]
    simp only [sub_self, zero_smul, one_smul, zero_add]
    abel
  have hH_sub : ∀ z, 0 < lam z → H z - φ (F z) = lam z • (g z - f z - d) := by
    intro z h
    rw [hHz, hf_eq z h]
    module
  have hHnorm : ∀ z, 0 < lam z → ‖H z - φ (F z)‖ < R / 4 := by
    intro z h
    rw [hH_sub z h, norm_smul, Real.norm_of_nonneg (hlam01 z).1]
    have h1 : ‖g z - f z - d‖ < R / 4 :=
      (norm_sub_le _ _).trans_lt (by linarith [hgf z, hd])
    calc lam z * ‖g z - f z - d‖ ≤ ‖g z - f z - d‖ :=
          mul_le_of_le_one_left (norm_nonneg _) (hlam01 z).2
      _ < R / 4 := h1
  have hHball : ∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → ‖H z - c‖ < R ∧ H z ≠ c := by
    intro z hz
    rcases (hlam01 z).1.lt_or_eq with hpos | hzero
    · have hsub' := hHnorm z hpos
      have hFz := hlam_pos z hpos
      refine ⟨?_, ?_⟩
      · calc ‖H z - c‖ = ‖(H z - φ (F z)) + (φ (F z) - c)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖H z - φ (F z)‖ + ‖φ (F z) - c‖ := norm_add_le _ _
          _ < R := by linarith
      · rcases (hlam01 z).2.lt_or_eq with hlt | heq
        · have h14' : R / 4 < ‖φ (F z) - c‖ := lt_of_chartCutoff_lt_one h14 hFz.1 hlt
          intro hHc
          rw [hHc, norm_sub_rev] at hsub'
          linarith
        · have h1 := hH_one z heq
          intro hHc
          rw [hHc, sub_self] at h1
          exact hgd z (sub_eq_zero.1 h1.symm)
    · have hHz' := hH_zero z hzero.symm
      refine ⟨by rw [hHz']; exact hz.2, ?_⟩
      rw [hHz']
      intro hφc
      have hκ1 : κ (F z) = 1 :=
        chartCutoff_eq_one h14 hz.1 (by rw [hφc, sub_self, norm_zero]; linarith)
      have : lam z = κ (F z) := rfl
      rw [this, hκ1] at hzero
      exact zero_ne_one hzero
  have hHtarget : ∀ z, F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R → H z ∈ φ.target := fun z hz =>
    hball (mem_ball_iff_norm.2 (hHball z hz).1)
  set S : Set (K) := {z | F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R} with hS
  have hSopen : IsOpen S := by
    have : S = F ⁻¹' (φ.symm '' ball c R) := by
      ext z
      simp only [hS, mem_ofPred_eq, mem_preimage, φ.symm_image_eq_source_inter_preimage hball,
        mem_inter_iff, mem_ball_iff_norm]
    rw [this]
    exact (φ.isOpen_image_symm_of_subset_target isOpen_ball hball).preimage hF
  have hcl : closure S ⊆ F ⁻¹' (φ.symm '' closedBall c R) := by
    refine closure_minimal (fun z hz => ⟨φ (F z), ?_, φ.left_inv hz.1⟩)
      ((isClosed_symm_image_closedBall hsub).preimage hF)
    rw [mem_closedBall_iff_norm]; exact hz.2.le
  have hcl' : ∀ z ∈ closure S, F z ∈ φ.source ∧ ‖φ (F z) - c‖ ≤ R := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := hcl hz
    have hyt : y ∈ φ.target := hsub hy
    refine ⟨hyz ▸ φ.map_target hyt, ?_⟩
    rw [← hyz, φ.right_inv hyt, ← mem_closedBall_iff_norm]; exact hy
  have hfront : ∀ z ∈ frontier S, φ.symm (H z) = F z := by
    intro z hz
    rw [hSopen.frontier_eq] at hz
    obtain ⟨hz1, hz2⟩ := hz
    obtain ⟨hzs, hzR⟩ := hcl' z hz1
    have hR' : ‖φ (F z) - c‖ = R := le_antisymm hzR (not_lt.1 fun h => hz2 ⟨hzs, h⟩)
    have hlam0 : lam z = 0 := chartCutoff_eq_zero h14 (Or.inr (by rw [hR']; linarith))
    rw [hH_zero z hlam0, φ.left_inv hzs]
  have hHcont : ContinuousOn H (closure S) := by
    have hFc : ContinuousOn (fun z => φ (F z)) (closure S) :=
      φ.continuousOn.comp hF.continuousOn fun z hz => (hcl' z hz).1
    exact ((continuousOn_const.sub hlamc.continuousOn).smul hFc).add
      (hlamc.continuousOn.smul ((continuousOn_const.add hg.continuousOn).sub continuousOn_const))
  have hHmaps : MapsTo H (closure S) φ.target := by
    intro z hz
    by_cases hzS : z ∈ S
    · exact hHtarget z hzS
    · obtain ⟨hzs, hzR⟩ := hcl' z hz
      have hR' : ‖φ (F z) - c‖ = R := le_antisymm hzR (not_lt.1 fun h => hzS ⟨hzs, h⟩)
      have hlam0 : lam z = 0 := chartCutoff_eq_zero h14 (Or.inr (by rw [hR']; linarith))
      rw [hH_zero z hlam0]
      exact φ.map_source hzs
  have hsymmH : ContinuousOn (fun z => φ.symm (H z)) (closure S) :=
    φ.continuousOn_symm.comp hHcont hHmaps
  refine ⟨fun z => if F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R then φ.symm (H z) else F z,
    ?_, ?_, ?_, ?_⟩
  · exact continuous_if hfront hsymmH hF.continuousOn
  · intro z hz
    by_cases hzS : F z ∈ φ.source ∧ ‖φ (F z) - c‖ < R
    · dsimp only at hz
      rw [ite_eq_left hzS] at hz
      have h1 := congrArg φ hz
      rw [φ.right_inv (hHtarget z hzS), φ.right_inv hc] at h1
      exact (hHball z hzS).2 h1
    · dsimp only at hz
      rw [ite_eq_right hzS] at hz
      refine hzS ⟨hz ▸ φ.map_target hc, ?_⟩
      rw [hz, φ.right_inv hc, sub_self, norm_zero]; exact hR
  · intro z hz
    exact ite_eq_right hz
  · intro z hz
    dsimp only
    rw [ite_eq_left hz]
    refine ⟨φ.map_target (hHtarget z hz), ?_⟩
    rw [φ.right_inv (hHtarget z hz)]
    exact (hHball z hz).1

section ChartDisk

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isChartDisk.exists_push_off_on_compact [T2Space M] (hmn : m < n) {e : Disk n → M}
    (he : isChartDisk e) {F : K → M} (hF : Continuous F) :
    ∃ F' : K → M, Continuous F' ∧ (∀ z, F' z ∉ e '' diskInterior n) ∧
      (∀ z, F z ∉ e '' diskInterior n → F' z = F z) ∧
      (∀ z, F z ∈ e '' diskInterior n → F' z ∈ range e) := by
  obtain ⟨φ, c, r, -, hr, hsub, he⟩ := he
  simp only [mem_image_diskInterior_iff hr hsub he, mem_range_chartDisk_iff hr hsub he]
  obtain ⟨F₁, hF₁, hne, hfix, hin⟩ := exists_push_off_center_on_compact hmn φ hr hsub hF
  obtain ⟨ret, hret, hretfix, hretin⟩ := exists_chartBall_retraction φ hr hsub
  refine ⟨fun z => ret (F₁ z), hret.comp_continuous hF₁ fun z => hne z, ?_, ?_, ?_⟩
  · intro z hz
    dsimp only at hz
    by_cases h₁ : F₁ z ∈ φ.source ∧ ‖φ (F₁ z) - c‖ < r
    · have := (hretin (F₁ z) (hne z) h₁).2
      rw [this] at hz
      exact lt_irrefl _ hz.2
    · rw [hretfix _ h₁] at hz
      exact h₁ hz
  · intro z hz
    dsimp only
    rw [hfix z hz, hretfix _ hz]
  · intro z hz
    dsimp only
    by_cases h₁ : F₁ z ∈ φ.source ∧ ‖φ (F₁ z) - c‖ < r
    · obtain ⟨h1, h2⟩ := hretin (F₁ z) (hne z) h₁
      exact ⟨h1, h2.le⟩
    · rw [hretfix _ h₁]
      exact ⟨(hin z hz).1, (hin z hz).2.le⟩

end ChartDisk

section DiskExtensions

variable [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

theorem isChartDisk.exists_disk_extension_avoiding {k : ℕ} (hkn : k + 2 ≤ n)
    {e : Disk n → M} (he : isChartDisk e)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, M))
    (hf : f.Nullhomotopic) (havoid : ∀ x, f x ∉ e '' diskInterior n) :
    ∃ F : C(Disk (k + 1), M), (∀ x, F x ∉ e '' diskInterior n) ∧
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) := by
  obtain ⟨G, hG⟩ := exists_disk_extension_of_nullhomotopic f hf
  obtain ⟨F, hF, hFavoid, hFfix, _⟩ := he.exists_push_off_on_compact
    (by omega : k + 1 < n) G.continuous
  refine ⟨⟨F, hF⟩, hFavoid, fun x => ?_⟩
  have hx : G x.1 ∉ e '' diskInterior n := by
    rw [hG x]
    exact havoid _
  exact (hFfix x.1 hx).trans (hG x)

theorem isChartDisk.exists_disk_extension_compl_of_homotopyEquiv_sphere {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, ((e '' diskInterior n)ᶜ : Set M))) :
    ∃ F : C(Disk (k + 1), ((e '' diskInterior n)ᶜ : Set M)),
      ∀ x : diskSphere (k + 1), F x.1 = f (diskSphereHomeomorph (k + 1) x) := by
  let fM : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, M) :=
    ⟨fun x => (f x).1, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨G, hG, hboundary⟩ := he.exists_disk_extension_avoiding hkn fM
    (nullhomotopic_map_of_homotopyEquiv_sphere hkn eM fM) (fun x => (f x).2)
  refine ⟨⟨fun x => ⟨G x, hG x⟩, G.continuous.subtype_mk _⟩, fun x => ?_⟩
  exact Subtype.ext (hboundary x)

theorem isChartDisk.nullhomotopic_map_compl_of_homotopyEquiv_sphere {k : ℕ}
    (hkn : k + 2 ≤ n) {e : Disk n → M} (he : isChartDisk e)
    (eM : M ≃ₕ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (f : C(sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1, ((e '' diskInterior n)ᶜ : Set M))) :
    f.Nullhomotopic := by
  obtain ⟨F, hF⟩ := he.exists_disk_extension_compl_of_homotopyEquiv_sphere hkn eM f
  exact nullhomotopic_of_disk_extension f F hF

end DiskExtensions

end DifferentialGeometry.Topology
