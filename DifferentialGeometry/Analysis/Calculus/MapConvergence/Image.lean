import DifferentialGeometry.Analysis.Calculus.Inverse.MovingImplicit

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem eventually_closedBall_subset_image
    {U : Set E} (hU : IsOpen U) {f : ℕ → E → E}
    (hf : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) L)
    (hconv : MapCInfConvergenceOnCompacts U f id)
    {x : E} (hx : x ∈ U) :
    ∃ δ > 0, ∀ᶠ n in atTop, Metric.closedBall x δ ⊆ f n '' U := by
  classical
  obtain ⟨q, hq, hqU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let R : ℝ := q / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRq : R < q := by dsimp [R]; linarith
  have hLU : Metric.closedBall x R ⊆ U :=
    (Metric.closedBall_subset_ball hRq).trans hqU
  let D : Set E := Metric.ball x R
  have hDU : D ⊆ U := Metric.ball_subset_closedBall.trans hLU
  have hreg : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) D :=
    (hf (Metric.closedBall x R) (isCompact_closedBall x R) hLU).mono
      fun _ hn => hn.mono Metric.ball_subset_closedBall
  let g : ℕ → E → E := fun n => if ContDiffOn ℝ ∞ (f n) D then f n else id
  have hg : ∀ n, ContDiffOn ℝ ∞ (g n) D := by
    intro n
    dsimp only [g]
    split_ifs with hn
    · exact hn
    · exact contDiffOn_id
  have hgeq : ∀ᶠ n in atTop, g n = f n := by
    filter_upwards [hreg] with n hn
    simp only [g, if_pos hn]
  have hconvD : MapCInfConvergenceOnCompacts D f id :=
    fun L hL hLD p => hconv L hL (hLD.trans hDU) p
  have hgconv : MapCInfConvergenceOnCompacts D g id :=
    hconvD.congr_eventually Metric.isOpen_ball
      (hgeq.mono fun _ hn _ _ => congrFun hn _) (fun _ _ => rfl)
  obtain ⟨r, δ, _, hrR, hδ, N, hN⟩ := Analysis.exists_preim_tail
    Metric.isOpen_ball hg contDiffOn_id hgconv (Metric.mem_ball_self hR)
    (A := ContinuousLinearEquiv.refl ℝ E) (by simpa using hasStrictFDerivAt_id x) hR
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hgeq, eventually_ge_atTop N] with n hn hnN
  intro y hy
  obtain ⟨z, hz, hzy⟩ := (hN n hnN).2 y hy
  exact ⟨z, hDU (Metric.closedBall_subset_ball hrR hz), hn ▸ hzy⟩

private theorem eventually_subset_image_of_compact_local_smoothness
    {U K : Set E} (hU : IsOpen U) {f : ℕ → E → E}
    (hconv : MapCInfConvergenceOnCompacts U f id)
    (hf : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) L)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᶠ n in atTop, K ⊆ f n '' U := by
  classical
  have hlocal : ∀ x : K, ∃ δ > 0,
      ∀ᶠ n in atTop, Metric.closedBall (x : E) δ ⊆ f n '' U :=
    fun x => eventually_closedBall_subset_image hU hf hconv (hKU x.2)
  choose δ hδ hcap using hlocal
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : E) (δ x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hδ ⟨x, hx⟩)⟩)
  have hcaps : ∀ᶠ n in atTop, ∀ x ∈ s,
      Metric.closedBall (x : E) (δ x) ⊆ f n '' U :=
    (eventually_all_finset s).mpr fun x _ => hcap x
  filter_upwards [hcaps] with n hn x hx
  obtain ⟨z, hxz⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨hzs, hxz⟩ := mem_iUnion.mp hxz
  exact hn z hzs (Metric.ball_subset_closedBall hxz)

theorem MapCInfConvergenceOnCompacts.exists_compact_eventually_subset_image
    {U K : Set E} (hU : IsOpen U) {f : ℕ → E → E}
    (hconv : MapCInfConvergenceOnCompacts U f id)
    (hf : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) L)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : Set E, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
      ∀ᶠ n in atTop, K ⊆ f n '' L := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have hIU : interior L ⊆ U := interior_subset.trans hLU
  have hconvI : MapCInfConvergenceOnCompacts (interior L) f id :=
    fun A hA hAI p => hconv A hA (hAI.trans hIU) p
  have hcap := eventually_subset_image_of_compact_local_smoothness isOpen_interior hconvI
    (fun A hA hAI => hf A hA (hAI.trans hIU)) hK hKL
  exact ⟨L, hL, hKL, hLU, hcap.mono fun _ hn => hn.trans (image_mono interior_subset)⟩

theorem MapCInfConvergenceOnCompacts.eventually_subset_image
    {U K : Set E} (hU : IsOpen U) {f : ℕ → E → E}
    (hconv : MapCInfConvergenceOnCompacts U f id)
    (hf : ∀ L : Set E, IsCompact L → L ⊆ U →
      ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (f n) L)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᶠ n in atTop, K ⊆ f n '' U := by
  obtain ⟨L, _, _, hLU, hcap⟩ :=
    hconv.exists_compact_eventually_subset_image hU hf hK hKU
  exact hcap.mono fun _ hn => hn.trans (image_mono hLU)

end DifferentialGeometry.CheegerGromovCompactness

end
