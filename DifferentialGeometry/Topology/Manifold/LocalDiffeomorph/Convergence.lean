import DifferentialGeometry.Analysis.Calculus.MapConvergence.LocalInvertibility
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Coordinates

section

noncomputable section
open Set Filter Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff

variable {E G H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace Q] [ChartedSpace E Q]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]

theorem eventually_injOn_nhds_of_open_coordinate_convergence
    (U : TopologicalSpace.Opens E) (e : OpenPartialHomeomorph U Q)
    (he : e.source = univ)
    (hesmooth : ContMDiff (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ e)
    (V : TopologicalSpace.Opens Q)
    (c : ∀ n, PartialDiffeomorph (modelWithCornersSelf ℝ E) I E (M n) ∞)
    (F : ∀ n, Q → M n)
    (hF : ∀ n, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F n) V)
    (A : ℕ → E → E)
    (hA : MapCInfConvergenceOnCompacts (Subtype.val '' (e ⁻¹' (V : Set Q))) A id)
    (hcoords : ∀ n (z : U), A n z = (c n).symm (F n (e z)))
    (himage : ∀ L : Set E, IsCompact L → L ⊆ Subtype.val '' (e ⁻¹' (V : Set Q)) →
      ∀ᶠ n in atTop, ∀ z : U, (z : E) ∈ L → F n (e z) ∈ (c n).target)
    {z : U} (hzV : e z ∈ V) :
    ∃ W ∈ nhds (e z), ∀ᶠ n in atTop, InjOn (F n) W := by
  let Ω := Subtype.val '' (e ⁻¹' (V : Set Q))
  have hopen : IsOpen Ω := U.isOpen.isOpenMap_subtype_val _
    (V.isOpen.preimage (continuousOn_univ.mp (he ▸ e.continuousOn)))
  have hzΩ : (z : E) ∈ Ω := ⟨z, hzV, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z hzΩ
  let L := Metric.closedBall (z : E) (r / 2)
  let B := Metric.ball (z : E) (r / 2)
  have hLΩ : L ⊆ Ω := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hLΩ
  have hBU : B ⊆ (U : Set E) := by
    intro y hy
    obtain ⟨w, _, rfl⟩ := hBΩ hy
    exact w.property
  have hBV : ∀ (y : E) (hy : y ∈ B), e ⟨y, hBU hy⟩ ∈ V := by
    intro y hy
    obtain ⟨w, hw, hwval⟩ := hBΩ hy
    have hwEq : (⟨y, hBU hy⟩ : U) = w := Subtype.ext hwval.symm
    change e w ∈ V at hw
    simpa only [hwEq] using hw
  have htarget := himage L (isCompact_closedBall _ _) hLΩ
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℝ (A n) B := by
    filter_upwards [htarget] with n hn
    have hsm := DifferentialGeometry.Topology.Manifold.contDiffOn_of_open_coordinate_map
      U V.isOpen hesmooth (hF n) (c n) hBU hBV
      (fun y hy => hn ⟨y,hBU hy⟩ (Metric.ball_subset_closedBall hy)) (hcoords n)
    exact hsm.differentiableOn (by simp)
  have hAB : MapCInfConvergenceOnCompacts B A id :=
    fun K hK hKB p => hA K hK (hKB.trans hBΩ) p
  obtain ⟨S, hS, hinj⟩ := hAB.eventually_injOn_nhds Metric.isOpen_ball hdiff
    (Metric.mem_ball_self (by positivity))
  refine ⟨e '' (Subtype.val ⁻¹' S), e.image_mem_nhds (he.symm ▸ mem_univ z)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hS), ?_⟩
  filter_upwards [hinj] with n hn
  rintro a ⟨u, hu, rfl⟩ b ⟨v, hv, rfl⟩ heq
  have huv : (u : E) = v := hn hu hv (by rw [hcoords, hcoords, heq])
  exact congrArg e (Subtype.ext huv)

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

noncomputable section
open Set Filter Topology
namespace DifferentialGeometry.CheegerGromovCompactness
open scoped ContDiff

variable {E G H Q : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [CompleteSpace E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace H]
  {I : ModelWithCorners ℝ G H} [TopologicalSpace Q] [ChartedSpace E Q]
  {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]

theorem eventually_isLocalDiffeomorphOn_nhds_of_open_coordinate_convergence
    (U : TopologicalSpace.Opens E) (e : OpenPartialHomeomorph U Q)
    (he : e.source = univ)
    (helocal : IsLocalDiffeomorph (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ e)
    (V : TopologicalSpace.Opens Q)
    (c : ∀ n, PartialDiffeomorph (modelWithCornersSelf ℝ E) I E (M n) ∞)
    (F : ∀ n, Q → M n)
    (hF : ∀ n, ContMDiffOn (modelWithCornersSelf ℝ E) I ∞ (F n) V)
    (A : ℕ → E → E)
    (hA : MapCInfConvergenceOnCompacts (Subtype.val '' (e ⁻¹' (V : Set Q))) A id)
    (hcoords : ∀ n (z : U), A n z = (c n).symm (F n (e z)))
    (himage : ∀ L : Set E, IsCompact L → L ⊆ Subtype.val '' (e ⁻¹' (V : Set Q)) →
      ∀ᶠ n in atTop, ∀ z : U, (z : E) ∈ L → F n (e z) ∈ (c n).target)
    {z : U} (hzV : e z ∈ V) :
    ∃ W : Set Q, IsOpen W ∧ e z ∈ W ∧ W ⊆ V ∧
      ∀ᶠ n in atTop, IsLocalDiffeomorphOn (modelWithCornersSelf ℝ E) I ∞ (F n) W := by
  let Ω := Subtype.val '' (e ⁻¹' (V : Set Q))
  have hopen : IsOpen Ω := U.isOpen.isOpenMap_subtype_val _
    (V.isOpen.preimage (continuousOn_univ.mp (he ▸ e.continuousOn)))
  have hzΩ : (z : E) ∈ Ω := ⟨z, hzV, rfl⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z hzΩ
  let L := Metric.closedBall (z : E) (r / 2)
  let B := Metric.ball (z : E) (r / 2)
  have hLΩ : L ⊆ Ω := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBΩ : B ⊆ Ω := Metric.ball_subset_closedBall.trans hLΩ
  have hBU : B ⊆ (U : Set E) := by
    intro y hy
    obtain ⟨w, _, rfl⟩ := hBΩ hy
    exact w.property
  have hBV : ∀ (y : E) (hy : y ∈ B), e ⟨y, hBU hy⟩ ∈ V := by
    intro y hy
    obtain ⟨w, hw, hwval⟩ := hBΩ hy
    have hwEq : (⟨y, hBU hy⟩ : U) = w := Subtype.ext hwval.symm
    change e w ∈ V at hw
    simpa only [hwEq] using hw
  have htarget := himage L (isCompact_closedBall _ _) hLΩ
  have hsmooth : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (A n) B := by
    filter_upwards [htarget] with n hn
    have hsm := DifferentialGeometry.Topology.Manifold.contDiffOn_of_open_coordinate_map
      U V.isOpen helocal.contMDiff (hF n) (c n) hBU hBV
      (fun y hy => hn ⟨y,hBU hy⟩ (Metric.ball_subset_closedBall hy)) (hcoords n)
    exact hsm
  have hAB : MapCInfConvergenceOnCompacts B A id :=
    fun K hK hKB p => hA K hK (hKB.trans hBΩ) p
  let L' := Metric.closedBall (z : E) (r / 4)
  let B' := Metric.ball (z : E) (r / 4)
  have hL'B : L' ⊆ B := Metric.closedBall_subset_ball (by linarith)
  have hB'U : B' ⊆ (U : Set E) := Metric.ball_subset_closedBall.trans (hL'B.trans hBU)
  have hlocal := hAB.eventually_isLocalDiffeomorphOn Metric.isOpen_ball
    (isCompact_closedBall _ _) hL'B hsmooth
  let W := e '' (Subtype.val ⁻¹' B')
  have hWopen : IsOpen W := e.isOpen_image_of_subset_source
    (Metric.isOpen_ball.preimage continuous_subtype_val) (by rw [he]; exact subset_univ _)
  refine ⟨W, hWopen, ⟨z, Metric.mem_ball_self (by positivity), rfl⟩, ?_, ?_⟩
  · rintro q ⟨u, hu, rfl⟩
    exact hBV u (hL'B (Metric.ball_subset_closedBall hu))
  · filter_upwards [hlocal, htarget] with n hn ht
    rintro ⟨q, ⟨u, hu, rfl⟩⟩
    have huB : (u : E) ∈ B := hL'B (Metric.ball_subset_closedBall hu)
    have huV : e u ∈ V := hBV u huB
    apply IsLocalDiffeomorphAt.of_open_coordinate_map U (helocal u) (c n)
      (ht u (Metric.ball_subset_closedBall huB))
      ((hF n).contMDiffAt (V.isOpen.mem_nhds huV)).continuousAt
      (Filter.Eventually.of_forall (hcoords n))
    exact hn ⟨u, Metric.ball_subset_closedBall hu⟩

end DifferentialGeometry.CheegerGromovCompactness

end

end
