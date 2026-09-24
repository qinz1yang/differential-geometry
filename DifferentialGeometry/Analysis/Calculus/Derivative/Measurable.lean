import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.Analysis
variable {P : Type*} [TopologicalSpace P] [MeasurableSpace P] [OpensMeasurableSpace P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem measurable_fderiv_with_param_of_continuousOn
    {U : Set E} (hU : IsOpen U) {f : P → E → F}
    (hf : ContinuousOn f.uncurry (univ ×ˢ U)) :
    Measurable (fun p : P × U => fderiv ℝ (f p.1) p.2) := by
  classical
  have hlocal (x : U) : ∃ r : ℝ, 0 < r ∧ ∃ G : P → E → F,
      Continuous G.uncurry ∧ ∀ p y, y ∈ Metric.ball (x : E) r →
        fderiv ℝ (G p) y = fderiv ℝ (f p) y := by
    obtain ⟨r, hr, hrU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds x.property)
    obtain ⟨χ, hχone, _, hχsupp, _⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen (isCompact_closedBall (x : E) r) hU hrU
    let G : P → E → F := fun p y => χ y • f p y
    have hG : Continuous G.uncurry := by
      apply continuous_iff_continuousAt.mpr
      intro p
      by_cases hp : p.2 ∈ U
      · exact (χ.continuous.continuousAt.comp continuousAt_snd).smul
          ((hf p ⟨mem_univ _, hp⟩).continuousAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _, hp⟩))
      · have hn : p.2 ∉ tsupport χ := fun hx => hp (hχsupp hx)
        apply (continuousAt_const (y := (0 : F))).congr_of_eventuallyEq
        filter_upwards [continuous_snd.continuousAt.eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hn)] with q hq
        change χ q.2 • f q.1 q.2 = 0
        rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]
    refine ⟨r, hr, G, hG, ?_⟩
    intro p y hy
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    change χ z • f p z = f p z
    rw [hχone (Metric.ball_subset_closedBall hz), Pi.one_apply, one_smul]
  choose r hr G hG hsame using hlocal
  obtain ⟨s, hs, hcover⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover
    (fun x : U => Metric.ball (x : E) (r x)) (fun _ => Metric.isOpen_ball)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  let _ := hs.toEncodable
  have hm (x : U) : Measurable (fun p : P × U => fderiv ℝ (G x p.1) p.2) :=
    (measurable_fderiv_with_param ℝ (hG x)).comp
      (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  intro B hB
  have heq : (fun p : P × U => fderiv ℝ (f p.1) p.2) ⁻¹' B =
      ⋃ x : s, {p : P × U | (p.2 : E) ∈ Metric.ball ((x : U) : E) (r x)} ∩
        (fun p : P × U => fderiv ℝ (G x p.1) p.2) ⁻¹' B := by
    ext p
    constructor
    · intro hp
      obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp (hcover p.2.property)
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hpx, by
        change fderiv ℝ (G x p.1) p.2 ∈ B
        rw [hsame x p.1 p.2 hpx]
        exact hp⟩
    · intro hp
      obtain ⟨x, hpx, hx⟩ := mem_iUnion.mp hp
      change fderiv ℝ (G x p.1) p.2 ∈ B at hx
      rwa [hsame x p.1 p.2 hpx] at hx
  rw [heq]
  exact MeasurableSet.iUnion fun x : s =>
    ((Metric.isOpen_ball.measurableSet.preimage (measurable_subtype_coe.comp measurable_snd)).inter (hm x hB))
end DifferentialGeometry.Analysis
