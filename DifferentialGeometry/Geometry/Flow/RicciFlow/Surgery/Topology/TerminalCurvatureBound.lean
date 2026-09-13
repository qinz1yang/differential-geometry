import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TerminalRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTerminalConvergence

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ D.carrier) :
    terminalRegularRegion S.base.metric a b = ⊤ := by
  obtain ⟨C, _hC, hbound⟩ :=
    exists_curvature_bound_on_carrier_interval_of_isSolutionOn (I := I) S hS hsub
  refine terminalRegularRegion_eq_top_of_uniform_bound (I := I) S.base.metric a b hab
    (Real.sqrt C) (Real.sqrt_nonneg C) (fun t ht y => ?_)
  refine Real.sqrt_le_sqrt ?_
  simpa only [SolutionOn.family_metric, metricRm04_apply]
    using hbound t (Ico_subset_Icc_self ht) y

theorem mapsTo_terminalRegularRegion_of_isSolutionOn_closedInterval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ D.carrier)
    {A : Type*} (f : A → M) (u : Set A) :
    MapsTo f u (terminalRegularRegion S.base.metric a b) := by
  rw [terminalRegularRegion_eq_top_of_isSolutionOn_closedInterval S hS hab hsub]
  exact fun _ _ => Set.mem_univ _

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

theorem ClosedSlab.mem_terminalRegularRegion {u v : ℝ} (G : P.ClosedSlab u v)
    (x : P.Carrier) :
    x ∈ (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularRegion := by
  rw [G.terminalRegularRegion_eq_univ P]
  exact Set.mem_univ x

theorem ClosedSlab.mapsTo_retainedCore {u v : ℝ} {Q D N : OrientedThreeStage.{u}}
    (X : SmoothCutCapTransition P Q D N) (G : P.ClosedSlab u v) :
    MapsTo (Subtype.val : X.trace.tubes.core → P.Carrier) X.trace.retainedCore
      (G.restrictIncoming le_rfl G.lt le_rfl).terminalRegularRegion :=
  fun _ _ => G.mem_terminalRegularRegion _

theorem IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint {a s : ℝ}
    (G : P.IncomingSlab a s) (h : G.SingularEndpoint) :
    G.terminalRegularRegion ≠ Set.univ := by
  classical
  intro htop
  have hmem : ∀ x : P.Carrier, x ∈ G.terminalRegularRegion := fun x => by
    rw [htop]
    exact Set.mem_univ x
  simp only [IncomingSlab.terminalRegularRegion, Set.mem_ofPred_eq] at hmem
  have hmem' : ∀ x : P.Carrier, ∃ (U : Set P.Carrier) (a' K : ℝ),
      IsOpen U ∧ x ∈ U ∧ a' ∈ Ico a s ∧ 0 ≤ K ∧
        ∀ y ∈ U, ∀ t ∈ Ico a' s, G.riemannNorm t y ≤ K := by
    intro x
    obtain ⟨U, hU, hxU, a', ha', K, hK, hb⟩ := hmem x
    exact ⟨U, a', K, hU, hxU, ha', hK, hb⟩
  choose U a' K hU hxU ha' hK hbound using hmem'
  have hcover : (Set.univ : Set P.Carrier) ⊆ ⋃ x, U x :=
    fun y _ => Set.mem_iUnion.mpr ⟨y, hxU y⟩
  obtain ⟨tcover, htcover⟩ := isCompact_univ.elim_finite_subcover U hU hcover
  let S : Finset (Option P.Carrier) := insert none (tcover.image some)
  have hSne : S.Nonempty := ⟨none, by simp [S]⟩
  let A : Option P.Carrier → ℝ := fun o => o.elim a a'
  let B : Option P.Carrier → ℝ := fun o => o.elim 0 K
  have hA : ∀ o ∈ S, A o ∈ Ico a s := by
    intro o _
    rcases o with _ | x
    · exact ⟨le_rfl, G.lt⟩
    · exact ha' x
  have hB : ∀ o ∈ S, 0 ≤ B o := by
    intro o _
    rcases o with _ | x
    · exact le_rfl
    · exact hK x
  obtain ⟨oA, hoA, hAmax⟩ := S.exists_max_image A hSne
  obtain ⟨oB, hoB, hBmax⟩ := S.exists_max_image B hSne
  let a₀ : ℝ := A oA
  let K₀ : ℝ := B oB
  have ha₀ : a₀ ∈ Ico a s := hA oA hoA
  have hK₀ : 0 ≤ K₀ := hB oB hoB
  have hbound₀ : ∀ y : P.Carrier, ∀ t ∈ Ico a₀ s, G.riemannNorm t y ≤ K₀ := by
    intro y t ht
    have hy : y ∈ ⋃ i ∈ tcover, U i := htcover (Set.mem_univ y)
    rw [Set.mem_iUnion] at hy
    obtain ⟨x, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨hx, hyx⟩ := hy
    have hsome : some x ∈ S :=
      Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hx)
    have h1 : a' x ≤ a₀ := hAmax (some x) hsome
    have h2 : K x ≤ K₀ := hBmax (some x) hsome
    exact (hbound x y hyx t ⟨h1.trans ht.1, ht.2⟩).trans h2
  obtain ⟨t, ht, y, hyt⟩ := h (K₀ + 1) (by linarith) a₀ ha₀
  exact absurd (hbound₀ y t ⟨ht.1.le, ht.2⟩)
    (not_le.mpr (lt_trans (lt_add_one K₀) hyt))

end OrientedThreeStage

theorem GeometricCutoffRecord.terminalRegularRegion_ne_univ
    {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
    (R : GeometricCutoffRecord H i parameters) :
    (H.event i).incoming.terminalRegularRegion ≠ Set.univ :=
  OrientedThreeStage.IncomingSlab.terminalRegularRegion_ne_univ_of_singularEndpoint _
    R.singular

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
