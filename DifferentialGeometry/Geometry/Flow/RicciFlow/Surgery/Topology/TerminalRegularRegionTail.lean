import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.IncomingSlabCapBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCorePresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open DifferentialGeometry.Topology

def boundaryFrameReversingData (P : OrientedThreeStage.{u})
    (T : SphericalTubeSystem P.toClosedOrientedManifold)
    (attaching : T.Boundary → Sphere 2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Sphere 2) : Prop :=
  ∀ (b : T.Boundary) (z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (v w : TangentSpace (𝓡 2) z),
    let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        P.toClosedOrientedManifold.Carrier :=
      T.boundarySphere b ∘ attaching b
    let _ : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
      inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin 3)))
    let d := mfderiv (𝓡 2) (𝓡 3) f z
    let e := mfderiv (𝓡 2) (𝓡 3)
      (Subtype.val : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 →
        EuclideanSpace ℝ (Fin 3)) z
    (0 < ((P.toClosedOrientedManifold.orientation.orientation (f z)).someBasis (by
      change Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
      simp)).det
      (Fin.cons (T.outwardVector b (attaching b z))
          (Fin.cons (d v) (Fin.cons (d w) ![])))) ↔
      (if b.2 then (1 : ℝ) else -1) *
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det
          (Fin.cons z.1 (Fin.cons (e v) (Fin.cons (e w) ![]))) < 0

namespace OrientedThreeStage

variable {P : OrientedThreeStage.{u}}

namespace IncomingSlab

variable {a s : ℝ} (G : P.IncomingSlab a s)

def HasTerminalCurvatureBound : Prop :=
  ∃ a' ∈ Ico a s, ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : P.Carrier, ∀ t ∈ Ico a' s, G.riemannNorm t x ≤ K

theorem terminalRegularRegion_eq_univ_of_hasTerminalCurvatureBound
    (h : G.HasTerminalCurvatureBound) : G.terminalRegularRegion = univ := by
  obtain ⟨a', ha', K, hK, hb⟩ := h
  apply eq_univ_of_forall
  intro x
  exact ⟨univ, isOpen_univ, mem_univ x, a', ha', K, hK, fun y _ t ht => hb y t ht⟩

theorem hasTerminalCurvatureBound_of_terminalRegularRegion_eq_univ
    (h : G.terminalRegularRegion = univ) : G.HasTerminalCurvatureBound := by
  classical
  have hmem : ∀ x : P.Carrier, x ∈ G.terminalRegularRegion := fun x => by
    rw [h]
    exact mem_univ x
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
  refine ⟨A oA, hA oA hoA, B oB, hB oB hoB, fun y t ht => ?_⟩
  have hy : y ∈ ⋃ i ∈ tcover, U i := htcover (Set.mem_univ y)
  rw [Set.mem_iUnion] at hy
  obtain ⟨x, hy⟩ := hy
  rw [Set.mem_iUnion] at hy
  obtain ⟨hx, hyx⟩ := hy
  have hsome : some x ∈ S := Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hx)
  exact (hbound x y hyx t ⟨(hAmax (some x) hsome).trans ht.1, ht.2⟩).trans
    (hBmax (some x) hsome)

theorem terminalRegularRegion_eq_univ_iff_hasTerminalCurvatureBound :
    G.terminalRegularRegion = univ ↔ G.HasTerminalCurvatureBound :=
  ⟨G.hasTerminalCurvatureBound_of_terminalRegularRegion_eq_univ,
    G.terminalRegularRegion_eq_univ_of_hasTerminalCurvatureBound⟩

theorem not_hasTerminalCurvatureBound_of_singularEndpoint (h : G.SingularEndpoint) :
    ¬ G.HasTerminalCurvatureBound := by
  rintro ⟨a', ha', K, hK, hb⟩
  obtain ⟨t, ht, x, hx⟩ := h (K + 1) (by linarith) a' ha'
  exact absurd (hb x t ⟨ht.1.le, ht.2⟩) (not_le.mpr (by linarith))

theorem hasTerminalCurvatureBound_of_forall_bound_Icc
    {a' : ℝ} (ha' : a' ∈ Ico a s) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x : P.Carrier, ∀ t ∈ Icc a' s, G.riemannNorm t x ≤ K) :
    G.HasTerminalCurvatureBound :=
  ⟨a', ha', K, hK, fun x t ht => h x t ⟨ht.1, ht.2.le⟩⟩

theorem le_riemannNorm_at_right_of_hasTerminalCurvatureBound
    (h : G.HasTerminalCurvatureBound) {x : P.Carrier}
    (hcont : Tendsto (fun t : ℝ => G.riemannNorm t x) (𝓝[<] s) (𝓝 (G.riemannNorm s x))) :
    ∃ K : ℝ, 0 ≤ K ∧ G.riemannNorm s x ≤ K := by
  obtain ⟨a', ha', K, hK, hb⟩ := h
  exact ⟨K, hK, le_of_tendsto hcont (by
    filter_upwards [Ioo_mem_nhdsLT ha'.2] with t ht
    exact hb x t ⟨ht.1.le, ht.2⟩)⟩

theorem subset_terminalRegularRegion_of_forall_bound_Icc
    {U : Set P.Carrier} (hU : IsOpen U) {a' : ℝ} (ha' : a' ∈ Ico a s) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ y ∈ U, ∀ t ∈ Icc a' s, G.riemannNorm t y ≤ K) :
    U ⊆ G.terminalRegularRegion := by
  intro y hy
  exact ⟨U, hU, hy, a', ha', K, hK, fun z hz t ht => h z hz t ⟨ht.1, ht.2.le⟩⟩

theorem mapsTo_terminalRegularRegion_of_hasTerminalCurvatureBound
    (h : G.HasTerminalCurvatureBound) {A : Type*} (f : A → P.Carrier) (u : Set A) :
    MapsTo f u G.terminalRegularRegion := by
  rw [G.terminalRegularRegion_eq_univ_of_hasTerminalCurvatureBound h]
  exact fun _ _ => Set.mem_univ _

end IncomingSlab

theorem ClosedSlab.hasTerminalCurvatureBound {u v : ℝ} (G : P.ClosedSlab u v) :
    (G.restrictIncoming le_rfl G.lt le_rfl).HasTerminalCurvatureBound :=
  (IncomingSlab.terminalRegularRegion_eq_univ_iff_hasTerminalCurvatureBound _).mp
    (G.terminalRegularRegion_eq_univ P)

theorem IncomingSlab.hasTerminalCurvatureBound_of_eq_closedSlabRestriction {u v : ℝ}
    (H : P.ClosedSlab u v) {G' : P.IncomingSlab u v}
    (h : H.restrictIncoming le_rfl H.lt le_rfl = G') : G'.HasTerminalCurvatureBound :=
  h ▸ H.hasTerminalCurvatureBound

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}}

theorem retained_terminal_of_hasTerminalCurvatureBound (X : SmoothCutCapTransition P Q D N)
    {a s : ℝ} (G : P.IncomingSlab a s) (h : G.HasTerminalCurvatureBound) :
    ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore → x.1 ∈ G.terminalRegularRegion :=
  fun x _ => by
    rw [G.terminalRegularRegion_eq_univ_of_hasTerminalCurvatureBound h]
    exact Set.mem_univ x.1

theorem boundaryFrameReversing_of_isEmpty_index (X : SmoothCutCapTransition P Q D N)
    [IsEmpty X.trace.tubes.Index] : X.boundaryFrameReversing :=
  haveI : IsEmpty (SphericalTubeSystem.ofSmoothCutCapTransition X).Index := ‹_›
  fun b _ _ _ => isEmptyElim b.1

theorem boundaryFrameReversing_iff_data (X : SmoothCutCapTransition P Q D N) :
    X.boundaryFrameReversing ↔
      boundaryFrameReversingData P (SphericalTubeSystem.ofSmoothCutCapTransition X)
        X.attaching :=
  Iff.rfl

end SmoothCutCapTransition

end OrientedThreeStage

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
